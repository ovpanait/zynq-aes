#include <crypto/internal/skcipher.h>
#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/of_platform.h>
#include <linux/platform_device.h>

#include "zynqaes.h"

/* Assume only one device for now */
struct zynqaes_dev *zynqaes_dd;

static void zynqaes_set_key_bit(unsigned int key_len, struct zynqaes_reqctx_base *rctx)
{
	switch (key_len) {
	case AES_KEYSIZE_128:
		rctx->cmd |= ZYNQAES_KEY_128_FLAG;
		break;
	case AES_KEYSIZE_256:
		rctx->cmd |= ZYNQAES_KEY_256_FLAG;
		break;
	default:
		break;
	}
}

static struct zynqaes_dma_ctx *zynqaes_create_dma_ctx(struct zynqaes_reqctx_base *rctx)
{
	struct zynqaes_dma_ctx *dma_ctx;

	dma_ctx = kzalloc(sizeof(struct zynqaes_dma_ctx), GFP_ATOMIC);
	if (dma_ctx == NULL) {
		dev_err(zynqaes_dd->dev,
			"[%s:%d] tx: tx_buf: Allocating memory failed\n",
			__func__, __LINE__);

		goto err;
	}

	dma_ctx->rctx = rctx;

	return dma_ctx;

err:
	return NULL;
}

static void zynqaes_skcipher_dma_callback(void *data)
{
	struct zynqaes_dma_ctx *dma_ctx = data;
	struct zynqaes_skcipher_reqctx *rctx = container_of(dma_ctx->rctx,
			struct zynqaes_skcipher_reqctx, base);

	dma_unmap_sg(zynqaes_dd->dev, dma_ctx->tx_sg, dma_ctx->tx_nents,
			DMA_TO_DEVICE);
	dma_unmap_sg(zynqaes_dd->dev, dma_ctx->rx_sg, dma_ctx->rx_nents,
			DMA_FROM_DEVICE);

	crypto_finalize_skcipher_request(zynqaes_dd->engine, rctx->areq, 0);

	kfree(dma_ctx);
}

static int zynqaes_dma_op(struct zynqaes_dma_ctx *dma_ctx)
{
	struct dma_async_tx_descriptor *tx_chan_desc;
	struct dma_async_tx_descriptor *rx_chan_desc;
	unsigned int tx_sg_len;
	unsigned int rx_sg_len;
	int ret;

	/* Tx Channel */
	tx_sg_len = dma_map_sg(zynqaes_dd->dev, dma_ctx->tx_sg, dma_ctx->tx_nents, DMA_TO_DEVICE);
	if (!tx_sg_len) {
		dev_err(zynqaes_dd->dev, "[%s:%d] dma_map_sg: tx error\n",
					__func__, __LINE__);

		ret = -ENOMEM;
		goto err;
	}

	tx_chan_desc = dmaengine_prep_slave_sg(zynqaes_dd->tx_chan, dma_ctx->tx_sg,
					tx_sg_len, DMA_MEM_TO_DEV,
					DMA_CTRL_ACK);
	if (!tx_chan_desc) {
		dev_err(zynqaes_dd->dev, "[%s:%d] dmaengine_prep_slave_sg error\n",
					__func__, __LINE__);

		ret = -ECOMM;
		goto err;
	}

	dma_ctx->tx_cookie = dmaengine_submit(tx_chan_desc);
	if (dma_submit_error(dma_ctx->tx_cookie)) {
		dev_err(zynqaes_dd->dev, "[%s:%d] tx_cookie: dmaengine_submit error\n",
					__func__, __LINE__);

		ret = -ECOMM;
		goto err;
	}

	dma_async_issue_pending(zynqaes_dd->tx_chan);

	/* Rx Channel */
	rx_sg_len = dma_map_sg(zynqaes_dd->dev, dma_ctx->rx_sg, dma_ctx->rx_nents, DMA_FROM_DEVICE);
	if (rx_sg_len == 0) {
		dev_err(zynqaes_dd->dev, "[%s:%d] dma_map_sg: rx error\n",
					__func__, __LINE__);

		ret = -ENOMEM;
		goto err;
	}

	rx_chan_desc = dmaengine_prep_slave_sg(zynqaes_dd->rx_chan, dma_ctx->rx_sg,
					rx_sg_len, DMA_DEV_TO_MEM,
					DMA_CTRL_ACK | DMA_PREP_INTERRUPT);
	if (!rx_chan_desc) {
		dev_err(zynqaes_dd->dev, "[%s:%d] dmaengine_prep_slave_sg error\n",
					__func__, __LINE__);

		ret = -ECOMM;
		goto err;
	}

	rx_chan_desc->callback = dma_ctx->callback;
	rx_chan_desc->callback_param = dma_ctx;

	dma_ctx->rx_cookie = dmaengine_submit(rx_chan_desc);
	if (dma_submit_error(dma_ctx->rx_cookie)) {
		dev_err(zynqaes_dd->dev, "[%s:%d] rx_cookie: dmaengine_submit error\n",
					__func__, __LINE__);

		ret = -ECOMM;
		goto err;
	}

	dma_async_issue_pending(zynqaes_dd->rx_chan);

	return 0;

err:
	return ret;
}

static int zynqaes_skcipher_enqueue_next_dma_op(struct zynqaes_skcipher_reqctx *rctx)
{
	struct zynqaes_ctx *ctx;
	struct zynqaes_dma_ctx *dma_ctx;
	struct skcipher_request *areq;
	int ret;
	unsigned int nsg;

	struct scatterlist *sg;
	unsigned int src_nbytes;

	ctx = rctx->base.ctx;
	areq = rctx->areq;

	dma_ctx = zynqaes_create_dma_ctx(&rctx->base);
	if (dma_ctx == NULL) {
		dev_err(zynqaes_dd->dev, "[%s:%d] zynqaes_create_dma_ctx failed.",
					__func__, __LINE__);

		goto out_err;
	}

	nsg = rctx->base.ivsize ? 4 : 3;

	sg_init_table(dma_ctx->tx_sg, nsg);
	sg_set_buf(&dma_ctx->tx_sg[0], &rctx->base.cmd, sizeof(rctx->base.cmd));
	sg_set_buf(&dma_ctx->tx_sg[1], ctx->key, ctx->key_len);
	if (rctx->base.ivsize) {
		sg_set_buf(&dma_ctx->tx_sg[2], rctx->base.iv, AES_BLOCK_SIZE);
	}
	sg_chain(dma_ctx->tx_sg, nsg, areq->src);

	/*
	 * In ipsec, the last scatterlist has 12 extra bytes (ESP authenc. data).
	 * Since the hw expects rctx->nbytes in total, resize it so the total 
	 * scatterlist array length is rctx->nbytes.
	 */
	src_nbytes = 0;
	for (sg = areq->src; sg; sg = sg_next(sg)) {
		++dma_ctx->tx_nents;
		src_nbytes += sg->length;

		if (sg_is_last(sg) && (src_nbytes > rctx->nbytes)) {
			sg->length -= (src_nbytes - rctx->nbytes);
		}
	}

	dma_ctx->rx_sg = areq->dst;
	dma_ctx->rx_nents = sg_nents(dma_ctx->rx_sg);
	dma_ctx->tx_nents += nsg - 1;

	dma_ctx->callback = zynqaes_skcipher_dma_callback;

	dev_dbg(zynqaes_dd->dev, "[%s:%d] dma_ctx->tx_nents: %d\n",
			__func__, __LINE__, dma_ctx->tx_nents);
	dev_dbg(zynqaes_dd->dev, "[%s:%d] dma_ctx->rx_nents: %d\n",
			__func__, __LINE__, dma_ctx->rx_nents);

	ret = zynqaes_dma_op(dma_ctx);
	if (ret) {
		dev_err(zynqaes_dd->dev, "[%s:%d] zynqaes_dma_op failed with: %d",
					__func__, __LINE__, ret);
		goto free_dma_ctx;
	}

	return 0;

free_dma_ctx:
	kfree(dma_ctx);

out_err:
	return ret;
}

static int zynqaes_skcipher_crypt_req(struct crypto_engine *engine,
			     void *req)
{
	struct skcipher_request *areq = container_of(req, struct skcipher_request, base);
	struct crypto_skcipher *cipher = crypto_skcipher_reqtfm(areq);
	struct crypto_tfm *tfm = crypto_skcipher_tfm(cipher);
	struct zynqaes_ctx *ctx = crypto_tfm_ctx(tfm);
	struct zynqaes_skcipher_reqctx *rctx = skcipher_request_ctx(areq);

	int ret;

	rctx->base.ctx = ctx;
	rctx->base.ivsize = crypto_skcipher_ivsize(cipher);

	rctx->areq = areq;
	rctx->nbytes = areq->cryptlen;

	zynqaes_set_key_bit(ctx->key_len, &rctx->base);

	dev_dbg(zynqaes_dd->dev, "[%s:%d] rctx->nbytes: %u\n",
				__func__, __LINE__, rctx->nbytes);
	dev_dbg(zynqaes_dd->dev, "[%s:%d] rctx->cmd: %x\n",
				__func__, __LINE__, rctx->base.cmd);

	if (rctx->base.ivsize) {
		memcpy(rctx->base.iv, areq->iv, rctx->base.ivsize);
	}

	ret = zynqaes_skcipher_enqueue_next_dma_op(rctx);
	if (ret) {
		dev_err(zynqaes_dd->dev, "[%s:%d] zynqaes_dma_op failed with: %d",
					__func__, __LINE__, ret);
		goto out;
	}

	return 0;

out:
	return ret;
}

static int zynqaes_skcipher_crypt(struct skcipher_request *areq, const u32 cmd)
{
	struct zynqaes_skcipher_reqctx *rctx = skcipher_request_ctx(areq);

	dev_dbg(zynqaes_dd->dev, "[%s:%d] Entering function\n",
				__func__, __LINE__);

	rctx->base.cmd = cmd;

	return crypto_transfer_skcipher_request_to_engine(zynqaes_dd->engine, areq);
}

static int zynqaes_setkey(struct zynqaes_ctx *ctx, const u8 *key,
			  unsigned int len)
{
	int ret = 0;

	dev_dbg(zynqaes_dd->dev, "[%s:%d] Entering function\n",
				__func__, __LINE__);

	switch (len) {
	case AES_KEYSIZE_128:
	case AES_KEYSIZE_256:
		ctx->key_len = len;
		memcpy(ctx->key, key, len);

		break;
	case AES_KEYSIZE_192:
		dev_info(zynqaes_dd->dev,
			"[%s:%d] 192-bit keys not supported!",
			__func__, __LINE__);

		ret = -ENOTSUPP;
		break;
	default:
		dev_err(zynqaes_dd->dev,
			"[%s:%d] Invalid key size! (must be 128/192/256 bits)",
			__func__, __LINE__);

		ret = -EINVAL;
	}

	return ret;
}

static int zynqaes_skcipher_setkey(struct crypto_skcipher *tfm, const u8 *key,
				   unsigned int len)
{
	struct zynqaes_ctx *ctx = crypto_skcipher_ctx(tfm);

	return zynqaes_setkey(ctx, key, len);
}

static int zynqaes_ecb_encrypt(struct skcipher_request *areq)
{
	return zynqaes_skcipher_crypt(areq, ZYNQAES_ECB_ENCRYPT);
}

static int zynqaes_ecb_decrypt(struct skcipher_request *areq)
{
	return zynqaes_skcipher_crypt(areq, ZYNQAES_ECB_DECRYPT);
}

static int zynqaes_cbc_encrypt(struct skcipher_request *areq)
{
	return zynqaes_skcipher_crypt(areq, ZYNQAES_CBC_ENCRYPT);
}

static int zynqaes_cbc_decrypt(struct skcipher_request *areq)
{
	return zynqaes_skcipher_crypt(areq, ZYNQAES_CBC_DECRYPT);
}

static int zynqaes_pcbc_encrypt(struct skcipher_request *areq)
{
	return zynqaes_skcipher_crypt(areq, ZYNQAES_PCBC_ENCRYPT);
}

static int zynqaes_pcbc_decrypt(struct skcipher_request *areq)
{
	return zynqaes_skcipher_crypt(areq, ZYNQAES_PCBC_DECRYPT);
}

static int zynqaes_ctr_encrypt(struct skcipher_request *areq)
{
	return zynqaes_skcipher_crypt(areq, ZYNQAES_CTR_ENCRYPT);
}

static int zynqaes_ctr_decrypt(struct skcipher_request *areq)
{
	return zynqaes_skcipher_crypt(areq, ZYNQAES_CTR_DECRYPT);
}

static int zynqaes_cfb_encrypt(struct skcipher_request *areq)
{
	return zynqaes_skcipher_crypt(areq, ZYNQAES_CFB_ENCRYPT);
}

static int zynqaes_cfb_decrypt(struct skcipher_request *areq)
{
	return zynqaes_skcipher_crypt(areq, ZYNQAES_CFB_DECRYPT);
}

static int zynqaes_ofb_encrypt(struct skcipher_request *areq)
{
	return zynqaes_skcipher_crypt(areq, ZYNQAES_OFB_ENCRYPT);
}

static int zynqaes_ofb_decrypt(struct skcipher_request *areq)
{
	return zynqaes_skcipher_crypt(areq, ZYNQAES_OFB_DECRYPT);
}

static int zynqaes_skcipher_init(struct crypto_skcipher *tfm)
{
	struct zynqaes_ctx *ctx = crypto_skcipher_ctx(tfm);

	crypto_skcipher_set_reqsize(tfm, sizeof(struct zynqaes_skcipher_reqctx));

	ctx->enginectx.op.prepare_request = NULL;
	ctx->enginectx.op.unprepare_request = NULL;
	ctx->enginectx.op.do_one_request = zynqaes_skcipher_crypt_req;

	return 0;
}

static struct skcipher_alg zynqaes_ecb_alg = {
	.base.cra_name		=	"ecb(aes)",
	.base.cra_driver_name	=	"zynqaes-ecb",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	AES_BLOCK_SIZE,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_ctx),
	.base.cra_module	=	THIS_MODULE,

	.min_keysize		=	AES_MIN_KEY_SIZE,
	.max_keysize		=	AES_MAX_KEY_SIZE,
	.init			=	zynqaes_skcipher_init,
	.setkey			=	zynqaes_skcipher_setkey,
	.encrypt		=	zynqaes_ecb_encrypt,
	.decrypt		=	zynqaes_ecb_decrypt,
};

static struct skcipher_alg zynqaes_cbc_alg = {
	.base.cra_name		=	"cbc(aes)",
	.base.cra_driver_name	=	"zynqaes-cbc",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	AES_BLOCK_SIZE,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_ctx),
	.base.cra_module	=	THIS_MODULE,

	.min_keysize		=	AES_MIN_KEY_SIZE,
	.max_keysize		=	AES_MAX_KEY_SIZE,
	.ivsize			=	AES_BLOCK_SIZE,
	.init			=	zynqaes_skcipher_init,
	.setkey			=	zynqaes_skcipher_setkey,
	.encrypt		=	zynqaes_cbc_encrypt,
	.decrypt		=	zynqaes_cbc_decrypt,
};

static struct skcipher_alg zynqaes_pcbc_alg = {
	.base.cra_name		=	"pcbc(aes)",
	.base.cra_driver_name	=	"zynqaes-pcbc",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	AES_BLOCK_SIZE,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_ctx),
	.base.cra_module	=	THIS_MODULE,

	.min_keysize		=	AES_MIN_KEY_SIZE,
	.max_keysize		=	AES_MAX_KEY_SIZE,
	.ivsize			=	AES_BLOCK_SIZE,
	.init			=	zynqaes_skcipher_init,
	.setkey			=	zynqaes_skcipher_setkey,
	.encrypt		=	zynqaes_pcbc_encrypt,
	.decrypt		=	zynqaes_pcbc_decrypt,
};

static struct skcipher_alg zynqaes_ctr_alg = {
	.base.cra_name		=	"ctr(aes)",
	.base.cra_driver_name	=	"zynqaes-ctr",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	AES_BLOCK_SIZE,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_ctx),
	.base.cra_module	=	THIS_MODULE,

	.min_keysize		=	AES_MIN_KEY_SIZE,
	.max_keysize		=	AES_MAX_KEY_SIZE,
	.ivsize			=	AES_BLOCK_SIZE,
	.init			=	zynqaes_skcipher_init,
	.setkey			=	zynqaes_skcipher_setkey,
	.encrypt		=	zynqaes_ctr_encrypt,
	.decrypt		=	zynqaes_ctr_decrypt,
};

static struct skcipher_alg zynqaes_cfb_alg = {
	.base.cra_name		=	"cfb(aes)",
	.base.cra_driver_name	=	"zynqaes-cfb",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	AES_BLOCK_SIZE,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_ctx),
	.base.cra_module	=	THIS_MODULE,

	.min_keysize		=	AES_MIN_KEY_SIZE,
	.max_keysize		=	AES_MAX_KEY_SIZE,
	.ivsize			=	AES_BLOCK_SIZE,
	.init			=	zynqaes_skcipher_init,
	.setkey			=	zynqaes_skcipher_setkey,
	.encrypt		=	zynqaes_cfb_encrypt,
	.decrypt		=	zynqaes_cfb_decrypt,
};

static struct skcipher_alg zynqaes_ofb_alg = {
	.base.cra_name		=	"ofb(aes)",
	.base.cra_driver_name	=	"zynqaes-ofb",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	AES_BLOCK_SIZE,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_ctx),
	.base.cra_module	=	THIS_MODULE,

	.min_keysize		=	AES_MIN_KEY_SIZE,
	.max_keysize		=	AES_MAX_KEY_SIZE,
	.ivsize			=	AES_BLOCK_SIZE,
	.init			=	zynqaes_skcipher_init,
	.setkey			=	zynqaes_skcipher_setkey,
	.encrypt		=	zynqaes_ofb_encrypt,
	.decrypt		=	zynqaes_ofb_decrypt,
};

static int zynqaes_probe(struct platform_device *pdev)
{
	int err;
	const char *dma_name;
	struct device_node *node;

	pr_debug("[%s:%d]: Entering function\n", __func__, __LINE__);

	zynqaes_dd = devm_kzalloc(&pdev->dev, sizeof(*zynqaes_dd), GFP_KERNEL);
	if (!zynqaes_dd) {
		dev_err(zynqaes_dd->dev,
			"[%s:%d] zynqaes_dev: Allocating memory failed\n",
			__func__, __LINE__);

		err = -ENOMEM;
		goto out_err;
	}

	zynqaes_dd->dev = &pdev->dev;

	if (!pdev->dev.of_node) {
		dev_err(zynqaes_dd->dev, "[%s:%d] OF node not found!\n",
					__func__, __LINE__);

		err = -ENODEV;
		goto out_err;
	}

	node = pdev->dev.of_node;
	err = of_property_read_string_index(node, "dma-names", 0, &dma_name);
	if (err) {
		dev_err(zynqaes_dd->dev,
			"[%s:%d] Tx: reading channel name failed!\n",
			__func__, __LINE__);

		goto out_err;
	}

	zynqaes_dd->tx_chan = dma_request_chan(zynqaes_dd->dev, dma_name);
	if (IS_ERR(zynqaes_dd->tx_chan)) {
		err = PTR_ERR(zynqaes_dd->tx_chan);
		dev_err(zynqaes_dd->dev,
			"[%s:%d] Tx: requesting channel failed!\n",
			__func__, __LINE__);

		goto out_err;
	}

	err = of_property_read_string_index(node, "dma-names", 1, &dma_name);
	if (err) {
		dev_err(zynqaes_dd->dev,
			"[%s:%d] Rx: reading channel name failed!\n",
			__func__, __LINE__);

		goto free_tx_chan;
	}

	zynqaes_dd->rx_chan = dma_request_chan(zynqaes_dd->dev, dma_name);
	if (IS_ERR(zynqaes_dd->rx_chan)) {
		err = PTR_ERR(zynqaes_dd->rx_chan);
		dev_err(zynqaes_dd->dev,
			"[%s:%d] Rx: requesting channel failed!\n",
			__func__, __LINE__);

		goto free_tx_chan;
	}

	/* Initialize crypto engine */
	zynqaes_dd->engine = crypto_engine_alloc_init(zynqaes_dd->dev, 1);
	if (zynqaes_dd->engine == NULL) {
		err = -ENOMEM;
		goto free_rx_chan;
	}

	err = crypto_engine_start(zynqaes_dd->engine);
	if (err)
		goto free_engine;

	if ((err = crypto_register_skcipher(&zynqaes_ecb_alg)))
		goto free_engine;

	if ((err = crypto_register_skcipher(&zynqaes_cbc_alg)))
		goto free_ecb_alg;

	if ((err = crypto_register_skcipher(&zynqaes_ctr_alg)))
		goto free_cbc_alg;

	if ((err = crypto_register_skcipher(&zynqaes_pcbc_alg)))
		goto free_ctr_alg;

	if ((err = crypto_register_skcipher(&zynqaes_cfb_alg)))
		goto free_pcbc_alg;

	if ((err = crypto_register_skcipher(&zynqaes_ofb_alg)))
		goto free_cfb_alg;

	dev_dbg(zynqaes_dd->dev, "[%s:%d]: Probing successful \n",
				__func__, __LINE__);

	return 0;

free_cfb_alg:
	crypto_unregister_skcipher(&zynqaes_cfb_alg);

free_pcbc_alg:
	crypto_unregister_skcipher(&zynqaes_pcbc_alg);

free_ctr_alg:
	crypto_unregister_skcipher(&zynqaes_ctr_alg);

free_cbc_alg:
	crypto_unregister_skcipher(&zynqaes_cbc_alg);

free_ecb_alg:
	crypto_unregister_skcipher(&zynqaes_ecb_alg);

free_engine:
	if (zynqaes_dd->engine)
		crypto_engine_exit(zynqaes_dd->engine);

free_rx_chan:
	dma_release_channel(zynqaes_dd->rx_chan);

free_tx_chan:
	dma_release_channel(zynqaes_dd->tx_chan);

out_err:
	dev_err(&pdev->dev, "[%s:%d] Probe failed with error: %d",
			    __func__, __LINE__, err);

	return err;
}

static int zynqaes_remove(struct platform_device *pdev)
{
	dev_dbg(zynqaes_dd->dev, "[%s:%d] Entering function\n",
				__func__, __LINE__);

	crypto_unregister_skcipher(&zynqaes_ecb_alg);
	crypto_unregister_skcipher(&zynqaes_cbc_alg);
	crypto_unregister_skcipher(&zynqaes_ctr_alg);
	crypto_unregister_skcipher(&zynqaes_pcbc_alg);
	crypto_unregister_skcipher(&zynqaes_cfb_alg);
	crypto_unregister_skcipher(&zynqaes_ofb_alg);

	crypto_engine_exit(zynqaes_dd->engine);

	dmaengine_terminate_all(zynqaes_dd->rx_chan);
	dmaengine_terminate_all(zynqaes_dd->tx_chan);

	dma_release_channel(zynqaes_dd->rx_chan);
	dma_release_channel(zynqaes_dd->tx_chan);

	return 0;
}

static struct of_device_id zynqaes_of_match[] = {
	{ .compatible = "zynqaes-crypto-engine", },
	{}
};

MODULE_DEVICE_TABLE(of, zynqaes_of_match);

static struct platform_driver zynqaes_platform_driver = {
	.probe = zynqaes_probe,
	.remove = zynqaes_remove,
	.driver = {
		.name = "zynqaes",
		.owner = THIS_MODULE,
		.of_match_table = of_match_ptr(zynqaes_of_match),
	},
};

static int __init zynqaes_init(void)
{
	pr_debug("[%s:%d] Entering function\n", __func__, __LINE__);

	return platform_driver_register(&zynqaes_platform_driver);
}

static void __exit zynqaes_exit(void)
{
	pr_debug("[%s:%d] Entering function\n", __func__, __LINE__);

	platform_driver_unregister(&zynqaes_platform_driver);
}

module_init(zynqaes_init);
module_exit(zynqaes_exit);
MODULE_LICENSE("GPL");

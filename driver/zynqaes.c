#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/module.h>
#include <crypto/algapi.h>
#include <crypto/aes.h>
#include <crypto/scatterwalk.h>
#include <crypto/engine.h>
#include <asm/io.h>
#include <linux/of_platform.h>

#include <linux/dmaengine.h>
#include <linux/version.h>
#include <linux/dma-mapping.h>
#include <linux/dmapool.h>
#include <linux/slab.h>
#include <linux/platform_device.h>
#include <linux/workqueue.h>

#define ZYNQAES_CMD_LEN 4

#define ZYNQAES_KEY_EXPANSION_OP_BIT 0
#define ZYNQAES_ENCRYPTION_OP_BIT    1
#define ZYNQAES_DECRYPTION_OP_BIT    2
#define ZYNQAES_KEY_128_BIT          3
#define ZYNQAES_KEY_256_BIT          5
#define ZYNQAES_ECB_MODE_BIT         6
#define ZYNQAES_CBC_MODE_BIT         7
#define ZYNQAES_CTR_MODE_BIT         8
#define ZYNQAES_PCBC_MODE_BIT        9
#define ZYNQAES_CFB_MODE_BIT         10

#define ZYNQAES_KEY_128_FLAG     BIT(ZYNQAES_KEY_128_BIT)
#define ZYNQAES_KEY_256_FLAG     BIT(ZYNQAES_KEY_256_BIT)
#define ZYNQAES_ECB_FLAG         BIT(ZYNQAES_ECB_MODE_BIT)
#define ZYNQAES_CBC_FLAG         BIT(ZYNQAES_CBC_MODE_BIT)
#define ZYNQAES_CTR_FLAG         BIT(ZYNQAES_CTR_MODE_BIT)
#define ZYNQAES_CFB_FLAG         BIT(ZYNQAES_CFB_MODE_BIT)
#define ZYNQAES_PCBC_FLAG        BIT(ZYNQAES_PCBC_MODE_BIT)
#define ZYNQAES_ENCRYPTION_FLAG  BIT(ZYNQAES_ENCRYPTION_OP_BIT)
#define ZYNQAES_DECRYPTION_FLAG  BIT(ZYNQAES_DECRYPTION_OP_BIT)

#define ZYNQAES_ECB_ENCRYPT  (ZYNQAES_ECB_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_CBC_ENCRYPT  (ZYNQAES_CBC_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_CFB_ENCRYPT  (ZYNQAES_CFB_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_PCBC_ENCRYPT (ZYNQAES_PCBC_FLAG | ZYNQAES_ENCRYPTION_FLAG)

#define ZYNQAES_ECB_DECRYPT  (ZYNQAES_ECB_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_CBC_DECRYPT  (ZYNQAES_CBC_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_CFB_DECRYPT  (ZYNQAES_CFB_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_PCBC_DECRYPT (ZYNQAES_PCBC_FLAG | ZYNQAES_DECRYPTION_FLAG)

#define ZYNQAES_CTR_OP       (ZYNQAES_CTR_FLAG)

struct zynqaes_dev {
	struct device *dev;
	struct dma_chan *tx_chan;
	struct dma_chan *rx_chan;

	struct crypto_engine *engine;
};

struct zynqaes_reqctx {
	u32 cmd;
	u8 iv[AES_BLOCK_SIZE];

	struct ablkcipher_request *areq;
	unsigned int nbytes;

	struct zynqaes_ctx *ctx;
};

struct zynqaes_ctx {
	u8 key[AES_MAX_KEY_SIZE];
	unsigned int key_len;
};

struct zynqaes_dma_ctx {
	struct work_struct work;

	struct scatterlist tx_sg[4];
	struct scatterlist *rx_sg;

	unsigned int tx_nents;
	unsigned int rx_nents;

	dma_cookie_t tx_cookie;
	dma_cookie_t rx_cookie;
	dma_addr_t tx_dma_handle;
	dma_addr_t rx_dma_handle;

	struct zynqaes_reqctx *rctx;
};

/* Assume only one device for now */
static struct zynqaes_dev *dd;

static void zynqaes_set_key_bit(unsigned int key_len, struct zynqaes_reqctx *rctx)
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

static int is_iv_op(u32 cmd) {
	return cmd & (ZYNQAES_CBC_FLAG  | ZYNQAES_CTR_FLAG |
		      ZYNQAES_PCBC_FLAG | ZYNQAES_CFB_FLAG);
}

static struct zynqaes_dma_ctx *zynqaes_create_dma_ctx(struct zynqaes_reqctx *rctx)
{
	struct zynqaes_dma_ctx *dma_ctx;

	dma_ctx = kzalloc(sizeof(struct zynqaes_dma_ctx), GFP_ATOMIC);
	if (dma_ctx == NULL) {
		dev_err(dd->dev, "[%s:%d] tx: tx_buf: Allocating memory failed\n", __func__, __LINE__);
		goto err;
	}

	dma_ctx->rctx = rctx;

	return dma_ctx;

err:
	return NULL;
}

static void zynqaes_dma_callback(void *data)
{
	struct zynqaes_dma_ctx *dma_ctx = data;
	struct zynqaes_reqctx *rctx = dma_ctx->rctx;

	dma_unmap_sg(dd->dev, dma_ctx->tx_sg, dma_ctx->tx_nents, DMA_TO_DEVICE);
	dma_unmap_sg(dd->dev, dma_ctx->rx_sg, dma_ctx->rx_nents, DMA_FROM_DEVICE);

	crypto_finalize_cipher_request(dd->engine, rctx->areq, 0);

	kfree(dma_ctx);
}

static int zynqaes_dma_op(struct zynqaes_dma_ctx *dma_ctx)
{
	struct dma_async_tx_descriptor *tx_chan_desc;
	struct dma_async_tx_descriptor *rx_chan_desc;
	unsigned int tx_sg_len;
	unsigned int rx_sg_len;
	enum dma_ctrl_flags flags = DMA_CTRL_ACK;
	int ret;

	/* Tx Channel */
	tx_sg_len = dma_map_sg(dd->dev, dma_ctx->tx_sg, dma_ctx->tx_nents, DMA_TO_DEVICE);
	if (!tx_sg_len) {
		dev_err(dd->dev, "[%s:%d] dma_map_sg: tx error\n", __func__, __LINE__);
		ret = -ENOMEM;
		goto err;
	}

	tx_chan_desc = dmaengine_prep_slave_sg(dd->tx_chan, dma_ctx->tx_sg,
					tx_sg_len, DMA_MEM_TO_DEV, flags);
	if (!tx_chan_desc) {
		dev_err(dd->dev, "[%s:%d] dmaengine_prep_slave_sg error\n", __func__, __LINE__);
		ret = -ECOMM;
		goto err;
	}

	dma_ctx->tx_cookie = dmaengine_submit(tx_chan_desc);
	if (dma_submit_error(dma_ctx->tx_cookie)) {
		dev_err(dd->dev, "[%s:%d] tx_cookie: dmaengine_submit error\n", __func__, __LINE__);
		ret = -ECOMM;
		goto err;
	}

	dma_async_issue_pending(dd->tx_chan);

	/* Rx Channel */
	flags |= DMA_PREP_INTERRUPT;

	rx_sg_len = dma_map_sg(dd->dev, dma_ctx->rx_sg, dma_ctx->rx_nents, DMA_FROM_DEVICE);
	if (rx_sg_len == 0) {
		dev_err(dd->dev, "[%s:%d] dma_map_sg: rx error\n", __func__, __LINE__);
		ret = -ENOMEM;
		goto err;
	}

	rx_chan_desc = dmaengine_prep_slave_sg(dd->rx_chan, dma_ctx->rx_sg,
				rx_sg_len, DMA_DEV_TO_MEM, flags);
	if (!rx_chan_desc) {
		dev_err(dd->dev, "[%s:%d] dmaengine_prep_slave_sg error\n", __func__, __LINE__);
		ret = -ECOMM;
		goto err;
	}

	rx_chan_desc->callback = zynqaes_dma_callback;
	rx_chan_desc->callback_param = dma_ctx;

	dma_ctx->rx_cookie = dmaengine_submit(rx_chan_desc);
	if (dma_submit_error(dma_ctx->rx_cookie)) {
		dev_err(dd->dev, "[%s:%d] rx_cookie: dmaengine_submit error\n", __func__, __LINE__);
		ret = -ECOMM;
		goto err;
	}

	dma_async_issue_pending(dd->rx_chan);

	return 0;

err:
	return ret;
}

static int zynqaes_enqueue_next_dma_op(struct zynqaes_reqctx *rctx)
{
	struct zynqaes_ctx *ctx;
	struct zynqaes_dma_ctx *dma_ctx;
	struct ablkcipher_request *areq;
	int ret;
	unsigned int nsg;

	struct scatterlist *sg;
	unsigned int src_nbytes;

	ctx = rctx->ctx;
	areq = rctx->areq;

	dma_ctx = zynqaes_create_dma_ctx(rctx);
	if (dma_ctx == NULL) {
		dev_err(dd->dev, "[%s:%d] zynqaes_create_dma_ctx failed.", __func__, __LINE__);
		goto out_err;
	}

	nsg = is_iv_op(rctx->cmd) ? 4 : 3;

	sg_init_table(dma_ctx->tx_sg, nsg);
	sg_set_buf(&dma_ctx->tx_sg[0], &rctx->cmd, sizeof(rctx->cmd));
	sg_set_buf(&dma_ctx->tx_sg[1], ctx->key, ctx->key_len);
	if (is_iv_op(rctx->cmd)) {
		sg_set_buf(&dma_ctx->tx_sg[2], rctx->iv, AES_BLOCK_SIZE);
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

	dev_dbg(dd->dev, "[%s:%d] dma_ctx->tx_nents: %d\n", __func__, __LINE__, dma_ctx->tx_nents);
	dev_dbg(dd->dev, "[%s:%d] dma_ctx->rx_nents: %d\n", __func__, __LINE__, dma_ctx->rx_nents);

	ret = zynqaes_dma_op(dma_ctx);
	if (ret) {
		dev_err(dd->dev, "[%s:%d] zynqaes_dma_op failed with: %d", __func__, __LINE__, ret);
		goto free_dma_ctx;
	}

	return 0;

free_dma_ctx:
	kfree(dma_ctx);

out_err:
	return ret;
}

static int zynqaes_crypt_req(struct crypto_engine *engine,
			     struct ablkcipher_request *areq)
{
	struct crypto_ablkcipher *cipher = crypto_ablkcipher_reqtfm(areq);
	struct crypto_tfm *tfm = crypto_ablkcipher_tfm(cipher);
	struct zynqaes_ctx *ctx = crypto_tfm_ctx(tfm);
	struct zynqaes_reqctx *rctx = ablkcipher_request_ctx(areq);

	int ret;

	rctx->ctx = ctx;
	rctx->areq = areq;
	rctx->nbytes = areq->nbytes;

	zynqaes_set_key_bit(ctx->key_len, rctx);

	dev_dbg(dd->dev, "[%s:%d] rctx->nbytes: %u\n", __func__, __LINE__, rctx->nbytes);
	dev_dbg(dd->dev, "[%s:%d] rctx->cmd: %x\n", __func__, __LINE__, rctx->cmd);

	if (is_iv_op(rctx->cmd)) {
		memcpy(rctx->iv, areq->info, AES_BLOCK_SIZE);
	}

	ret = zynqaes_enqueue_next_dma_op(rctx);
	if (ret) {
		dev_err(dd->dev, "[%s:%d] zynqaes_dma_op failed with: %d", __func__, __LINE__, ret);
		goto out;
	}

	return 0;

out:
	return ret;
}

static int zynqaes_crypt(struct ablkcipher_request *areq, const u32 cmd)
{
	struct zynqaes_reqctx *rctx = ablkcipher_request_ctx(areq);

	dev_dbg(dd->dev, "[%s:%d] Entering function\n", __func__, __LINE__);

	rctx->cmd = cmd;

	return crypto_transfer_cipher_request_to_engine(dd->engine, areq);
}

static int zynqaes_setkey(struct crypto_ablkcipher *cipher, const u8 *key,
			    unsigned int len)
{
	struct crypto_tfm *tfm = crypto_ablkcipher_tfm(cipher);
	struct zynqaes_ctx *ctx = crypto_tfm_ctx(tfm);

	dev_dbg(dd->dev, "[%s:%d] Entering function\n", __func__, __LINE__);

	switch (len) {
	case AES_KEYSIZE_128:
	case AES_KEYSIZE_256:
		ctx->key_len = len;
		memcpy(ctx->key, key, len);
		break;
	default:
		dev_info(dd->dev, "[%s:%d] Key size of %u bytes not supported!",
				__func__, __LINE__, len);
		return -ENOTSUPP;
	}

	return 0;
}

static int zynqaes_ecb_encrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_ECB_ENCRYPT);
}

static int zynqaes_ecb_decrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_ECB_DECRYPT);
}

static int zynqaes_cbc_encrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_CBC_ENCRYPT);
}

static int zynqaes_cbc_decrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_CBC_DECRYPT);
}

static int zynqaes_pcbc_encrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_PCBC_ENCRYPT);
}

static int zynqaes_pcbc_decrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_PCBC_DECRYPT);
}

static int zynqaes_ctr_op(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_CTR_OP);
}

static int zynqaes_cfb_encrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_CFB_ENCRYPT);
}

static int zynqaes_cfb_decrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_CFB_DECRYPT);
}

static int zynqaes_cra_init(struct crypto_tfm *tfm)
{
	tfm->crt_ablkcipher.reqsize = sizeof(struct zynqaes_reqctx);

	return 0;
}

static struct crypto_alg zynqaes_ecb_alg = {
	.cra_name		=	"ecb(aes)",
	.cra_driver_name	=	"zynqaes-ecb",
	.cra_priority		=	100,
	.cra_flags		=	CRYPTO_ALG_TYPE_ABLKCIPHER |
					CRYPTO_ALG_ASYNC,
	.cra_blocksize		=	AES_BLOCK_SIZE,
	.cra_ctxsize		=	sizeof(struct zynqaes_ctx),
	.cra_type		=	&crypto_ablkcipher_type,
	.cra_module		=	THIS_MODULE,
	.cra_init		= 	zynqaes_cra_init,
	.cra_u			=	{
		.ablkcipher = {
			.min_keysize		=	AES_MIN_KEY_SIZE,
			.max_keysize		=	AES_MAX_KEY_SIZE,
			.setkey	   		= 	zynqaes_setkey,
			.encrypt		=	zynqaes_ecb_encrypt,
			.decrypt		=	zynqaes_ecb_decrypt,
		}
	}
};

static struct crypto_alg zynqaes_cbc_alg = {
	.cra_name		=	"cbc(aes)",
	.cra_driver_name	=	"zynqaes-cbc",
	.cra_priority		=	100,
	.cra_flags		=	CRYPTO_ALG_TYPE_ABLKCIPHER |
					CRYPTO_ALG_ASYNC,
	.cra_blocksize		=	AES_BLOCK_SIZE,
	.cra_ctxsize		=	sizeof(struct zynqaes_ctx),
	.cra_type		=	&crypto_ablkcipher_type,
	.cra_module		=	THIS_MODULE,
	.cra_init		= 	zynqaes_cra_init,
	.cra_u			=	{
		.ablkcipher = {
			.min_keysize		=	AES_MIN_KEY_SIZE,
			.max_keysize		=	AES_MAX_KEY_SIZE,
			.ivsize			=	AES_BLOCK_SIZE,
			.setkey	   		= 	zynqaes_setkey,
			.encrypt		=	zynqaes_cbc_encrypt,
			.decrypt		=	zynqaes_cbc_decrypt,
		}
	}
};

static struct crypto_alg zynqaes_pcbc_alg = {
	.cra_name		=	"pcbc(aes)",
	.cra_driver_name	=	"zynqaes-pcbc",
	.cra_priority		=	100,
	.cra_flags		=	CRYPTO_ALG_TYPE_ABLKCIPHER |
					CRYPTO_ALG_ASYNC,
	.cra_blocksize		=	AES_BLOCK_SIZE,
	.cra_ctxsize		=	sizeof(struct zynqaes_ctx),
	.cra_type		=	&crypto_ablkcipher_type,
	.cra_module		=	THIS_MODULE,
	.cra_init		= 	zynqaes_cra_init,
	.cra_u			=	{
		.ablkcipher = {
			.min_keysize		=	AES_MIN_KEY_SIZE,
			.max_keysize		=	AES_MAX_KEY_SIZE,
			.ivsize			=	AES_BLOCK_SIZE,
			.setkey	   		= 	zynqaes_setkey,
			.encrypt		=	zynqaes_pcbc_encrypt,
			.decrypt		=	zynqaes_pcbc_decrypt,
		}
	}
};

static struct crypto_alg zynqaes_ctr_alg = {
	.cra_name		=	"ctr(aes)",
	.cra_driver_name	=	"zynqaes-ctr",
	.cra_priority		=	100,
	.cra_flags		=	CRYPTO_ALG_TYPE_ABLKCIPHER |
					CRYPTO_ALG_ASYNC,
	.cra_blocksize		=	AES_BLOCK_SIZE,
	.cra_ctxsize		=	sizeof(struct zynqaes_ctx),
	.cra_type		=	&crypto_ablkcipher_type,
	.cra_module		=	THIS_MODULE,
	.cra_init		= 	zynqaes_cra_init,
	.cra_u			=	{
		.ablkcipher = {
			.min_keysize		=	AES_MIN_KEY_SIZE,
			.max_keysize		=	AES_MAX_KEY_SIZE,
			.ivsize			=	AES_BLOCK_SIZE,
			.setkey			=	zynqaes_setkey,
			.encrypt		=	zynqaes_ctr_op,
			.decrypt		=	zynqaes_ctr_op,
		}
	}
};

static struct crypto_alg zynqaes_cfb_alg = {
	.cra_name		=	"cfb(aes)",
	.cra_driver_name	=	"zynqaes-cfb",
	.cra_priority		=	100,
	.cra_flags		=	CRYPTO_ALG_TYPE_ABLKCIPHER |
					CRYPTO_ALG_ASYNC,
	.cra_blocksize		=	AES_BLOCK_SIZE,
	.cra_ctxsize		=	sizeof(struct zynqaes_ctx),
	.cra_type		=	&crypto_ablkcipher_type,
	.cra_module		=	THIS_MODULE,
	.cra_init		= 	zynqaes_cra_init,
	.cra_u			=	{
		.ablkcipher = {
			.min_keysize		=	AES_MIN_KEY_SIZE,
			.max_keysize		=	AES_MAX_KEY_SIZE,
			.ivsize			=	AES_BLOCK_SIZE,
			.setkey			=	zynqaes_setkey,
			.encrypt		=	zynqaes_cfb_encrypt,
			.decrypt		=	zynqaes_cfb_decrypt,
		}
	}
};

static int zynqaes_probe(struct platform_device *pdev)
{
	int err;

	pr_debug("[%s:%d]: Entering function\n", __func__, __LINE__);

	dd = kmalloc(sizeof(struct zynqaes_dev), GFP_KERNEL);
	if (dd == NULL) {
		dev_err(dd->dev, "[%s:%d] zynqaes_dev: Allocating memory failed\n", __func__, __LINE__);
		err = -ENOMEM;
		goto out_err;
	}

	dd->dev = &pdev->dev;

	dd->tx_chan = dma_request_chan(dd->dev, "axidma0");
	if (IS_ERR(dd->tx_chan)) {
		err = PTR_ERR(dd->tx_chan);
		dev_err(dd->dev, "[%s:%d] xilinx_dmatest: No Tx channel\n", __func__, __LINE__);
		goto free_zynqaes_dev;
	}

	dd->rx_chan = dma_request_chan(dd->dev, "axidma1");
	if (IS_ERR(dd->rx_chan)) {
		err = PTR_ERR(dd->rx_chan);
		dev_err(dd->dev, "[%s:%d] xilinx_dmatest: No Rx channel\n", __func__, __LINE__);
		goto free_tx_chan;
	}

	/* Initialize crypto engine */
	dd->engine = crypto_engine_alloc_init(dd->dev, 1);
	if (dd->engine == NULL) {
		err = -ENOMEM;
		goto free_rx_chan;
	}

	dd->engine->cipher_one_request = zynqaes_crypt_req;
	err = crypto_engine_start(dd->engine);
	if (err)
		goto free_engine;

	if ((err = crypto_register_alg(&zynqaes_ecb_alg)))
		goto free_engine;

	if ((err = crypto_register_alg(&zynqaes_cbc_alg)))
		goto free_ecb_alg;

	if ((err = crypto_register_alg(&zynqaes_ctr_alg)))
		goto free_cbc_alg;

	if ((err = crypto_register_alg(&zynqaes_pcbc_alg)))
		goto free_ctr_alg;

	if ((err = crypto_register_alg(&zynqaes_cfb_alg)))
		goto free_pcbc_alg;

	dev_dbg(dd->dev, "[%s:%d]: Probing successful \n", __func__, __LINE__);

	return 0;

free_pcbc_alg:
	crypto_unregister_alg(&zynqaes_pcbc_alg);

free_ctr_alg:
	crypto_unregister_alg(&zynqaes_ctr_alg);

free_cbc_alg:
	crypto_unregister_alg(&zynqaes_cbc_alg);

free_ecb_alg:
	crypto_unregister_alg(&zynqaes_ecb_alg);

free_engine:
	if (dd->engine)
		crypto_engine_exit(dd->engine);

free_rx_chan:
	dma_release_channel(dd->rx_chan);

free_tx_chan:
	dma_release_channel(dd->tx_chan);

free_zynqaes_dev:
	kfree(dd);

out_err:
	dev_err(&pdev->dev, "[%s:%d] Probe failed with error: %d", __func__, __LINE__, err);

	return err;
}

static int zynqaes_remove(struct platform_device *pdev)
{
	dev_dbg(dd->dev, "[%s:%d] Entering function\n", __func__, __LINE__);

	dmaengine_terminate_all(dd->rx_chan);
	dmaengine_terminate_all(dd->tx_chan);

	crypto_unregister_alg(&zynqaes_ecb_alg);
	crypto_unregister_alg(&zynqaes_cbc_alg);
	crypto_unregister_alg(&zynqaes_ctr_alg);
	crypto_unregister_alg(&zynqaes_pcbc_alg);
	crypto_unregister_alg(&zynqaes_cfb_alg);

	dma_release_channel(dd->rx_chan);
	dma_release_channel(dd->tx_chan);

	crypto_engine_stop(dd->engine);
	crypto_engine_exit(dd->engine);

	kfree(dd);

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

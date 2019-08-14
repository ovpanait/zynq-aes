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

#define ZYNQAES_ECB_ENCRYPT 0x20
#define ZYNQAES_ECB_DECRYPT 0x30

#define ZYNQAES_CBC_ENCRYPT 0x40
#define ZYNQAES_CBC_DECRYPT 0x41

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
	u8 key[AES_KEYSIZE_128];
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

static int is_cbc_op(u32 cmd) {
	return (cmd == ZYNQAES_CBC_ENCRYPT) || (cmd == ZYNQAES_CBC_DECRYPT);
}

static int is_ecb_op(u32 cmd) {
	return (cmd == ZYNQAES_ECB_ENCRYPT) || (cmd == ZYNQAES_ECB_DECRYPT);
}

static struct zynqaes_dma_ctx *zynqaes_create_dma_ctx(struct zynqaes_reqctx *rctx)
{
	struct zynqaes_dma_ctx *dma_ctx;

	dma_ctx = kmalloc(sizeof(struct zynqaes_dma_ctx), GFP_KERNEL);
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

	tx_chan_desc = dmaengine_prep_slave_sg(dd->tx_chan, dma_ctx->tx_sg, tx_sg_len, DMA_MEM_TO_DEV, flags);
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

	rx_chan_desc = dmaengine_prep_slave_sg(dd->rx_chan, dma_ctx->rx_sg, rx_sg_len, DMA_DEV_TO_MEM, flags);
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
	unsigned int tx_nbytes_dma;
	unsigned int rx_nbytes_dma;

	tx_nbytes_dma = rctx->nbytes;
	rx_nbytes_dma = rctx->nbytes;
	ctx = rctx->ctx;
	areq = rctx->areq;

	dma_ctx = zynqaes_create_dma_ctx(rctx);
	if (dma_ctx == NULL) {
		dev_err(dd->dev, "[%s:%d] zynqaes_create_dma_ctx failed.", __func__, __LINE__);
		goto out_err;
	}

	nsg = is_cbc_op(rctx->cmd) ? 4 : 3;

	sg_init_table(dma_ctx->tx_sg, nsg);
	sg_set_buf(&dma_ctx->tx_sg[0], &rctx->cmd, sizeof(rctx->cmd));
	sg_set_buf(&dma_ctx->tx_sg[1], ctx->key, AES_KEYSIZE_128);
	tx_nbytes_dma += ZYNQAES_CMD_LEN + AES_KEYSIZE_128;
	if (is_cbc_op(rctx->cmd)) {
		sg_set_buf(&dma_ctx->tx_sg[2], rctx->iv, AES_BLOCK_SIZE);
		tx_nbytes_dma += AES_KEYSIZE_128;
	}
	sg_chain(dma_ctx->tx_sg, nsg, areq->src);

	dma_ctx->rx_sg = areq->dst;

	dma_ctx->tx_nents = sg_nents_for_len(dma_ctx->tx_sg, tx_nbytes_dma);
	dma_ctx->rx_nents = sg_nents_for_len(dma_ctx->rx_sg, rx_nbytes_dma);

	dev_dbg(dd->dev, "[%s:%d] dma_ctx->tx_nents: %d\n", __func__, __LINE__, dma_ctx->tx_nents);
	dev_dbg(dd->dev, "[%s:%d] dma_ctx->rx_nents: %d\n", __func__, __LINE__, dma_ctx->rx_nents);

	ret = zynqaes_dma_op(dma_ctx);
	if (ret) {
		dev_err(dd->dev, "[%s:%d] zynqaes_dma_op failed with: %d", __func__, __LINE__, ret);
		goto out_err;
	}

	return 0;

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

	dev_dbg(dd->dev, "[%s:%d] crypto operation: %s\n", __func__, __LINE__,
		rctx->cmd == ZYNQAES_ECB_ENCRYPT ? "ECB_ENCRYPT" : "ECB_DECRYPT");

	rctx->ctx = ctx;
	rctx->areq = areq;
	rctx->nbytes = areq->nbytes;

	dev_dbg(dd->dev, "[%s:%d] rctx->nbytes: %u\n", __func__, __LINE__, rctx->nbytes);

	if (is_cbc_op(rctx->cmd)) {
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

	memcpy(ctx->key, key, len);

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
			.min_keysize		=	AES_KEYSIZE_128,
			.max_keysize		=	AES_KEYSIZE_128,
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
			.min_keysize		=	AES_KEYSIZE_128,
			.max_keysize		=	AES_KEYSIZE_128,
			.ivsize			=	AES_BLOCK_SIZE,
			.setkey	   		= 	zynqaes_setkey,
			.encrypt		=	zynqaes_cbc_encrypt,
			.decrypt		=	zynqaes_cbc_decrypt,
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

	dev_dbg(dd->dev, "[%s:%d]: Probing successful \n", __func__, __LINE__);

	return 0;

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

	dma_release_channel(dd->rx_chan);
	dma_release_channel(dd->tx_chan);

	crypto_engine_stop(dd->engine);
	crypto_engine_exit(dd->engine);

	kfree(dd);

	return 0;
}

static struct of_device_id zynqaes_of_match[] = {
	{ .compatible = "xlnx,axi-dma-test-1.00.a", },
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

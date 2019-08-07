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

#define ZYNQAES_CMD_LEN 4

#define ZYNQAES_FIFO_NBYTES 32768

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

	u8 *src_buf;
	u8 *dst_buf;

	struct zynqaes_ctx *ctx;
};

struct zynqaes_ctx {
	u8 key[AES_KEYSIZE_128];
};

struct zynqaes_dma_ctx {
	u8 *tx_buf;
	u8 *rx_buf;

	dma_cookie_t tx_cookie;
	dma_cookie_t rx_cookie;
	dma_addr_t tx_dma_handle;
	dma_addr_t rx_dma_handle;
	int tx_nbytes;
	int rx_nbytes;

	struct completion rx_cmp;

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

static unsigned int zynqaes_ecb_set_txkbuf(struct zynqaes_reqctx *rctx, u8 *src_buf, u8 *tx_kbuf, int payload_nbytes, const u32 cmd)
{
	struct zynqaes_ctx *ctx = rctx->ctx;

	memcpy(tx_kbuf, &cmd, ZYNQAES_CMD_LEN);
	memcpy(tx_kbuf + ZYNQAES_CMD_LEN, ctx->key, AES_KEYSIZE_128);
	memcpy(tx_kbuf + ZYNQAES_CMD_LEN + AES_KEYSIZE_128, src_buf, payload_nbytes);

	return payload_nbytes + AES_KEYSIZE_128 + ZYNQAES_CMD_LEN;
}

static unsigned int zynqaes_cbc_set_txkbuf(struct zynqaes_reqctx *rctx, u8 *payload_buf, u8 *tx_kbuf, int payload_nbytes, const u32 cmd)
{
	struct zynqaes_ctx *ctx = rctx->ctx;

	memcpy(tx_kbuf, &cmd, ZYNQAES_CMD_LEN);
	memcpy(tx_kbuf + ZYNQAES_CMD_LEN, ctx->key, AES_KEYSIZE_128);
	memcpy(tx_kbuf + ZYNQAES_CMD_LEN + AES_KEYSIZE_128, rctx->iv, AES_BLOCK_SIZE);
	memcpy(tx_kbuf + ZYNQAES_CMD_LEN + AES_KEYSIZE_128 + AES_BLOCK_SIZE, payload_buf, payload_nbytes);

	return ZYNQAES_CMD_LEN + AES_KEYSIZE_128 + AES_BLOCK_SIZE + payload_nbytes;
}

static unsigned int zynqaes_set_txkbuf(struct zynqaes_reqctx *rctx, u8 *payload_buf, u8 *tx_kbuf, int payload_nbytes, const u32 cmd)
{
	switch (cmd) {
	case ZYNQAES_ECB_ENCRYPT:
	case ZYNQAES_ECB_DECRYPT:
		return zynqaes_ecb_set_txkbuf(rctx, payload_buf, tx_kbuf, payload_nbytes, cmd);
		break;
	case ZYNQAES_CBC_ENCRYPT:
	case ZYNQAES_CBC_DECRYPT:
		return zynqaes_cbc_set_txkbuf(rctx, payload_buf, tx_kbuf, payload_nbytes, cmd);
		break;
	default:
		break;
	}

	return -ENOMEM;
}

static void zynqaes_get_rxkbuf(struct zynqaes_reqctx *rctx, u8 *src_buf, u8 *dst_buf, u8 *rx_kbuf, int payload_nbytes, const u32 cmd)
{
	if (dst_buf != NULL)
		memcpy(dst_buf, rx_kbuf, payload_nbytes);

	switch(cmd) {
	case ZYNQAES_CBC_ENCRYPT:
		memcpy(rctx->iv, dst_buf + (payload_nbytes - AES_BLOCK_SIZE), AES_BLOCK_SIZE);
		break;
	case ZYNQAES_CBC_DECRYPT:
		memcpy(rctx->iv, src_buf + (payload_nbytes - AES_BLOCK_SIZE), AES_BLOCK_SIZE);
		break;
	default:
		break;
	}
}

static void axidma_sync_callback(void *data)
{
	struct zynqaes_dma_ctx *dma_ctx = data;

	dma_unmap_single(dd->dev, dma_ctx->tx_dma_handle, dma_ctx->tx_nbytes, DMA_TO_DEVICE);
	dma_unmap_single(dd->dev, dma_ctx->rx_dma_handle, dma_ctx->rx_nbytes, DMA_FROM_DEVICE);

	complete(&dma_ctx->rx_cmp);
}

static struct zynqaes_dma_ctx *zynqaes_create_dma_ctx(struct zynqaes_reqctx *rctx)
{
	struct zynqaes_dma_ctx *dma_ctx;

	dma_ctx = kmalloc(sizeof(struct zynqaes_dma_ctx), GFP_KERNEL);
	if (dma_ctx == NULL) {
		dev_err(dd->dev, "[%s:%d] tx: tx_buf: Allocating memory failed\n", __func__, __LINE__);
		goto err;
	}

	dma_ctx->tx_buf = kmalloc(ZYNQAES_FIFO_NBYTES + ZYNQAES_CMD_LEN + 2 * AES_KEYSIZE_128, GFP_KERNEL);
	if (dma_ctx->tx_buf == NULL) {
		dev_err(dd->dev, "[%s:%d] tx: tx_buf: Allocating memory failed\n", __func__, __LINE__);
		goto free_dma_ctx;
	}

	dma_ctx->rx_buf = kmalloc(ZYNQAES_FIFO_NBYTES, GFP_KERNEL);
	if (dma_ctx->rx_buf == NULL) {
		dev_err(dd->dev, "[%s:%d] rx: rx_buf: Allocating memory failed\n", __func__, __LINE__);
		goto free_tx_buf;
	}

	dma_ctx->rctx = rctx;
	init_completion(&dma_ctx->rx_cmp);

	return dma_ctx;

free_tx_buf:
	kfree(dma_ctx->tx_buf);

free_dma_ctx:
	kfree(dma_ctx);

err:
	return NULL;
}

static int zynqaes_dma_op(struct zynqaes_dma_ctx *dma_ctx, int src_nbytes, int dst_nbytes)
{
	unsigned long timeout;
	struct dma_async_tx_descriptor *tx_chan_desc;
	struct dma_async_tx_descriptor *rx_chan_desc;
	enum dma_ctrl_flags flags = DMA_CTRL_ACK;
	enum dma_status status;
	int ret = 0;

	u8 *tx_buf = dma_ctx->tx_buf;
	u8 *rx_buf = dma_ctx->rx_buf;

	dev_dbg(dd->dev, "[%s:%d]", __func__, __LINE__);

	dma_ctx->tx_dma_handle = dma_map_single(dd->dev, tx_buf, src_nbytes, DMA_TO_DEVICE);
	dma_ctx->rx_dma_handle = dma_map_single(dd->dev, rx_buf, dst_nbytes, DMA_FROM_DEVICE);

	/* Tx Channel */
	tx_chan_desc = dmaengine_prep_slave_single(dd->tx_chan, dma_ctx->tx_dma_handle, src_nbytes, DMA_MEM_TO_DEV, flags);
	if (!tx_chan_desc) {
		dev_err(dd->dev, "[%s:%d] dmaengine_prep_slave_single error\n", __func__, __LINE__);
		ret = -ECOMM;
		goto err;
	}
	dma_ctx->tx_cookie = dmaengine_submit(tx_chan_desc);
	if (dma_submit_error(dma_ctx->tx_cookie)) {
		dev_err(dd->dev, "[%s:%d] tx_cookie: xdma_prep_buffer error\n", __func__, __LINE__);
		ret = -ECOMM;
		goto err;
	}

	/* Rx Channel */
	flags |= DMA_PREP_INTERRUPT;
	rx_chan_desc = dmaengine_prep_slave_single(dd->rx_chan, dma_ctx->rx_dma_handle, dst_nbytes, DMA_DEV_TO_MEM, flags);
	if (!rx_chan_desc) {
		dev_err(dd->dev, "[%s:%d] dmaengine_prep_slave_single error\n", __func__, __LINE__);
		ret = -ECOMM;
		goto err;
	}
	rx_chan_desc->callback = axidma_sync_callback;
	rx_chan_desc->callback_param = dma_ctx;
	dma_ctx->rx_cookie = dmaengine_submit(rx_chan_desc);
	if (dma_submit_error(dma_ctx->rx_cookie)) {
		dev_err(dd->dev, "[%s:%d] rx_cookie: xdma_prep_buffer error\n", __func__, __LINE__);
		ret = -ECOMM;
		goto err;
	}

	reinit_completion(&dma_ctx->rx_cmp);
	dma_async_issue_pending(dd->tx_chan);
	dma_async_issue_pending(dd->rx_chan);

	status = dma_async_is_tx_complete(dd->rx_chan, dma_ctx->rx_cookie, NULL, NULL);
	do {
		timeout = msecs_to_jiffies(5000);

		timeout = wait_for_completion_timeout(&dma_ctx->rx_cmp, timeout);
		status = dma_async_is_tx_complete(dd->rx_chan, dma_ctx->rx_cookie, NULL, NULL);

		if (status != DMA_COMPLETE) {
			dev_err(dd->dev, "[%s:%d] DMA returned completion callback status of: %s\n",
			__func__, __LINE__, status == DMA_ERROR ? "error" : "in progress");

			if (status == DMA_ERROR) {
				ret = -EINVAL;
			}
		}

		if (timeout == 0)  {
			dev_err(dd->dev, "[%s:%d] DMA timed out\n", __func__, __LINE__);
			ret = -ETIMEDOUT;
		}
	} while(status != DMA_COMPLETE && !ret);

err:
	return ret;
}

static int zynqaes_crypt_req(struct crypto_engine *engine,
			      struct ablkcipher_request *areq)
{
	struct crypto_ablkcipher *cipher = crypto_ablkcipher_reqtfm(areq);
	struct crypto_tfm *tfm = crypto_ablkcipher_tfm(cipher);
	struct zynqaes_ctx *ctx = crypto_tfm_ctx(tfm);
	struct zynqaes_reqctx *rctx = ablkcipher_request_ctx(areq);

	const u32 cmd = rctx->cmd;
	int ret = 0;

	unsigned int nbytes;
	unsigned int nbytes_total;

	unsigned int tx_i = 0;

	dev_dbg(dd->dev, "[%s:%d] crypto operation: %s\n", __func__, __LINE__,
		cmd == ZYNQAES_ECB_ENCRYPT ? "ECB_ENCRYPT" : "ECB_DECRYPT");

	nbytes_total = areq->nbytes;
	dev_dbg(dd->dev, "[%s:%d] nbytes_total: %d\n", __func__, __LINE__, nbytes_total);

	rctx->src_buf = kmalloc(nbytes_total, GFP_KERNEL);
	if (rctx->src_buf == NULL) {
		dev_err(dd->dev, "[%s:%d] tx: src_buf: Allocating memory failed\n", __func__, __LINE__);
		ret = -ENOMEM;
		goto out;
	}

	rctx->dst_buf = kmalloc(nbytes_total, GFP_KERNEL);
	if (rctx->dst_buf == NULL) {
		dev_err(dd->dev, "[%s:%d] rx: dst_buf: Allocating memory failed\n", __func__, __LINE__);
		ret = -ENOMEM;
		goto out_src_buf;
	}

	nbytes = nbytes_total;
	rctx->ctx = ctx;

	scatterwalk_map_and_copy(rctx->src_buf, areq->src, 0, nbytes_total, 0);

	if (is_cbc_op(cmd))
		memcpy(rctx->iv, areq->info, AES_BLOCK_SIZE);

	while (nbytes != 0) {
		struct zynqaes_dma_ctx *dma_ctx;
		unsigned int dma_nbytes;
		unsigned int in_nbytes;

		dma_nbytes = (nbytes < ZYNQAES_FIFO_NBYTES) ? nbytes : ZYNQAES_FIFO_NBYTES;
		dev_dbg(dd->dev, "[%s:%d] nbytes: %d\n", __func__, __LINE__, nbytes);
		dev_dbg(dd->dev, "[%s:%d] dma_nbytes: %d\n", __func__, __LINE__, dma_nbytes);

		dma_ctx = zynqaes_create_dma_ctx(rctx);
		if (dma_ctx == NULL) {
			dev_err(dd->dev, "[%s:%d] zynqaes_create_dma_ctx failed with: %d", __func__, __LINE__, ret);
			goto out_dst_buf;
		}

		in_nbytes = zynqaes_set_txkbuf(rctx, rctx->src_buf + tx_i, dma_ctx->tx_buf, dma_nbytes, cmd);
		dma_ctx->tx_nbytes = in_nbytes;
		dma_ctx->rx_nbytes = dma_nbytes;

		ret = zynqaes_dma_op(dma_ctx, in_nbytes, dma_nbytes);
		if (ret) {
			dev_err(dd->dev, "[%s:%d] zynqaes_dma_op failed with: %d", __func__, __LINE__, ret);
			goto out_dst_buf;
		}

		zynqaes_get_rxkbuf(rctx, rctx->src_buf + tx_i, rctx->dst_buf + tx_i, dma_ctx->rx_buf, dma_ctx->rx_nbytes, cmd);

		kfree(dma_ctx->rx_buf);
		kfree(dma_ctx->tx_buf);
		kfree(dma_ctx);

		tx_i += dma_nbytes;
		nbytes -= dma_nbytes;
	}

	dev_dbg(dd->dev, "[%s:%d]", __func__, __LINE__);

	scatterwalk_map_and_copy(rctx->dst_buf, areq->dst, 0, nbytes_total, 1);

	crypto_finalize_cipher_request(dd->engine, areq, 0);

	dev_dbg(dd->dev, "[%s:%d]", __func__, __LINE__);
out_dst_buf:
	kfree(rctx->dst_buf);

out_src_buf:
	kfree(rctx->src_buf);

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

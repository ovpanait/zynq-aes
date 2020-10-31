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

#define ZYNQAES_IVSIZE_MAX AES_BLOCK_SIZE

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
#define ZYNQAES_OFB_MODE_BIT         11

#define ZYNQAES_ENCRYPTION_FLAG  BIT(ZYNQAES_ENCRYPTION_OP_BIT)
#define ZYNQAES_DECRYPTION_FLAG  BIT(ZYNQAES_DECRYPTION_OP_BIT)
#define ZYNQAES_KEY_128_FLAG     BIT(ZYNQAES_KEY_128_BIT)
#define ZYNQAES_KEY_256_FLAG     BIT(ZYNQAES_KEY_256_BIT)
#define ZYNQAES_ECB_FLAG         BIT(ZYNQAES_ECB_MODE_BIT)
#define ZYNQAES_CBC_FLAG         BIT(ZYNQAES_CBC_MODE_BIT)
#define ZYNQAES_CTR_FLAG         BIT(ZYNQAES_CTR_MODE_BIT)
#define ZYNQAES_CFB_FLAG         BIT(ZYNQAES_CFB_MODE_BIT)
#define ZYNQAES_OFB_FLAG         BIT(ZYNQAES_OFB_MODE_BIT)
#define ZYNQAES_PCBC_FLAG        BIT(ZYNQAES_PCBC_MODE_BIT)

#define ZYNQAES_ECB_ENCRYPT  (ZYNQAES_ECB_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_CBC_ENCRYPT  (ZYNQAES_CBC_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_CTR_ENCRYPT  (ZYNQAES_CTR_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_CFB_ENCRYPT  (ZYNQAES_CFB_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_OFB_ENCRYPT  (ZYNQAES_OFB_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_PCBC_ENCRYPT (ZYNQAES_PCBC_FLAG | ZYNQAES_ENCRYPTION_FLAG)

#define ZYNQAES_ECB_DECRYPT  (ZYNQAES_ECB_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_CBC_DECRYPT  (ZYNQAES_CBC_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_CTR_DECRYPT  (ZYNQAES_CTR_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_CFB_DECRYPT  (ZYNQAES_CFB_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_OFB_DECRYPT  (ZYNQAES_OFB_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_PCBC_DECRYPT (ZYNQAES_PCBC_FLAG | ZYNQAES_DECRYPTION_FLAG)

struct zynqaes_dev {
	struct device *dev;
	struct dma_chan *tx_chan;
	struct dma_chan *rx_chan;

	struct crypto_engine *engine;
};

struct zynqaes_reqctx {
	u32 cmd;
	u8 iv[ZYNQAES_IVSIZE_MAX];
	unsigned int ivsize;

	struct ablkcipher_request *areq;
	unsigned int nbytes;

	struct zynqaes_ctx *ctx;
};

struct zynqaes_ctx {
	struct crypto_engine_ctx enginectx;
	u8 key[AES_MAX_KEY_SIZE];
	unsigned int key_len;
};

struct zynqaes_dma_ctx {
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

	crypto_finalize_ablkcipher_request(dd->engine, rctx->areq, 0);

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
	tx_sg_len = dma_map_sg(dd->dev, dma_ctx->tx_sg, dma_ctx->tx_nents, DMA_TO_DEVICE);
	if (!tx_sg_len) {
		dev_err(dd->dev, "[%s:%d] dma_map_sg: tx error\n", __func__, __LINE__);
		ret = -ENOMEM;
		goto err;
	}

	tx_chan_desc = dmaengine_prep_slave_sg(dd->tx_chan, dma_ctx->tx_sg,
					tx_sg_len, DMA_MEM_TO_DEV,
					DMA_CTRL_ACK);
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
	rx_sg_len = dma_map_sg(dd->dev, dma_ctx->rx_sg, dma_ctx->rx_nents, DMA_FROM_DEVICE);
	if (rx_sg_len == 0) {
		dev_err(dd->dev, "[%s:%d] dma_map_sg: rx error\n", __func__, __LINE__);
		ret = -ENOMEM;
		goto err;
	}

	rx_chan_desc = dmaengine_prep_slave_sg(dd->rx_chan, dma_ctx->rx_sg,
					rx_sg_len, DMA_DEV_TO_MEM,
					DMA_CTRL_ACK | DMA_PREP_INTERRUPT);
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

	nsg = rctx->ivsize ? 4 : 3;

	sg_init_table(dma_ctx->tx_sg, nsg);
	sg_set_buf(&dma_ctx->tx_sg[0], &rctx->cmd, sizeof(rctx->cmd));
	sg_set_buf(&dma_ctx->tx_sg[1], ctx->key, ctx->key_len);
	if (rctx->ivsize) {
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
			     void *req)
{
	struct ablkcipher_request *areq = container_of(req, struct ablkcipher_request, base);
	struct crypto_ablkcipher *cipher = crypto_ablkcipher_reqtfm(areq);
	struct crypto_tfm *tfm = crypto_ablkcipher_tfm(cipher);
	struct zynqaes_ctx *ctx = crypto_tfm_ctx(tfm);
	struct zynqaes_reqctx *rctx = ablkcipher_request_ctx(areq);

	int ret;

	rctx->ctx = ctx;
	rctx->areq = areq;
	rctx->nbytes = areq->nbytes;
	rctx->ivsize = crypto_ablkcipher_ivsize(cipher);

	zynqaes_set_key_bit(ctx->key_len, rctx);

	dev_dbg(dd->dev, "[%s:%d] rctx->nbytes: %u\n", __func__, __LINE__, rctx->nbytes);
	dev_dbg(dd->dev, "[%s:%d] rctx->cmd: %x\n", __func__, __LINE__, rctx->cmd);

	if (rctx->ivsize) {
		memcpy(rctx->iv, areq->info, rctx->ivsize);
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

	return crypto_transfer_ablkcipher_request_to_engine(dd->engine, areq);
}

static int zynqaes_setkey(struct crypto_ablkcipher *cipher, const u8 *key,
			    unsigned int len)
{
	struct crypto_tfm *tfm = crypto_ablkcipher_tfm(cipher);
	struct zynqaes_ctx *ctx = crypto_tfm_ctx(tfm);
	int ret = 0;

	dev_dbg(dd->dev, "[%s:%d] Entering function\n", __func__, __LINE__);

	switch (len) {
	case AES_KEYSIZE_128:
	case AES_KEYSIZE_256:
		ctx->key_len = len;
		memcpy(ctx->key, key, len);
		break;
	case AES_KEYSIZE_192:
		dev_info(dd->dev, "[%s:%d] 192-bit keys not supported!",
				__func__, __LINE__);
		ret = -ENOTSUPP;
		break;
	default:
		crypto_ablkcipher_set_flags(cipher, CRYPTO_TFM_RES_BAD_KEY_LEN);
		dev_err(dd->dev, "[%s:%d] Invalid key size! (must be 128/192/256 bits)",
				__func__, __LINE__);

		ret = -EINVAL;
	}

	return ret;
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

static int zynqaes_ctr_encrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_CTR_ENCRYPT);
}

static int zynqaes_ctr_decrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_CTR_DECRYPT);
}

static int zynqaes_cfb_encrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_CFB_ENCRYPT);
}

static int zynqaes_cfb_decrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_CFB_DECRYPT);
}

static int zynqaes_ofb_encrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_OFB_ENCRYPT);
}

static int zynqaes_ofb_decrypt(struct ablkcipher_request *areq)
{
	return zynqaes_crypt(areq, ZYNQAES_OFB_DECRYPT);
}

static int zynqaes_cra_init(struct crypto_tfm *tfm)
{
	struct zynqaes_ctx *ctx = crypto_tfm_ctx(tfm);

	tfm->crt_ablkcipher.reqsize = sizeof(struct zynqaes_reqctx);

	ctx->enginectx.op.prepare_request = NULL;
	ctx->enginectx.op.unprepare_request = NULL;
	ctx->enginectx.op.do_one_request = zynqaes_crypt_req;

	return 0;
}

static struct crypto_alg zynqaes_ecb_alg = {
	.cra_name		=	"ecb(aes)",
	.cra_driver_name	=	"zynqaes-ecb",
	.cra_priority		=	200,
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
	.cra_priority		=	200,
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
	.cra_priority		=	200,
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
	.cra_priority		=	200,
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
			.encrypt		=	zynqaes_ctr_encrypt,
			.decrypt		=	zynqaes_ctr_decrypt,
		}
	}
};

static struct crypto_alg zynqaes_cfb_alg = {
	.cra_name		=	"cfb(aes)",
	.cra_driver_name	=	"zynqaes-cfb",
	.cra_priority		=	200,
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

static struct crypto_alg zynqaes_ofb_alg = {
	.cra_name		=	"ofb(aes)",
	.cra_driver_name	=	"zynqaes-ofb",
	.cra_priority		=	200,
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
			.encrypt		=	zynqaes_ofb_encrypt,
			.decrypt		=	zynqaes_ofb_decrypt,
		}
	}
};

static int zynqaes_probe(struct platform_device *pdev)
{
	int err;
	const char *dma_name;
	struct device_node *node;

	pr_debug("[%s:%d]: Entering function\n", __func__, __LINE__);

	dd = devm_kzalloc(&pdev->dev, sizeof(*dd), GFP_KERNEL);
	if (!dd) {
		dev_err(dd->dev, "[%s:%d] zynqaes_dev: Allocating memory failed\n", __func__, __LINE__);
		err = -ENOMEM;
		goto out_err;
	}

	dd->dev = &pdev->dev;

	if (!pdev->dev.of_node) {
		dev_err(dd->dev, "[%s:%d] OF node not found!\n", __func__, __LINE__);
		err = -ENODEV;
		goto out_err;
	}

	node = pdev->dev.of_node;
	err = of_property_read_string_index(node, "dma-names", 0, &dma_name);
	if (err) {
		dev_err(dd->dev, "[%s:%d] Tx: reading channel name failed!\n", __func__, __LINE__);
		goto out_err;
	}

	dd->tx_chan = dma_request_chan(dd->dev, dma_name);
	if (IS_ERR(dd->tx_chan)) {
		err = PTR_ERR(dd->tx_chan);
		dev_err(dd->dev, "[%s:%d] Tx: requesting channel failed!\n", __func__, __LINE__);
		goto out_err;
	}

	err = of_property_read_string_index(node, "dma-names", 1, &dma_name);
	if (err) {
		dev_err(dd->dev, "[%s:%d] Rx: reading channel name failed!\n", __func__, __LINE__);
		goto free_tx_chan;
	}

	dd->rx_chan = dma_request_chan(dd->dev, dma_name);
	if (IS_ERR(dd->rx_chan)) {
		err = PTR_ERR(dd->rx_chan);
		dev_err(dd->dev, "[%s:%d] Rx: requesting channel failed!\n", __func__, __LINE__);
		goto free_tx_chan;
	}

	/* Initialize crypto engine */
	dd->engine = crypto_engine_alloc_init(dd->dev, 1);
	if (dd->engine == NULL) {
		err = -ENOMEM;
		goto free_rx_chan;
	}

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

	if ((err = crypto_register_alg(&zynqaes_ofb_alg)))
		goto free_cfb_alg;

	dev_dbg(dd->dev, "[%s:%d]: Probing successful \n", __func__, __LINE__);

	return 0;

free_cfb_alg:
	crypto_unregister_alg(&zynqaes_cfb_alg);

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

out_err:
	dev_err(&pdev->dev, "[%s:%d] Probe failed with error: %d", __func__, __LINE__, err);

	return err;
}

static int zynqaes_remove(struct platform_device *pdev)
{
	dev_dbg(dd->dev, "[%s:%d] Entering function\n", __func__, __LINE__);

	crypto_unregister_alg(&zynqaes_ecb_alg);
	crypto_unregister_alg(&zynqaes_cbc_alg);
	crypto_unregister_alg(&zynqaes_ctr_alg);
	crypto_unregister_alg(&zynqaes_pcbc_alg);
	crypto_unregister_alg(&zynqaes_cfb_alg);
	crypto_unregister_alg(&zynqaes_ofb_alg);

	crypto_engine_exit(dd->engine);

	dmaengine_terminate_all(dd->rx_chan);
	dmaengine_terminate_all(dd->tx_chan);

	dma_release_channel(dd->rx_chan);
	dma_release_channel(dd->tx_chan);

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

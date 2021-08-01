#include <crypto/internal/skcipher.h>

#include "zynqaes.h"

struct zynqaes_skcipher_ctx {
	struct zynqaes_ctx base;
};

struct zynqaes_skcipher_reqctx {
	struct zynqaes_skcipher_ctx *ctx;

	struct skcipher_request *areq;
	struct scatterlist tx_sg[4];
	unsigned int nbytes;

	struct zynqaes_reqctx_base base;
};

static void zynqaes_skcipher_sg_restore(struct scatterlist *sg,
					unsigned int nents,
					unsigned int remainder)
{
	if (!remainder || !nents)
		return;

	while (--nents > 0 && sg)
		sg = sg_next(sg);

	if (!sg)
		return;

	sg->length += remainder;

	return;
}

static void zynqaes_skcipher_dma_sg_restore(struct zynqaes_dma_ctx *dma)
{
	zynqaes_skcipher_sg_restore(dma->tx_sg, dma->tx_nents,
				    dma->tx_remainder);

	zynqaes_skcipher_sg_restore(dma->rx_sg, dma->rx_nents,
				    dma->rx_remainder);
}

static void zynqaes_skcipher_dma_callback(void *data)
{
	struct zynqaes_reqctx_base *rctx_base = data;
	struct zynqaes_dma_ctx *dma_ctx = &rctx_base->dma_ctx;
	struct zynqaes_skcipher_reqctx *rctx_sk = container_of(rctx_base,
					struct zynqaes_skcipher_reqctx, base);
	struct zynqaes_dev *dd = rctx_base->dd;

	dma_unmap_sg(dd->dev, dma_ctx->tx_sg, dma_ctx->tx_nents,
			DMA_TO_DEVICE);
	dma_unmap_sg(dd->dev, dma_ctx->rx_sg, dma_ctx->rx_nents,
			DMA_FROM_DEVICE);

	zynqaes_skcipher_dma_sg_restore(dma_ctx);

	crypto_finalize_skcipher_request(dd->engine, rctx_sk->areq, 0);
}

static int zynqaes_skcipher_enqueue_next_dma_op(struct zynqaes_skcipher_reqctx *rctx)
{
	struct zynqaes_dma_ctx *dma_ctx = &rctx->base.dma_ctx;
	struct zynqaes_skcipher_ctx *ctx = rctx->ctx;
	struct skcipher_request *areq = rctx->areq;
	struct zynqaes_dev *dd = rctx->base.dd;

	unsigned int nsg = rctx->base.ivsize ? 4 : 3;
	struct scatterlist *sg;
	unsigned int nbytes;
	int ret;

	memset(dma_ctx, 0, sizeof(*dma_ctx));

	sg_init_table(rctx->tx_sg, nsg);
	sg_set_buf(&rctx->tx_sg[0], &rctx->base.cmd, sizeof(rctx->base.cmd));
	sg_set_buf(&rctx->tx_sg[1], ctx->base.key, ctx->base.key_len);
	if (rctx->base.ivsize) {
		sg_set_buf(&rctx->tx_sg[2], rctx->base.iv, AES_BLOCK_SIZE);
	}
	sg_chain(rctx->tx_sg, nsg, areq->src);
	dma_ctx->tx_sg = rctx->tx_sg;

	/*
	 * In ipsec, the last scatterlist has 12 extra bytes (ESP authenc. data).
	 * Since the hw expects rctx->nbytes in total, resize it so the total 
	 * scatterlist array length is rctx->nbytes.
	 */
	dma_ctx->tx_remainder = 0;
	dma_ctx->rx_remainder = 0;

	nbytes = rctx->nbytes;
	for (sg = areq->src; sg; sg = sg_next(sg)) {
		++dma_ctx->tx_nents;

		if (sg->length == nbytes)
			break;

		if (sg->length > nbytes) {
			dma_ctx->tx_remainder = sg->length - nbytes;
			sg->length = nbytes;
			break;
		}

		nbytes -= sg->length;
	}
	dma_ctx->tx_nents += nsg - 1;

	dma_ctx->rx_sg = areq->dst;
	dma_ctx->rx_nents = sg_nents_for_len(dma_ctx->rx_sg, rctx->nbytes);

	dma_ctx->callback = zynqaes_skcipher_dma_callback;

	dev_dbg(dd->dev, "[%s:%d] dma_ctx->tx_nents: %d\n", __func__, __LINE__,
			dma_ctx->tx_nents);
	dev_dbg(dd->dev, "[%s:%d] dma_ctx->rx_nents: %d\n", __func__, __LINE__,
			dma_ctx->rx_nents);

	ret = zynqaes_dma_op(&rctx->base);
	if (ret) {
		dev_err(dd->dev, "[%s:%d] zynqaes_dma_op failed with: %d",
					__func__, __LINE__, ret);
		goto out_err;
	}

	return 0;

out_err:
	return ret;
}

static int zynqaes_skcipher_crypt_req(struct crypto_engine *engine,
			     void *req)
{
	struct skcipher_request *areq = container_of(req, struct skcipher_request, base);
	struct crypto_skcipher *cipher = crypto_skcipher_reqtfm(areq);
	struct crypto_tfm *tfm = crypto_skcipher_tfm(cipher);
	struct zynqaes_skcipher_ctx *ctx = crypto_tfm_ctx(tfm);
	struct zynqaes_skcipher_reqctx *rctx = skcipher_request_ctx(areq);
	struct zynqaes_dev *dd = rctx->base.dd;
	int ret;

	rctx->ctx = ctx;
	rctx->areq = areq;
	rctx->nbytes = areq->cryptlen;
	rctx->base.ivsize = crypto_skcipher_ivsize(cipher);

	zynqaes_set_key_bit(ctx->base.key_len, &rctx->base);

	dev_dbg(dd->dev, "[%s:%d] rctx->nbytes: %u\n", __func__, __LINE__,
			rctx->nbytes);
	dev_dbg(dd->dev, "[%s:%d] rctx->cmd: %x\n", __func__, __LINE__,
			rctx->base.cmd);

	if (rctx->base.ivsize) {
		memcpy(rctx->base.iv, areq->iv, rctx->base.ivsize);
	}

	ret = zynqaes_skcipher_enqueue_next_dma_op(rctx);
	if (ret) {
		dev_err(dd->dev, "[%s:%d] zynqaes_dma_op failed with: %d",
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
	struct zynqaes_dev *dd = zynqaes_find_dev();

	rctx->base.dd = dd;
	rctx->base.cmd = cmd;

	return crypto_transfer_skcipher_request_to_engine(dd->engine, areq);
}

static int zynqaes_skcipher_setkey(struct crypto_skcipher *tfm, const u8 *key,
				   unsigned int len)
{
	struct zynqaes_skcipher_ctx *ctx = crypto_skcipher_ctx(tfm);

	return zynqaes_setkey(&ctx->base, key, len);
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
	struct zynqaes_skcipher_ctx *ctx = crypto_skcipher_ctx(tfm);

	crypto_skcipher_set_reqsize(tfm, sizeof(struct zynqaes_skcipher_reqctx));

	ctx->base.enginectx.op.prepare_request = NULL;
	ctx->base.enginectx.op.unprepare_request = NULL;
	ctx->base.enginectx.op.do_one_request = zynqaes_skcipher_crypt_req;

	return 0;
}

static struct skcipher_alg zynqaes_skcipher_algs[] = {
{
	.base.cra_name		=	"ecb(aes)",
	.base.cra_driver_name	=	"zynqaes-ecb",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	AES_BLOCK_SIZE,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_skcipher_ctx),
	.base.cra_module	=	THIS_MODULE,

	.min_keysize		=	AES_MIN_KEY_SIZE,
	.max_keysize		=	AES_MAX_KEY_SIZE,
	.init			=	zynqaes_skcipher_init,
	.setkey			=	zynqaes_skcipher_setkey,
	.encrypt		=	zynqaes_ecb_encrypt,
	.decrypt		=	zynqaes_ecb_decrypt,
}, {
	.base.cra_name		=	"cbc(aes)",
	.base.cra_driver_name	=	"zynqaes-cbc",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	AES_BLOCK_SIZE,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_skcipher_ctx),
	.base.cra_module	=	THIS_MODULE,

	.min_keysize		=	AES_MIN_KEY_SIZE,
	.max_keysize		=	AES_MAX_KEY_SIZE,
	.ivsize			=	AES_BLOCK_SIZE,
	.init			=	zynqaes_skcipher_init,
	.setkey			=	zynqaes_skcipher_setkey,
	.encrypt		=	zynqaes_cbc_encrypt,
	.decrypt		=	zynqaes_cbc_decrypt,
}, {
	.base.cra_name		=	"pcbc(aes)",
	.base.cra_driver_name	=	"zynqaes-pcbc",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	AES_BLOCK_SIZE,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_skcipher_ctx),
	.base.cra_module	=	THIS_MODULE,

	.min_keysize		=	AES_MIN_KEY_SIZE,
	.max_keysize		=	AES_MAX_KEY_SIZE,
	.ivsize			=	AES_BLOCK_SIZE,
	.init			=	zynqaes_skcipher_init,
	.setkey			=	zynqaes_skcipher_setkey,
	.encrypt		=	zynqaes_pcbc_encrypt,
	.decrypt		=	zynqaes_pcbc_decrypt,
}, {
	.base.cra_name		=	"ctr(aes)",
	.base.cra_driver_name	=	"zynqaes-ctr",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	AES_BLOCK_SIZE,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_skcipher_ctx),
	.base.cra_module	=	THIS_MODULE,

	.min_keysize		=	AES_MIN_KEY_SIZE,
	.max_keysize		=	AES_MAX_KEY_SIZE,
	.ivsize			=	AES_BLOCK_SIZE,
	.init			=	zynqaes_skcipher_init,
	.setkey			=	zynqaes_skcipher_setkey,
	.encrypt		=	zynqaes_ctr_encrypt,
	.decrypt		=	zynqaes_ctr_decrypt,
}, {
	.base.cra_name		=	"cfb(aes)",
	.base.cra_driver_name	=	"zynqaes-cfb",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	AES_BLOCK_SIZE,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_skcipher_ctx),
	.base.cra_module	=	THIS_MODULE,

	.min_keysize		=	AES_MIN_KEY_SIZE,
	.max_keysize		=	AES_MAX_KEY_SIZE,
	.ivsize			=	AES_BLOCK_SIZE,
	.init			=	zynqaes_skcipher_init,
	.setkey			=	zynqaes_skcipher_setkey,
	.encrypt		=	zynqaes_cfb_encrypt,
	.decrypt		=	zynqaes_cfb_decrypt,
}, {
	.base.cra_name		=	"ofb(aes)",
	.base.cra_driver_name	=	"zynqaes-ofb",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	AES_BLOCK_SIZE,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_skcipher_ctx),
	.base.cra_module	=	THIS_MODULE,

	.min_keysize		=	AES_MIN_KEY_SIZE,
	.max_keysize		=	AES_MAX_KEY_SIZE,
	.ivsize			=	AES_BLOCK_SIZE,
	.init			=	zynqaes_skcipher_init,
	.setkey			=	zynqaes_skcipher_setkey,
	.encrypt		=	zynqaes_ofb_encrypt,
	.decrypt		=	zynqaes_ofb_decrypt,
}
};

void zynqaes_unregister_skciphers(void)
{
	crypto_unregister_skciphers(zynqaes_skcipher_algs,
				    ARRAY_SIZE(zynqaes_skcipher_algs));
}

int zynqaes_register_skciphers(void)
{
	return crypto_register_skciphers(zynqaes_skcipher_algs,
					  ARRAY_SIZE(zynqaes_skcipher_algs));
}

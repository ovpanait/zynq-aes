#include <crypto/internal/aead.h>
#include <crypto/gcm.h>

#include "zynqaes.h"

#define ZYNQAES_GCM_TX_HEADER_NSG 6
#define ZYNQAES_GCM_TX_EXTRA_NSG  4
#define ZYNQAES_GCM_RX_EXTRA_NSG  3

struct zynqaes_aead_ctx {
	struct zynqaes_ctx base;

	unsigned int authsize;

	/* Due to hardware GCM limitations, we need to pad inputs that are not
	 * multiples of AES_BLOCK_SIZE.
	 */
	u8 zero_blk[AES_BLOCK_SIZE];
};

struct zynqaes_aead_reqctx {
	struct zynqaes_aead_ctx *aead_ctx;
	struct aead_request *areq;

	bool need_padding;

	struct scatterlist tx_sg_header[ZYNQAES_GCM_TX_HEADER_NSG];
	struct scatterlist *tx_sg_pad;
	u64 tx_nbytes;

	struct scatterlist *rx_sg;
	u64 rx_nbytes;

	u64 cryptlen_nbits;
	u64 cryptlen_nbytes_pad;
	unsigned int cryptlen_nbytes;
	unsigned int cryptlen_padding;

	u64 assoclen_nbits;
	u64 assoclen_nbytes_pad;
	unsigned int assoclen_nbytes;
	unsigned int assoclen_padding;

	u8 in_tag[ZYNQAES_TAG_MAX];
	u8 out_tag[ZYNQAES_TAG_MAX];

	struct zynqaes_reqctx_base base;
};

#ifdef DEBUG
static void zynqaes_aead_dump_sg(struct scatterlist *sg)
{
	unsigned int nbytes = 0;
	unsigned int index = 0;
	u8 buf[AES_BLOCK_SIZE];

	nbytes = sg->length;

	while (nbytes >= AES_BLOCK_SIZE) {
		scatterwalk_map_and_copy(buf, sg, index, AES_BLOCK_SIZE, 0);
		print_hex_dump_debug("", DUMP_PREFIX_NONE, 16, 1, buf,
				     AES_BLOCK_SIZE, false);
		index += AES_BLOCK_SIZE;
		nbytes -= AES_BLOCK_SIZE;
	}

	if (nbytes) {
		scatterwalk_map_and_copy(buf, sg, index, nbytes, 0);
		print_hex_dump_debug("", DUMP_PREFIX_NONE, 16, 1, buf,
				     nbytes, false);
	}
}

static void zynqaes_aead_print_sg_list(struct scatterlist *sg)
{
	while (sg) {
		zynqaes_aead_dump_sg(sg);
		sg = sg_next(sg);
	}
}

static void zynqaes_aead_debug_rctx(struct zynqaes_aead_reqctx *rctx)
{
	struct zynqaes_dev *dd = rctx->base.dd;

	dev_dbg(dd->dev, "rctx->need_padding: %d\n", rctx->need_padding);

	dev_dbg(dd->dev, "rctx->assoclen_nbits: %llu\n",
						rctx->assoclen_nbits);
	dev_dbg(dd->dev, "rctx->assoclen_nbytes: %u\n",
						rctx->assoclen_nbytes);
	dev_dbg(dd->dev, "rctx->assoclen_nbytes_pad: %llu\n",
						rctx->assoclen_nbytes_pad);
	dev_dbg(dd->dev, "rctx->assoclen_padding: %u\n",
						rctx->assoclen_padding);

	dev_dbg(dd->dev, "rctx->cryptlen_nbytes: %u\n",
						rctx->cryptlen_nbytes);
	dev_dbg(dd->dev, "rctx->cryptlen_nbits: %llu\n",
						rctx->cryptlen_nbits);
	dev_dbg(dd->dev, "rctx->cryptlen_nbytes_pad: %llu\n",
						rctx->cryptlen_nbytes_pad);
	dev_dbg(dd->dev, "rctx->cryptlen_padding: %u\n",
						rctx->cryptlen_padding);
}

static void zynqaes_dump_dma_ctx(struct zynqaes_dev *dd,
				 struct zynqaes_dma_ctx *dma_ctx)
{
	struct scatterlist *sg;
	u64 nents;

	dev_dbg(dd->dev, "[%s:%d] dma_ctx->tx_nents: %d\n", __func__, __LINE__,
			 dma_ctx->tx_nents);
	dev_dbg(dd->dev, "[%s:%d] dma_ctx->rx_nents: %d\n", __func__, __LINE__,
			 dma_ctx->rx_nents);

	for (nents = dma_ctx->tx_nents, sg = dma_ctx->tx_sg; nents;
						sg = sg_next(sg), --nents) {
		dev_dbg(dd->dev, "dma_ctx->tx_sg: length: %u", sg->length);
		zynqaes_aead_dump_sg(sg);
	}
	for (nents = dma_ctx->rx_nents, sg = dma_ctx->rx_sg; nents;
						sg = sg_next(sg), --nents) {
		dev_dbg(dd->dev, "dma_ctx->rx_sg: length: %u", sg->length);
		zynqaes_aead_dump_sg(sg);
	}
}
#endif

static int zynqaes_aead_setkey(struct crypto_aead *tfm, const u8 *key,
				   unsigned int len)
{
	struct zynqaes_aead_ctx *aead_ctx = crypto_aead_ctx(tfm);
	struct zynqaes_ctx *ctx = &aead_ctx->base;

	return zynqaes_setkey(ctx, key, len);
}

static int zynqaes_aead_setauthsize(struct crypto_aead *aead,
				       unsigned int authsize)
{
	struct crypto_tfm *tfm = crypto_aead_tfm(aead);
	struct zynqaes_aead_ctx *tfm_ctx = crypto_tfm_ctx(tfm);

	tfm_ctx->authsize = authsize;

	return 0;
}

static void zynqaes_aead_sg_restore(struct scatterlist *sg,
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

static int zynqaes_aead_sg_resize(struct scatterlist *sg, u64 nbytes, unsigned int *remainder)
{
	if (!nbytes)
		return 0;

	for (; sg && nbytes > sg->length; sg = sg_next(sg))
		nbytes -= sg->length;

	if (!sg)
		return -EINVAL;

	*remainder = sg->length - nbytes;
	sg->length = nbytes;

	return 0;
}

static void zynqaes_aead_dma_sg_restore(struct zynqaes_dma_ctx *dma)
{
	zynqaes_aead_sg_restore(dma->tx_sg, dma->tx_nents,
				    dma->tx_remainder);

	zynqaes_aead_sg_restore(dma->rx_sg, dma->rx_nents,
				    dma->rx_remainder);
}

static int zynqaes_aead_sg_copy(struct scatterlist *dst,
				struct scatterlist *src,
				unsigned int nbytes,
				struct scatterlist src_next[2])
{
	int nsg = 0;

	for (;;) {
		if (!nbytes)
			break;

		if (src->length > nbytes)
			break;

		/* Chain entries have src->length == 0, so skip them */
		if (src->length) {
			sg_set_page(dst, sg_page(src), src->length, src->offset);
			nbytes -= src->length;
			dst = sg_next(dst);
			++nsg;
		}

		src = sg_next(src);
	}

	if (nbytes) {
		sg_set_page(dst, sg_page(src), nbytes, src->offset);
		dst = sg_next(dst);
		++nsg;
	}

	if (src) {
		unsigned int len = src->length - nbytes;
		unsigned int offset = src->offset + nbytes;
		struct page *page = sg_page(src);

		sg_init_table(src_next, 2);
		sg_set_page(src_next, page, len, offset);
		scatterwalk_crypto_chain(src_next, sg_next(src), 2);
	}

	return nsg;
}

static void zynqaes_aead_dma_callback(void *data)
{
	struct zynqaes_dev *dd;
	struct zynqaes_dma_ctx *dma_ctx;
	struct zynqaes_reqctx_base *rctx_base;
	struct zynqaes_aead_reqctx *rctx_aead;
	int ret = 0;

	rctx_base = data;
	dd = rctx_base->dd;
	dma_ctx = &rctx_base->dma_ctx;
	rctx_aead = container_of(rctx_base, struct zynqaes_aead_reqctx, base);

	dma_unmap_sg(dd->dev, dma_ctx->tx_sg, dma_ctx->tx_nents,
			DMA_TO_DEVICE);
	dma_unmap_sg(dd->dev, dma_ctx->rx_sg, dma_ctx->rx_nents,
			DMA_FROM_DEVICE);

	zynqaes_aead_dma_sg_restore(dma_ctx);

	if (rctx_base->cmd & ZYNQAES_DECRYPTION_FLAG) {
		/* Compare computed tag to the provided one */
		print_hex_dump_debug("tag out: ", DUMP_PREFIX_NONE,
				     16, 1, rctx_aead->out_tag,
				     rctx_aead->aead_ctx->authsize,
				     false);

		if (memcmp(rctx_aead->in_tag, rctx_aead->out_tag,
					rctx_aead->aead_ctx->authsize))
			ret = -EBADMSG;
	}

	kfree(rctx_aead->tx_sg_pad);
	kfree(rctx_aead->rx_sg);

	crypto_finalize_aead_request(dd->engine, rctx_aead->areq, ret);
}

static int zynqaes_aead_enqueue_next_dma_op(struct zynqaes_aead_reqctx *rctx)
{
	struct zynqaes_dev *dd;
	struct zynqaes_ctx *ctx;
	struct zynqaes_aead_ctx *aead_ctx;
	struct zynqaes_dma_ctx *dma_ctx;
	struct aead_request *areq;
	u64 src_size;
	u64 nents;
	int ret;

	struct scatterlist *sg_dst_crypt;
	struct scatterlist sg_nxt[2];
	struct scatterlist *sg_ptr;

	areq = rctx->areq;
	dd = rctx->base.dd;
	ctx = rctx->base.ctx;
	aead_ctx = rctx->aead_ctx;
	dma_ctx = &rctx->base.dma_ctx;

	memset(dma_ctx, 0, sizeof(*dma_ctx));

	rctx->assoclen_nbytes_pad = round_up((u64)rctx->assoclen_nbytes,
					     AES_BLOCK_SIZE);
	rctx->cryptlen_nbytes_pad = round_up((u64)rctx->cryptlen_nbytes,
					     AES_BLOCK_SIZE);
	rctx->assoclen_padding = rctx->assoclen_nbytes_pad - rctx->assoclen_nbytes;
	rctx->cryptlen_padding = rctx->cryptlen_nbytes_pad - rctx->cryptlen_nbytes;
	rctx->need_padding = rctx->assoclen_padding || rctx->cryptlen_padding;

#ifdef DEBUG
	zynqaes_aead_debug_rctx(rctx);
#endif

	/* Rx path */
	/* Skip to cryptdata in areq->dst */
	sg_dst_crypt = scatterwalk_ffwd(sg_nxt, areq->dst, areq->assoclen);
	nents = sg_nents(sg_dst_crypt);

	rctx->rx_sg = kzalloc((nents + ZYNQAES_GCM_RX_EXTRA_NSG) *
			      sizeof(struct scatterlist), GFP_ATOMIC);
	if (!rctx->rx_sg) {
		dev_err(dd->dev, "rctx->rx_sg: Memory allocation failed!");
		ret = -ENOMEM;
		goto out_err;
	}

	sg_ptr = rctx->rx_sg;
	sg_ptr += zynqaes_aead_sg_copy(sg_ptr, sg_dst_crypt,
					rctx->cryptlen_nbytes,
					sg_nxt);

	if (rctx->cryptlen_padding) {
		sg_set_buf(sg_ptr, aead_ctx->zero_blk, rctx->cryptlen_padding);
		++sg_ptr;
	}

	if (rctx->base.cmd & ZYNQAES_DECRYPTION_FLAG)
		sg_set_buf(sg_ptr, rctx->out_tag, ZYNQAES_TAG_MAX);
	else {
		unsigned int authsize = rctx->aead_ctx->authsize;

		sg_ptr += zynqaes_aead_sg_copy(sg_ptr, sg_nxt, authsize, sg_nxt);

		if (authsize < ZYNQAES_TAG_MAX) {
			sg_set_buf(sg_ptr, rctx->out_tag, ZYNQAES_TAG_MAX - authsize);
			++sg_ptr;
		}

		--sg_ptr;
	}
	sg_mark_end(sg_ptr);

	/* Tx path */
	src_size = rctx->assoclen_nbytes_pad + rctx->cryptlen_nbytes_pad;
	rctx->tx_sg_pad = NULL;
	rctx->tx_nbytes = 0;

	sg_init_table(rctx->tx_sg_header, ZYNQAES_GCM_TX_HEADER_NSG);
	sg_set_buf(&rctx->tx_sg_header[0], &rctx->base.cmd, sizeof(rctx->base.cmd));
	sg_set_buf(&rctx->tx_sg_header[1], ctx->key, ctx->key_len);
	sg_set_buf(&rctx->tx_sg_header[2], rctx->base.iv, AES_BLOCK_SIZE);
	sg_set_buf(&rctx->tx_sg_header[3], &rctx->assoclen_nbits, sizeof(u64));
	sg_set_buf(&rctx->tx_sg_header[4], &rctx->cryptlen_nbits, sizeof(u64));
	rctx->tx_nbytes += sizeof(rctx->base.cmd) + ctx->key_len +
			   AES_BLOCK_SIZE + sizeof(u64) + sizeof(u64) +
			   src_size;

	if (rctx->need_padding) {
		nents = sg_nents(areq->src);

		rctx->tx_sg_pad = kzalloc((nents + ZYNQAES_GCM_TX_EXTRA_NSG) *
					  sizeof(struct scatterlist), GFP_ATOMIC);
		if (!rctx->tx_sg_pad) {
			dev_err(dd->dev, "rctx->tx_sg_pad: Memory allocation failed!");
			ret = -ENOMEM;
			goto free_rx_sg;
		}

		sg_ptr = rctx->tx_sg_pad;
		sg_ptr += zynqaes_aead_sg_copy(sg_ptr, areq->src,
					       areq->assoclen,
					       sg_nxt);

		if (rctx->assoclen_padding) {
			sg_set_buf(sg_ptr, aead_ctx->zero_blk,
					   rctx->assoclen_padding);
			sg_ptr++;
		}

		sg_ptr += zynqaes_aead_sg_copy(sg_ptr, sg_nxt,
					       rctx->cryptlen_nbytes,
					       sg_nxt);
		if (rctx->cryptlen_padding)
			sg_set_buf(sg_ptr, aead_ctx->zero_blk,
					   rctx->cryptlen_padding);

		sg_chain(rctx->tx_sg_header, ZYNQAES_GCM_TX_HEADER_NSG,
			 rctx->tx_sg_pad);
	} else {
		/* Both assoc data and crypto payload lenghts are multiples of
		 * AES_BLOCK_SIZE, so we just chain the scatterlist provided by
		 * the crypto layer.
		 */
		ret = zynqaes_aead_sg_resize(areq->src, src_size,
					     &dma_ctx->tx_remainder);
		if (ret)
			goto free_rx_sg;

		sg_chain(rctx->tx_sg_header, ZYNQAES_GCM_TX_HEADER_NSG,
			 areq->src);
	}

	/* Set up dma_ctx struct and perform DMA. */
	dma_ctx->tx_sg = rctx->tx_sg_header;
	dma_ctx->rx_sg = rctx->rx_sg;
	dma_ctx->tx_nents = sg_nents_for_len(dma_ctx->tx_sg, rctx->tx_nbytes);
	dma_ctx->rx_nents = sg_nents(dma_ctx->rx_sg);
	dma_ctx->callback = zynqaes_aead_dma_callback;

#ifdef DEBUG
	zynqaes_dump_dma_ctx(dd, dma_ctx);
#endif

	ret = zynqaes_dma_op(&rctx->base);
	if (ret) {
		dev_err(dd->dev, "[%s:%d] zynqaes_dma_op failed with: %d",
			__func__, __LINE__, ret);
		goto free_tx_sg_pad;
	}

	return 0;

free_tx_sg_pad:
	kfree(rctx->tx_sg_pad);

free_rx_sg:
	kfree(rctx->rx_sg);

out_err:
	return ret;
}

static int zynqaes_aead_crypt_req(struct crypto_engine *engine,
			     void *req)
{
	struct aead_request *areq = container_of(req, struct aead_request, base);
	struct crypto_aead *cipher = crypto_aead_reqtfm(areq);
	struct crypto_tfm *tfm = crypto_aead_tfm(cipher);
	struct zynqaes_aead_ctx *aead_ctx = crypto_tfm_ctx(tfm);
	struct zynqaes_aead_reqctx *rctx = aead_request_ctx(areq);
	struct zynqaes_dev *dd = rctx->base.dd;
	struct zynqaes_ctx *ctx = &aead_ctx->base;
	int ret;

#ifdef DEBUG
	pr_debug("areq->src:\n");
	zynqaes_aead_print_sg_list(areq->src);
	pr_debug("areq->dst:\n");
	zynqaes_aead_print_sg_list(areq->dst);
#endif

	rctx->base.ctx = ctx;
	rctx->base.ivsize = crypto_aead_ivsize(cipher);

	rctx->areq = areq;
	rctx->aead_ctx = aead_ctx;
	rctx->cryptlen_nbytes = areq->cryptlen;
	if (rctx->base.cmd & ZYNQAES_DECRYPTION_FLAG) {
		rctx->cryptlen_nbytes -= aead_ctx->authsize;

		scatterwalk_map_and_copy(rctx->in_tag, areq->src,
					areq->assoclen + areq->cryptlen -
					aead_ctx->authsize, aead_ctx->authsize, 0);
	}
	rctx->assoclen_nbytes = areq->assoclen;
	rctx->cryptlen_nbits = cpu_to_be64((u64)rctx->cryptlen_nbytes * 8);
	rctx->assoclen_nbits = cpu_to_be64((u64)rctx->assoclen_nbytes * 8);

	zynqaes_set_key_bit(ctx->key_len, &rctx->base);

	dev_dbg(dd->dev, "[%s:%d] rctx->cmd: %x\n", __func__, __LINE__,
		rctx->base.cmd);

	memset(rctx->base.iv, 0, ZYNQAES_IVSIZE_MAX);
	memcpy(rctx->base.iv, areq->iv, rctx->base.ivsize);

	ret = zynqaes_aead_enqueue_next_dma_op(rctx);
	if (ret) {
		dev_err(dd->dev, "[%s:%d] zynqaes_dma_op failed with: %d",
			__func__, __LINE__, ret);
		goto out;
	}

	return 0;

out:
	return ret;
}

static int zynqaes_aead_crypt(struct aead_request *areq, const u32 cmd)
{
	struct zynqaes_aead_reqctx *rctx = aead_request_ctx(areq);
	struct zynqaes_dev *dd = zynqaes_find_dev();

	rctx->base.dd = dd;
	rctx->base.cmd = cmd;

	return crypto_transfer_aead_request_to_engine(dd->engine, areq);
}

static int zynqaes_gcm_encrypt(struct aead_request *areq)
{
	return zynqaes_aead_crypt(areq, ZYNQAES_GCM_ENCRYPT);
}

static int zynqaes_gcm_decrypt(struct aead_request *areq)
{
	return zynqaes_aead_crypt(areq, ZYNQAES_GCM_DECRYPT);
}

static int zynqaes_aead_init(struct crypto_aead *tfm)
{
	struct zynqaes_aead_ctx *aead_ctx = crypto_aead_ctx(tfm);
	struct zynqaes_ctx *ctx = &aead_ctx->base;

	crypto_aead_set_reqsize(tfm, sizeof(struct zynqaes_aead_reqctx));

	ctx->enginectx.op.prepare_request = NULL;
	ctx->enginectx.op.unprepare_request = NULL;
	ctx->enginectx.op.do_one_request = zynqaes_aead_crypt_req;

	return 0;
}

static struct aead_alg zynqaes_aead_algs[] = {
{
	.base.cra_name		=	"gcm(aes)",
	.base.cra_driver_name	=	"zynqaes-gcm",
	.base.cra_priority	=	200,
	.base.cra_flags		=	CRYPTO_ALG_ASYNC,
	.base.cra_blocksize	=	1,
	.base.cra_ctxsize	=	sizeof(struct zynqaes_aead_ctx),
	.base.cra_module	=	THIS_MODULE,

	.init			=	zynqaes_aead_init,
	.setkey			=	zynqaes_aead_setkey,
	.setauthsize		=	zynqaes_aead_setauthsize,
	.encrypt		=	zynqaes_gcm_encrypt,
	.decrypt		=	zynqaes_gcm_decrypt,
	.ivsize			=	GCM_AES_IV_SIZE,
	.maxauthsize		=	AES_BLOCK_SIZE,
}
};

void zynqaes_unregister_aeads(void)
{
	crypto_unregister_aeads(zynqaes_aead_algs,
				    ARRAY_SIZE(zynqaes_aead_algs));
}

int zynqaes_register_aeads(void)
{
	return crypto_register_aeads(zynqaes_aead_algs,
					  ARRAY_SIZE(zynqaes_aead_algs));
}

#ifndef __ZYNQAES_H__
#define __ZYNQAES_H__

#include <crypto/aes.h>
#include <crypto/algapi.h>
#include <crypto/engine.h>
#include <crypto/scatterwalk.h>
#include <linux/dma-mapping.h>
#include <linux/dmaengine.h>
#include <linux/dmapool.h>
#include <linux/slab.h>
#include <linux/workqueue.h>

#define ZYNQAES_CMD_LEN 4

#define ZYNQAES_IVSIZE_MAX AES_BLOCK_SIZE
#define ZYNQAES_TAG_MAX AES_BLOCK_SIZE

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
#define ZYNQAES_GCM_MODE_BIT         12

#define ZYNQAES_ENCRYPTION_FLAG  BIT(ZYNQAES_ENCRYPTION_OP_BIT)
#define ZYNQAES_DECRYPTION_FLAG  BIT(ZYNQAES_DECRYPTION_OP_BIT)
#define ZYNQAES_KEY_128_FLAG     BIT(ZYNQAES_KEY_128_BIT)
#define ZYNQAES_KEY_256_FLAG     BIT(ZYNQAES_KEY_256_BIT)
#define ZYNQAES_ECB_FLAG         BIT(ZYNQAES_ECB_MODE_BIT)
#define ZYNQAES_CBC_FLAG         BIT(ZYNQAES_CBC_MODE_BIT)
#define ZYNQAES_CTR_FLAG         BIT(ZYNQAES_CTR_MODE_BIT)
#define ZYNQAES_CFB_FLAG         BIT(ZYNQAES_CFB_MODE_BIT)
#define ZYNQAES_OFB_FLAG         BIT(ZYNQAES_OFB_MODE_BIT)
#define ZYNQAES_GCM_FLAG         BIT(ZYNQAES_GCM_MODE_BIT)
#define ZYNQAES_PCBC_FLAG        BIT(ZYNQAES_PCBC_MODE_BIT)

#define ZYNQAES_ECB_ENCRYPT  (ZYNQAES_ECB_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_CBC_ENCRYPT  (ZYNQAES_CBC_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_CTR_ENCRYPT  (ZYNQAES_CTR_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_CFB_ENCRYPT  (ZYNQAES_CFB_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_OFB_ENCRYPT  (ZYNQAES_OFB_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_GCM_ENCRYPT  (ZYNQAES_GCM_FLAG  | ZYNQAES_ENCRYPTION_FLAG)
#define ZYNQAES_PCBC_ENCRYPT (ZYNQAES_PCBC_FLAG | ZYNQAES_ENCRYPTION_FLAG)

#define ZYNQAES_ECB_DECRYPT  (ZYNQAES_ECB_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_CBC_DECRYPT  (ZYNQAES_CBC_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_CTR_DECRYPT  (ZYNQAES_CTR_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_CFB_DECRYPT  (ZYNQAES_CFB_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_OFB_DECRYPT  (ZYNQAES_OFB_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_GCM_DECRYPT  (ZYNQAES_GCM_FLAG  | ZYNQAES_DECRYPTION_FLAG)
#define ZYNQAES_PCBC_DECRYPT (ZYNQAES_PCBC_FLAG | ZYNQAES_DECRYPTION_FLAG)

struct zynqaes_dev {
	struct device *dev;
	struct dma_chan *tx_chan;
	struct dma_chan *rx_chan;

	struct crypto_engine *engine;
};

struct zynqaes_ctx {
	struct crypto_engine_ctx enginectx;
	u8 key[AES_MAX_KEY_SIZE];
	unsigned int key_len;
};

struct zynqaes_dma_ctx {
	struct scatterlist *tx_sg;
	struct scatterlist *rx_sg;

	unsigned int tx_nents;
	unsigned int rx_nents;

	unsigned int tx_remainder;
	unsigned int rx_remainder;

	dma_cookie_t tx_cookie;
	dma_cookie_t rx_cookie;
	dma_addr_t tx_dma_handle;
	dma_addr_t rx_dma_handle;

	void (*callback)(void *);
};

struct zynqaes_reqctx_base {
	struct zynqaes_dev *dd;

	u32 cmd;
	u8 iv[ZYNQAES_IVSIZE_MAX];
	unsigned int ivsize;

	struct zynqaes_ctx *ctx;
	struct zynqaes_dma_ctx dma_ctx;
};

struct zynqaes_dev *zynqaes_find_dev(void);
void zynqaes_set_key_bit(unsigned int key_len, struct zynqaes_reqctx_base *rctx);
int zynqaes_setkey(struct zynqaes_ctx *ctx, const u8 *key, unsigned int len);

int zynqaes_dma_op(struct zynqaes_reqctx_base *rctx);

void zynqaes_unregister_skciphers(void);
int zynqaes_register_skciphers(void);

void zynqaes_unregister_aeads(void);
int zynqaes_register_aeads(void);

#endif

#ifndef __AF_ALG_H__
#define __AF_ALG_H__

#ifndef SOL_ALG
#define SOL_ALG 279
#endif

#define AES_BLOCK_SIZE  16
#define AES_IV_SIZE     16
#define AES_KEY128_SIZE 16
#define AES_KEY192_SIZE 24
#define AES_KEY256_SIZE 32

#define GCM_IV_SIZE  12
#define GCM_AAD_SIZE 16
#define GCM_TAGLEN   16

struct crypto_op {
	int tfmfd;
	int opfd;
	struct msghdr msg;
	struct iovec iov;

	size_t iv_size;
	size_t aad_size;
	size_t taglen;
};

void dump_buffer(FILE *file, char *msg, uint8_t *buf, unsigned int size);
void dump_aes_buffer(FILE *file, char *msg, uint8_t *aes_buf, int blocks_no);
void buf_eq(char *desc, uint8_t *buf1, uint8_t *buf2, unsigned int nbytes);

struct crypto_op *crypto_op_create(void);
void crypto_op_init(struct crypto_op *cop, size_t iv_size,
				size_t aad_size, size_t taglen);
void crypto_op_finish(struct crypto_op *cop);
int alloc_buffer(uint8_t **buf, unsigned int size);

int af_alg_sock_setup(struct crypto_op *cop, struct sockaddr_alg *sa);
int af_alg_set_key(struct crypto_op *cop, uint8_t *key, size_t key_size);
int af_alg_set_iv(struct crypto_op *cop, uint8_t *iv);
void *af_alg_get_iv_ptr(struct crypto_op *cop);
int af_alg_set_taglen(struct crypto_op *cop);
int af_alg_set_aadlen(struct crypto_op *cop);

int encrypt(struct crypto_op *cop, uint8_t *data_in, size_t data_in_len,
			uint8_t *data_out, size_t data_out_len);
int decrypt(struct crypto_op *cop, uint8_t *data_in, size_t data_in_len,
			uint8_t *data_out, size_t data_out_len);
#endif

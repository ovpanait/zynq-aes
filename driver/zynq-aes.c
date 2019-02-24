#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/module.h>
#include <crypto/algapi.h>
#include <crypto/aes.h>
#include <asm/io.h>
#include <linux/of_platform.h>

#include <linux/dmaengine.h>
#include <linux/module.h>
#include <linux/version.h>
#include <linux/kernel.h>
#include <linux/dma-mapping.h>
#include <linux/slab.h>
#include <linux/platform_device.h>

#define WAIT 	1
#define NO_WAIT 0

#define ZYNQAES_CMD_LEN 4

#define ZYNQAES_128_BLKS 16

static const u32 zynqaes_encrypt_cmd = 0x20;
static const u32 zynqaes_set_key_cmd = 0x10;
 
static struct dma_chan *tx_chan;
static struct dma_chan *rx_chan;
static struct completion tx_cmp;
static struct completion rx_cmp;
static dma_cookie_t tx_cookie;
static dma_cookie_t rx_cookie;
static dma_addr_t tx_dma_handle;
static dma_addr_t rx_dma_handle;

static const int src_dma_length = ZYNQAES_CMD_LEN + ZYNQAES_128_BLKS; 
static const int dest_dma_length = ZYNQAES_128_BLKS;
static char *encrypt_buf;
static char *key_buf;
static char *cipher_buf;

static void axidma_sync_callback(void *completion)
{
	//dump_stack();
	complete(completion);

}

static dma_cookie_t axidma_prep_buffer(struct dma_chan *chan, dma_addr_t buf, size_t len, 
					enum dma_transfer_direction dir, struct completion *cmp) 
{
	//printk(KERN_INFO "%d: Entering function %s\n", __LINE__, __func__);
	enum dma_ctrl_flags flags = DMA_CTRL_ACK | DMA_PREP_INTERRUPT;
	struct dma_async_tx_descriptor *chan_desc;
	dma_cookie_t cookie;

	chan_desc = dmaengine_prep_slave_single(chan, buf, len, dir, flags);

	/* Make sure the operation was completed successfully
	 */
	if (!chan_desc) {
		printk(KERN_ERR "dmaengine_prep_slave_single error\n");
		cookie = -EBUSY;
	} else {
		chan_desc->callback = axidma_sync_callback;
		chan_desc->callback_param = cmp;

		cookie = dmaengine_submit(chan_desc);
	
	}
	return cookie;
}

static void axidma_start_transfer(struct dma_chan *chan, struct completion *cmp, 
					dma_cookie_t cookie, int wait)
{
	//printk(KERN_INFO "%s:%d: Entering function %s\n", __FILE__, __LINE__, __func__);
	unsigned long timeout = msecs_to_jiffies(5000);
	enum dma_status status;

	init_completion(cmp);
	dma_async_issue_pending(chan);

	if (wait) {
		//printk("Waiting for DMA to complete...\n");

		timeout = wait_for_completion_timeout(cmp, timeout);
		status = dma_async_is_tx_complete(chan, cookie, NULL, NULL);

		if (timeout == 0)  {
			printk(KERN_ERR "DMA timed out\n");
		} else if (status != DMA_COMPLETE) {
			printk(KERN_ERR "DMA returned completion callback status of: %s\n",
			       status == DMA_ERROR ? "error" : "in progress");
		}
	}
}

static int zynqaes_dma_op(char *msg, char *src_dma_buffer, char *dest_dma_buffer)
{
	memcpy(src_dma_buffer + ZYNQAES_CMD_LEN, msg, AES_KEYSIZE_128);
	//print_hex_dump(KERN_INFO, "source: ", DUMP_PREFIX_NONE, 32, 1, src_dma_buffer, src_dma_length, false);

	//print_hex_dump(KERN_INFO, "dest before: ", DUMP_PREFIX_NONE, 32, 1, dest_dma_buffer, dest_dma_length, false);

	//printk(KERN_INFO "xxx: %s:%d\n", __func__, __LINE__);
	if (!rx_chan || !rx_chan->device || !rx_chan->device->dev) {
		printk(KERN_INFO "pula rx: %s:%d\n", __func__, __LINE__);
		return 0;
	}
	
	if (!tx_chan || !tx_chan->device || !tx_chan->device->dev) {
		printk(KERN_INFO "pula tx: %s:%d\n", __func__, __LINE__);
		return 0;
	}
	
	rx_dma_handle = dma_map_single(rx_chan->device->dev, dest_dma_buffer, dest_dma_length, DMA_FROM_DEVICE);
	tx_dma_handle = dma_map_single(tx_chan->device->dev, src_dma_buffer, src_dma_length, DMA_TO_DEVICE);

	//printk(KERN_INFO "xxx: %s:%d\n", __func__, __LINE__);
	rx_cookie = axidma_prep_buffer(rx_chan, rx_dma_handle, dest_dma_length, DMA_DEV_TO_MEM, &rx_cmp);
	tx_cookie = axidma_prep_buffer(tx_chan, tx_dma_handle, src_dma_length, DMA_MEM_TO_DEV, &tx_cmp);
	
	//printk(KERN_INFO "xxx: %s:%d\n", __func__, __LINE__);
	if (dma_submit_error(tx_cookie)) {
		printk(KERN_ERR "xdma_prep_buffer error\n");
		kfree(src_dma_buffer);
		kfree(dest_dma_buffer);	
		return -1;
	}

	axidma_start_transfer(tx_chan, &tx_cmp, tx_cookie, WAIT);
	axidma_start_transfer(rx_chan, &rx_cmp, rx_cookie, WAIT);

	dma_unmap_single(rx_chan->device->dev, rx_dma_handle, dest_dma_length, DMA_FROM_DEVICE);
	dma_unmap_single(tx_chan->device->dev, tx_dma_handle, src_dma_length, DMA_TO_DEVICE);
	
	//print_hex_dump(KERN_INFO, "dest after: ", DUMP_PREFIX_NONE, 32, 1, dest_dma_buffer, dest_dma_length, false);

	return 0;
}

static int zynqaes_dma_buf_init(void)
{
	encrypt_buf = kzalloc(src_dma_length, GFP_KERNEL);
	if (!encrypt_buf) {
		printk(KERN_ERR "encrypt_buf: Allocating DMA memory failed\n");
		goto err_mem;
	}
	memcpy(encrypt_buf, &zynqaes_encrypt_cmd, ZYNQAES_CMD_LEN);

	key_buf = kzalloc(src_dma_length, GFP_KERNEL);
	if (!key_buf) {
		printk(KERN_ERR "key_buf: Allocating DMA memory failed\n");
		goto err_mem;
	}
	memcpy(key_buf, &zynqaes_set_key_cmd, ZYNQAES_CMD_LEN);

	cipher_buf = kzalloc(dest_dma_length, GFP_KERNEL);
	if (!cipher_buf) {
		printk(KERN_ERR "cipher_buf: Allocating DMA memory failed\n");
		goto err_mem;
	}

	return 0;

err_mem:
	return -ENOMEM;
}

static int zynqaes_setkey(struct crypto_tfm *tfm, const u8 *in_key,
			    unsigned int key_len)
{
	//printk(KERN_INFO "%s:%d: Entering function\n", __func__, __LINE__);

	zynqaes_dma_op(in_key, key_buf, cipher_buf);

	return 0;
}

static int zynqaes_ecb_encrypt(struct blkcipher_desc *desc,
			     struct scatterlist *dst, struct scatterlist *src,
			     unsigned int nbytes)
{
	int rv;
	struct blkcipher_walk walk;

	//printk(KERN_INFO "%s:%d: Entering function\n", __func__, __LINE__);

	blkcipher_walk_init(&walk, dst, src, nbytes);
	rv = blkcipher_walk_virt(desc, &walk);

	while ((walk.nbytes)) {
		zynqaes_dma_op(walk.src.virt.addr, encrypt_buf, cipher_buf);
		memcpy(walk.dst.virt.addr, cipher_buf, AES_BLOCK_SIZE);

		rv = blkcipher_walk_done(desc, &walk, walk.nbytes - AES_BLOCK_SIZE);
	}

	return rv;
}

/*static int zynqaes_ecb_decrypt(struct blkcipher_desc *desc,
			     struct scatterlist *dst, struct scatterlist *src,
			     unsigned int nbytes)
{
	int rv;
	struct blkcipher_walk walk;

	blkcipher_walk_init(&walk, dst, src, nbytes);
	rv = blkcipher_walk_virt(desc, &walk);

	while ((walk.nbytes)) {
		//zynqaes_write(walk.src.virt.addr, AES_MODE_DECRYPT);
		//zynqaes_read(walk.dst.virt.addr);

		rv = blkcipher_walk_done(desc, &walk, walk.nbytes - AES_BLOCK_SIZE);
	}

	return rv;
}*/

static struct crypto_alg zynqaes_ecb_alg = {
	.cra_name		=	"ecb(myaes)",
	.cra_driver_name	=	"zynqaes-ecb",
	.cra_priority		=	100,
	.cra_flags		=	CRYPTO_ALG_TYPE_BLKCIPHER,
	.cra_blocksize		=	AES_BLOCK_SIZE,
	.cra_type		=	&crypto_blkcipher_type,
	.cra_module		=	THIS_MODULE,
	.cra_u			=	{
		.blkcipher = {
			.min_keysize		=	AES_KEYSIZE_128,
			.max_keysize		=	AES_KEYSIZE_128,
			.setkey	   		= 	zynqaes_setkey,
			.encrypt		=	zynqaes_ecb_encrypt,
//			.decrypt		=	zynqaes_ecb_decrypt,
		}
	}
};

static int zynqaes_probe(struct platform_device *pdev)
{
	int err;

	printk(KERN_INFO "%s:%d: Entering function\n", __func__, __LINE__);

	tx_chan = dma_request_slave_channel(&pdev->dev, "axidma0");
	if (IS_ERR(tx_chan)) {
		pr_err("xilinx_dmatest: No Tx channel\n");
		return PTR_ERR(tx_chan);
	}

	rx_chan = dma_request_slave_channel(&pdev->dev, "axidma1");
	if (IS_ERR(rx_chan)) {
		err = PTR_ERR(rx_chan);
		pr_err("xilinx_dmatest: No Rx channel\n");
		goto free_tx;
	}

	err = zynqaes_dma_buf_init();
	if (err == -ENOMEM)
		goto free_rx;

	if ((err = crypto_register_alg(&zynqaes_ecb_alg)))
		goto free_rx;

	printk(KERN_INFO "%s: %d: Probing successful \n", __func__, __LINE__);
	return 0;

	printk(KERN_INFO "%s: %d: Probing failed \n", __func__, __LINE__);

free_rx:
	dma_release_channel(rx_chan);
	printk(KERN_INFO "%s:%d: Release rx\n", __func__, __LINE__);
free_tx:
	dma_release_channel(tx_chan);

	return err;
}

static int zynqaes_remove(struct platform_device *pdev)
{
	printk(KERN_INFO "%s:%d: Entering function\n", __func__, __LINE__);

	crypto_unregister_alg(&zynqaes_ecb_alg);

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
	printk(KERN_INFO "%s:%d: Entering function\n", __func__, __LINE__);

	return platform_driver_register(&zynqaes_platform_driver);
}

static void __exit zynqaes_exit(void)
{
	printk(KERN_INFO "%s:%d: Entering function\n", __func__, __LINE__);

	platform_driver_unregister(&zynqaes_platform_driver);
}

module_init(zynqaes_init);
module_exit(zynqaes_exit);
MODULE_LICENSE("GPL");

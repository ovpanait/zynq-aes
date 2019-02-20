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

#if 0
static struct dma_chan *tx_chan;
static struct dma_chan *rx_chan;
static struct completion tx_cmp;
static struct completion rx_cmp;
static dma_cookie_t tx_cookie;
static dma_cookie_t rx_cookie;
static dma_addr_t tx_dma_handle;
static dma_addr_t rx_dma_handle;

#define WAIT 	1
#define NO_WAIT 0

#define AES_SET_KEY 0x10
#define AES_ENCRYPT 0x20

/* Handle a callback and indicate the DMA transfer is complete to another
 * thread of control
 */
static void axidma_sync_callback(void *completion)
{
	/* Step 9, indicate the DMA transaction completed to allow the other
	 * thread of control to finish processing
	 */ 
	//dump_stack();
	complete(completion);

}

/* Prepare a DMA buffer to be used in a DMA transaction, submit it to the DMA engine 
 * to queued and return a cookie that can be used to track that status of the 
 * transaction
 */
static dma_cookie_t axidma_prep_buffer(struct dma_chan *chan, dma_addr_t buf, size_t len, 
					enum dma_transfer_direction dir, struct completion *cmp) 
{
	//printk(KERN_INFO "%d: Entering function %s\n", __LINE__, __func__);
	enum dma_ctrl_flags flags = DMA_CTRL_ACK | DMA_PREP_INTERRUPT;
	struct dma_async_tx_descriptor *chan_desc;
	dma_cookie_t cookie;

	/* Step 5, create a buffer (channel)  descriptor for the buffer since only a  
	 * single buffer is being used for this transfer
	 */

	chan_desc = dmaengine_prep_slave_single(chan, buf, len, dir, flags);

	/* Make sure the operation was completed successfully
	 */
	if (!chan_desc) {
		printk(KERN_ERR "dmaengine_prep_slave_single error\n");
		cookie = -EBUSY;
	} else {
		chan_desc->callback = axidma_sync_callback;
		chan_desc->callback_param = cmp;

		/* Step 6, submit the transaction to the DMA engine so that it's queued
		 * up to be processed later and get a cookie to track it's status
		 */

		cookie = dmaengine_submit(chan_desc);
	
	}
	return cookie;
}

/* Start a DMA transfer that was previously submitted to the DMA engine and then
 * wait for it complete, timeout or have an error
 */
static void axidma_start_transfer(struct dma_chan *chan, struct completion *cmp, 
					dma_cookie_t cookie, int wait)
{
	//printk(KERN_INFO "%s:%d: Entering function %s\n", __FILE__, __LINE__, __func__);
	unsigned long timeout = msecs_to_jiffies(5000);
	enum dma_status status;

	/* Step 7, initialize the completion before using it and then start the 
	 * DMA transaction which was previously queued up in the DMA engine
	 */

	init_completion(cmp);
	dma_async_issue_pending(chan);

	if (wait) {
		printk("Waiting for DMA to complete...\n");

		/* Step 8, wait for the transaction to complete, timeout, or get
		 * get an error
		 */

		timeout = wait_for_completion_timeout(cmp, timeout);
		status = dma_async_is_tx_complete(chan, cookie, NULL, NULL);

		/* Determine if the transaction completed without a timeout and
		 * withtout any errors
		 */
		if (timeout == 0)  {
			printk(KERN_ERR "DMA timed out\n");
		} else if (status != DMA_COMPLETE) {
			printk(KERN_ERR "DMA returned completion callback status of: %s\n",
			       status == DMA_ERROR ? "error" : "in progress");
		}
	}
}

static int aes_send(uint32_t *M, char *src_dma_buffer, int src_dma_length, 
			char *dest_dma_buffer, int dest_dma_length)
{
	memcpy(src_dma_buffer, M, src_dma_length);
	print_hex_dump(KERN_INFO, "source: ", DUMP_PREFIX_NONE, 32, 1, src_dma_buffer, src_dma_length, false);

	print_hex_dump(KERN_INFO, "dest: ", DUMP_PREFIX_NONE, 32, 1, dest_dma_buffer, dest_dma_length, false);

	//printk(KERN_INFO "xxx: %s:%d\n", __func__, __LINE__);
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

	print_hex_dump(KERN_INFO, "dest: ", DUMP_PREFIX_NONE, 32, 1, dest_dma_buffer, dest_dma_length, false);

	return 0;
}

static int axidma_test_transfer(void)
{
	int src_dma_length = 4*5; 
	int dest_dma_length = 4*4;

	//printk(KERN_INFO "%s:%d: Entering function %s\n", __FILE__, __LINE__, __func__);

	char *src_dma_buffer = kmalloc(src_dma_length, GFP_KERNEL);
	char *dest_dma_buffer = kzalloc(dest_dma_length, GFP_KERNEL);

	if (!src_dma_buffer || !dest_dma_buffer) {
		printk(KERN_ERR "Allocating DMA memory failed\n");
		return -1;
	}

	//printk(KERN_INFO "xxx: %s:%d\n", __func__,__LINE__);
	uint32_t M1[]=  {
		AES_SET_KEY,
		//key
		0x54686174,
		0x73206D79,
		0x204B756E,
		0x67204675
	};
	aes_send(M1, src_dma_buffer, src_dma_length, dest_dma_buffer, dest_dma_length);

	uint32_t M2[] = {
		AES_ENCRYPT,
		// plaintext
		0x54776F20,
		0x4F6E6520,
		0x4E696E65,
		0x2054776F,
	};
	aes_send(M2, src_dma_buffer, src_dma_length, dest_dma_buffer, dest_dma_length);

	kfree(src_dma_buffer);
	kfree(dest_dma_buffer);	

	return 0;
}

static const int src_dma_length = 4*5; 
static const int dest_dma_length = 4*4;

static char *src_dma_buffer;
static char *dest_dma_buffer

static int zynqaes_init_buffers()
{
	src_dma_buffer = kmalloc(src_dma_length, GFP_KERNEL);
	dest_dma_buffer = kzalloc(dest_dma_length, GFP_KERNEL);

	if (!src_dma_buffer || !dest_dma_buffer) {
		printk(KERN_ERR "Allocating DMA memory failed\n");
		return -1;
	}
}

#endif

enum AES_MODE {
	AES_MODE_ENCRYPT = 0x00000000,
	AES_MODE_DECRYPT = 0x01010101,
	AES_MODE_SET_KEY = 0x02020202
};

void zynqaes_write(const void *src, enum AES_MODE mode)
{
	//memcpy_toio((u8*)virt_addr + OFFSET_DIN, src, AES_BLOCK_SIZE);
	//iowrite32(mode, (u8*)virt_addr + OFFSET_CTL);

	//while (ioread32((u8*)virt_addr + OFFSET_STAT) == 0) {
		//idle
	//}
}

void zynqaes_read(void *dst)
{
	//memcpy_fromio(dst, (u8*)virt_addr + OFFSET_DOUT, AES_BLOCK_SIZE);
	//
}

static int zynqaes_setkey(struct crypto_tfm *tfm, const u8 *in_key,
			    unsigned int key_len)
{
	//zynqaes_write(in_key, AES_MODE_SET_KEY);

	return 0;
}

static int zynqaes_ecb_encrypt(struct blkcipher_desc *desc,
			     struct scatterlist *dst, struct scatterlist *src,
			     unsigned int nbytes)
{
	int rv;
	struct blkcipher_walk walk;

	blkcipher_walk_init(&walk, dst, src, nbytes);
	rv = blkcipher_walk_virt(desc, &walk);

	while ((walk.nbytes)) {
		//zynqaes_write(walk.src.virt.addr, AES_MODE_ENCRYPT);
		//zynqaes_read(walk.dst.virt.addr);

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
	.cra_name		=	"ecb(aes)",
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

	printk(KERN_INFO "%s:%d: Entering function", __func__, __LINE__);

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

	if ((err = crypto_register_alg(&zynqaes_ecb_alg)))
		goto free_rx;

	//err = axidma_test_transfer();

	printk(KERN_INFO "%s: %d: Probing successful \n", __func__, __LINE__);
	return 0;

	printk(KERN_INFO "%s: %d: Probing failed \n", __func__, __LINE__);

free_rx:
	dma_release_channel(rx_chan);

free_tx:
	dma_release_channel(tx_chan);

	return err;
}

static int zynqaes_remove(struct platform_device *pdev)
{
	printk(KERN_INFO "%s:%d: Entering function", __func__, __LINE__);

	crypto_unregister_alg(&zynqaes_ecb_alg);
	return 0;
}

static struct of_device_id zynqaes_of_match[] = {
	{ .compatible = "zynqaes,zynqaes-1.00.a", },
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

module_platform_driver(zynqaes_platform_driver);

#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/module.h>
#include <crypto/algapi.h>
#include <crypto/aes.h>
#include <asm/io.h>
#include <linux/of_platform.h>

#include <linux/dmaengine.h>
#include <linux/version.h>
#include <linux/dma-mapping.h>
#include <linux/slab.h>
#include <linux/platform_device.h>

#define ZYNQAES_CMD_LEN 4

static const u32 zynqaes_encrypt_cmd = 0x20;
static const u32 zynqaes_set_key_cmd = 0x10;
 
static struct dma_chan *tx_chan;
static struct dma_chan *rx_chan;
static struct completion rx_cmp;
static dma_cookie_t tx_cookie;
static dma_cookie_t rx_cookie;
static dma_addr_t tx_dma_handle;
static dma_addr_t rx_dma_handle;

static const int src_dma_length = ZYNQAES_CMD_LEN + AES_BLOCK_SIZE;
static const int dest_dma_length = AES_BLOCK_SIZE;
static char *encrypt_buf;
static char *key_buf;
static char *cipher_buf;

static void axidma_sync_callback(void *completion)
{
	complete(completion);
}

static int zynqaes_dma_op(char *msg, char *src_dma_buffer, char *dest_dma_buffer)
{
	unsigned long timeout = msecs_to_jiffies(5000);
	struct dma_async_tx_descriptor *tx_chan_desc;
	struct dma_async_tx_descriptor *rx_chan_desc;
	enum dma_ctrl_flags flags = DMA_CTRL_ACK;
	enum dma_status status;

	//printk(KERN_INFO "xxx: %s:%d\n", __func__, __LINE__);

	memcpy(src_dma_buffer + ZYNQAES_CMD_LEN, msg, AES_KEYSIZE_128);

	rx_dma_handle = dma_map_single(rx_chan->device->dev, dest_dma_buffer, dest_dma_length, DMA_FROM_DEVICE);
	tx_dma_handle = dma_map_single(tx_chan->device->dev, src_dma_buffer, src_dma_length, DMA_TO_DEVICE);

	/* Tx Channel */
	tx_chan_desc = dmaengine_prep_slave_single(tx_chan, tx_dma_handle, src_dma_length, DMA_MEM_TO_DEV, flags);
	if (!tx_chan_desc) {
		printk(KERN_ERR "dmaengine_prep_slave_single error\n");
		goto err;
	}
	tx_cookie = dmaengine_submit(tx_chan_desc);
	if (dma_submit_error(tx_cookie)) {
		printk(KERN_ERR "tx_cookie: xdma_prep_buffer error\n");
		goto err;
	}

	/* Rx Channel */
	flags |= DMA_PREP_INTERRUPT;
	rx_chan_desc = dmaengine_prep_slave_single(rx_chan, rx_dma_handle, dest_dma_length, DMA_DEV_TO_MEM, flags);
	if (!rx_chan_desc) {
		printk(KERN_ERR "dmaengine_prep_slave_single error\n");
		goto err;
	}
	rx_chan_desc->callback = axidma_sync_callback;
	rx_chan_desc->callback_param = &rx_cmp;
	rx_cookie = dmaengine_submit(rx_chan_desc);
	if (dma_submit_error(rx_cookie)) {
		printk(KERN_ERR "rx_cookie: xdma_prep_buffer error\n");
		goto err;
	}

	init_completion(&rx_cmp);
	dma_async_issue_pending(tx_chan);
	dma_async_issue_pending(rx_chan);

	status = dma_async_is_tx_complete(rx_chan, rx_cookie, NULL, NULL);
	if (status != DMA_COMPLETE) {
		timeout = wait_for_completion_timeout(&rx_cmp, timeout);
		status = dma_async_is_tx_complete(rx_chan, rx_cookie, NULL, NULL);

		if (timeout == 0)  {
			printk(KERN_ERR "DMA timed out\n");
		} else if (status != DMA_COMPLETE) {
			printk(KERN_ERR "DMA returned completion callback status of: %s\n",
			status == DMA_ERROR ? "error" : "in progress");
		}
	}

	dma_unmap_single(rx_chan->device->dev, rx_dma_handle, dest_dma_length, DMA_FROM_DEVICE);
	dma_unmap_single(tx_chan->device->dev, tx_dma_handle, src_dma_length, DMA_TO_DEVICE);

	return 0;

err:
	return -EBUSY;
}

static int zynqaes_setkey(struct crypto_ablkcipher *cipher, const u8 *in_key,
			    unsigned int key_len)
{
	//printk(KERN_INFO "%s:%d: Entering function\n", __func__, __LINE__);

	zynqaes_dma_op(in_key, key_buf, cipher_buf);

	return 0;
}

static int zynqaes_ecb_encrypt(struct ablkcipher_request *areq)
{
	struct ablkcipher_walk walk;
	unsigned long src_paddr;
	unsigned long dst_paddr;
	int ret;
	int nbytes;
	u8 *in_ptr;
	u8 *out_ptr;

	//printk(KERN_INFO "%s:%d: Entering function\n", __func__, __LINE__);

	ablkcipher_walk_init(&walk, areq->dst, areq->src, areq->nbytes);
	ret = ablkcipher_walk_phys(areq, &walk);

	if (ret) {
		printk(KERN_ERR "[%s]: ablkcipher_walk_phys() failed!",
			__func__);
		goto out;
	}

	while ((nbytes = walk.nbytes) > 0) {
		src_paddr = (page_to_phys(walk.src.page) + walk.src.offset);
		in_ptr = phys_to_virt(src_paddr);

		dst_paddr = (page_to_phys(walk.dst.page) + walk.dst.offset);
		out_ptr = phys_to_virt(dst_paddr);

		zynqaes_dma_op(in_ptr, encrypt_buf, cipher_buf);
		memcpy(out_ptr, cipher_buf, AES_BLOCK_SIZE);

		nbytes -= AES_BLOCK_SIZE;
		ret = ablkcipher_walk_done(areq, &walk, nbytes);
		if (ret)
			goto out;
	}
	ablkcipher_walk_complete(&walk);

out:
	return ret;
}

static struct crypto_alg zynqaes_ecb_alg = {
	.cra_name		=	"ecb(aes)",
	.cra_driver_name	=	"zynqaes-ecb",
	.cra_priority		=	100,
	.cra_flags		=	CRYPTO_ALG_TYPE_BLKCIPHER | CRYPTO_ALG_ASYNC,
	.cra_blocksize		=	AES_BLOCK_SIZE,
	.cra_type		=	&crypto_ablkcipher_type,
	.cra_module		=	THIS_MODULE,
	.cra_u			=	{
		.ablkcipher = {
			.min_keysize		=	AES_KEYSIZE_128,
			.max_keysize		=	AES_KEYSIZE_128,
			.setkey	   		= 	zynqaes_setkey,
			.encrypt		=	zynqaes_ecb_encrypt,
//			.decrypt		=	zynqaes_ecb_decrypt,
		}
	}
};

static int zynqaes_dma_buf_alloc(void)
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
		goto free_encrypt;
	}
	memcpy(key_buf, &zynqaes_set_key_cmd, ZYNQAES_CMD_LEN);

	cipher_buf = kzalloc(dest_dma_length, GFP_KERNEL);
	if (!cipher_buf) {
		printk(KERN_ERR "cipher_buf: Allocating DMA memory failed\n");
		goto free_key;
	}

	return 0;

free_key:
	kfree(key_buf);

free_encrypt:
	kfree(encrypt_buf);

err_mem:
	return -ENOMEM;
}

static void zynqaes_dma_buf_free(void)
{
	kfree(encrypt_buf);
	kfree(key_buf);
	kfree(cipher_buf);
}

static int zynqaes_probe(struct platform_device *pdev)
{
	int err;

	printk(KERN_INFO "%s:%d: Entering function\n", __func__, __LINE__);

	tx_chan = dma_request_chan(&pdev->dev, "axidma0");
	if (IS_ERR(tx_chan)) {
		err = PTR_ERR(tx_chan);
		pr_err("xilinx_dmatest: No Tx channel\n");
		goto out_err;
	}

	rx_chan = dma_request_chan(&pdev->dev, "axidma1");
	if (IS_ERR(rx_chan)) {
		err = PTR_ERR(rx_chan);
		pr_err("xilinx_dmatest: No Rx channel\n");
		goto free_tx;
	}

	err = zynqaes_dma_buf_alloc();
	if (err == -ENOMEM)
		goto free_rx;

	if ((err = crypto_register_alg(&zynqaes_ecb_alg)))
		goto free_rx;

	printk(KERN_INFO "%s: %d: Probing successful \n", __func__, __LINE__);
	return 0;

free_rx:
	dma_release_channel(rx_chan);

free_tx:
	dma_release_channel(tx_chan);

out_err:
	dev_err(&pdev->dev, "Probe failed with error: %d", err);

	return err;
}

static int zynqaes_remove(struct platform_device *pdev)
{
	printk(KERN_INFO "%s:%d: Entering function\n", __func__, __LINE__);

	crypto_unregister_alg(&zynqaes_ecb_alg);

	zynqaes_dma_buf_free();

	dma_release_channel(rx_chan);
	dma_release_channel(tx_chan);

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

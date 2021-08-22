#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/of_platform.h>
#include <linux/platform_device.h>
#include <linux/version.h>

#include "zynqaes.h"

struct zynqaes_dev *zynqaes_dd;

struct zynqaes_dev *zynqaes_find_dev(void)
{
	/* TODO - support a device list */
	return zynqaes_dd;
}

void zynqaes_set_key_bit(unsigned int key_len, struct zynqaes_reqctx_base *rctx)
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

int zynqaes_dma_op(struct zynqaes_reqctx_base *rctx)
{
	struct zynqaes_dma_ctx *dma_ctx;
	struct zynqaes_dev *dd;

	struct dma_async_tx_descriptor *tx_chan_desc;
	struct dma_async_tx_descriptor *rx_chan_desc;
	unsigned int tx_sg_len;
	unsigned int rx_sg_len;
	int ret;

	dma_ctx = &rctx->dma_ctx;
	dd = rctx->dd;

	/* Tx Channel */
	tx_sg_len = dma_map_sg(dd->dev, dma_ctx->tx_sg, dma_ctx->tx_nents, DMA_TO_DEVICE);
	if (!tx_sg_len) {
		dev_err(dd->dev, "[%s:%d] dma_map_sg: tx error\n",
					__func__, __LINE__);

		ret = -ENOMEM;
		goto err;
	}

	tx_chan_desc = dmaengine_prep_slave_sg(dd->tx_chan, dma_ctx->tx_sg,
				tx_sg_len, DMA_MEM_TO_DEV,
				DMA_CTRL_ACK);
	if (!tx_chan_desc) {
		dev_err(dd->dev, "[%s:%d] dmaengine_prep_slave_sg error\n",
					__func__, __LINE__);

		ret = -ECOMM;
		goto err;
	}

	dma_ctx->tx_cookie = dmaengine_submit(tx_chan_desc);
	if (dma_submit_error(dma_ctx->tx_cookie)) {
		dev_err(dd->dev, "[%s:%d] tx_cookie: dmaengine_submit error\n",
					__func__, __LINE__);

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
		dev_err(dd->dev, "[%s:%d] dmaengine_prep_slave_sg error\n",
					__func__, __LINE__);

		ret = -ECOMM;
		goto err;
	}

	rx_chan_desc->callback = dma_ctx->callback;
	rx_chan_desc->callback_param = rctx;

	dma_ctx->rx_cookie = dmaengine_submit(rx_chan_desc);
	if (dma_submit_error(dma_ctx->rx_cookie)) {
		dev_err(dd->dev, "[%s:%d] rx_cookie: dmaengine_submit error\n",
					__func__, __LINE__);

		ret = -ECOMM;
		goto err;
	}

	dma_async_issue_pending(dd->rx_chan);

	return 0;

err:
	return ret;
}

int zynqaes_setkey(struct zynqaes_ctx *ctx, const u8 *key,
			  unsigned int len)
{
	int ret = 0;

	switch (len) {
	case AES_KEYSIZE_128:
	case AES_KEYSIZE_192:
	case AES_KEYSIZE_256:
		ctx->key_len = len;
		memcpy(ctx->key, key, len);
		break;
	default:
		ret = -EINVAL;
	}

	return ret;
}

static int zynqaes_probe(struct platform_device *pdev)
{
	int err;
	const char *dma_name;
	struct device_node *node;

	pr_debug("[%s:%d]: Entering function\n", __func__, __LINE__);

	zynqaes_dd = devm_kzalloc(&pdev->dev, sizeof(*zynqaes_dd), GFP_KERNEL);
	if (!zynqaes_dd) {
		dev_err(zynqaes_dd->dev,
			"[%s:%d] zynqaes_dev: Allocating memory failed\n",
			__func__, __LINE__);

		err = -ENOMEM;
		goto out_err;
	}

	zynqaes_dd->dev = &pdev->dev;

	if (!pdev->dev.of_node) {
		dev_err(zynqaes_dd->dev, "[%s:%d] OF node not found!\n",
					__func__, __LINE__);

		err = -ENODEV;
		goto out_err;
	}

	node = pdev->dev.of_node;
	err = of_property_read_string_index(node, "dma-names", 0, &dma_name);
	if (err) {
		dev_err(zynqaes_dd->dev,
			"[%s:%d] Tx: reading channel name failed!\n",
			__func__, __LINE__);

		goto out_err;
	}

	zynqaes_dd->tx_chan = dma_request_chan(zynqaes_dd->dev, dma_name);
	if (IS_ERR(zynqaes_dd->tx_chan)) {
		err = PTR_ERR(zynqaes_dd->tx_chan);
		dev_err(zynqaes_dd->dev,
			"[%s:%d] Tx: requesting channel failed!\n",
			__func__, __LINE__);

		goto out_err;
	}

	err = of_property_read_string_index(node, "dma-names", 1, &dma_name);
	if (err) {
		dev_err(zynqaes_dd->dev,
			"[%s:%d] Rx: reading channel name failed!\n",
			__func__, __LINE__);

		goto free_tx_chan;
	}

	zynqaes_dd->rx_chan = dma_request_chan(zynqaes_dd->dev, dma_name);
	if (IS_ERR(zynqaes_dd->rx_chan)) {
		err = PTR_ERR(zynqaes_dd->rx_chan);
		dev_err(zynqaes_dd->dev,
			"[%s:%d] Rx: requesting channel failed!\n",
			__func__, __LINE__);

		goto free_tx_chan;
	}

	/* Initialize crypto engine */
	zynqaes_dd->engine = crypto_engine_alloc_init(zynqaes_dd->dev, 1);
	if (zynqaes_dd->engine == NULL) {
		err = -ENOMEM;
		goto free_rx_chan;
	}

	err = crypto_engine_start(zynqaes_dd->engine);
	if (err)
		goto free_engine;

	if ((err = zynqaes_register_skciphers()))
		goto free_engine;

	if ((err = zynqaes_register_aeads()))
		goto unregister_skciphers;

	dev_dbg(zynqaes_dd->dev, "[%s:%d]: Probing successful \n",
				__func__, __LINE__);

	return 0;

unregister_skciphers:
	zynqaes_unregister_skciphers();

free_engine:
	if (zynqaes_dd->engine)
		crypto_engine_exit(zynqaes_dd->engine);

free_rx_chan:
	dma_release_channel(zynqaes_dd->rx_chan);

free_tx_chan:
	dma_release_channel(zynqaes_dd->tx_chan);

out_err:
	dev_err(&pdev->dev, "[%s:%d] Probe failed with error: %d",
			    __func__, __LINE__, err);

	return err;
}

static int zynqaes_remove(struct platform_device *pdev)
{
	dev_dbg(zynqaes_dd->dev, "[%s:%d] Entering function\n",
				__func__, __LINE__);

	zynqaes_unregister_skciphers();
	zynqaes_unregister_aeads();

	crypto_engine_exit(zynqaes_dd->engine);

	dmaengine_terminate_all(zynqaes_dd->rx_chan);
	dmaengine_terminate_all(zynqaes_dd->tx_chan);

	dma_release_channel(zynqaes_dd->rx_chan);
	dma_release_channel(zynqaes_dd->tx_chan);

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

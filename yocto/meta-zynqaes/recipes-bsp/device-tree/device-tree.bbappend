FILESEXTRAPATHS_prepend := "${THISDIR}/files:"

SRC_URI_append = " \
    file://pl-zynqaes.dts \
    "

EXTRA_DT_FILES_append = "pl-zynqaes.dts"

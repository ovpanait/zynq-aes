FILESEXTRAPATHS_prepend := "${THISDIR}/files:"

SRC_URI_append = " \
    file://0001-speed.c-Add-benchmark-for-2-4-32-64-kB-blocks.patch \
    "

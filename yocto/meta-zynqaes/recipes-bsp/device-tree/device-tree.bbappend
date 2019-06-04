FILESEXTRAPATHS_prepend := "${THISDIR}/files:"

SRC_URI_append = " \
    file://pl-zynqaes.dts \
    file://amba-pl.dtsi \
    "

do_configure_append() {
        echo "/include/ \"amba-pl.dtsi\"" >> ${WORKDIR}/zynq-artyz7.dts
}

FILESEXTRAPATHS_prepend := "${THISDIR}/files:"

PL_ZYNQAES_DTSI = "pl-zynqaes.dtsi"

SRC_URI_append = " \
    file://${PL_ZYNQAES_DTSI} \
    "

do_configure_append() {
        echo "/include/ \"${PL_ZYNQAES_DTSI}\"" >> ${WORKDIR}/zynq-artyz7.dts
}

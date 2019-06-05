SUMMARY = "Zynqaes firmware"
LICENSE = "MIT"
LIC_FILES_CHKSUM = "file://${COREBASE}/meta/COPYING.MIT;md5=3da9cfbcb788c80a0384361b4de20420"

SRC_URI[md5sum] = "9b578e2fc2f28a49e04a9b7f9ba55edd"
SRC_URI[sha256sum] = "c08c2d92fee5cbc79766b5f06c684a8262cdf466558480f1d96cbfc2be1688a9"

SRC_URI = "https://github.com/ovpanait/zynq-aes/raw/master/release/firmware/${PN}-xc7z020clg400-1_${PV}.bit.bin"

do_compile() {
	:
}

do_install() {
	install -d ${D}${nonarch_base_libdir}/firmware/
	install ${WORKDIR}/*.bit.bin ${D}${nonarch_base_libdir}/firmware/
}

PACKAGES = "${PN}-xc7z020clg400-1"

FILES_${PN}-xc7z020clg400-1 = "${nonarch_base_libdir}/firmware/${PN}-xc7z020clg400-1_${PV}.bit.bin"

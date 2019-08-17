SUMMARY = "Prebuilt zynqaes firmware for Z7-20 SoC"
LICENSE = "MIT"
LIC_FILES_CHKSUM = "file://${COREBASE}/meta/COPYING.MIT;md5=3da9cfbcb788c80a0384361b4de20420"

inherit deploy

ZYNQAES_FIRMWARE = "${BPN}_${PV}.bit"

SRC_URI[md5sum] = "a328b1ed7cf1850f38543068b59f971d"
SRC_URI[sha256sum] = "8ede024003287e99af2f7467b2791d47e49c5868c1b2ffdeea6d26826f4af452"

SRC_URI = "https://github.com/ovpanait/zynq-aes/releases/download/v${PV}/${ZYNQAES_FIRMWARE}"

do_compile() {
	:
}

do_install() {
	install -d ${D}${nonarch_base_libdir}/firmware/
	install ${WORKDIR}/${ZYNQAES_FIRMWARE} ${D}${nonarch_base_libdir}/firmware/
}

do_deploy () {
	install -D ${WORKDIR}/${ZYNQAES_FIRMWARE} ${DEPLOYDIR}
	ln -sfr ${DEPLOYDIR}/${ZYNQAES_FIRMWARE} ${DEPLOYDIR}/bitstream
}

addtask deploy before do_build after do_install

FILES_${PN} = "${nonarch_base_libdir}/firmware/${ZYNQAES_FIRMWARE}"
PROVIDES += "virtual/bitstream"

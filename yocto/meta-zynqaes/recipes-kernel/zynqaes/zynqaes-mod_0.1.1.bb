SUMMARY = "Zynqaes kernel module"
LICENSE = "GPLv2"
LIC_FILES_CHKSUM = "file://COPYING;md5=12f884d2ae1ff87c09e5b7ccc2c4ca7e"

inherit module

SRC_URI[md5sum] = "2434364b10d20f9b05ac5c2dec1f0c95"
SRC_URI[sha256sum] = "2cd8a2777b85ae56bdf7998d37a6c042433ef8310535b9d5e069645e745c1bc1"

SRC_URI = "https://github.com/ovpanait/zynq-aes/releases/download/v${PV}/${BPN}_${PV}.tar.gz"

# The inherit of module.bbclass will automatically name module packages with
# "kernel-module-" prefix as required by the oe-core build environment.

RPROVIDES_${PN} += "kernel-module-zynqaes"

SUMMARY = "Zynqaes kernel module"
LICENSE = "GPLv2"
LIC_FILES_CHKSUM = "file://COPYING;md5=12f884d2ae1ff87c09e5b7ccc2c4ca7e"

inherit module

SRC_URI[md5sum] = "12912309ee64b5930c4c24f31b71a0b6"
SRC_URI[sha256sum] = "039b3bb4a95a7f0a907b2267a85b4cee296c7fccbbae1fca45c3071d6b85c8e8"

SRC_URI = "https://github.com/ovpanait/zynq-aes/raw/master/releases/artyz7/v${PV}/${PN}_${PV}.tar.gz \
          "

# The inherit of module.bbclass will automatically name module packages with
# "kernel-module-" prefix as required by the oe-core build environment.

RPROVIDES_${PN} += "kernel-module-zynqaes"

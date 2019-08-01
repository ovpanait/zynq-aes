FILESEXTRAPATHS_prepend := "${THISDIR}/linux-xlnx:"

SRC_URI += " \
	file://usercrypto.scc \
	file://ftrace.scc \
	file://ipsec.scc \
	"

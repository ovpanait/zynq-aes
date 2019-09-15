HDL_DIR = hdl
TB_DIR = tb
TOOLS_DIR = tools
SIM_DIR = simulation

HDL_SOURCES := $(shell find $(HDL_DIR))   

IP_NAME = zynq_aes
IP_REPO_PREFIX = ip_repo_
IP_REPO_DIR = $(SIM_DIR)/$(IP_REPO_PREFIX)$(IP_NAME)

$(IP_REPO_DIR): $(HDL_SOURCES)
	rm -rf $@
	mkdir -p simulation

	vivado -mode tcl \
	-source "${TOOLS_DIR}/create_ip.tcl" \
	-nolog -nojour \
	-tclargs $(IP_NAME) stream master_slave $(SIM_DIR)

ip: $(IP_REPO_DIR)

test: ip

clean:
	rm -rf simulation

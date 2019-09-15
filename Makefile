HDL_DIR = $(shell readlink -f hdl)
TB_DIR = $(shell readlink -f tb/zynq_aes_top)
TOOLS_DIR = $(shell readlink -f tools)
SIM_DIR = $(shell readlink -f simulation)
XSIM_DIR = $(SIM_DIR)/export_sim/xsim

HDL_SOURCES := $(shell find $(HDL_DIR))   

IP_NAME = zynq_aes
IP_VERSION = 1.0
IP_REPO_PREFIX = ip_repo_
IP_REPO_DIR = $(SIM_DIR)/$(IP_REPO_PREFIX)$(IP_NAME)

SIM_PROJ_NAME = test_proj
SIM_PROJ = $(SIM_DIR)/$(SIM_PROJ_NAME)

$(IP_REPO_DIR): $(HDL_SOURCES)
	rm -rf $@
	mkdir -p simulation

	vivado -mode tcl \
	-source "${TOOLS_DIR}/create_ip.tcl" \
	-nolog -nojour \
	-tclargs $(IP_NAME) stream master_slave $(SIM_DIR)

$(SIM_PROJ): $(IP_REPO_DIR)
	rm -rf $@
	vivado -mode tcl \
	-source "$(TOOLS_DIR)/create_axi_stream_sim_proj.tcl" \
	-nolog -nojour \
	-tclargs $(IP_REPO_DIR) $(TB_DIR) $(SIM_DIR)

sim: $(SIM_PROJ)
	cd $(XSIM_DIR); ./tb_main.sh -reset_run && ./tb_main.sh

test: sim

clean:
	rm -rf $(SIM_DIR)

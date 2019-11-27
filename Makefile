VIP_SIM = 0

HDL_DIR = $(shell readlink -f hdl)
HDL_INCLUDE = $(HDL_DIR)/include

TB_TOP = $(shell readlink -f tb)
TB_INCLUDE = $(TB_TOP)/include

ifeq (VIP_SIM, 1)
TB_DIR = $(TB_TOP)/zynq_aes_top_vip
else
TB_DIR = $(TB_TOP)/zynq_aes_top_novip
endif

TOOLS_DIR = $(shell readlink -f tools)
SIM_DIR = $(shell readlink -f simulation)
XSIM_DIR = $(SIM_DIR)/export_sim/xsim
BD_DIR = $(shell readlink -f bd)
SYNTH_DIR = $(shell readlink -f synthesis)
REPORTS_DIR = $(SYNTH_DIR)/reports

HDL_SOURCES := $(shell find $(HDL_DIR))   

IP_NAME = zynq_aes
IP_VERSION = 1.0
IP_REPO_PREFIX = ip_repo_
IP_REPO_DIR = $(SIM_DIR)/$(IP_REPO_PREFIX)$(IP_NAME)

SIM_PROJ_NAME = test_proj
SIM_PROJ = $(SIM_DIR)/$(SIM_PROJ_NAME)

PART ?= xc7z020clg400-1

$(IP_REPO_DIR): $(HDL_SOURCES)
	rm -rf $@
	mkdir -p simulation

	vivado -mode tcl \
	-source "${TOOLS_DIR}/create_ip.tcl" \
	-nolog -nojour \
	-tclargs $(IP_NAME) stream master_slave $(SIM_DIR)

$(SIM_PROJ): $(IP_REPO_DIR)
	rm -rf $@
	HDL_INCLUDE=$(HDL_INCLUDE) TB_INCLUDE=$(TB_INCLUDE) vivado -mode tcl \
	-source "$(TOOLS_DIR)/create_axi_stream_sim_proj.tcl" \
	-nolog -nojour \
	-tclargs $(IP_REPO_DIR) $(TB_DIR) $(SIM_DIR)

$(XSIM_DIR): $(HDL_SOURCES)
	rm -rf $@
	HDL_INCLUDE=$(HDL_INCLUDE) TB_INCLUDE=$(TB_INCLUDE) vivado -mode tcl \
	-source "$(TOOLS_DIR)/export_sim.tcl" \
	-nolog -nojour \
	-tclargs $(TB_DIR) $(SIM_DIR)

sim_novip: $(XSIM_DIR)
	cd $(XSIM_DIR); ./tb_main.sh -reset_run && ./tb_main.sh

sim_vip: $(SIM_PROJ)
	cd $(XSIM_DIR); ./tb_main.sh -reset_run && ./tb_main.sh

test: sim_novip

$(SYNTH_DIR): $(IP_REPO_DIR)
	rm -rf $@
	mkdir -p $@
	TOOLS_DIR=$(TOOLS_DIR) PART=$(PART) vivado -mode tcl \
	-source "$(TOOLS_DIR)/gen_bitstream.tcl" \
	-nolog -nojour \
	-tclargs $(BD_DIR) $(IP_REPO_DIR) $(SYNTH_DIR) $(REPORTS_DIR)

bitstream: $(SYNTH_DIR)

clean_sim:
	rm -rf $(SIM_DIR)

clean_bitstream:
	rm -rf $(SYNTH_DIR)

.PHONY: clean

clean: clean_sim clean_bitstream

#set -x

TOOLS_TOP=$(realpath $(dirname "${0}"))

HDL_DIR=$(realpath hdl)
TB_DIR=$(realpath tb)
TB_TOP_INCLUDE=$(realpath tb_include)

cp -a "${1}" "${HDL_DIR}"
cp -a "${2}" "${TB_DIR}"
[ -d "${3}" ] && cp -a "${3}" "${TB_TOP_INCLUDE}"

xsim_opts="-work xil_defaultlib --relax -d SIMULATION=1"
for dir in "${HDL_DIR}/include" "${TB_DIR}/include" "${TB_TOP_INCLUDE}"; do
	[ -d "${dir}" ] && xsim_opts="${xsim_opts} -i ${dir}"
done

xvlog_opts="${xsim_opts}"
xsv_opts="${xsim_opts} -sv"

# RUN_STEP: <compile>
compile()
{
	VLOG_FILES="$(find ${HDL_DIR} -iname *.v)"
	SV_FILES="$(find ${HDL_DIR} ${TB_DIR} -iname *.sv)"

	[ ! -z "${VLOG_FILES}" ] && xvlog ${xvlog_opts} ${VLOG_FILES} 2>&1 | tee -a compile.log
	[ ! -z "${SV_FILES}" ] && xvlog ${xsv_opts} ${SV_FILES} 2>&1 | tee -a compile.log
}

# RUN_STEP: <elaborate>
elaborate()
{
	xelab --relax --debug typical --mt auto -d "SIMULATION=1" -L xil_defaultlib -L unisims_ver -L unimacro_ver -L secureip --snapshot tb_main xil_defaultlib.tb_main -log elaborate.log
}

# RUN_STEP: <simulate>
simulate()
{
	xsim tb_main -key {Behavioral:sim_1:Functional:tb_main} -tclbatch "${TOOLS_TOP}/xsim_init.tcl" -log simulate.log
}

run()
{
	# Testbench code gets test stimulus from external data files using
	# $fopen(). XSIM treats the $fopen() file path as relative to the
	# directory from which xsim is invoked.
	cd ${TB_DIR}

	compile
	elaborate
	simulate
}

run

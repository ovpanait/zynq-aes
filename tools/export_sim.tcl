# Command line parameters
if {$argc < 2} {
	puts "
Usage:
[file tail ${argv0}] TB_DIR OUTPUT_DIR

TB_DIR            directory containing the tb sources
OUTPUT_DIR        output directory for the generated project/simulation env
"

exit 1
}

set hdl_include $env(HDL_INCLUDE)
set tb_include $env(TB_INCLUDE)

set tb_dir [lindex $argv 0]
set out_dir [lindex $argv 1]

file mkdir ${out_dir}

read_verilog [glob ./hdl/*.v]
read_verilog [glob -nocomplain ./hdl/*.sv] -quiet
read_verilog [glob -nocomplain ${hdl_include}/*.vh] -quiet

add_files -fileset [get_filesets sim_1] [glob -nocomplain ${tb_dir} ] -quiet

#read_xdc [ glob -nocomplain ./xdc/*.xdc ] -quiet

set_property top tb_main [current_fileset -simset]

export_simulation \
    -force \
    -simulator xsim \
    -directory ${out_dir}/export_sim \
    -include [list ${tb_dir}/include ${hdl_include} ${tb_include}] \
    -define [list {SIMULATION=1}]

exit

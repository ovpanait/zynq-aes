proc get_cpus_no {} {
	if {![catch {open "/proc/cpuinfo"} f]} {
		set cores [regexp -all -line {^processor\s} [read $f]]
		close $f
		if {$cores > 0} {
			return $cores
		}
	}
}

set cpus_no [get_cpus_no]

set tools_dir $env(TOOLS_DIR)
set part $env(PART)

set bd_dir [lindex $argv 0]
set ip_repo_dir [lindex $argv 1]
set synth_dir [lindex $argv 2]
set reports_dir [lindex $argv 3]

set out_dir ${synth_dir}/output

set bd_name zynq_aes_bd
set proj_name zynq_aes
set proj_path "${synth_dir}/${proj_name}"

source [glob ${bd_dir}/*.tcl]

file mkdir ${proj_path}
file mkdir ${reports_dir}
file mkdir ${out_dir}

create_project -part ${part} ${proj_name} ${proj_path}

# Add ip
set_property ip_repo_paths ${ip_repo_dir} [current_project]
update_ip_catalog -rebuild

# Generate bd
cr_bd_zynq_aes_bd ""

# Create verilog wrapper
make_wrapper -files [get_files ${proj_path}/${proj_name}.srcs/sources_1/bd/${bd_name}/${bd_name}.bd] -top
add_files -norecurse ${proj_path}/${proj_name}.srcs/sources_1/bd/${bd_name}/hdl/${bd_name}_wrapper.v

# Synth, Implement, Generate bitstream
launch_runs synth_1 -jobs ${cpus_no}
wait_on_run synth_1
if {[get_property PROGRESS [get_runs synth_1]] != "100%"} {   
	error "ERROR: synth_1 failed"   
}
open_run synth_1 -name netlist_1
report_timing_summary -delay_type max -report_unconstrained -check_timing_verbose -max_paths 10 -input_pins -file ${reports_dir}/syn_timing.rpt
report_power -file ${reports_dir}/syn_power.rpt

launch_runs impl_1 -jobs ${cpus_no} -to_step write_bitstream
wait_on_run impl_1
open_run impl_1
if {[get_property PROGRESS [get_runs impl_1]] != "100%"} {   
	error "ERROR: impl_1 failed"   
}
report_timing_summary -delay_type min_max -report_unconstrained -check_timing_verbose -max_paths 10 -input_pins -file ${reports_dir}/imp_timing.rpt
report_power -file ${reports_dir}/imp_power.rpt

write_hw_platform -fixed -include_bit -force -file ${out_dir}/zynqaes_hw.xsa

file copy [glob ${proj_path}/${proj_name}.runs/impl_1/*.bit] ${out_dir}

exit

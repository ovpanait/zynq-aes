# Command line parameters
if {$argc < 3} {
	puts "
Usage:
[file tail ${argv0}] IP_REPO_DIR TB_DIR OUTPUT_DIR

IP_REPO_DIR       directory containing the IPs
TB_DIR            directory containing the tb sources
OUTPUT_DIR        output directory for the generated project/simulation env
"

exit 1
}

set ip_repo_dir [lindex $argv 0]
set tb_dir [lindex $argv 1]
set out_dir [lindex $argv 2]

set proj_name test_proj
set proj_path "${out_dir}/${proj_name}"

file mkdir ${proj_path}
create_project -part xc7z020clg400-1 ${proj_name} ${proj_path}

# Add ip
set_property ip_repo_paths ${ip_repo_dir} [current_project]
update_ip_catalog -rebuild

source [glob ${tb_dir}/*.tcl]
cr_bd_design_1 ""

# Create verilog wrapper
make_wrapper -files [get_files ${proj_path}/${proj_name}.srcs/sources_1/bd/design_1/design_1.bd] -top
add_files -norecurse ${proj_path}/${proj_name}.srcs/sources_1/bd/design_1/hdl/design_1_wrapper.v

generate_target all [get_files ${proj_path}/${proj_name}.srcs/sources_1/bd/design_1/design_1.bd]
catch { config_ip_cache -export [get_ips -all design_1_axi4stream_vip_0_0] }
catch { config_ip_cache -export [get_ips -all design_1_axi4stream_vip_1_0] }
export_ip_user_files -of_objects [get_files ${proj_path}/${proj_name}.srcs/sources_1/bd/design_1/design_1.bd] -no_script -sync -force -quiet
create_ip_run [get_files -of_objects [get_fileset sources_1] [get_files ${proj_path}/${proj_name}.srcs/sources_1/bd/design_1/design_1.bd]]
launch_runs -jobs 8 {design_1_axi4stream_vip_0_0_synth_1 design_1_axi4stream_vip_1_0_synth_1}

# Simulation
set_property SOURCE_SET sources_1 [get_filesets sim_1]
add_files -fileset [get_filesets sim_1] -norecurse ${tb_dir}/tb_main.sv

foreach ip [get_ips] {
	add_files -fileset [get_filesets sim_1] [get_files -compile_order sources -used_in simulation -of [get_files [set ip].xci]]
}

update_compile_order -fileset sim_1
set_property top tb_main [get_filesets sim_1]
set_property top_lib xil_defaultlib [get_filesets sim_1]

get_files -compile_order sources -used_in simulation

set outputDir ${out_dir}
file mkdir $outputDir

export_simulation \
    -simulator xsim \
    -ip_user_files_dir ${proj_path}/${proj_name}.ip_user_files \
    -ipstatic_source_dir ${proj_path}/${proj_name}.ip_user_files/ipstatic \
    -use_ip_compiled_libs \
    -force \
    -directory "$outputDir/export_sim" \
    -include [list "[pwd]/hdl/include" "${tb_dir}/include" "[pwd]/tb/include"] \
    -define [list {SIMULATION=1}]

close_project
exit

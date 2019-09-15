source $env(TCL_INCLUDE)/debug.tcl

# Command line parameters
if {$argc < 4} {
	puts "
Usage:
${argv0} IP_NAME AXI_TYPE INTERFACE_TYPE OUTPUT_DIR

IP_NAME           name for the generated IP
AXI_TYPE          full   | lite  | stream
INTERFACE_TYPE    master | slave | master_slave
OUTPUT_DIR        output directory where the ip repository will be generated
"
}

set ip_name [lindex $argv 0]
set axi_type [lindex $argv 1]
set int_type [lindex $argv 2]
set out_dir [lindex $argv 3]

# IP info
set ip_repo_name "ip_repo_${ip_name}"
set ip_path "${out_dir}/${ip_repo_name}/${ip_name}"

set interface_name_slave "S00_AXI"
set interface_name_master "M00_AXI"
if {${axi_type} == "stream"} {
	append interface_name_slave "S"
	append interface_name_master "S"
}

create_project -part xc7z020clg400-1 ${ip_name} ${ip_path}

# Create peripheral
create_peripheral user.org user ${ip_name} 1.0 -dir ${ip_path}
set open_core [ipx::find_open_core user.org:user:${ip_name}:1.0]

if {${int_type} == "slave" || ${int_type} == "master_slave"} {
    add_peripheral_interface ${interface_name_slave} \
	-interface_mode slave \
	-axi_type ${axi_type} \
	${open_core}
}
if {${int_type} == "master" || ${int_type} == "master_slave"} {
    add_peripheral_interface $interface_name_master \
	-interface_mode master \
	-axi_type ${axi_type} \
	${open_core}
}
generate_peripheral ${open_core}
write_peripheral ${open_core}

# IP edit project
ipx::edit_ip_in_project -upgrade true -name edit_${ip_name} -directory ${ip_path} ${ip_path}/${ip_name}_1.0/component.xml

# Add hdl sources
set ip_hdl_dir "${ip_path}/${ip_name}_1.0/hdl"
remove_files {*}[glob "${ip_hdl_dir}/*.v"]
file delete {*}[glob "${ip_hdl_dir}/*.v"]
file copy {*}[add_files ./hdl] ${ip_hdl_dir}
set_property top ${ip_name} [current_fileset]

# Add testbench sources
# TODO

update_compile_order -fileset [current_fileset]
ipx::merge_project_changes files [ipx::current_core]
ipx::merge_project_changes hdl_parameters [ipx::current_core]

# Check for syntax errors
# If we don't do this here, it will generate subtle errors when running simulation
synth_design -rtl

set_property core_revision 1 [ipx::current_core]
ipx::update_source_project_archive -component [ipx::current_core]
ipx::create_xgui_files [ipx::current_core]
ipx::update_checksums [ipx::current_core]
ipx::save_core [ipx::current_core]

close_project -delete

# Close initial project
close_project -delete

exit



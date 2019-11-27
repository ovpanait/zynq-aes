# Proc to create BD design_1

proc cr_bd_design_1 { parentCell } {
  # CHANGE DESIGN NAME HERE
  set design_name design_1

  common::send_msg_id "BD_TCL-003" "INFO" "Currently there is no design <$design_name> in project, so creating one..."

  create_bd_design $design_name

  set bCheckIPsPassed 1
  ##################################################################
  # CHECK IPs
  ##################################################################
  set bCheckIPs 1
  if { $bCheckIPs == 1 } {
     set list_check_ips "\ 
  xilinx.com:ip:axi4stream_vip:1.1\
  user.org:user:zynq_aes:1.0\
  "

   set list_ips_missing ""
   common::send_msg_id "BD_TCL-006" "INFO" "Checking if the following IPs exist in the project's IP catalog: $list_check_ips ."

   foreach ip_vlnv $list_check_ips {
      set ip_obj [get_ipdefs -all $ip_vlnv]
      if { $ip_obj eq "" } {
         lappend list_ips_missing $ip_vlnv
      }
   }

   if { $list_ips_missing ne "" } {
      catch {common::send_msg_id "BD_TCL-115" "ERROR" "The following IPs are not found in the IP Catalog:\n  $list_ips_missing\n\nResolution: Please add the repository containing the IP(s) to the project." }
      set bCheckIPsPassed 0
   }

  }

  if { $bCheckIPsPassed != 1 } {
    common::send_msg_id "BD_TCL-1003" "WARNING" "Will not continue with creation of design due to the error(s) above."
    return 3
  }

  variable script_folder

  if { $parentCell eq "" } {
     set parentCell [get_bd_cells /]
  }

  # Get object for parentCell
  set parentObj [get_bd_cells $parentCell]
  if { $parentObj == "" } {
     catch {common::send_msg_id "BD_TCL-100" "ERROR" "Unable to find parent cell <$parentCell>!"}
     return
  }

  # Make sure parentObj is hier blk
  set parentType [get_property TYPE $parentObj]
  if { $parentType ne "hier" } {
     catch {common::send_msg_id "BD_TCL-101" "ERROR" "Parent <$parentObj> has TYPE = <$parentType>. Expected to be <hier>."}
     return
  }

  # Save current instance; Restore later
  set oldCurInst [current_bd_instance .]

  # Set parent object as current
  current_bd_instance $parentObj


  # Create interface ports

  # Create ports
  set aclk [ create_bd_port -dir I -type clk aclk ]
  set aresetn [ create_bd_port -dir I -type rst aresetn ]

  # Create instance: axi4stream_vip_0, and set properties
  set axi4stream_vip_0 [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi4stream_vip:1.1 axi4stream_vip_0 ]
  set_property -dict [ list \
   CONFIG.HAS_TLAST {1} \
   CONFIG.INTERFACE_MODE {MASTER} \
   CONFIG.TDATA_NUM_BYTES {4} \
 ] $axi4stream_vip_0

  # Create instance: axi4stream_vip_1, and set properties
  set axi4stream_vip_1 [ create_bd_cell -type ip -vlnv xilinx.com:ip:axi4stream_vip:1.1 axi4stream_vip_1 ]
  set_property -dict [ list \
   CONFIG.INTERFACE_MODE {SLAVE} \
   CONFIG.TDATA_NUM_BYTES {4} \
 ] $axi4stream_vip_1

  # Create instance: zynq_aes_0, and set properties
  set zynq_aes_0 [ create_bd_cell -type ip -vlnv user.org:user:zynq_aes:1.0 zynq_aes_0 ]

  # Create interface connections
  connect_bd_intf_net -intf_net axi4stream_vip_0_M_AXIS [get_bd_intf_pins axi4stream_vip_0/M_AXIS] [get_bd_intf_pins zynq_aes_0/S00_AXIS]
  connect_bd_intf_net -intf_net zynq_aes_0_M00_AXIS [get_bd_intf_pins axi4stream_vip_1/S_AXIS] [get_bd_intf_pins zynq_aes_0/M00_AXIS]

  # Create port connections
  connect_bd_net -net aclk_0_1 [get_bd_ports aclk] [get_bd_pins axi4stream_vip_0/aclk] [get_bd_pins axi4stream_vip_1/aclk] [get_bd_pins zynq_aes_0/m00_axis_aclk] [get_bd_pins zynq_aes_0/s00_axis_aclk]
  connect_bd_net -net aresetn_0_1 [get_bd_ports aresetn] [get_bd_pins axi4stream_vip_0/aresetn] [get_bd_pins axi4stream_vip_1/aresetn] [get_bd_pins zynq_aes_0/m00_axis_aresetn] [get_bd_pins zynq_aes_0/s00_axis_aresetn]

  # Create address segments


  # Restore current instance
  current_bd_instance $oldCurInst

  save_bd_design
  close_bd_design $design_name 
}
# End of cr_bd_design_1()

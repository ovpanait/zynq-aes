set aes_clk [get_clocks -of_objects [get_nets -hierarchical aes_clk]]
set saxis_clk [get_clocks -of_objects [get_nets -hierarchical s00_axis_aclk]]
set maxis_clk [get_clocks -of_objects [get_nets -hierarchical m00_axis_aclk]]

# Slave fifo
set_max_delay -from [get_cells -hier -filter {NAME =~ *slave_fifo/write_ptr_gray_reg[*] }] -to [get_cells -hier -filter {NAME =~ *slave_fifo/write_ptr_synchronizer/sync0_reg[*] }] -datapath_only [get_property -min PERIOD $saxis_clk]
set_max_delay -from [get_cells -hier -filter {NAME =~ *slave_fifo/read_ptr_gray_reg[*] }] -to [get_cells -hier -filter {NAME =~ *slave_fifo/read_ptr_synchronizer/sync0_reg[*] }] -datapath_only [get_property -min PERIOD $aes_clk]

# Master fifo
set_max_delay -from [get_cells -hier -filter {NAME =~ *master_fifo/write_ptr_gray_reg[*] }] -to [get_cells -hier -filter {NAME =~ *master_fifo/write_ptr_synchronizer/sync0_reg[*] }] -datapath_only [get_property -min PERIOD $aes_clk]
set_max_delay -from [get_cells -hier -filter {NAME =~ *master_fifo/read_ptr_gray_reg[*] }] -to [get_cells -hier -filter {NAME =~ *master_fifo/read_ptr_synchronizer/sync0_reg[*] }] -datapath_only [get_property -min PERIOD $maxis_clk]

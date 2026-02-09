## Clock signal
set_property -dict { PACKAGE_PIN E3    IOSTANDARD LVCMOS33 } [get_ports { clk_i }]; #IO_L12P_T1_MRCC_35 Sch=gclk[100]
create_clock -add -name sys_clk_pin -period 10.00 -waveform {0 5} [get_ports { clk_i }];

## Switches
set_property -dict { PACKAGE_PIN A8    IOSTANDARD LVCMOS33 } [get_ports { rst_i }]; #IO_L12N_T1_MRCC_16 Sch=sw[0]

# Exclude all ports except clk_i and rst_i from I/O timing
set_false_path -from [get_ports {imem_rdata_i imem_addr_o mem_rdata_i mem_done_i mem_valid_o mem_wen_o mem_addr_o mem_wdata_o mem_strb_o}]
set_false_path -to [get_ports {imem_rdata_i imem_addr_o mem_rdata_i mem_done_i mem_valid_o mem_wen_o mem_addr_o mem_wdata_o mem_strb_o}]


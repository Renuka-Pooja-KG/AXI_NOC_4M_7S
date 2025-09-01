# AXI NOC 4M 7S UVM Verification - Compile List
# Common directory: /home/sgeuser100/renuka_dv/ONGOING_PROJECTS/AXI_NOC_4M_7S/
# RTL and Verification subdirectories

# RTL Files
/home/sgeuser100/renuka_dv/ONGOING_PROJECTS/AXI_NOC_4M_7S/RTL/axi_master_1_slave_router.sv
/home/sgeuser100/renuka_dv/ONGOING_PROJECTS/AXI_NOC_4M_7S/RTL/axi_master_2_slave_router.sv
/home/sgeuser100/renuka_dv/ONGOING_PROJECTS/AXI_NOC_4M_7S/RTL/axi_master_3_slave_router.sv
/home/sgeuser100/renuka_dv/ONGOING_PROJECTS/AXI_NOC_4M_7S/RTL/amba_axi_m4s7.v
/home/sgeuser100/renuka_dv/ONGOING_PROJECTS/AXI_NOC_4M_7S/RTL/AXI_TO_AXI_NOC_ARBITER_4_TO_7_CONFIG.sv

// UVM Verification include dirs
+incdir+/home/sgeuser100/renuka_dv/ONGOING_PROJECTS/AXI_NOC_4M_7S/Verification/UVME
# UVM Verification Files
#Package parameters
/home/sgeuser100/renuka_dv/ONGOING_PROJECTS/AXI_NOC_4M_7S/Verification/UVME/package/axi_common_types_pkg.sv
# Interface files are included in axi_noc_pkg.sv - no need to compile individually

# Package
/home/sgeuser100/renuka_dv/ONGOING_PROJECTS/AXI_NOC_4M_7S/Verification/UVME/package/axi_noc_pkg.sv

# Top Testbench
/home/sgeuser100/renuka_dv/ONGOING_PROJECTS/AXI_NOC_4M_7S/Verification/UVME/top/axi_noc_tb_top.sv

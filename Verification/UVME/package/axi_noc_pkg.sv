// Package file for AXI NoC UVM Verification
// This package includes all UVM components for the 4-Master 7-Slave AXI NoC

package axi_noc_pkg;

  // Import UVM
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  // Import common AXI types package
  import axi_common_types_pkg::*;

  // ===== INTERFACES =====
  `include "interfaces/M0_interface.sv"
  `include "interfaces/M1_interface.sv"
  `include "interfaces/M2_interface.sv"
  `include "interfaces/M3_interface.sv"
  `include "interfaces/S0_interface.sv"
  `include "interfaces/S1_interface.sv"
  `include "interfaces/S2_interface.sv"
  `include "interfaces/S3_interface.sv"
  `include "interfaces/S4_interface.sv"
  `include "interfaces/S5_interface.sv"
  `include "interfaces/S6_interface.sv"

  // ===== MASTER 0 (M0) AGENT COMPONENTS =====
  `include "agents/M0_agent/M0_seq_item.sv"
  `include "agents/M0_agent/M0_sequencer.sv"
  `include "agents/M0_agent/M0_driver.sv"
  `include "agents/M0_agent/M0_monitor.sv"
  `include "agents/M0_agent/M0_agent.sv"
  
  // ===== MASTER 1 (M1) AGENT COMPONENTS =====
  `include "agents/M1_agent/M1_seq_item.sv"
  `include "agents/M1_agent/M1_sequencer.sv"
  `include "agents/M1_agent/M1_driver.sv"
  `include "agents/M1_agent/M1_monitor.sv"
  `include "agents/M1_agent/M1_agent.sv"
  
  // ===== MASTER 2 (M2) AGENT COMPONENTS =====
  `include "agents/M2_agent/M2_seq_item.sv"
  `include "agents/M2_agent/M2_sequencer.sv"
  `include "agents/M2_agent/M2_driver.sv"
  `include "agents/M2_agent/M2_monitor.sv"
  `include "agents/M2_agent/M2_agent.sv"
  
  // ===== MASTER 3 (M3) AGENT COMPONENTS =====
  `include "agents/M3_agent/M3_seq_item.sv"
  `include "agents/M3_agent/M3_sequencer.sv"
  `include "agents/M3_agent/M3_driver.sv"
  `include "agents/M3_agent/M3_monitor.sv"
  `include "agents/M3_agent/M3_agent.sv"
  
  // ===== SLAVE 0 (S0) AGENT COMPONENTS =====
  `include "agents/S0_agent/S0_seq_item.sv"
  `include "agents/S0_agent/S0_sequencer.sv"
  `include "agents/S0_agent/S0_driver.sv"
  `include "agents/S0_agent/S0_monitor.sv"
  `include "agents/S0_agent/S0_agent.sv"
  
  // ===== SLAVE 1 (S1) AGENT COMPONENTS =====
  `include "agents/S1_agent/S1_seq_item.sv"
  `include "agents/S1_agent/S1_sequencer.sv"
  `include "agents/S1_agent/S1_driver.sv"
  `include "agents/S1_agent/S1_monitor.sv"
  `include "agents/S1_agent/S1_agent.sv"
  
  // ===== SLAVE 2 (S2) AGENT COMPONENTS =====
  `include "agents/S2_agent/S2_seq_item.sv"
  `include "agents/S2_agent/S2_sequencer.sv"
  `include "agents/S2_agent/S2_driver.sv"
  `include "agents/S2_agent/S2_monitor.sv"
  `include "agents/S2_agent/S2_agent.sv"
  
  // ===== SLAVE 3 (S3) AGENT COMPONENTS =====
  `include "agents/S3_agent/S3_seq_item.sv"
  `include "agents/S3_agent/S3_sequencer.sv"
  `include "agents/S3_agent/S3_driver.sv"
  `include "agents/S3_agent/S3_monitor.sv"
  `include "agents/S3_agent/S3_agent.sv"
  
  // ===== SLAVE 4 (S4) AGENT COMPONENTS =====
  `include "agents/S4_agent/S4_seq_item.sv"
  `include "agents/S4_agent/S4_sequencer.sv"
  `include "agents/S4_agent/S4_driver.sv"
  `include "agents/S4_agent/S4_monitor.sv"
  `include "agents/S4_agent/S4_agent.sv"
  
  // ===== SLAVE 5 (S5) AGENT COMPONENTS =====
  `include "agents/S5_agent/S5_seq_item.sv"
  `include "agents/S5_agent/S5_sequencer.sv"
  `include "agents/S5_agent/S5_driver.sv"
  `include "agents/S5_agent/S5_monitor.sv"
  `include "agents/S5_agent/S5_agent.sv"
  
  // ===== SLAVE 6 (S6) AGENT COMPONENTS =====
  `include "agents/S6_agent/S6_seq_item.sv"
  `include "agents/S6_agent/S6_sequencer.sv"
  `include "agents/S6_agent/S6_driver.sv"
  `include "agents/S6_agent/S6_monitor.sv"
  `include "agents/S6_agent/S6_agent.sv"
  
  // ===== SEQUENCES =====
  // Base sequences for masters and slaves

  // Master-specific sequences
  `include "sequences/M0_seq.sv"
  `include "sequences/M1_seq.sv"
  `include "sequences/M2_seq.sv"
  `include "sequences/M3_seq.sv"
  
  // Slave-specific sequences
  `include "sequences/S0_seq.sv"
  `include "sequences/S1_seq.sv"
  `include "sequences/S2_seq.sv"
  `include "sequences/S3_seq.sv"
  `include "sequences/S4_seq.sv"
  `include "sequences/S5_seq.sv"
  `include "sequences/S6_seq.sv"

  // ===== VIRTUAL SEQUENCER =====
  `include "agents/virtual_sequencer.sv"
  `include "sequences/axi_noc_virtual_seq.sv"
  
  // ===== ENVIRONMENT COMPONENTS =====
  // Coverage components
  // `include "coverage/axi_master_coverage.sv"
  // `include "coverage/axi_slave_coverage.sv"
  // `include "coverage/axi_noc_coverage.sv"
  
  // // Scoreboard and protocol checkers
  // `include "env/axi_noc_scoreboard.sv"
  // `include "env/axi_protocol_checker.sv"
  `include "env/axi_noc_env.sv"
  
  // ===== TESTBENCH TOP =====
  `include "top/axi_noc_tb_top.sv"
  
  // ===== TEST FILES =====
  // Base test class
  `include "tests/test.sv"
  
  // // Master tests
  // `include "./tests/m0_tests.sv"
  // `include "./tests/m1_tests.sv"
  // `include "./tests/m2_tests.sv"
  // `include "./tests/m3_tests.sv"
  
  // // Slave tests
  // `include "./tests/s0_tests.sv"
  // `include "./tests/s1_tests.sv"
  // `include "./tests/s2_tests.sv"
  // `include "./tests/s3_tests.sv"
  // `include "./tests/s4_tests.sv"
  // `include "./tests/s5_tests.sv"
  // `include "./tests/s6_tests.sv"
  
  // // System-level tests
  // `include "./tests/system_tests.sv"
  // `include "./tests/concurrent_access_tests.sv"
  // `include "./tests/arbitration_tests.sv"
  // `include "./tests/bandwidth_tests.sv"
  // `include "./tests/latency_tests.sv"
  
  // // Reset and initialization tests
  // `include "./tests/reset_test.sv"
  // `include "./tests/initialization_test.sv"
  
  // // Error and corner case tests
  // `include "./tests/error_injection_tests.sv"
  // `include "./tests/corner_case_tests.sv"
  // `include "./tests/stress_tests.sv"
  
  // // Performance and regression tests
  // `include "./tests/performance_tests.sv"
  // `include "./tests/regression_tests.sv"

endpackage
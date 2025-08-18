//=============================================================================
// AXI Master 0 Configuration
//=============================================================================
// This file contains the Master 0 UVM configuration object for the NOC verification
// environment. It defines configuration parameters for Master 0.

`ifndef AXI_MASTER0_CONFIG_SV
`define AXI_MASTER0_CONFIG_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

class axi_master0_config extends uvm_object;
    
    // UVM Factory Registration
    `uvm_object_utils(axi_master0_config)
    
    // Configuration parameters
    int unsigned master_id = 0;
    int unsigned timeout = 1000;
    bit enable_coverage = 1;
    bit enable_checks = 1;
    
    // Access control parameters (Master 0 has full access to all slaves)
    int unsigned allowed_slaves[] = '{0, 1, 2, 3, 4, 5, 6}; // S0, S1, S2, S3, S4, S5, S6
    
    // Constructor
    function new(string name = "axi_master0_config");
        super.new(name);
    endfunction
    
    // Check if slave is allowed
    function bit is_slave_allowed(input int unsigned slave_id);
        foreach(allowed_slaves[i]) begin
            if (allowed_slaves[i] == slave_id) return 1;
        end
        return 0;
    endfunction
    
    // Get allowed slaves array
    function int unsigned[] get_allowed_slaves();
        return allowed_slaves;
    endfunction
    
    // Set timeout value
    function void set_timeout(input int unsigned timeout_val);
        timeout = timeout_val;
    endfunction
    
    // Enable/disable coverage
    function void set_coverage_enable(input bit enable);
        enable_coverage = enable;
    endfunction
    
    // Enable/disable checks
    function void set_checks_enable(input bit enable);
        enable_checks = enable;
    endfunction
    
endclass : axi_master0_config

`endif // AXI_MASTER0_CONFIG_SV


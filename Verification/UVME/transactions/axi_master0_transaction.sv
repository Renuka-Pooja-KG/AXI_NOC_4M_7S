//=============================================================================
// AXI Master 0 Transaction Class
//=============================================================================
// This file contains the Master 0 specific AXI transaction class that has
// full access to all slaves (S0-S6).

`ifndef AXI_MASTER0_TRANSACTION_SV
`define AXI_MASTER0_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_master_transaction.sv"

// AXI Master 0 Transaction Class
class axi_master0_transaction extends axi_master_transaction;
    
    // Master 0 specific constraints
    constraint master0_constraints {
        // Master 0 can access all slaves
        master_id == 0;
        slave_id inside {0, 1, 2, 3, 4, 5, 6};
        
        // Address can be anywhere in the valid range
        addr >= 32'h0000_0000;
        addr <= 32'h0000_FFFF;
        
        // Master 0 has highest priority, so shorter delays
        response_delay <= 5;
    }
    
    // Constructor
    function new(string name = "axi_master0_transaction");
        super.new(name);
        master_id = 0;
        // Master 0 can access all slaves
        allowed_slaves = '{0, 1, 2, 3, 4, 5, 6};
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils(axi_master0_transaction)
    
    // Master 0 specific utility functions
    function bit can_access_slave(int slave);
        // Master 0 can access all slaves
        return 1;
    endfunction
    
    // Override get_transaction_info to include Master 0 specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, " [MASTER0_FULL_ACCESS]"};
        return info;
    endfunction
    
endclass : axi_master0_transaction

`endif // AXI_MASTER0_TRANSACTION_SV

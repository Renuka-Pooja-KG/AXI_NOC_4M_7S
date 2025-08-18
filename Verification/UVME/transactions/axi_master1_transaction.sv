//=============================================================================
// AXI Master 1 Transaction Class
//=============================================================================
// This file contains the Master 1 specific AXI transaction class that has
// restricted access to only slaves S1, S3, and S4.

`ifndef AXI_MASTER1_TRANSACTION_SV
`define AXI_MASTER1_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_master_transaction.sv"

// AXI Master 1 Transaction Class
class axi_master1_transaction extends axi_master_transaction;
    
    // Master 1 specific constraints
    constraint master1_constraints {
        // Master 1 can only access S1, S3, S4
        master_id == 1;
        slave_id inside {1, 3, 4};
        
        // Address must be within allowed slave ranges
        if (slave_id == 1) addr inside {[32'h0000_2000:32'h0000_2FFF]};
        else if (slave_id == 3) addr inside {[32'h0000_6000:32'h0000_6FFF]};
        else if (slave_id == 4) addr inside {[32'h0000_8000:32'h0000_8FFF]};
        
        // Master 1 has medium priority
        response_delay <= 8;
    }
    
    // Constructor
    function new(string name = "axi_master1_transaction");
        super.new(name);
        master_id = 1;
        // Master 1 can only access S1, S3, S4
        allowed_slaves = '{1, 3, 4};
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils(axi_master1_transaction)
    
    // Master 1 specific utility functions
    function bit can_access_slave(int slave);
        // Master 1 can only access S1, S3, S4
        return (slave == 1 || slave == 3 || slave == 4);
    endfunction
    
    // Override get_transaction_info to include Master 1 specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, " [MASTER1_RESTRICTED_S1_S3_S4]"};
        return info;
    endfunction
    
endclass : axi_master1_transaction

`endif // AXI_MASTER1_TRANSACTION_SV

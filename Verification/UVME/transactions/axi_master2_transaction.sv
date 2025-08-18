//=============================================================================
// AXI Master 2 Transaction Class
//=============================================================================
// This file contains the Master 2 specific AXI transaction class that has
// restricted access to only slaves S1, S2, and S4.

`ifndef AXI_MASTER2_TRANSACTION_SV
`define AXI_MASTER2_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_master_transaction.sv"

// AXI Master 2 Transaction Class
class axi_master2_transaction extends axi_master_transaction;
    
    // Master 2 specific constraints
    constraint master2_constraints {
        // Master 2 can only access S1, S2, S4
        master_id == 2;
        slave_id inside {1, 2, 4};
        
        // Address must be within allowed slave ranges
        if (slave_id == 1) addr inside {[32'h0000_2000:32'h0000_2FFF]};
        else if (slave_id == 2) addr inside {[32'h0000_4000:32'h0000_4FFF]};
        else if (slave_id == 4) addr inside {[32'h0000_8000:32'h0000_8FFF]};
        
        // Master 2 has medium priority
        response_delay <= 8;
    }
    
    // Constructor
    function new(string name = "axi_master2_transaction");
        super.new(name);
        master_id = 2;
        // Master 2 can only access S1, S2, S4
        allowed_slaves = '{1, 2, 4};
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils(axi_master2_transaction)
    
    // Master 2 specific utility functions
    function bit can_access_slave(int slave);
        // Master 2 can only access S1, S2, S4
        return (slave == 1 || slave == 2 || slave == 4);
    endfunction
    
    // Override get_transaction_info to include Master 2 specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, " [MASTER2_RESTRICTED_S1_S2_S4]"};
        return info;
    endfunction
    
endclass : axi_master2_transaction

`endif // AXI_MASTER2_TRANSACTION_SV

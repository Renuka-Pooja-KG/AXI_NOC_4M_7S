//=============================================================================
// AXI Master 3 Transaction Class
//=============================================================================
// This file contains the Master 3 specific AXI transaction class that has
// restricted access to only slaves S1, S5, and S6.

`ifndef AXI_MASTER3_TRANSACTION_SV
`define AXI_MASTER3_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_master_transaction.sv"

// AXI Master 3 Transaction Class
class axi_master3_transaction extends axi_master_transaction;
    
    // Master 3 specific constraints
    constraint master3_constraints {
        // Master 3 can only access S1, S5, S6
        master_id == 3;
        slave_id inside {1, 5, 6};
        
        // Address must be within allowed slave ranges
        if (slave_id == 1) addr inside {[32'h0000_2000:32'h0000_2FFF]};
        else if (slave_id == 5) addr inside {[32'h0000_A000:32'h0000_AFFF]};
        else if (slave_id == 6) addr inside {[32'h0000_C000:32'h0000_CFFF]};
        
        // Master 3 has medium priority
        response_delay <= 8;
    }
    
    // Constructor
    function new(string name = "axi_master3_transaction");
        super.new(name);
        master_id = 3;
        // Master 3 can only access S1, S5, S6
        allowed_slaves = '{1, 5, 6};
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils(axi_master3_transaction)
    
    // Master 3 specific utility functions
    function bit can_access_slave(int slave);
        // Master 3 can only access S1, S5, S6
        return (slave == 1 || slave == 5 || slave == 6);
    endfunction
    
    // Override get_transaction_info to include Master 3 specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, " [MASTER3_RESTRICTED_S1_S5_S6]"};
        return info;
    endfunction
    
endclass : axi_master3_transaction

`endif // AXI_MASTER3_TRANSACTION_SV

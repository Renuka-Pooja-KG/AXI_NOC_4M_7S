//=============================================================================
// AXI Master Transaction Class
//=============================================================================
// This file contains the master-specific AXI transaction class that extends
// the base transaction with master-specific functionality and constraints.

`ifndef AXI_MASTER_TRANSACTION_SV
`define AXI_MASTER_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_transaction.sv"

// AXI Master Transaction Class
class axi_master_transaction extends axi_transaction;
    
    // Master-specific fields
    rand bit [3:0] awid;             // Write address ID
    rand bit [3:0] arid;             // Read address ID
    rand bit [3:0] wid;              // Write data ID
    
    // Master state tracking
    bit aw_valid_sent;               // Write address valid sent
    bit w_valid_sent;                // Write data valid sent
    bit ar_valid_sent;               // Read address valid sent
    bit b_ready_sent;                // Write response ready sent
    bit r_ready_sent;                // Read data ready sent
    
    // Master access control
    int unsigned allowed_slaves[];   // Array of slaves this master can access
    
    // Constraints for master-specific behavior
    constraint master_specific_constraints {
        // ID constraints
        awid == master_id;
        arid == master_id;
        wid == master_id;
        
        // Master-specific slave access constraints
        if (master_id == 0) {
            // M0 can access all slaves
            slave_id inside {0, 1, 2, 3, 4, 5, 6};
        } else if (master_id == 1) {
            // M1 can only access S1, S3, S4
            slave_id inside {1, 3, 4};
        } else if (master_id == 2) {
            // M2 can only access S1, S2, S4
            slave_id inside {1, 2, 4};
        } else if (master_id == 3) {
            // M3 can only access S1, S5, S6
            slave_id inside {1, 5, 6};
        }
        
        // Address must be within allowed slave range
        if (slave_id == 0) addr inside {[32'h0000_0000:32'h0000_0FFF]};
        else if (slave_id == 1) addr inside {[32'h0000_2000:32'h0000_2FFF]};
        else if (slave_id == 2) addr inside {[32'h0000_4000:32'h0000_4FFF]};
        else if (slave_id == 3) addr inside {[32'h0000_6000:32'h0000_6FFF]};
        else if (slave_id == 4) addr inside {[32'h0000_8000:32'h0000_8FFF]};
        else if (slave_id == 5) addr inside {[32'h0000_A000:32'h0000_AFFF]};
        else if (slave_id == 6) addr inside {[32'h0000_C000:32'h0000_CFFF]};
    }
    
    // Constructor
    function new(string name = "axi_master_transaction");
        super.new(name);
        aw_valid_sent = 0;
        w_valid_sent = 0;
        ar_valid_sent = 0;
        b_ready_sent = 0;
        r_ready_sent = 0;
        
        // Initialize allowed slaves based on master ID
        case(master_id)
            0: allowed_slaves = '{0, 1, 2, 3, 4, 5, 6}; // All slaves
            1: allowed_slaves = '{1, 3, 4};              // S1, S3, S4
            2: allowed_slaves = '{1, 2, 4};              // S1, S2, S4
            3: allowed_slaves = '{1, 5, 6};              // S1, S5, S6
        endcase
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils_begin(axi_master_transaction)
        `uvm_field_int(awid, UVM_ALL_ON)
        `uvm_field_int(arid, UVM_ALL_ON)
        `uvm_field_int(wid, UVM_ALL_ON)
        `uvm_field_int(aw_valid_sent, UVM_ALL_ON)
        `uvm_field_int(w_valid_sent, UVM_ALL_ON)
        `uvm_field_int(ar_valid_sent, UVM_ALL_ON)
        `uvm_field_int(b_ready_sent, UVM_ALL_ON)
        `uvm_field_int(r_ready_sent, UVM_ALL_ON)
        `uvm_field_sarray_int(allowed_slaves, UVM_ALL_ON)
    `uvm_object_utils_end
    
    // Master-specific utility functions
    function void set_master_id(int id);
        master_id = id;
        // Update allowed slaves
        case(master_id)
            0: allowed_slaves = '{0, 1, 2, 3, 4, 5, 6};
            1: allowed_slaves = '{1, 3, 4};
            2: allowed_slaves = '{1, 2, 4};
            3: allowed_slaves = '{1, 5, 6};
        endcase
    endfunction
    
    function bit can_access_slave(int slave);
        foreach(allowed_slaves[i]) begin
            if (allowed_slaves[i] == slave) return 1;
        end
        return 0;
    endfunction
    
    function void mark_aw_sent();
        aw_valid_sent = 1;
    endfunction
    
    function void mark_w_sent();
        w_valid_sent = 1;
    endfunction
    
    function void mark_ar_sent();
        ar_valid_sent = 1;
    endfunction
    
    function void mark_b_ready();
        b_ready_sent = 1;
    endfunction
    
    function void mark_r_ready();
        r_ready_sent = 1;
    endfunction
    
    function bit is_write_complete();
        return (aw_valid_sent && w_valid_sent && b_ready_sent);
    endfunction
    
    function bit is_read_complete();
        return (ar_valid_sent && r_ready_sent);
    endfunction
    
    function bit is_transaction_complete();
        if (trans_type == AXI_WRITE) return is_write_complete();
        else return is_read_complete();
    endfunction
    
    // Override get_transaction_info to include master-specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, $sformatf(" AWID:%0d ARID:%0d WID:%0d", awid, arid, wid)};
        return info;
    endfunction
    
endclass : axi_master_transaction

`endif // AXI_MASTER_TRANSACTION_SV

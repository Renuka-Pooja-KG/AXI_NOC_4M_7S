//=============================================================================
// AXI Slave 0 Transaction Class
//=============================================================================
// This file contains the Slave 0 specific AXI transaction class with
// address range 0x0000_0000-0x0000_0FFF.

`ifndef AXI_SLAVE0_TRANSACTION_SV
`define AXI_SLAVE0_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_slave_transaction.sv"

// AXI Slave 0 Transaction Class
class axi_slave0_transaction extends axi_slave_transaction;
    
    // Slave 0 specific constraints
    constraint slave0_constraints {
        // Slave 0 specific address range
        slave_id == 0;
        addr >= 32'h0000_0000;
        addr <= 32'h0000_0FFF;
        
        // Slave 0 base and end addresses
        base_addr == 32'h0000_0000;
        end_addr == 32'h0000_0FFF;
        
        // Slave 0 can be accessed by any master
        master_id inside {0, 1, 2, 3};
        
        // Slave 0 has fast response time
        response_delay <= 3;
    }
    
    // Constructor
    function new(string name = "axi_slave0_transaction");
        super.new(name);
        slave_id = 0;
        base_addr = 32'h0000_0000;
        end_addr = 32'h0000_0FFF;
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils(axi_slave0_transaction)
    
    // Slave 0 specific utility functions
    function bit is_address_in_range(bit [31:0] address);
        return (address >= 32'h0000_0000 && address <= 32'h0000_0FFF);
    endfunction
    
    // Override get_transaction_info to include Slave 0 specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, " [SLAVE0_0x0000_0000-0x0000_0FFF]"};
        return info;
    endfunction
    
endclass : axi_slave0_transaction

`endif // AXI_SLAVE0_TRANSACTION_SV

//=============================================================================
// AXI Slave 1 Transaction Class
//=============================================================================
// This file contains the Slave 1 specific AXI transaction class with
// address range 0x0000_2000-0x0000_2FFF.

`ifndef AXI_SLAVE1_TRANSACTION_SV
`define AXI_SLAVE1_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_slave_transaction.sv"

// AXI Slave 1 Transaction Class
class axi_slave1_transaction extends axi_slave_transaction;
    
    // Slave 1 specific constraints
    constraint slave1_constraints {
        // Slave 1 specific address range
        slave_id == 1;
        addr >= 32'h0000_2000;
        addr <= 32'h0000_2FFF;
        
        // Slave 1 base and end addresses
        base_addr == 32'h0000_2000;
        end_addr == 32'h0000_2FFF;
        
        // Slave 1 can be accessed by all masters (M0, M1, M2, M3)
        master_id inside {0, 1, 2, 3};
        
        // Slave 1 has medium response time
        response_delay <= 5;
    }
    
    // Constructor
    function new(string name = "axi_slave1_transaction");
        super.new(name);
        slave_id = 1;
        base_addr = 32'h0000_2000;
        end_addr = 32'h0000_2FFF;
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils(axi_slave1_transaction)
    
    // Slave 1 specific utility functions
    function bit is_address_in_range(bit [31:0] address);
        return (address >= 32'h0000_2000 && address <= 32'h0000_2FFF);
    endfunction
    
    // Override get_transaction_info to include Slave 1 specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, " [SLAVE1_0x0000_2000-0x0000_2FFF]"};
        return info;
    endfunction
    
endclass : axi_slave1_transaction

`endif // AXI_SLAVE1_TRANSACTION_SV

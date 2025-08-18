//=============================================================================
// AXI Slave 4 Transaction Class
//=============================================================================
// This file contains the Slave 4 specific AXI transaction class with
// address range 0x0000_8000-0x0000_8FFF.

`ifndef AXI_SLAVE4_TRANSACTION_SV
`define AXI_SLAVE4_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_slave_transaction.sv"

// AXI Slave 4 Transaction Class
class axi_slave4_transaction extends axi_slave_transaction;
    
    // Slave 4 specific constraints
    constraint slave4_constraints {
        // Slave 4 specific address range
        slave_id == 4;
        addr >= 32'h0000_8000;
        addr <= 32'h0000_8FFF;
        
        // Slave 4 base and end addresses
        base_addr == 32'h0000_8000;
        end_addr == 32'h0000_8FFF;
        
        // Slave 4 can be accessed by M0, M1, and M2
        master_id inside {0, 1, 2};
        
        // Slave 4 has medium response time
        response_delay <= 5;
    }
    
    // Constructor
    function new(string name = "axi_slave4_transaction");
        super.new(name);
        slave_id = 4;
        base_addr = 32'h0000_8000;
        end_addr = 32'h0000_8FFF;
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils(axi_slave4_transaction)
    
    // Slave 4 specific utility functions
    function bit is_address_in_range(bit [31:0] address);
        return (address >= 32'h0000_8000 && address <= 32'h0000_8FFF);
    endfunction
    
    // Override get_transaction_info to include Slave 4 specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, " [SLAVE4_0x0000_8000-0x0000_8FFF]"};
        return info;
    endfunction
    
endclass : axi_slave4_transaction

`endif // AXI_SLAVE4_TRANSACTION_SV

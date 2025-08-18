//=============================================================================
// AXI Slave 2 Transaction Class
//=============================================================================
// This file contains the Slave 2 specific AXI transaction class with
// address range 0x0000_4000-0x0000_4FFF.

`ifndef AXI_SLAVE2_TRANSACTION_SV
`define AXI_SLAVE2_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_slave_transaction.sv"

// AXI Slave 2 Transaction Class
class axi_slave2_transaction extends axi_slave_transaction;
    
    // Slave 2 specific constraints
    constraint slave2_constraints {
        // Slave 2 specific address range
        slave_id == 2;
        addr >= 32'h0000_4000;
        addr <= 32'h0000_4FFF;
        
        // Slave 2 base and end addresses
        base_addr == 32'h0000_4000;
        end_addr == 32'h0000_4FFF;
        
        // Slave 2 can only be accessed by M0 and M2
        master_id inside {0, 2};
        
        // Slave 2 has medium response time
        response_delay <= 5;
    }
    
    // Constructor
    function new(string name = "axi_slave2_transaction");
        super.new(name);
        slave_id = 2;
        base_addr = 32'h0000_4000;
        end_addr = 32'h0000_4FFF;
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils(axi_slave2_transaction)
    
    // Slave 2 specific utility functions
    function bit is_address_in_range(bit [31:0] address);
        return (address >= 32'h0000_4000 && address <= 32'h0000_4FFF);
    endfunction
    
    // Override get_transaction_info to include Slave 2 specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, " [SLAVE2_0x0000_4000-0x0000_4FFF]"};
        return info;
    endfunction
    
endclass : axi_slave2_transaction

`endif // AXI_SLAVE2_TRANSACTION_SV

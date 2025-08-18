//=============================================================================
// AXI Slave 3 Transaction Class
//=============================================================================
// This file contains the Slave 3 specific AXI transaction class with
// address range 0x0000_6000-0x0000_6FFF.

`ifndef AXI_SLAVE3_TRANSACTION_SV
`define AXI_SLAVE3_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_slave_transaction.sv"

// AXI Slave 3 Transaction Class
class axi_slave3_transaction extends axi_slave_transaction;
    
    // Slave 3 specific constraints
    constraint slave3_constraints {
        // Slave 3 specific address range
        slave_id == 3;
        addr >= 32'h0000_6000;
        addr <= 32'h0000_6FFF;
        
        // Slave 3 base and end addresses
        base_addr == 32'h0000_6000;
        end_addr == 32'h0000_6FFF;
        
        // Slave 3 can only be accessed by M0 and M1
        master_id inside {0, 1};
        
        // Slave 3 has medium response time
        response_delay <= 5;
    }
    
    // Constructor
    function new(string name = "axi_slave3_transaction");
        super.new(name);
        slave_id = 3;
        base_addr = 32'h0000_6000;
        end_addr = 32'h0000_6FFF;
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils(axi_slave3_transaction)
    
    // Slave 3 specific utility functions
    function bit is_address_in_range(bit [31:0] address);
        return (address >= 32'h0000_6000 && address <= 32'h0000_6FFF);
    endfunction
    
    // Override get_transaction_info to include Slave 3 specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, " [SLAVE3_0x0000_6000-0x0000_6FFF]"};
        return info;
    endfunction
    
endclass : axi_slave3_transaction

`endif // AXI_SLAVE3_TRANSACTION_SV

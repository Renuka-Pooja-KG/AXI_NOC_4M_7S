//=============================================================================
// AXI Slave 5 Transaction Class
//=============================================================================
// This file contains the Slave 5 specific AXI transaction class with
// address range 0x0000_A000-0x0000_AFFF.

`ifndef AXI_SLAVE5_TRANSACTION_SV
`define AXI_SLAVE5_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_slave_transaction.sv"

// AXI Slave 5 Transaction Class
class axi_slave5_transaction extends axi_slave_transaction;
    
    // Slave 5 specific constraints
    constraint slave5_constraints {
        // Slave 5 specific address range
        slave_id == 5;
        addr >= 32'h0000_A000;
        addr <= 32'h0000_AFFF;
        
        // Slave 5 base and end addresses
        base_addr == 32'h0000_A000;
        end_addr == 32'h0000_AFFF;
        
        // Slave 5 can only be accessed by M0 and M3
        master_id inside {0, 3};
        
        // Slave 5 has medium response time
        response_delay <= 5;
    }
    
    // Constructor
    function new(string name = "axi_slave5_transaction");
        super.new(name);
        slave_id = 5;
        base_addr = 32'h0000_A000;
        end_addr = 32'h0000_AFFF;
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils(axi_slave5_transaction)
    
    // Slave 5 specific utility functions
    function bit is_address_in_range(bit [31:0] address);
        return (address >= 32'h0000_A000 && address <= 32'h0000_AFFF);
    endfunction
    
    // Override get_transaction_info to include Slave 5 specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, " [SLAVE5_0x0000_A000-0x0000_AFFF]"};
        return info;
    endfunction
    
endclass : axi_slave5_transaction

`endif // AXI_SLAVE5_TRANSACTION_SV

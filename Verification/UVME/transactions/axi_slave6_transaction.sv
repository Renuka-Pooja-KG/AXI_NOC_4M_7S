//=============================================================================
// AXI Slave 6 Transaction Class
//=============================================================================
// This file contains the Slave 6 specific AXI transaction class with
// address range 0x0000_C000-0x0000_CFFF.

`ifndef AXI_SLAVE6_TRANSACTION_SV
`define AXI_SLAVE6_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_slave_transaction.sv"

// AXI Slave 6 Transaction Class
class axi_slave6_transaction extends axi_slave_transaction;
    
    // Slave 6 specific constraints
    constraint slave6_constraints {
        // Slave 6 specific address range
        slave_id == 6;
        addr >= 32'h0000_C000;
        addr <= 32'h0000_CFFF;
        
        // Slave 6 base and end addresses
        base_addr == 32'h0000_C000;
        end_addr == 32'h0000_CFFF;
        
        // Slave 6 can only be accessed by M0 and M3
        master_id inside {0, 3};
        
        // Slave 6 has medium response time
        response_delay <= 5;
    }
    
    // Constructor
    function new(string name = "axi_slave6_transaction");
        super.new(name);
        slave_id = 6;
        base_addr = 32'h0000_C000;
        end_addr = 32'h0000_CFFF;
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils(axi_slave6_transaction)
    
    // Slave 6 specific utility functions
    function bit is_address_in_range(bit [31:0] address);
        return (address >= 32'h0000_C000 && address <= 32'h0000_CFFF);
    endfunction
    
    // Override get_transaction_info to include Slave 6 specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, " [SLAVE6_0x0000_C000-0x0000_CFFF]"};
        return info;
    endfunction
    
endclass : axi_slave6_transaction

`endif // AXI_SLAVE6_TRANSACTION_SV

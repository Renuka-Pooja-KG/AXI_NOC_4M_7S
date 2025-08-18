//=============================================================================
// AXI Slave Transaction Class
//=============================================================================
// This file contains the slave-specific AXI transaction class that extends
// the base transaction with slave-specific functionality and constraints.

`ifndef AXI_SLAVE_TRANSACTION_SV
`define AXI_SLAVE_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"
`include "axi_transaction.sv"

// AXI Slave Transaction Class
class axi_slave_transaction extends axi_transaction;
    
    // Slave-specific fields
    rand bit [5:0] bid;              // Write response ID
    rand bit [5:0] rid;              // Read response ID
    
    // Slave state tracking
    bit aw_ready_sent;               // Write address ready sent
    bit w_ready_sent;                // Write data ready sent
    bit ar_ready_sent;               // Read address ready sent
    bit b_valid_sent;                // Write response valid sent
    bit r_valid_sent;                // Read data valid sent
    
    // Slave response behavior
    rand int unsigned response_delay; // Response delay in clock cycles
    rand bit inject_error;            // Inject error response
    
    // Slave address range
    bit [31:0] base_addr;            // Base address for this slave
    bit [31:0] end_addr;             // End address for this slave
    
    // Constraints for slave-specific behavior
    constraint slave_specific_constraints {
        // Response delay constraints
        response_delay >= 0;
        response_delay <= 10;
        
        // Address must be within this slave's range
        addr >= base_addr;
        addr <= end_addr;
        
        // Slave ID must match the address range
        if (addr >= 32'h0000_0000 && addr <= 32'h0000_0FFF) slave_id == 0;
        else if (addr >= 32'h0000_2000 && addr <= 32'h0000_2FFF) slave_id == 1;
        else if (addr >= 32'h0000_4000 && addr <= 32'h0000_4FFF) slave_id == 2;
        else if (addr >= 32'h0000_6000 && addr <= 32'h0000_6FFF) slave_id == 3;
        else if (addr >= 32'h0000_8000 && addr <= 32'h0000_8FFF) slave_id == 4;
        else if (addr >= 32'h0000_A000 && addr <= 32'h0000_AFFF) slave_id == 5;
        else if (addr >= 32'h0000_C000 && addr <= 32'h0000_CFFF) slave_id == 6;
        
        // ID constraints (slave ID + master ID)
        bid[5:4] == slave_id[2:0];
        bid[3:0] == master_id;
        rid[5:4] == slave_id[2:0];
        rid[3:0] == master_id;
    }
    
    // Constructor
    function new(string name = "axi_slave_transaction");
        super.new(name);
        aw_ready_sent = 0;
        w_ready_sent = 0;
        ar_ready_sent = 0;
        b_valid_sent = 0;
        r_valid_sent = 0;
        response_delay = 0;
        inject_error = 0;
        
        // Set address range based on slave ID
        case(slave_id)
            0: begin base_addr = 32'h0000_0000; end_addr = 32'h0000_0FFF; end
            1: begin base_addr = 32'h0000_2000; end_addr = 32'h0000_2FFF; end
            2: begin base_addr = 32'h0000_4000; end_addr = 32'h0000_4FFF; end
            3: begin base_addr = 32'h0000_6000; end_addr = 32'h0000_6FFF; end
            4: begin base_addr = 32'h0000_8000; end_addr = 32'h0000_8FFF; end
            5: begin base_addr = 32'h0000_A000; end_addr = 32'h0000_AFFF; end
            6: begin base_addr = 32'h0000_C000; end_addr = 32'h0000_CFFF; end
        endcase
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils_begin(axi_slave_transaction)
        `uvm_field_int(bid, UVM_ALL_ON)
        `uvm_field_int(rid, UVM_ALL_ON)
        `uvm_field_int(aw_ready_sent, UVM_ALL_ON)
        `uvm_field_int(w_ready_sent, UVM_ALL_ON)
        `uvm_field_int(ar_ready_sent, UVM_ALL_ON)
        `uvm_field_int(b_valid_sent, UVM_ALL_ON)
        `uvm_field_int(r_valid_sent, UVM_ALL_ON)
        `uvm_field_int(response_delay, UVM_ALL_ON)
        `uvm_field_int(inject_error, UVM_ALL_ON)
        `uvm_field_int(base_addr, UVM_ALL_ON)
        `uvm_field_int(end_addr, UVM_ALL_ON)
    `uvm_object_utils_end
    
    // Slave-specific utility functions
    function void set_slave_id(int id);
        slave_id = id;
        // Update address range
        case(slave_id)
            0: begin base_addr = 32'h0000_0000; end_addr = 32'h0000_0FFF; end
            1: begin base_addr = 32'h0000_2000; end_addr = 32'h0000_2FFF; end
            2: begin base_addr = 32'h0000_4000; end_addr = 32'h0000_4FFF; end
            3: begin base_addr = 32'h0000_6000; end_addr = 32'h0000_6FFF; end
            4: begin base_addr = 32'h0000_8000; end_addr = 32'h0000_8FFF; end
            5: begin base_addr = 32'h0000_A000; end_addr = 32'h0000_AFFF; end
            6: begin base_addr = 32'h0000_C000; end_addr = 32'h0000_CFFF; end
        endcase
    endfunction
    
    function void mark_aw_ready();
        aw_ready_sent = 1;
    endfunction
    
    function void mark_w_ready();
        w_ready_sent = 1;
    endfunction
    
    function void mark_ar_ready();
        ar_ready_sent = 1;
    endfunction
    
    function void mark_b_valid();
        b_valid_sent = 1;
    endfunction
    
    function void mark_r_valid();
        r_valid_sent = 1;
    endfunction
    
    function bit is_write_ready();
        return (aw_ready_sent && w_ready_sent);
    endfunction
    
    function bit is_read_ready();
        return ar_ready_sent;
    endfunction
    
    function bit is_write_response_sent();
        return b_valid_sent;
    endfunction
    
    function bit is_read_response_sent();
        return r_valid_sent;
    endfunction
    
    function bit is_transaction_ready();
        if (trans_type == AXI_WRITE) return is_write_ready();
        else return is_read_ready();
    endfunction
    
    function bit is_response_sent();
        if (trans_type == AXI_WRITE) return is_write_response_sent();
        else return is_read_response_sent();
    endfunction
    
    // Generate response based on transaction type and error injection
    function axi_resp_type_e generate_response();
        if (inject_error) begin
            // Randomly choose between SLVERR and DECERR
            if ($random % 2) return AXI_SLVERR;
            else return AXI_DECERR;
        end else begin
            // Normal response
            if ($random % 10 == 0) return AXI_EXOKAY; // 10% chance of EXOKAY
            else return AXI_OKAY;
        end
    endfunction
    
    // Override get_transaction_info to include slave-specific info
    function string get_transaction_info();
        string info = super.get_transaction_info();
        info = {info, $sformatf(" BID:%0d RID:%0d Delay:%0d", bid, rid, response_delay)};
        if (inject_error) info = {info, " [ERROR_INJECTED]"};
        return info;
    endfunction
    
endclass : axi_slave_transaction

`endif // AXI_SLAVE_TRANSACTION_SV

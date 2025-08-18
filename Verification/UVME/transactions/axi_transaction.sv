//=============================================================================
// AXI Transaction Base Class
//=============================================================================
// This file contains the base AXI transaction class that defines the common
// structure for all AXI transactions in the NOC verification environment.

`ifndef AXI_TRANSACTION_SV
`define AXI_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

// AXI Transaction Types
typedef enum {
    AXI_READ,
    AXI_WRITE
} axi_trans_type_e;

// AXI Burst Types
typedef enum {
    AXI_FIXED,
    AXI_INCR,
    AXI_WRAP
} axi_burst_type_e;

// AXI Response Types
typedef enum {
    AXI_OKAY,
    AXI_EXOKAY,
    AXI_SLVERR,
    AXI_DECERR
} axi_resp_type_e;

// AXI Lock Types
typedef enum {
    AXI_NORMAL,
    AXI_EXCLUSIVE,
    AXI_LOCKED
} axi_lock_type_e;

// AXI Transaction Class
class axi_transaction extends uvm_sequence_item;
    
    // Transaction Identification
    rand int unsigned master_id;      // Master ID (0-3)
    rand int unsigned slave_id;       // Slave ID (0-6)
    rand int unsigned transaction_id; // Unique transaction ID
    
    // Transaction Type
    rand axi_trans_type_e trans_type;
    
    // Address Information
    rand bit [31:0] addr;            // Transaction address
    rand bit [3:0]  len;             // Burst length (0-15)
    rand bit [2:0]  size;            // Transfer size (0-7)
    rand axi_burst_type_e burst;     // Burst type
    rand axi_lock_type_e lock;       // Lock type
    rand bit [3:0]  cache;           // Cache attributes
    rand bit [2:0]  prot;            // Protection attributes
    rand bit [3:0]  qos;             // Quality of service
    rand bit [3:0]  region;          // Region identifier
    
    // Data Information
    rand bit [31:0] data[];          // Data array for burst transfers
    rand bit [3:0]  strb[];          // Strobe array for burst transfers
    
    // Response Information
    rand axi_resp_type_e resp;       // Response status
    rand bit [5:0]  id;              // Response ID
    
    // Timing Information
    time start_time;                 // Transaction start time
    time end_time;                   // Transaction end time
    
    // Control Fields
    rand bit is_last;                // Last transfer in burst
    rand bit valid;                  // Valid signal
    rand bit ready;                  // Ready signal
    
    // Constraints
    constraint addr_range {
        addr >= 32'h0000_0000;
        addr <= 32'h0000_FFFF;
    }
    
    constraint len_range {
        len >= 0;
        len <= 15;
    }
    
    constraint size_range {
        size >= 0;
        size <= 7;
    }
    
    constraint master_id_range {
        master_id >= 0;
        master_id <= 3;
    }
    
    constraint slave_id_range {
        slave_id >= 0;
        slave_id <= 6;
    }
    
    constraint data_array_size {
        data.size() == len + 1;
        strb.size() == len + 1;
    }
    
    constraint strb_valid {
        foreach(strb[i]) {
            strb[i] >= 4'h0;
            strb[i] <= 4'hF;
        }
    }
    
    // Constructor
    function new(string name = "axi_transaction");
        super.new(name);
    endfunction
    
    // UVM Field Macros
    `uvm_object_utils_begin(axi_transaction)
        `uvm_field_int(master_id, UVM_ALL_ON)
        `uvm_field_int(slave_id, UVM_ALL_ON)
        `uvm_field_int(transaction_id, UVM_ALL_ON)
        `uvm_field_enum(axi_trans_type_e, trans_type, UVM_ALL_ON)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(len, UVM_ALL_ON)
        `uvm_field_int(size, UVM_ALL_ON)
        `uvm_field_enum(axi_burst_type_e, burst, UVM_ALL_ON)
        `uvm_field_enum(axi_lock_type_e, lock, UVM_ALL_ON)
        `uvm_field_int(cache, UVM_ALL_ON)
        `uvm_field_int(prot, UVM_ALL_ON)
        `uvm_field_int(qos, UVM_ALL_ON)
        `uvm_field_int(region, UVM_ALL_ON)
        `uvm_field_sarray_int(data, UVM_ALL_ON)
        `uvm_field_sarray_int(strb, UVM_ALL_ON)
        `uvm_field_enum(axi_resp_type_e, resp, UVM_ALL_ON)
        `uvm_field_int(id, UVM_ALL_ON)
        `uvm_field_time(start_time, UVM_ALL_ON)
        `uvm_field_time(end_time, UVM_ALL_ON)
        `uvm_field_int(is_last, UVM_ALL_ON)
        `uvm_field_int(valid, UVM_ALL_ON)
        `uvm_field_int(ready, UVM_ALL_ON)
    `uvm_object_utils_end
    
    // Utility Functions
    function void set_start_time();
        start_time = $time;
    endfunction
    
    function void set_end_time();
        end_time = $time;
    endfunction
    
    function time get_duration();
        return end_time - start_time;
    endfunction
    
    function string get_transaction_info();
        return $sformatf("M%d->S%d %s Addr:0x%08X Len:%0d Size:%0d Burst:%s", 
                        master_id, slave_id, trans_type.name(), addr, len, size, burst.name());
    endfunction
    
    function bit is_valid_for_master(int master, int slave);
        case(master)
            0: return 1; // M0 can access all slaves
            1: return (slave == 1 || slave == 3 || slave == 4); // M1: S1, S3, S4
            2: return (slave == 1 || slave == 2 || slave == 4); // M2: S1, S2, S4
            3: return (slave == 1 || slave == 5 || slave == 6); // M3: S1, S5, S6
            default: return 0;
        endcase
    endfunction
    
    function bit is_address_valid();
        case(slave_id)
            0: return (addr >= 32'h0000_0000 && addr <= 32'h0000_0FFF);
            1: return (addr >= 32'h0000_2000 && addr <= 32'h0000_2FFF);
            2: return (addr >= 32'h0000_4000 && addr <= 32'h0000_4FFF);
            3: return (addr >= 32'h0000_6000 && addr <= 32'h0000_6FFF);
            4: return (addr >= 32'h0000_8000 && addr <= 32'h0000_8FFF);
            5: return (addr >= 32'h0000_A000 && addr <= 32'h0000_AFFF);
            6: return (addr >= 32'h0000_C000 && addr <= 32'h0000_CFFF);
            default: return 0;
        endcase
    endfunction
    
endclass : axi_transaction

`endif // AXI_TRANSACTION_SV

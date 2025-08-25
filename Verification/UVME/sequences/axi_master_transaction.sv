//=============================================================================
// Generic AXI Master Transaction Class
//=============================================================================
// Contains all AXI signal values for driving the interface

`ifndef AXI_MASTER_TRANSACTION_SV
`define AXI_MASTER_TRANSACTION_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

// Transaction type enumeration
typedef enum bit [1:0] {
    AXI_WRITE = 2'b00,
    AXI_READ  = 2'b01
} axi_trans_type_e;

// Burst type enumeration
typedef enum bit [1:0] {
    AXI_FIXED = 2'b00,
    AXI_INCR  = 2'b01,
    AXI_WRAP  = 2'b10
} axi_burst_type_e;

// Lock type enumeration
typedef enum bit {
    AXI_NORMAL = 1'b0,
    AXI_EXCLUSIVE = 1'b1
} axi_lock_type_e;

// Response type enumeration
typedef enum bit [1:0] {
    AXI_OKAY    = 2'b00,
    AXI_EXOKAY  = 2'b01,
    AXI_SLVERR  = 2'b10,
    AXI_DECERR  = 2'b11
} axi_response_type_e;

class axi_master_transaction extends uvm_sequence_item;
    
    // Transaction identification
    rand int unsigned master_id;      // 0, 1, 2, or 3
    rand int unsigned slave_id;       // 0, 1, 2, 3, 4, 5, or 6
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    rand bit [3:0]  awid;           // Write address ID
    rand bit [31:0] awaddr;         // Write address
    rand bit [7:0]  awlen;          // Burst length (0-15)
    rand bit [2:0]  awsize;         // Burst size
    rand bit [1:0]  awburst;        // Burst type
    rand bit        awlock;          // Lock type
    rand bit [3:0]  awcache;        // Cache attributes
    rand bit [2:0]  awprot;         // Protection attributes
    rand bit [3:0]  awqos;          // Quality of service
    rand bit [3:0]  awregion;       // Region identifier
    rand bit        awvalid;         // Write address valid
    bit             awready;         // Write address ready (from slave)
    
    // ===== WRITE DATA CHANNEL (W) =====
    rand bit [31:0] wdata;          // Write data
    rand bit [3:0]  wstrb;          // Write strobes
    rand bit        wlast;          // Write last
    rand bit        wvalid;         // Write valid
    bit             wready;         // Write ready (from slave)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    bit [3:0]       bid;            // Write response ID (from slave)
    bit [1:0]       bresp;          // Write response (from slave)
    bit             bvalid;         // Write response valid (from slave)
    rand bit        bready;         // Write response ready
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    rand bit [3:0]  arid;           // Read address ID
    rand bit [31:0] araddr;         // Read address
    rand bit [7:0]  arlen;          // Burst length (0-15)
    rand bit [2:0]  arsize;         // Burst size
    rand bit [1:0]  arburst;        // Burst type
    rand bit        arlock;          // Lock type
    rand bit [3:0]  arcache;        // Cache attributes
    rand bit [2:0]  arprot;         // Protection attributes
    rand bit [3:0]  arqos;          // Quality of service
    rand bit [3:0]  arregion;       // Region identifier
    rand bit        arvalid;         // Read address valid
    bit             arready;         // Read address ready (from slave)
    
    // ===== READ DATA CHANNEL (R) =====
    bit [3:0]       rid;            // Read ID (from slave)
    bit [31:0]     rdata;          // Read data (from slave)
    bit [1:0]      rresp;          // Read response (from slave)
    bit             rlast;          // Read last (from slave)
    bit             rvalid;         // Read valid (from slave)
    rand bit        rready;         // Read ready
    
    // ===== BURST DATA ARRAYS =====
    rand bit [31:0] burst_data[];   // Array for burst data
    rand bit [3:0]  burst_strobe[]; // Array for burst strobes
    
    // ===== STATUS AND TIMING =====
    bit             transaction_complete;
    time            start_time;
    time            end_time;
    
    // Constraints
    constraint master_id_c {
        master_id inside {[0:3]};
    }
    
    constraint slave_id_c {
        slave_id inside {[0:6]};
    }
    
    constraint awid_c {
        awid inside {[0:15]};
    }
    
    constraint arid_c {
        arid inside {[0:15]};
    }
    
    constraint awlen_c {
        awlen inside {[0:15]};
    }
    
    constraint arlen_c {
        arlen inside {[0:15]};
    }
    
    constraint awsize_c {
        awsize inside {[0:7]};
    }
    
    constraint arsize_c {
        arsize inside {[0:7]};
    }
    
    constraint awburst_c {
        awburst inside {[0:2]};
    }
    
    constraint arburst_c {
        arburst inside {[0:2]};
    }
    
    constraint awlock_c {
        awlock inside {[0:1]};
    }
    
    constraint arlock_c {
        arlock inside {[0:1]};
    }
    
    constraint awcache_c {
        awcache inside {[0:15]};
    }
    
    constraint arcache_c {
        arcache inside {[0:15]};
    }
    
    constraint awprot_c {
        awprot inside {[0:7]};
    }
    
    constraint arprot_c {
        arprot inside {[0:7]};
    }
    
    constraint awqos_c {
        awqos inside {[0:15]};
    }
    
    constraint arqos_c {
        arqos inside {[0:15]};
    }
    
    constraint awregion_c {
        awregion inside {[0:15]};
    }
    
    constraint arregion_c {
        arregion inside {[0:15]};
    }
    
    constraint address_alignment_c {
        if (trans_type == AXI_WRITE) {
            awaddr % (1 << awsize) == 0;
        } else {
            araddr % (1 << arsize) == 0;
        }
    }
    
    // Master-specific slave access constraints
    constraint access_control_c {
        if (master_id == 0) {
            // M0 can access all slaves
            slave_id inside {[0:6]};
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
    }
    
    // Address range constraints based on slave
    constraint address_range_c {
        if (slave_id == 0) {
            if (trans_type == AXI_WRITE) awaddr inside {[32'h0000_0000:32'h0000_0FFF]};
            else araddr inside {[32'h0000_0000:32'h0000_0FFF]};
        } else if (slave_id == 1) {
            if (trans_type == AXI_WRITE) awaddr inside {[32'h0000_2000:32'h0000_2FFF]};
            else araddr inside {[32'h0000_2000:32'h0000_2FFF]};
        } else if (slave_id == 2) {
            if (trans_type == AXI_WRITE) awaddr inside {[32'h0000_4000:32'h0000_4FFF]};
            else araddr inside {[32'h0000_4000:32'h0000_4FFF]};
        } else if (slave_id == 3) {
            if (trans_type == AXI_WRITE) awaddr inside {[32'h0000_6000:32'h0000_6FFF]};
            else araddr inside {[32'h0000_6000:32'h0000_6FFF]};
        } else if (slave_id == 4) {
            if (trans_type == AXI_WRITE) awaddr inside {[32'h0000_8000:32'h0000_8FFF]};
            else araddr inside {[32'h0000_8000:32'h0000_8FFF]};
        } else if (slave_id == 5) {
            if (trans_type == AXI_WRITE) awaddr inside {[32'h0000_A000:32'h0000_AFFF]};
            else araddr inside {[32'h0000_A000:32'h0000_AFFF]};
        } else if (slave_id == 6) {
            if (trans_type == AXI_WRITE) awaddr inside {[32'h0000_C000:32'h0000_CFFF]};
            else araddr inside {[32'h0000_C000:32'h0000_CFFF]};
        }
    }
    
    // Burst data array size constraint
    constraint burst_data_size_c {
        if (trans_type == AXI_WRITE) {
            burst_data.size() == (awlen + 1);
            burst_strobe.size() == (awlen + 1);
        } else {
            burst_data.size() == (arlen + 1);
        }
    }
    
    // Constructor
    function new(string name = "axi_master_transaction");
        super.new(name);
        transaction_complete = 0;
        start_time = 0;
        end_time = 0;
        
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
    endfunction
    
    // Set master ID
    function void set_master_id(int id);
        master_id = id;
    endfunction
    
    // Set slave ID
    function void set_slave_id(int id);
        slave_id = id;
    endfunction
    
    // Set transaction type
    function void set_transaction_type(axi_trans_type_e type);
        trans_type = type;
    endfunction
    
    // Set burst parameters
    function void set_burst_parameters(int length, axi_burst_type_e burst, int size);
        if (trans_type == AXI_WRITE) begin
            awlen = length - 1;  // AXI length is 0-based
            awburst = burst;
            awsize = $clog2(size);
        end else begin
            arlen = length - 1;
            arburst = burst;
            arsize = $clog2(size);
        end
        
        // Resize arrays
        burst_data = new[length];
        burst_strobe = new[length];
    endfunction
    
    // Set address
    function void set_address(bit [31:0] addr);
        if (trans_type == AXI_WRITE) begin
            awaddr = addr;
        end else begin
            araddr = addr;
        end
    endfunction
    
    // Set burst data
    function void set_burst_data(int index, bit [31:0] data);
        if (index < burst_data.size()) begin
            burst_data[index] = data;
        end
    endfunction
    
    // Set burst strobe
    function void set_burst_strobe(int index, bit [3:0] strobe);
        if (index < burst_strobe.size()) begin
            burst_strobe[index] = strobe;
        end
    endfunction
    
    // Check if transaction is complete
    function bit is_complete();
        return transaction_complete;
    endfunction
    
    // Mark transaction as complete
    function void mark_complete();
        transaction_complete = 1;
        end_time = $time;
    endfunction
    
    // Get transaction duration
    function time get_duration();
        return end_time - start_time;
    endfunction
    
    // Get transaction info string
    function string get_transaction_info();
        if (trans_type == AXI_WRITE) begin
            return $sformatf("M%0d->S%0d WRITE ID=%0d Len=%0d Addr=0x%08x Burst=%s", 
                            master_id, slave_id, awid, (awlen + 1), awaddr, 
                            awburst.name());
        end else begin
            return $sformatf("M%0d->S%0d READ ID=%0d Len=%0d Addr=0x%08x Burst=%s", 
                            master_id, slave_id, arid, (arlen + 1), araddr, 
                            arburst.name());
        end
    endfunction
    
    // UVM Field Macros - Automatic copy, compare, print, etc.
    `uvm_object_utils_begin(axi_master_transaction)
        `uvm_field_int(master_id, UVM_ALL_ON)
        `uvm_field_int(slave_id, UVM_ALL_ON)
        `uvm_field_enum(trans_type, axi_trans_type_e, UVM_ALL_ON)
        `uvm_field_int(awid, UVM_ALL_ON)
        `uvm_field_int(awaddr, UVM_ALL_ON)
        `uvm_field_int(awlen, UVM_ALL_ON)
        `uvm_field_int(awsize, UVM_ALL_ON)
        `uvm_field_enum(awburst, axi_burst_type_e, UVM_ALL_ON)
        `uvm_field_int(awlock, UVM_ALL_ON)
        `uvm_field_int(awcache, UVM_ALL_ON)
        `uvm_field_int(awprot, UVM_ALL_ON)
        `uvm_field_int(awqos, UVM_ALL_ON)
        `uvm_field_int(awregion, UVM_ALL_ON)
        `uvm_field_int(awvalid, UVM_ALL_ON)
        `uvm_field_int(wdata, UVM_ALL_ON)
        `uvm_field_int(wstrb, UVM_ALL_ON)
        `uvm_field_int(wlast, UVM_ALL_ON)
        `uvm_field_int(wvalid, UVM_ALL_ON)
        `uvm_field_int(arid, UVM_ALL_ON)
        `uvm_field_int(araddr, UVM_ALL_ON)
        `uvm_field_int(arlen, UVM_ALL_ON)
        `uvm_field_int(arsize, UVM_ALL_ON)
        `uvm_field_enum(arburst, axi_burst_type_e, UVM_ALL_ON)
        `uvm_field_int(arlock, UVM_ALL_ON)
        `uvm_field_int(arcache, UVM_ALL_ON)
        `uvm_field_int(arprot, UVM_ALL_ON)
        `uvm_field_int(arqos, UVM_ALL_ON)
        `uvm_field_int(arregion, UVM_ALL_ON)
        `uvm_field_int(arvalid, UVM_ALL_ON)
        `uvm_field_array_int(burst_data, UVM_ALL_ON)
        `uvm_field_array_int(burst_strobe, UVM_ALL_ON)
        `uvm_field_int(transaction_complete, UVM_ALL_ON)
        `uvm_field_time(start_time, UVM_ALL_ON)
        `uvm_field_time(end_time, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : axi_master_transaction

`endif // AXI_MASTER_TRANSACTION_SV
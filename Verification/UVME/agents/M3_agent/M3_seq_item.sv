//=============================================================================
// M3 Agent Sequence Item Class
//=============================================================================
// Standalone sequence item for Master 3 with limited access to S1, S5, S6
// Extends uvm_sequence_item directly

import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the common AXI types package
import axi_common_types_pkg::*;

class M3_seq_item extends uvm_sequence_item;
    
    // M3-specific transaction identification
    rand int unsigned m3_transaction_id;  // Unique transaction ID for M3
    rand axi_slave_id_e slave_id;         // Target slave (1, 5, 6 only)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    rand bit [AXI_ID_WIDTH-1:0]     M3_AWID;           // Write address ID
    rand bit [AXI_ADDR_WIDTH-1:0]   M3_AWADDR;         // Write address
    rand bit [AXI_LEN_WIDTH-1:0]    M3_AWLEN;          // Burst length (0-15)
    rand bit [AXI_SIZE_WIDTH-1:0]   M3_AWSIZE;         // Burst size
    rand bit [AXI_BURST_WIDTH-1:0]  M3_AWBURST;        // Burst type
    rand bit [AXI_LOCK_WIDTH-1:0]   M3_AWLOCK;          // Lock type
    rand bit [AXI_CACHE_WIDTH-1:0]  M3_AWCACHE;        // Cache attributes
    rand bit [AXI_PROT_WIDTH-1:0]   M3_AWPROT;         // Protection attributes
    rand bit [AXI_QOS_WIDTH-1:0]    M3_AWQOS;          // Quality of service
    rand bit [AXI_REGION_WIDTH-1:0] M3_AWREGION;       // Region identifier
    rand bit                        M3_AWVALID;         // Write address valid
    bit                             M3_AWREADY;         // Write address ready (from slave)
    
    // ===== WRITE DATA CHANNEL (W) =====
    rand bit [AXI_DATA_WIDTH-1:0]   M3_WDATA;          // Write data
    rand bit [AXI_STRB_WIDTH-1:0]   M3_WSTRB;          // Write strobes
    rand bit                        M3_WLAST;          // Write last
    rand bit                        M3_WVALID;         // Write valid
    bit                             M3_WREADY;         // Write ready (from slave)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    bit [AXI_ID_WIDTH-1:0]          M3_BID;            // Write response ID (from slave)
    bit [AXI_RESP_WIDTH-1:0]        M3_BRESP;          // Write response (from slave)
    bit                             M3_BVALID;         // Write response valid (from slave)
    rand bit                        M3_BREADY;         // Write response ready
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    rand bit [AXI_ID_WIDTH-1:0]     M3_ARID;           // Read address ID
    rand bit [AXI_ADDR_WIDTH-1:0]   M3_ARADDR;         // Read address
    rand bit [AXI_LEN_WIDTH-1:0]    M3_ARLEN;          // Burst length (0-15)
    rand bit [AXI_SIZE_WIDTH-1:0]   M3_ARSIZE;         // Burst size
    rand bit [AXI_BURST_WIDTH-1:0]  M3_ARBURST;        // Burst type
    rand bit [AXI_LOCK_WIDTH-1:0]   M3_ARLOCK;          // Lock type
    rand bit [AXI_CACHE_WIDTH-1:0]  M3_ARCACHE;        // Cache attributes
    rand bit [AXI_PROT_WIDTH-1:0]   M3_ARPROT;         // Protection attributes
    rand bit [AXI_QOS_WIDTH-1:0]    M3_ARQOS;          // Quality of service
    rand bit [AXI_REGION_WIDTH-1:0] M3_ARREGION;       // Region identifier
    rand bit                        M3_ARVALID;         // Read address valid
    bit                             M3_ARREADY;         // Read address ready (from slave)
    
    // ===== READ DATA CHANNEL (R) =====
    bit [AXI_ID_WIDTH-1:0]          M3_RID;            // Read ID (from slave)
    bit [AXI_DATA_WIDTH-1:0]        M3_RDATA;          // Read data (from slave)
    bit [AXI_RESP_WIDTH-1:0]        M3_RRESP;          // Read response (from slave)
    bit                             M3_RLAST;          // Read last (from slave)
    bit                             M3_RVALID;         // Read valid (from slave)
    rand bit                        M3_RREADY;         // Read ready
    
    // ===== BURST DATA ARRAYS =====
    rand bit [AXI_DATA_WIDTH-1:0]   burst_data[];   // Array for burst data
    rand bit [AXI_STRB_WIDTH-1:0]   burst_strobe[]; // Array for burst strobes
    
    // Constraints
    constraint slave_id_c {
        slave_id inside {AXI_SLAVE_1, AXI_SLAVE_5, AXI_SLAVE_6};  // M3 can only access S1, S5, S6
    }
    
    constraint M3_awid_c {
        M3_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};  // Full ID range
    }
    
    constraint M3_arid_c {
        M3_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};  // Full ID range
    }
    
    constraint M3_awlen_c {
        M3_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};  // Burst length 1-16
    }
    
    constraint M3_arlen_c {
        M3_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};  // Burst length 1-16
    }
    
    constraint M3_awsize_c {
        M3_AWSIZE inside {[0:AXI_SIZE_WIDTH-1]};  // Transfer size 1, 2, 4, 8, 16, 32, 64, 128 bytes
    }
    
    constraint M3_arsize_c {
        M3_ARSIZE inside {[0:AXI_SIZE_WIDTH-1]};  // Transfer size 1, 2, 4, 8, 16, 32, 64, 128 bytes
    }
    
    constraint M3_awburst_c {
        M3_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};  // All burst types
    }
    
    constraint M3_arburst_c {
        M3_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};  // All burst types
    }
    
    constraint M3_awlock_c {
        M3_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};  // All lock types
    }
    
    constraint M3_arlock_c {
        M3_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};  // All lock types
    }
    
    constraint M3_awcache_c {
        M3_AWCACHE inside {[0:(1<<AXI_CACHE_WIDTH)-1]}; // All cache combinations
    }
    
    constraint M3_arcache_c {
        M3_ARCACHE inside {[0:(1<<AXI_CACHE_WIDTH)-1]}; // All cache combinations
    }
    
    constraint M3_awprot_c {
        M3_AWPROT inside {[0:(1<<AXI_PROT_WIDTH)-1]};  // All protection combinations
    }
    
    constraint M3_arprot_c {
        M3_ARPROT inside {[0:(1<<AXI_PROT_WIDTH)-1]};  // All protection combinations
    }
    
    constraint M3_awqos_c {
        M3_AWQOS inside {[0:(1<<AXI_QOS_WIDTH)-1]};  // All QoS levels
    }
    
    constraint M3_arqos_c {
        M3_ARQOS inside {[0:(1<<AXI_QOS_WIDTH)-1]};  // All QoS levels
    }
    
    constraint M3_awregion_c {
        M3_AWREGION inside {[0:(1<<AXI_REGION_WIDTH)-1]}; // All region identifiers
    }
    
    constraint M3_arregion_c {
        M3_ARREGION inside {[0:(1<<AXI_REGION_WIDTH)-1]}; // All region identifiers
    }
    
    // Address range constraints based on slave using package constants
    constraint address_range_c {
        if (slave_id == AXI_SLAVE_1) {
            if (trans_type == AXI_WRITE) {
                M3_AWADDR inside {[SLAVE_1_BASE_ADDR:SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M3_ARADDR inside {[SLAVE_1_BASE_ADDR:SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_5) {
            if (trans_type == AXI_WRITE) {
                M3_AWADDR inside {[SLAVE_5_BASE_ADDR:SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M3_ARADDR inside {[SLAVE_5_BASE_ADDR:SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_6) {
            if (trans_type == AXI_WRITE) {
                M3_AWADDR inside {[SLAVE_6_BASE_ADDR:SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M3_ARADDR inside {[SLAVE_6_BASE_ADDR:SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        }
    }
    
    // Address alignment constraints using package function
    constraint address_alignment_c {
        if (trans_type == AXI_WRITE) {
            M3_AWADDR % (1 << M3_AWSIZE) == 0;
        } else {
            M3_ARADDR % (1 << M3_ARSIZE) == 0;
        }
    }
    
    // Burst data array size constraint
    constraint burst_data_size_c {
        if (trans_type == AXI_WRITE) {
            burst_data.size() == get_burst_length(M3_AWLEN);
            burst_strobe.size() == get_burst_length(M3_AWLEN);
        } else {
            burst_data.size() == get_burst_length(M3_ARLEN);
        }
    }
    
    // Constructor
    function new(string name = "M3_seq_item");
        super.new(name);
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
    endfunction
    
    // UVM Field Macros for automatic copy, compare, print, etc.
    `uvm_object_utils_begin(M3_seq_item)
        `uvm_field_int(m3_transaction_id, UVM_ALL_ON)
        `uvm_field_int(slave_id, UVM_ALL_ON)
        `uvm_field_int(trans_type, UVM_ALL_ON)
        `uvm_field_int(M3_AWID, UVM_ALL_ON)
        `uvm_field_int(M3_AWADDR, UVM_ALL_ON)
        `uvm_field_int(M3_AWLEN, UVM_ALL_ON)
        `uvm_field_int(M3_AWSIZE, UVM_ALL_ON)
        `uvm_field_int(M3_AWBURST, UVM_ALL_ON)
        `uvm_field_int(M3_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(M3_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(M3_AWPROT, UVM_ALL_ON)
        `uvm_field_int(M3_AWQOS, UVM_ALL_ON)
        `uvm_field_int(M3_AWREGION, UVM_ALL_ON)
        `uvm_field_int(M3_AWVALID, UVM_ALL_ON)
        `uvm_field_int(M3_WDATA, UVM_ALL_ON)
        `uvm_field_int(M3_WSTRB, UVM_ALL_ON)
        `uvm_field_int(M3_WLAST, UVM_ALL_ON)
        `uvm_field_int(M3_WVALID, UVM_ALL_ON)
        `uvm_field_int(M3_ARID, UVM_ALL_ON)
        `uvm_field_int(M3_ARADDR, UVM_ALL_ON)
        `uvm_field_int(M3_ARLEN, UVM_ALL_ON)
        `uvm_field_int(M3_ARSIZE, UVM_ALL_ON)
        `uvm_field_int(M3_ARBURST, UVM_ALL_ON)
        `uvm_field_int(M3_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(M3_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(M3_ARPROT, UVM_ALL_ON)
        `uvm_field_int(M3_ARQOS, UVM_ALL_ON)
        `uvm_field_int(M3_ARREGION, UVM_ALL_ON)
        `uvm_field_int(M3_ARVALID, UVM_ALL_ON)
        `uvm_field_array_int(burst_data, UVM_ALL_ON)
        `uvm_field_array_int(burst_strobe, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : M3_seq_item

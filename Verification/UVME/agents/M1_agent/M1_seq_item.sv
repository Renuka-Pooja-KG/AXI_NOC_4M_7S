//=============================================================================
// M1 Agent Sequence Item Class
//=============================================================================
// Standalone sequence item for Master 1 with limited access to S1, S3, S4
// Extends uvm_sequence_item directly

import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the common AXI types package
import axi_common_types_pkg::*;

class M1_seq_item extends uvm_sequence_item;
    
    // M1-specific transaction identification
    rand int unsigned m1_transaction_id;  // Unique transaction ID for M1
    rand axi_slave_id_e slave_id;         // Target slave (1, 3, 4 only)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    rand bit [AXI_ID_WIDTH-1:0]     M1_AWID;           // Write address ID
    rand bit [AXI_ADDR_WIDTH-1:0]   M1_AWADDR;         // Write address
    rand bit [AXI_LEN_WIDTH-1:0]    M1_AWLEN;          // Burst length (0-15)
    rand bit [AXI_SIZE_WIDTH-1:0]   M1_AWSIZE;         // Burst size
    rand bit [AXI_BURST_WIDTH-1:0]  M1_AWBURST;        // Burst type
    rand bit [AXI_LOCK_WIDTH-1:0]   M1_AWLOCK;          // Lock type
    rand bit [AXI_CACHE_WIDTH-1:0]  M1_AWCACHE;        // Cache attributes
    rand bit [AXI_PROT_WIDTH-1:0]   M1_AWPROT;         // Protection attributes
    rand bit [AXI_QOS_WIDTH-1:0]    M1_AWQOS;          // Quality of service
    rand bit [AXI_REGION_WIDTH-1:0] M1_AWREGION;       // Region identifier
    rand bit                        M1_AWVALID;         // Write address valid
    bit                             M1_AWREADY;         // Write address ready (from slave)
    
    // ===== WRITE DATA CHANNEL (W) =====
    rand bit [AXI_DATA_WIDTH-1:0]   M1_WDATA;          // Write data
    rand bit [AXI_STRB_WIDTH-1:0]   M1_WSTRB;          // Write strobes
    rand bit                        M1_WLAST;          // Write last
    rand bit                        M1_WVALID;         // Write valid
    bit                             M1_WREADY;         // Write ready (from slave)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    bit [AXI_ID_WIDTH-1:0]          M1_BID;            // Write response ID (from slave)
    bit [AXI_RESP_WIDTH-1:0]        M1_BRESP;          // Write response (from slave)
    bit                             M1_BVALID;         // Write response valid (from slave)
    rand bit                        M1_BREADY;         // Write response ready
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    rand bit [AXI_ID_WIDTH-1:0]     M1_ARID;           // Read address ID
    rand bit [AXI_ADDR_WIDTH-1:0]   M1_ARADDR;         // Read address
    rand bit [AXI_LEN_WIDTH-1:0]    M1_ARLEN;          // Burst length (0-15)
    rand bit [AXI_SIZE_WIDTH-1:0]   M1_ARSIZE;         // Burst size
    rand bit [AXI_BURST_WIDTH-1:0]  M1_ARBURST;        // Burst type
    rand bit [AXI_LOCK_WIDTH-1:0]   M1_ARLOCK;          // Lock type
    rand bit [AXI_CACHE_WIDTH-1:0]  M1_ARCACHE;        // Cache attributes
    rand bit [AXI_PROT_WIDTH-1:0]   M1_ARPROT;         // Protection attributes
    rand bit [AXI_QOS_WIDTH-1:0]    M1_ARQOS;          // Quality of service
    rand bit [AXI_REGION_WIDTH-1:0] M1_ARREGION;       // Region identifier
    rand bit                        M1_ARVALID;         // Read address valid
    bit                             M1_ARREADY;         // Read address ready (from slave)
    
    // ===== READ DATA CHANNEL (R) =====
    bit [AXI_ID_WIDTH-1:0]          M1_RID;            // Read ID (from slave)
    bit [AXI_DATA_WIDTH-1:0]        M1_RDATA;          // Read data (from slave)
    bit [AXI_RESP_WIDTH-1:0]        M1_RRESP;          // Read response (from slave)
    bit                             M1_RLAST;          // Read last (from slave)
    bit                             M1_RVALID;         // Read valid (from slave)
    rand bit                        M1_RREADY;         // Read ready
    
    // ===== BURST DATA ARRAYS =====
    rand bit [AXI_DATA_WIDTH-1:0]   burst_data[];   // Array for burst data
    rand bit [AXI_STRB_WIDTH-1:0]   burst_strobe[]; // Array for burst strobes
    
    // Constraints
    constraint slave_id_c {
        slave_id inside {AXI_SLAVE_1, AXI_SLAVE_3, AXI_SLAVE_4};  // M1 can only access S1, S3, S4
    }
    
    constraint M1_awid_c {
        M1_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};  // Full ID range
    }
    
    constraint M1_arid_c {
        M1_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};  // Full ID range
    }
    
    constraint M1_awlen_c {
        M1_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};  // Burst length 1-16
    }
    
    constraint M1_arlen_c {
        M1_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};  // Burst length 1-16
    }
    
    constraint M1_awsize_c {
        M1_AWSIZE inside {[0:AXI_SIZE_WIDTH-1]};  // Transfer size 1, 2, 4, 8, 16, 32, 64, 128 bytes
    }
    
    constraint M1_arsize_c {
        M1_ARSIZE inside {[0:AXI_SIZE_WIDTH-1]};  // Transfer size 1, 2, 4, 8, 16, 32, 64, 128 bytes
    }
    
    constraint M1_awburst_c {
        M1_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};  // All burst types
    }
    
    constraint M1_arburst_c {
        M1_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};  // All burst types
    }
    
    constraint M1_awlock_c {
        M1_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};  // All lock types
    }
    
    constraint M1_arlock_c {
        M1_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};  // All lock types
    }
    
    constraint M1_awcache_c {
        M1_AWCACHE inside {[0:(1<<AXI_CACHE_WIDTH)-1]}; // All cache combinations
    }
    
    constraint M1_arcache_c {
        M1_ARCACHE inside {[0:(1<<AXI_CACHE_WIDTH)-1]}; // All cache combinations
    }
    
    constraint M1_awprot_c {
        M1_AWPROT inside {[0:(1<<AXI_PROT_WIDTH)-1]};  // All protection combinations
    }
    
    constraint M1_arprot_c {
        M1_ARPROT inside {[0:(1<<AXI_PROT_WIDTH)-1]};  // All protection combinations
    }
    
    constraint M1_awqos_c {
        M1_AWQOS inside {[0:(1<<AXI_QOS_WIDTH)-1]};  // All QoS levels
    }
    
    constraint M1_arqos_c {
        M1_ARQOS inside {[0:(1<<AXI_QOS_WIDTH)-1]};  // All QoS levels
    }
    
    constraint M1_awregion_c {
        M1_AWREGION inside {[0:(1<<AXI_REGION_WIDTH)-1]}; // All region identifiers
    }
    
    constraint M1_arregion_c {
        M1_ARREGION inside {[0:(1<<AXI_REGION_WIDTH)-1]}; // All region identifiers
    }
    
    // Address range constraints based on slave using package constants
    constraint address_range_c {
        if (slave_id == AXI_SLAVE_1) {
            if (trans_type == AXI_WRITE) {
                M1_AWADDR inside {[SLAVE_1_BASE_ADDR:SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M1_ARADDR inside {[SLAVE_1_BASE_ADDR:SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_3) {
            if (trans_type == AXI_WRITE) {
                M1_AWADDR inside {[SLAVE_3_BASE_ADDR:SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M1_ARADDR inside {[SLAVE_3_BASE_ADDR:SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_4) {
            if (trans_type == AXI_WRITE) {
                M1_AWADDR inside {[SLAVE_4_BASE_ADDR:SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M1_ARADDR inside {[SLAVE_4_BASE_ADDR:SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        }
    }
    
    // Address alignment constraints using package function
    constraint address_alignment_c {
        if (trans_type == AXI_WRITE) {
            M1_AWADDR % (1 << M1_AWSIZE) == 0;
        } else {
            M1_ARADDR % (1 << M1_ARSIZE) == 0;
        }
    }
    
    // Burst data array size constraint
    constraint burst_data_size_c {
        if (trans_type == AXI_WRITE) {
            burst_data.size() == get_burst_length(M1_AWLEN);
            burst_strobe.size() == get_burst_length(M1_AWLEN);
        } else {
            burst_data.size() == get_burst_length(M1_ARLEN);
        }
    }
    
    // Constructor
    function new(string name = "M1_seq_item");
        super.new(name);
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
    endfunction
    
    // UVM Field Macros for automatic copy, compare, print, etc.
    `uvm_object_utils_begin(M1_seq_item)
        `uvm_field_int(m1_transaction_id, UVM_ALL_ON)
        `uvm_field_enum(slave_id, UVM_ALL_ON)
        `uvm_field_enum(trans_type, UVM_ALL_ON)
        `uvm_field_int(M1_AWID, UVM_ALL_ON)
        `uvm_field_int(M1_AWADDR, UVM_ALL_ON)
        `uvm_field_int(M1_AWLEN, UVM_ALL_ON)
        `uvm_field_int(M1_AWSIZE, UVM_ALL_ON)
        `uvm_field_int(M1_AWBURST, UVM_ALL_ON)
        `uvm_field_int(M1_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(M1_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(M1_AWPROT, UVM_ALL_ON)
        `uvm_field_int(M1_AWQOS, UVM_ALL_ON)
        `uvm_field_int(M1_AWREGION, UVM_ALL_ON)
        `uvm_field_int(M1_AWVALID, UVM_ALL_ON)
        `uvm_field_int(M1_WDATA, UVM_ALL_ON)
        `uvm_field_int(M1_WSTRB, UVM_ALL_ON)
        `uvm_field_int(M1_WLAST, UVM_ALL_ON)
        `uvm_field_int(M1_WVALID, UVM_ALL_ON)
        `uvm_field_int(M1_ARID, UVM_ALL_ON)
        `uvm_field_int(M1_ARADDR, UVM_ALL_ON)
        `uvm_field_int(M1_ARLEN, UVM_ALL_ON)
        `uvm_field_int(M1_ARSIZE, UVM_ALL_ON)
        `uvm_field_int(M1_ARBURST, UVM_ALL_ON)
        `uvm_field_int(M1_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(M1_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(M1_ARPROT, UVM_ALL_ON)
        `uvm_field_int(M1_ARQOS, UVM_ALL_ON)
        `uvm_field_int(M1_ARREGION, UVM_ALL_ON)
        `uvm_field_int(M1_ARVALID, UVM_ALL_ON)
        `uvm_field_array_int(burst_data, UVM_ALL_ON)
        `uvm_field_array_int(burst_strobe, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : M1_seq_item

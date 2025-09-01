//=============================================================================
// M2 Agent Sequence Item Class
//=============================================================================
// Standalone sequence item for Master 2 with limited access to S1, S2, S4
// Extends uvm_sequence_item directly

import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the common AXI types package
import axi_common_types_pkg::*;

class M2_seq_item extends uvm_sequence_item;
    
    // M2-specific transaction identification
    rand int unsigned m2_transaction_id;  // Unique transaction ID for M2
    rand axi_slave_id_e slave_id;         // Target slave (1, 2, 4 only)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    rand bit [AXI_ID_WIDTH-1:0]     M2_AWID;           // Write address ID
    rand bit [AXI_ADDR_WIDTH-1:0]   M2_AWADDR;         // Write address
    rand bit [AXI_LEN_WIDTH-1:0]    M2_AWLEN;          // Burst length (0-15)
    rand bit [AXI_SIZE_WIDTH-1:0]   M2_AWSIZE;         // Burst size
    rand bit [AXI_BURST_WIDTH-1:0]  M2_AWBURST;        // Burst type
    rand bit [AXI_LOCK_WIDTH-1:0]   M2_AWLOCK;          // Lock type
    rand bit [AXI_CACHE_WIDTH-1:0]  M2_AWCACHE;        // Cache attributes
    rand bit [AXI_PROT_WIDTH-1:0]   M2_AWPROT;         // Protection attributes
    rand bit [AXI_QOS_WIDTH-1:0]    M2_AWQOS;          // Quality of service
    rand bit [AXI_REGION_WIDTH-1:0] M2_AWREGION;       // Region identifier
    rand bit                        M2_AWVALID;         // Write address valid
    bit                             M2_AWREADY;         // Write address ready (from slave)
    
    // ===== WRITE DATA CHANNEL (W) =====
    rand bit [AXI_DATA_WIDTH-1:0]   M2_WDATA;          // Write data
    rand bit [AXI_STRB_WIDTH-1:0]   M2_WSTRB;          // Write strobes
    rand bit                        M2_WLAST;          // Write last
    rand bit                        M2_WVALID;         // Write valid
    bit                             M2_WREADY;         // Write ready (from slave)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    bit [AXI_ID_WIDTH-1:0]          M2_BID;            // Write response ID (from slave)
    bit [AXI_RESP_WIDTH-1:0]        M2_BRESP;          // Write response (from slave)
    bit                             M2_BVALID;         // Write response valid (from slave)
    rand bit                        M2_BREADY;         // Write response ready
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    rand bit [AXI_ID_WIDTH-1:0]     M2_ARID;           // Read address ID
    rand bit [AXI_ADDR_WIDTH-1:0]   M2_ARADDR;         // Read address
    rand bit [AXI_LEN_WIDTH-1:0]    M2_ARLEN;          // Burst length (0-15)
    rand bit [AXI_SIZE_WIDTH-1:0]   M2_ARSIZE;         // Burst size
    rand bit [AXI_BURST_WIDTH-1:0]  M2_ARBURST;        // Burst type
    rand bit [AXI_LOCK_WIDTH-1:0]   M2_ARLOCK;          // Lock type
    rand bit [AXI_CACHE_WIDTH-1:0]  M2_ARCACHE;        // Cache attributes
    rand bit [AXI_PROT_WIDTH-1:0]   M2_ARPROT;         // Protection attributes
    rand bit [AXI_QOS_WIDTH-1:0]    M2_ARQOS;          // Quality of service
    rand bit [AXI_REGION_WIDTH-1:0] M2_ARREGION;       // Region identifier
    rand bit                        M2_ARVALID;         // Read address valid
    bit                             M2_ARREADY;         // Read address ready (from slave)
    
    // ===== READ DATA CHANNEL (R) =====
    bit [AXI_ID_WIDTH-1:0]          M2_RID;            // Read ID (from slave)
    bit [AXI_DATA_WIDTH-1:0]        M2_RDATA;          // Read data (from slave)
    bit [AXI_RESP_WIDTH-1:0]        M2_RRESP;          // Read response (from slave)
    bit                             M2_RLAST;          // Read last (from slave)
    bit                             M2_RVALID;         // Read valid (from slave)
    rand bit                        M2_RREADY;         // Read ready
    
    // ===== BURST DATA ARRAYS =====
    rand bit [AXI_DATA_WIDTH-1:0]   burst_data[];   // Array for burst data
    rand bit [AXI_STRB_WIDTH-1:0]   burst_strobe[]; // Array for burst strobes
    
    // Constraints
    constraint slave_id_c {
        slave_id inside {AXI_SLAVE_1, AXI_SLAVE_2, AXI_SLAVE_4};  // M2 can only access S1, S2, S4
    }
    
    constraint M2_awid_c {
        M2_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};  // Full ID range
    }
    
    constraint M2_arid_c {
        M2_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};  // Full ID range
    }
    
    constraint M2_awlen_c {
        M2_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};  // Burst length 1-16
    }
    
    constraint M2_arlen_c {
        M2_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};  // Burst length 1-16
    }
    
    constraint M2_awsize_c {
        M2_AWSIZE inside {[0:AXI_SIZE_WIDTH-1]};  // Transfer size 1, 2, 4, 8, 16, 32, 64, 128 bytes
    }
    
    constraint M2_arsize_c {
        M2_ARSIZE inside {[0:AXI_SIZE_WIDTH-1]};  // Transfer size 1, 2, 4, 8, 16, 32, 64, 128 bytes
    }
    
    constraint M2_awburst_c {
        M2_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};  // All burst types
    }
    
    constraint M2_arburst_c {
        M2_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};  // All burst types
    }
    
    constraint M2_awlock_c {
        M2_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};  // All lock types
    }
    
    constraint M2_arlock_c {
        M2_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};  // All lock types
    }
    
    constraint M2_awcache_c {
        M2_AWCACHE inside {[0:(1<<AXI_CACHE_WIDTH)-1]}; // All cache combinations
    }
    
    constraint M2_arcache_c {
        M2_ARCACHE inside {[0:(1<<AXI_CACHE_WIDTH)-1]}; // All cache combinations
    }
    
    constraint M2_awprot_c {
        M2_AWPROT inside {[0:(1<<AXI_PROT_WIDTH)-1]};  // All protection combinations
    }
    
    constraint M2_arprot_c {
        M2_ARPROT inside {[0:(1<<AXI_PROT_WIDTH)-1]};  // All protection combinations
    }
    
    constraint M2_awqos_c {
        M2_AWQOS inside {[0:(1<<AXI_QOS_WIDTH)-1]};  // All QoS levels
    }
    
    constraint M2_arqos_c {
        M2_ARQOS inside {[0:(1<<AXI_QOS_WIDTH)-1]};  // All QoS levels
    }
    
    constraint M2_awregion_c {
        M2_AWREGION inside {[0:(1<<AXI_REGION_WIDTH)-1]}; // All region identifiers
    }
    
    constraint M2_arregion_c {
        M2_ARREGION inside {[0:(1<<AXI_REGION_WIDTH)-1]}; // All region identifiers
    }
    
    // Address range constraints based on slave using package constants
    constraint address_range_c {
        if (slave_id == AXI_SLAVE_1) {
            if (trans_type == AXI_WRITE) {
                M2_AWADDR inside {[SLAVE_1_BASE_ADDR:SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M2_ARADDR inside {[SLAVE_1_BASE_ADDR:SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_2) {
            if (trans_type == AXI_WRITE) {
                M2_AWADDR inside {[SLAVE_2_BASE_ADDR:SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M2_ARADDR inside {[SLAVE_2_BASE_ADDR:SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_4) {
            if (trans_type == AXI_WRITE) {
                M2_AWADDR inside {[SLAVE_4_BASE_ADDR:SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M2_ARADDR inside {[SLAVE_4_BASE_ADDR:SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        }
    }
    
    // Address alignment constraints using package function
    constraint address_alignment_c {
        if (trans_type == AXI_WRITE) {
            M2_AWADDR % (1 << M2_AWSIZE) == 0;
        } else {
            M2_ARADDR % (1 << M2_ARSIZE) == 0;
        }
    }
    
    // Burst data array size constraint
    constraint burst_data_size_c {
        if (trans_type == AXI_WRITE) {
            burst_data.size() == get_burst_length(M2_AWLEN);
            burst_strobe.size() == get_burst_length(M2_AWLEN);
        } else {
            burst_data.size() == get_burst_length(M2_ARLEN);
        }
    }
    
    // Constructor
    function new(string name = "M2_seq_item");
        super.new(name);
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
    endfunction
    
    // UVM Field Macros for automatic copy, compare, print, etc.
    `uvm_object_utils_begin(M2_seq_item)
        `uvm_field_int(m2_transaction_id, UVM_ALL_ON)
        `uvm_field_int(slave_id, UVM_ALL_ON)
        `uvm_field_int(trans_type, UVM_ALL_ON)
        `uvm_field_int(M2_AWID, UVM_ALL_ON)
        `uvm_field_int(M2_AWADDR, UVM_ALL_ON)
        `uvm_field_int(M2_AWLEN, UVM_ALL_ON)
        `uvm_field_int(M2_AWSIZE, UVM_ALL_ON)
        `uvm_field_int(M2_AWBURST, UVM_ALL_ON)
        `uvm_field_int(M2_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(M2_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(M2_AWPROT, UVM_ALL_ON)
        `uvm_field_int(M2_AWQOS, UVM_ALL_ON)
        `uvm_field_int(M2_AWREGION, UVM_ALL_ON)
        `uvm_field_int(M2_AWVALID, UVM_ALL_ON)
        `uvm_field_int(M2_WDATA, UVM_ALL_ON)
        `uvm_field_int(M2_WSTRB, UVM_ALL_ON)
        `uvm_field_int(M2_WLAST, UVM_ALL_ON)
        `uvm_field_int(M2_WVALID, UVM_ALL_ON)
        `uvm_field_int(M2_ARID, UVM_ALL_ON)
        `uvm_field_int(M2_ARADDR, UVM_ALL_ON)
        `uvm_field_int(M2_ARLEN, UVM_ALL_ON)
        `uvm_field_int(M2_ARSIZE, UVM_ALL_ON)
        `uvm_field_int(M2_ARBURST, UVM_ALL_ON)
        `uvm_field_int(M2_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(M2_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(M2_ARPROT, UVM_ALL_ON)
        `uvm_field_int(M2_ARQOS, UVM_ALL_ON)
        `uvm_field_int(M2_ARREGION, UVM_ALL_ON)
        `uvm_field_int(M2_ARVALID, UVM_ALL_ON)
        `uvm_field_array_int(burst_data, UVM_ALL_ON)
        `uvm_field_array_int(burst_strobe, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : M2_seq_item

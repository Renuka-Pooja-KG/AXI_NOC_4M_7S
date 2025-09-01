//=============================================================================
// M0 Agent Sequence Item Class
//=============================================================================
// Standalone sequence item for Master 0 with full access to all slaves
// Extends uvm_sequence_item directly

import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the common AXI types package
import axi_common_types_pkg::*;

class M0_seq_item extends uvm_sequence_item;
    
    // M0-specific transaction identification
    rand int unsigned m0_transaction_id;  // Unique transaction ID for M0
    rand axi_slave_id_e slave_id;         // Target slave (0-6)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    rand bit [AXI_ID_WIDTH-1:0]     M0_AWID;           // Write address ID
    rand bit [AXI_ADDR_WIDTH-1:0]   M0_AWADDR;         // Write address
    rand bit [AXI_LEN_WIDTH-1:0]    M0_AWLEN;          // Burst length (0-15)
    rand bit [AXI_SIZE_WIDTH-1:0]   M0_AWSIZE;         // Burst size
    rand bit [AXI_BURST_WIDTH-1:0]  M0_AWBURST;        // Burst type
    rand bit [AXI_LOCK_WIDTH-1:0]   M0_AWLOCK;          // Lock type
    rand bit [AXI_CACHE_WIDTH-1:0]  M0_AWCACHE;        // Cache attributes
    rand bit [AXI_PROT_WIDTH-1:0]   M0_AWPROT;         // Protection attributes
    rand bit [AXI_QOS_WIDTH-1:0]    M0_AWQOS;          // Quality of service
    rand bit [AXI_REGION_WIDTH-1:0] M0_AWREGION;       // Region identifier
    rand bit                        M0_AWVALID;         // Write address valid
    bit                             M0_AWREADY;         // Write address ready (from slave)
    
    // ===== WRITE DATA CHANNEL (W) =====
    rand bit [AXI_DATA_WIDTH-1:0]   M0_WDATA;          // Write data
    rand bit [AXI_STRB_WIDTH-1:0]   M0_WSTRB;          // Write strobes
    rand bit                        M0_WLAST;          // Write last
    rand bit                        M0_WVALID;         // Write valid
    bit                             M0_WREADY;         // Write ready (from slave)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    bit [AXI_ID_WIDTH-1:0]          M0_BID;            // Write response ID (from slave)
    bit [AXI_RESP_WIDTH-1:0]        M0_BRESP;          // Write response (from slave)
    bit                             M0_BVALID;         // Write response valid (from slave)
    rand bit                        M0_BREADY;         // Write response ready
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    rand bit [AXI_ID_WIDTH-1:0]     M0_ARID;           // Read address ID
    rand bit [AXI_ADDR_WIDTH-1:0]   M0_ARADDR;         // Read address
    rand bit [AXI_LEN_WIDTH-1:0]    M0_ARLEN;          // Burst length (0-15)
    rand bit [AXI_SIZE_WIDTH-1:0]   M0_ARSIZE;         // Burst size
    rand bit [AXI_BURST_WIDTH-1:0]  M0_ARBURST;        // Burst type
    rand bit [AXI_LOCK_WIDTH-1:0]   M0_ARLOCK;          // Lock type
    rand bit [AXI_CACHE_WIDTH-1:0]  M0_ARCACHE;        // Cache attributes
    rand bit [AXI_PROT_WIDTH-1:0]   M0_ARPROT;         // Protection attributes
    rand bit [AXI_QOS_WIDTH-1:0]    M0_ARQOS;          // Quality of service
    rand bit [AXI_REGION_WIDTH-1:0] M0_ARREGION;       // Region identifier
    rand bit                        M0_ARVALID;         // Read address valid
    bit                             M0_ARREADY;         // Read address ready (from slave)
    
    // ===== READ DATA CHANNEL (R) =====
    bit [AXI_ID_WIDTH-1:0]          M0_RID;            // Read ID (from slave)
    bit [AXI_DATA_WIDTH-1:0]        M0_RDATA;          // Read data (from slave)
    bit [AXI_RESP_WIDTH-1:0]        M0_RRESP;          // Read response (from slave)
    bit                             M0_RLAST;          // Read last (from slave)
    bit                             M0_RVALID;         // Read valid (from slave)
    rand bit                        M0_RREADY;         // Read ready
    
    // ===== BURST DATA ARRAYS =====
    rand bit [AXI_DATA_WIDTH-1:0]   burst_data[];   // Array for burst data
    rand bit [AXI_STRB_WIDTH-1:0]   burst_strobe[]; // Array for burst strobes
    
    // Constraints
    constraint slave_id_c {
        slave_id inside {AXI_SLAVE_0, AXI_SLAVE_1, AXI_SLAVE_2, AXI_SLAVE_3, 
                        AXI_SLAVE_4, AXI_SLAVE_5, AXI_SLAVE_6};  // M0 can access all slaves
    }
    
    constraint M0_awid_c {
        M0_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};  // Full ID range
    }
    
    constraint M0_arid_c {
        M0_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};  // Full ID range
    }
    
    constraint M0_awlen_c {
        M0_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};  // Burst length 1-16
    }
    
    constraint M0_arlen_c {
        M0_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};  // Burst length 1-16
    }
    
    constraint M0_awsize_c {
        M0_AWSIZE inside {[0:AXI_SIZE_WIDTH-1]};  // Transfer size 1, 2, 4, 8, 16, 32, 64, 128 bytes
    }
    
    constraint M0_arsize_c {
        M0_ARSIZE inside {[0:AXI_SIZE_WIDTH-1]};  // Transfer size 1, 2, 4, 8, 16, 32, 64, 128 bytes
    }
    
    constraint M0_awburst_c {
        M0_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};  // All burst types
    }
    
    constraint M0_arburst_c {
        M0_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};  // All burst types
    }
    
    constraint M0_awlock_c {
        M0_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};  // All lock types
    }
    
    constraint M0_arlock_c {
        M0_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};  // All lock types
    }
    
    constraint M0_awcache_c {
        M0_AWCACHE inside {[0:(1<<AXI_CACHE_WIDTH)-1]}; // All cache combinations
    }
    
    constraint M0_arcache_c {
        M0_ARCACHE inside {[0:(1<<AXI_CACHE_WIDTH)-1]}; // All cache combinations
    }
    
    constraint M0_awprot_c {
        M0_AWPROT inside {[0:(1<<AXI_PROT_WIDTH)-1]};  // All protection combinations
    }
    
    constraint M0_arprot_c {
        M0_ARPROT inside {[0:(1<<AXI_PROT_WIDTH)-1]};  // All protection combinations
    }
    
    constraint M0_awqos_c {
        M0_AWQOS inside {[0:(1<<AXI_QOS_WIDTH)-1]};  // All QoS levels
    }
    
    constraint M0_arqos_c {
        M0_ARQOS inside {[0:(1<<AXI_QOS_WIDTH)-1]};  // All QoS levels
    }
    
    constraint M0_awregion_c {
        M0_AWREGION inside {[0:(1<<AXI_REGION_WIDTH)-1]}; // All region identifiers
    }
    
    constraint M0_arregion_c {
        M0_ARREGION inside {[0:(1<<AXI_REGION_WIDTH)-1]}; // All region identifiers
    }
    
    // Address range constraints based on slave using package constants
    constraint address_range_c {
        if (slave_id == AXI_SLAVE_0) {
            if (trans_type == AXI_WRITE) {
                M0_AWADDR inside {[SLAVE_0_BASE_ADDR:SLAVE_0_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M0_ARADDR inside {[SLAVE_0_BASE_ADDR:SLAVE_0_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_1) {
            if (trans_type == AXI_WRITE) {
                M0_AWADDR inside {[SLAVE_1_BASE_ADDR:SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M0_ARADDR inside {[SLAVE_1_BASE_ADDR:SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_2) {
            if (trans_type == AXI_WRITE) {
                M0_AWADDR inside {[SLAVE_2_BASE_ADDR:SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M0_ARADDR inside {[SLAVE_2_BASE_ADDR:SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_3) {
            if (trans_type == AXI_WRITE) {
                M0_AWADDR inside {[SLAVE_3_BASE_ADDR:SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M0_ARADDR inside {[SLAVE_3_BASE_ADDR:SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_4) {
            if (trans_type == AXI_WRITE) {
                M0_AWADDR inside {[SLAVE_4_BASE_ADDR:SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M0_ARADDR inside {[SLAVE_4_BASE_ADDR:SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_5) {
            if (trans_type == AXI_WRITE) {
                M0_AWADDR inside {[SLAVE_5_BASE_ADDR:SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M0_ARADDR inside {[SLAVE_5_BASE_ADDR:SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_6) {
            if (trans_type == AXI_WRITE) {
                M0_AWADDR inside {[SLAVE_6_BASE_ADDR:SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M0_ARADDR inside {[SLAVE_6_BASE_ADDR:SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        }
    }
    
    // Address alignment constraints using package function
    constraint address_alignment_c {
        if (trans_type == AXI_WRITE) {
            M0_AWADDR % (1 << M0_AWSIZE) == 0;
        } else {
            M0_ARADDR % (1 << M0_ARSIZE) == 0;
        }
    }
    
    // Burst data array size constraint
    constraint burst_data_size_c {
        if (trans_type == AXI_WRITE) {
            burst_data.size() == get_burst_length(M0_AWLEN);
            burst_strobe.size() == get_burst_length(M0_AWLEN);
        } else {
            burst_data.size() == get_burst_length(M0_ARLEN);
        }
    }
    
    // Constructor
    function new(string name = "M0_seq_item");
        super.new(name);
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
    endfunction
    
    // UVM Field Macros for automatic copy, compare, print, etc.
    `uvm_object_utils_begin(M0_seq_item)
        `uvm_field_int(m0_transaction_id, UVM_ALL_ON)
        `uvm_field_int(slave_id, UVM_ALL_ON)
        `uvm_field_int(trans_type, UVM_ALL_ON)
        `uvm_field_int(M0_AWID, UVM_ALL_ON)
        `uvm_field_int(M0_AWADDR, UVM_ALL_ON)
        `uvm_field_int(M0_AWLEN, UVM_ALL_ON)
        `uvm_field_int(M0_AWSIZE, UVM_ALL_ON)
        `uvm_field_int(M0_AWBURST, UVM_ALL_ON)
        `uvm_field_int(M0_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(M0_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(M0_AWPROT, UVM_ALL_ON)
        `uvm_field_int(M0_AWQOS, UVM_ALL_ON)
        `uvm_field_int(M0_AWREGION, UVM_ALL_ON)
        `uvm_field_int(M0_AWVALID, UVM_ALL_ON)
        `uvm_field_int(M0_WDATA, UVM_ALL_ON)
        `uvm_field_int(M0_WSTRB, UVM_ALL_ON)
        `uvm_field_int(M0_WLAST, UVM_ALL_ON)
        `uvm_field_int(M0_WVALID, UVM_ALL_ON)
        `uvm_field_int(M0_ARID, UVM_ALL_ON)
        `uvm_field_int(M0_ARADDR, UVM_ALL_ON)
        `uvm_field_int(M0_ARLEN, UVM_ALL_ON)
        `uvm_field_int(M0_ARSIZE, UVM_ALL_ON)
        `uvm_field_int(M0_ARBURST, UVM_ALL_ON)
        `uvm_field_int(M0_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(M0_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(M0_ARPROT, UVM_ALL_ON)
        `uvm_field_int(M0_ARQOS, UVM_ALL_ON)
        `uvm_field_int(M0_ARREGION, UVM_ALL_ON)
        `uvm_field_int(M0_ARVALID, UVM_ALL_ON)
        `uvm_field_array_int(burst_data, UVM_ALL_ON)
        `uvm_field_array_int(burst_strobe, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : M0_seq_item

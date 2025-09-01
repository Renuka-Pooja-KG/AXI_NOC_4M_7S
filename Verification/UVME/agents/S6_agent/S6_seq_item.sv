//=============================================================================
// S6 Agent Sequence Item Class
//=============================================================================
// Simple sequence item for Slave 6 with AXI slave interface

import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the common AXI types package
import axi_common_types_pkg::*;

class S6_seq_item extends uvm_sequence_item;
    
    // S6-specific transaction identification
    rand int unsigned s6_transaction_id;  // Unique transaction ID for S6
    rand axi_master_id_e master_id;       // Source master (0-3)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S6 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S6_AWID;           // Write address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S6_AWADDR;         // Write address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S6_AWLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S6_AWLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S6_AWSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S6_AWBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S6_AWCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S6_AWPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S6_AWQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S6_AWREGION;       // Region identifier (from master)
    bit                        S6_AWVALID;        // Write address valid (from master)
    rand bit                   S6_AWREADY;        // Write address ready (S6 drives this)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S6 receives these signals from masters
    bit [AXI_DATA_WIDTH-1:0]   S6_WDATA;          // Write data (from master)
    bit [AXI_STRB_WIDTH-1:0]   S6_WSTRB;          // Write strobes (from master)
    bit                        S6_WLAST;          // Write last (from master)
    bit                        S6_WVALID;         // Write valid (from master)
    rand bit                   S6_WREADY;         // Write ready (S6 drives this)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S6 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S6_BID;           // Write response ID (S6 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S6_BRESP;       // Write response (S6 drives this)
    rand bit                    S6_BVALID;         // Write response valid (S6 drives this)
    bit                         S6_BREADY;         // Write response ready (from master)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S6 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S6_ARID;           // Read address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S6_ARADDR;         // Read address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S6_ARLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S6_ARLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S6_ARSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S6_ARBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S6_ARCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S6_ARPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S6_ARQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S6_ARREGION;       // Region identifier (from master)
    bit                        S6_ARVALID;        // Read address valid (from master)
    rand bit                   S6_ARREADY;        // Read address ready (S6 drives this)
    
    // ===== READ DATA CHANNEL (R) =====
    // S6 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S6_RID;           // Read ID (S6 drives this)
    rand bit [AXI_DATA_WIDTH-1:0] S6_RDATA;       // Read data (S6 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S6_RRESP;       // Read response (S6 drives this)
    rand bit                    S6_RLAST;          // Read last (S6 drives this)
    rand bit                    S6_RVALID;         // Read valid (S6 drives this)
    bit                         S6_RREADY;         // Read ready (from master)
    
    // ===== BURST DATA ARRAYS =====
    rand bit [AXI_DATA_WIDTH-1:0]   burst_data[];   // Array for burst data
    rand bit [AXI_STRB_WIDTH-1:0]   burst_strobe[]; // Array for burst strobes
    
    // Constraints
    constraint master_id_c {
        master_id inside {AXI_MASTER_0, AXI_MASTER_1, AXI_MASTER_2, AXI_MASTER_3};
    }
    
    constraint s6_awid_c {
        S6_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s6_arid_c {
        S6_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s6_awlen_c {
        S6_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s6_arlen_c {
        S6_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s6_awsize_c {
        S6_AWSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s6_arsize_c {
        S6_ARSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s6_awburst_c {
        S6_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s6_arburst_c {
        S6_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s6_awlock_c {
        S6_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s6_arlock_c {
        S6_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s6_awcache_c {
        S6_AWCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s6_arcache_c {
        S6_ARCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s6_awprot_c {
        S6_AWPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s6_arprot_c {
        S6_ARPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s6_awqos_c {
        S6_AWQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s6_arqos_c {
        S6_ARQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s6_awregion_c {
        S6_AWREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s6_arregion_c {
        S6_ARREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s6_bresp_c {
        S6_BRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint s6_rresp_c {
        S6_RRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint burst_data_c {
        burst_data.size() == (S6_AWLEN + 1);
        burst_strobe.size() == (S6_AWLEN + 1);
    }
    
    // Constructor
    function new(string name = "S6_seq_item");
        super.new(name);
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
    endfunction
    
    // UVM field macros for automation
    `uvm_object_utils_begin(S6_seq_item)
        `uvm_field_int(s6_transaction_id, UVM_ALL_ON)
        `uvm_field_int(master_id, UVM_ALL_ON)
        `uvm_field_int(trans_type, UVM_ALL_ON)
        
        // Write Address Channel
        `uvm_field_int(S6_AWID, UVM_ALL_ON)
        `uvm_field_int(S6_AWADDR, UVM_ALL_ON)
        `uvm_field_int(S6_AWLEN, UVM_ALL_ON)
        `uvm_field_int(S6_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(S6_AWSIZE, UVM_ALL_ON)
        `uvm_field_int(S6_AWBURST, UVM_ALL_ON)
        `uvm_field_int(S6_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(S6_AWPROT, UVM_ALL_ON)
        `uvm_field_int(S6_AWQOS, UVM_ALL_ON)
        `uvm_field_int(S6_AWREGION, UVM_ALL_ON)
        `uvm_field_int(S6_AWVALID, UVM_ALL_ON)
        `uvm_field_int(S6_AWREADY, UVM_ALL_ON)
        
        // Write Data Channel
        `uvm_field_int(S6_WDATA, UVM_ALL_ON)
        `uvm_field_int(S6_WSTRB, UVM_ALL_ON)
        `uvm_field_int(S6_WLAST, UVM_ALL_ON)
        `uvm_field_int(S6_WVALID, UVM_ALL_ON)
        `uvm_field_int(S6_WREADY, UVM_ALL_ON)
        
        // Write Response Channel
        `uvm_field_int(S6_BID, UVM_ALL_ON)
        `uvm_field_int(S6_BRESP, UVM_ALL_ON)
        `uvm_field_int(S6_BVALID, UVM_ALL_ON)
        `uvm_field_int(S6_BREADY, UVM_ALL_ON)
        
        // Read Address Channel
        `uvm_field_int(S6_ARID, UVM_ALL_ON)
        `uvm_field_int(S6_ARADDR, UVM_ALL_ON)
        `uvm_field_int(S6_ARLEN, UVM_ALL_ON)
        `uvm_field_int(S6_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(S6_ARSIZE, UVM_ALL_ON)
        `uvm_field_int(S6_ARBURST, UVM_ALL_ON)
        `uvm_field_int(S6_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(S6_ARPROT, UVM_ALL_ON)
        `uvm_field_int(S6_ARQOS, UVM_ALL_ON)
        `uvm_field_int(S6_ARREGION, UVM_ALL_ON)
        `uvm_field_int(S6_ARVALID, UVM_ALL_ON)
        `uvm_field_int(S6_ARREADY, UVM_ALL_ON)
        
        // Read Data Channel
        `uvm_field_int(S6_RID, UVM_ALL_ON)
        `uvm_field_int(S6_RDATA, UVM_ALL_ON)
        `uvm_field_int(S6_RRESP, UVM_ALL_ON)
        `uvm_field_int(S6_RLAST, UVM_ALL_ON)
        `uvm_field_int(S6_RVALID, UVM_ALL_ON)
        `uvm_field_int(S6_RREADY, UVM_ALL_ON)
        
        // Arrays
        `uvm_field_array_int(burst_data, UVM_ALL_ON)
        `uvm_field_array_int(burst_strobe, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : S6_seq_item
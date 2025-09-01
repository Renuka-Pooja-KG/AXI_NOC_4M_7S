//=============================================================================
// S0 Agent Sequence Item Class
//=============================================================================
// Simple sequence item for Slave 0 with AXI slave interface

import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the common AXI types package
import axi_common_types_pkg::*;

class S0_seq_item extends uvm_sequence_item;
    
    // S0-specific transaction identification
    rand int unsigned s0_transaction_id;  // Unique transaction ID for S0
    rand axi_master_id_e master_id;       // Source master (0-3)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S0 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S0_AWID;           // Write address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S0_AWADDR;         // Write address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S0_AWLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S0_AWLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S0_AWSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S0_AWBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S0_AWCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S0_AWPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S0_AWQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S0_AWREGION;       // Region identifier (from master)
    bit                        S0_AWVALID;        // Write address valid (from master)
    rand bit                   S0_AWREADY;        // Write address ready (S0 drives this)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S0 receives these signals from masters
    bit [AXI_DATA_WIDTH-1:0]   S0_WDATA;          // Write data (from master)
    bit [AXI_STRB_WIDTH-1:0]   S0_WSTRB;          // Write strobes (from master)
    bit                        S0_WLAST;          // Write last (from master)
    bit                        S0_WVALID;         // Write valid (from master)
    rand bit                   S0_WREADY;         // Write ready (S0 drives this)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S0 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S0_BID;           // Write response ID (S0 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S0_BRESP;       // Write response (S0 drives this)
    rand bit                    S0_BVALID;         // Write response valid (S0 drives this)
    bit                         S0_BREADY;         // Write response ready (from master)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S0 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S0_ARID;           // Read address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S0_ARADDR;         // Read address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S0_ARLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S0_ARLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S0_ARSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S0_ARBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S0_ARCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S0_ARPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S0_ARQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S0_ARREGION;       // Region identifier (from master)
    bit                        S0_ARVALID;        // Read address valid (from master)
    rand bit                   S0_ARREADY;        // Read address ready (S0 drives this)
    
    // ===== READ DATA CHANNEL (R) =====
    // S0 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S0_RID;           // Read ID (S0 drives this)
    rand bit [AXI_DATA_WIDTH-1:0] S0_RDATA;       // Read data (S0 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S0_RRESP;       // Read response (S0 drives this)
    rand bit                    S0_RLAST;          // Read last (S0 drives this)
    rand bit                    S0_RVALID;         // Read valid (S0 drives this)
    bit                         S0_RREADY;         // Read ready (from master)
    
    // ===== BURST DATA ARRAYS =====
    rand bit [AXI_DATA_WIDTH-1:0]   burst_data[];   // Array for burst data
    rand bit [AXI_STRB_WIDTH-1:0]   burst_strobe[]; // Array for burst strobes
    
    // Constraints
    constraint master_id_c {
        master_id inside {AXI_MASTER_0, AXI_MASTER_1, AXI_MASTER_2, AXI_MASTER_3};
    }
    
    constraint s0_awid_c {
        S0_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s0_arid_c {
        S0_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s0_awlen_c {
        S0_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s0_arlen_c {
        S0_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s0_awsize_c {
        S0_AWSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s0_arsize_c {
        S0_ARSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s0_awburst_c {
        S0_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s0_arburst_c {
        S0_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s0_awlock_c {
        S0_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s0_arlock_c {
        S0_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s0_awcache_c {
        S0_AWCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s0_arcache_c {
        S0_ARCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s0_awprot_c {
        S0_AWPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s0_arprot_c {
        S0_ARPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s0_awqos_c {
        S0_AWQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s0_arqos_c {
        S0_ARQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s0_awregion_c {
        S0_AWREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s0_arregion_c {
        S0_ARREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s0_bresp_c {
        S0_BRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint s0_rresp_c {
        S0_RRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint burst_data_c {
        burst_data.size() == (S0_AWLEN + 1);
        burst_strobe.size() == (S0_AWLEN + 1);
    }
    
    // Constructor
    function new(string name = "S0_seq_item");
        super.new(name);
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
    endfunction
    
    // Custom string conversion function for enum fields
    function string convert2string();
        string result;
        result = $sformatf("S0_seq_item: trans_type=%s, master_id=%s, AWID=%0d, AWADDR=0x%0h", 
                          trans_type.name(), master_id.name(), S0_AWID, S0_AWADDR);
        return result;
    endfunction
    
    // UVM field macros for automation
    `uvm_object_utils_begin(S0_seq_item)
        `uvm_field_int(s0_transaction_id, UVM_ALL_ON)

        
        // Write Address Channel
        `uvm_field_int(S0_AWID, UVM_ALL_ON)
        `uvm_field_int(S0_AWADDR, UVM_ALL_ON)
        `uvm_field_int(S0_AWLEN, UVM_ALL_ON)
        `uvm_field_int(S0_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(S0_AWSIZE, UVM_ALL_ON)
        `uvm_field_int(S0_AWBURST, UVM_ALL_ON)
        `uvm_field_int(S0_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(S0_AWPROT, UVM_ALL_ON)
        `uvm_field_int(S0_AWQOS, UVM_ALL_ON)
        `uvm_field_int(S0_AWREGION, UVM_ALL_ON)
        `uvm_field_int(S0_AWVALID, UVM_ALL_ON)
        `uvm_field_int(S0_AWREADY, UVM_ALL_ON)
        
        // Write Data Channel
        `uvm_field_int(S0_WDATA, UVM_ALL_ON)
        `uvm_field_int(S0_WSTRB, UVM_ALL_ON)
        `uvm_field_int(S0_WLAST, UVM_ALL_ON)
        `uvm_field_int(S0_WVALID, UVM_ALL_ON)
        `uvm_field_int(S0_WREADY, UVM_ALL_ON)
        
        // Write Response Channel
        `uvm_field_int(S0_BID, UVM_ALL_ON)
        `uvm_field_int(S0_BRESP, UVM_ALL_ON)
        `uvm_field_int(S0_BVALID, UVM_ALL_ON)
        `uvm_field_int(S0_BREADY, UVM_ALL_ON)
        
        // Read Address Channel
        `uvm_field_int(S0_ARID, UVM_ALL_ON)
        `uvm_field_int(S0_ARADDR, UVM_ALL_ON)
        `uvm_field_int(S0_ARLEN, UVM_ALL_ON)
        `uvm_field_int(S0_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(S0_ARSIZE, UVM_ALL_ON)
        `uvm_field_int(S0_ARBURST, UVM_ALL_ON)
        `uvm_field_int(S0_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(S0_ARPROT, UVM_ALL_ON)
        `uvm_field_int(S0_ARQOS, UVM_ALL_ON)
        `uvm_field_int(S0_ARREGION, UVM_ALL_ON)
        `uvm_field_int(S0_ARVALID, UVM_ALL_ON)
        `uvm_field_int(S0_ARREADY, UVM_ALL_ON)
        
        // Read Data Channel
        `uvm_field_int(S0_RID, UVM_ALL_ON)
        `uvm_field_int(S0_RDATA, UVM_ALL_ON)
        `uvm_field_int(S0_RRESP, UVM_ALL_ON)
        `uvm_field_int(S0_RLAST, UVM_ALL_ON)
        `uvm_field_int(S0_RVALID, UVM_ALL_ON)
        `uvm_field_int(S0_RREADY, UVM_ALL_ON)
        
        // Arrays
        `uvm_field_array_int(burst_data, UVM_ALL_ON)
        `uvm_field_array_int(burst_strobe, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : S0_seq_item
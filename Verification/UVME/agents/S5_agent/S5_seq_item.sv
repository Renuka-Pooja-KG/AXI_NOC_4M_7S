//=============================================================================
// S5 Agent Sequence Item Class
//=============================================================================
// Simple sequence item for Slave 5 with AXI slave interface

import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the common AXI types package
import axi_common_types_pkg::*;

class S5_seq_item extends uvm_sequence_item;
    
    // S5-specific transaction identification
    rand int unsigned s5_transaction_id;  // Unique transaction ID for S5
    rand axi_master_id_e master_id;       // Source master (0-3)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S5 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S5_AWID;           // Write address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S5_AWADDR;         // Write address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S5_AWLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S5_AWLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S5_AWSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S5_AWBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S5_AWCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S5_AWPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S5_AWQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S5_AWREGION;       // Region identifier (from master)
    bit                        S5_AWVALID;        // Write address valid (from master)
    rand bit                   S5_AWREADY;        // Write address ready (S5 drives this)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S5 receives these signals from masters
    bit [AXI_DATA_WIDTH-1:0]   S5_WDATA;          // Write data (from master)
    bit [AXI_STRB_WIDTH-1:0]   S5_WSTRB;          // Write strobes (from master)
    bit                        S5_WLAST;          // Write last (from master)
    bit                        S5_WVALID;         // Write valid (from master)
    rand bit                   S5_WREADY;         // Write ready (S5 drives this)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S5 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S5_BID;           // Write response ID (S5 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S5_BRESP;       // Write response (S5 drives this)
    rand bit                    S5_BVALID;         // Write response valid (S5 drives this)
    bit                         S5_BREADY;         // Write response ready (from master)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S5 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S5_ARID;           // Read address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S5_ARADDR;         // Read address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S5_ARLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S5_ARLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S5_ARSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S5_ARBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S5_ARCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S5_ARPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S5_ARQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S5_ARREGION;       // Region identifier (from master)
    bit                        S5_ARVALID;        // Read address valid (from master)
    rand bit                   S5_ARREADY;        // Read address ready (S5 drives this)
    
    // ===== READ DATA CHANNEL (R) =====
    // S5 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S5_RID;           // Read ID (S5 drives this)
    rand bit [AXI_DATA_WIDTH-1:0] S5_RDATA;       // Read data (S5 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S5_RRESP;       // Read response (S5 drives this)
    rand bit                    S5_RLAST;          // Read last (S5 drives this)
    rand bit                    S5_RVALID;         // Read valid (S5 drives this)
    bit                         S5_RREADY;         // Read ready (from master)
    
    // ===== BURST DATA ARRAYS =====
    rand bit [AXI_DATA_WIDTH-1:0]   burst_data[];   // Array for burst data
    rand bit [AXI_STRB_WIDTH-1:0]   burst_strobe[]; // Array for burst strobes
    
    // Constraints
    constraint master_id_c {
        master_id inside {AXI_MASTER_0, AXI_MASTER_1, AXI_MASTER_2, AXI_MASTER_3};
    }
    
    constraint s5_awid_c {
        S5_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s5_arid_c {
        S5_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s5_awlen_c {
        S5_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s5_arlen_c {
        S5_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s5_awsize_c {
        S5_AWSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s5_arsize_c {
        S5_ARSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s5_awburst_c {
        S5_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s5_arburst_c {
        S5_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s5_awlock_c {
        S5_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s5_arlock_c {
        S5_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s5_awcache_c {
        S5_AWCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s5_arcache_c {
        S5_ARCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s5_awprot_c {
        S5_AWPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s5_arprot_c {
        S5_ARPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s5_awqos_c {
        S5_AWQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s5_arqos_c {
        S5_ARQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s5_awregion_c {
        S5_AWREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s5_arregion_c {
        S5_ARREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s5_bresp_c {
        S5_BRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint s5_rresp_c {
        S5_RRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint burst_data_c {
        burst_data.size() == (S5_AWLEN + 1);
        burst_strobe.size() == (S5_AWLEN + 1);
    }
    
    // Constructor
    function new(string name = "S5_seq_item");
        super.new(name);
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
    endfunction
    
    // Custom string conversion function for enum fields
    function string convert2string();
        string result;
        result = $sformatf("S5_seq_item: trans_type=%s, master_id=%s, AWID=%0d, AWADDR=0x%0h", 
                          trans_type.name(), master_id.name(), S5_AWID, S5_AWADDR);
        return result;
    endfunction
    
    // UVM field macros for automation
    `uvm_object_utils_begin(S5_seq_item)
        `uvm_field_int(s5_transaction_id, UVM_ALL_ON)

        
        // Write Address Channel
        `uvm_field_int(S5_AWID, UVM_ALL_ON)
        `uvm_field_int(S5_AWADDR, UVM_ALL_ON)
        `uvm_field_int(S5_AWLEN, UVM_ALL_ON)
        `uvm_field_int(S5_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(S5_AWSIZE, UVM_ALL_ON)
        `uvm_field_int(S5_AWBURST, UVM_ALL_ON)
        `uvm_field_int(S5_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(S5_AWPROT, UVM_ALL_ON)
        `uvm_field_int(S5_AWQOS, UVM_ALL_ON)
        `uvm_field_int(S5_AWREGION, UVM_ALL_ON)
        `uvm_field_int(S5_AWVALID, UVM_ALL_ON)
        `uvm_field_int(S5_AWREADY, UVM_ALL_ON)
        
        // Write Data Channel
        `uvm_field_int(S5_WDATA, UVM_ALL_ON)
        `uvm_field_int(S5_WSTRB, UVM_ALL_ON)
        `uvm_field_int(S5_WLAST, UVM_ALL_ON)
        `uvm_field_int(S5_WVALID, UVM_ALL_ON)
        `uvm_field_int(S5_WREADY, UVM_ALL_ON)
        
        // Write Response Channel
        `uvm_field_int(S5_BID, UVM_ALL_ON)
        `uvm_field_int(S5_BRESP, UVM_ALL_ON)
        `uvm_field_int(S5_BVALID, UVM_ALL_ON)
        `uvm_field_int(S5_BREADY, UVM_ALL_ON)
        
        // Read Address Channel
        `uvm_field_int(S5_ARID, UVM_ALL_ON)
        `uvm_field_int(S5_ARADDR, UVM_ALL_ON)
        `uvm_field_int(S5_ARLEN, UVM_ALL_ON)
        `uvm_field_int(S5_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(S5_ARSIZE, UVM_ALL_ON)
        `uvm_field_int(S5_ARBURST, UVM_ALL_ON)
        `uvm_field_int(S5_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(S5_ARPROT, UVM_ALL_ON)
        `uvm_field_int(S5_ARQOS, UVM_ALL_ON)
        `uvm_field_int(S5_ARREGION, UVM_ALL_ON)
        `uvm_field_int(S5_ARVALID, UVM_ALL_ON)
        `uvm_field_int(S5_ARREADY, UVM_ALL_ON)
        
        // Read Data Channel
        `uvm_field_int(S5_RID, UVM_ALL_ON)
        `uvm_field_int(S5_RDATA, UVM_ALL_ON)
        `uvm_field_int(S5_RRESP, UVM_ALL_ON)
        `uvm_field_int(S5_RLAST, UVM_ALL_ON)
        `uvm_field_int(S5_RVALID, UVM_ALL_ON)
        `uvm_field_int(S5_RREADY, UVM_ALL_ON)
        
        // Arrays
        `uvm_field_array_int(burst_data, UVM_ALL_ON)
        `uvm_field_array_int(burst_strobe, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : S5_seq_item
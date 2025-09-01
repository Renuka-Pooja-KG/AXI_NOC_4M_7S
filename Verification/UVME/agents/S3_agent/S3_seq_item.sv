//=============================================================================
// S3 Agent Sequence Item Class
//=============================================================================
// Simple sequence item for Slave 3 with AXI slave interface

import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the common AXI types package
import axi_common_types_pkg::*;

class S3_seq_item extends uvm_sequence_item;
    
    // S3-specific transaction identification
    rand int unsigned s3_transaction_id;  // Unique transaction ID for S3
    rand axi_master_id_e master_id;       // Source master (0-3)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S3 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S3_AWID;           // Write address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S3_AWADDR;         // Write address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S3_AWLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S3_AWLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S3_AWSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S3_AWBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S3_AWCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S3_AWPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S3_AWQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S3_AWREGION;       // Region identifier (from master)
    bit                        S3_AWVALID;        // Write address valid (from master)
    rand bit                   S3_AWREADY;        // Write address ready (S3 drives this)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S3 receives these signals from masters
    bit [AXI_DATA_WIDTH-1:0]   S3_WDATA;          // Write data (from master)
    bit [AXI_STRB_WIDTH-1:0]   S3_WSTRB;          // Write strobes (from master)
    bit                        S3_WLAST;          // Write last (from master)
    bit                        S3_WVALID;         // Write valid (from master)
    rand bit                   S3_WREADY;         // Write ready (S3 drives this)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S3 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S3_BID;           // Write response ID (S3 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S3_BRESP;       // Write response (S3 drives this)
    rand bit                    S3_BVALID;         // Write response valid (S3 drives this)
    bit                         S3_BREADY;         // Write response ready (from master)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S3 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S3_ARID;           // Read address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S3_ARADDR;         // Read address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S3_ARLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S3_ARLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S3_ARSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S3_ARBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S3_ARCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S3_ARPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S3_ARQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S3_ARREGION;       // Region identifier (from master)
    bit                        S3_ARVALID;        // Read address valid (from master)
    rand bit                   S3_ARREADY;        // Read address ready (S3 drives this)
    
    // ===== READ DATA CHANNEL (R) =====
    // S3 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S3_RID;           // Read ID (S3 drives this)
    rand bit [AXI_DATA_WIDTH-1:0] S3_RDATA;       // Read data (S3 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S3_RRESP;       // Read response (S3 drives this)
    rand bit                    S3_RLAST;          // Read last (S3 drives this)
    rand bit                    S3_RVALID;         // Read valid (S3 drives this)
    bit                         S3_RREADY;         // Read ready (from master)
    
    // ===== BURST DATA ARRAYS =====
    rand bit [AXI_DATA_WIDTH-1:0]   burst_data[];   // Array for burst data
    rand bit [AXI_STRB_WIDTH-1:0]   burst_strobe[]; // Array for burst strobes
    
    // Constraints
    constraint master_id_c {
        master_id inside {AXI_MASTER_0, AXI_MASTER_1, AXI_MASTER_2, AXI_MASTER_3};
    }
    
    constraint s3_awid_c {
        S3_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s3_arid_c {
        S3_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s3_awlen_c {
        S3_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s3_arlen_c {
        S3_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s3_awsize_c {
        S3_AWSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s3_arsize_c {
        S3_ARSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s3_awburst_c {
        S3_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s3_arburst_c {
        S3_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s3_awlock_c {
        S3_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s3_arlock_c {
        S3_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s3_awcache_c {
        S3_AWCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s3_arcache_c {
        S3_ARCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s3_awprot_c {
        S3_AWPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s3_arprot_c {
        S3_ARPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s3_awqos_c {
        S3_AWQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s3_arqos_c {
        S3_ARQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s3_awregion_c {
        S3_AWREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s3_arregion_c {
        S3_ARREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s3_bresp_c {
        S3_BRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint s3_rresp_c {
        S3_RRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint burst_data_c {
        burst_data.size() == (S3_AWLEN + 1);
        burst_strobe.size() == (S3_AWLEN + 1);
    }
    
    // Constructor
    function new(string name = "S3_seq_item");
        super.new(name);
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
    endfunction
    
    // Custom string conversion function for enum fields
    function string convert2string();
        string result;
        result = $sformatf("S3_seq_item: trans_type=%s, master_id=%s, AWID=%0d, AWADDR=0x%0h", 
                          trans_type.name(), master_id.name(), S3_AWID, S3_AWADDR);
        return result;
    endfunction
    
    // UVM field macros for automation
    `uvm_object_utils_begin(S3_seq_item)
        `uvm_field_int(s3_transaction_id, UVM_ALL_ON)

        
        // Write Address Channel
        `uvm_field_int(S3_AWID, UVM_ALL_ON)
        `uvm_field_int(S3_AWADDR, UVM_ALL_ON)
        `uvm_field_int(S3_AWLEN, UVM_ALL_ON)
        `uvm_field_int(S3_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(S3_AWSIZE, UVM_ALL_ON)
        `uvm_field_int(S3_AWBURST, UVM_ALL_ON)
        `uvm_field_int(S3_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(S3_AWPROT, UVM_ALL_ON)
        `uvm_field_int(S3_AWQOS, UVM_ALL_ON)
        `uvm_field_int(S3_AWREGION, UVM_ALL_ON)
        `uvm_field_int(S3_AWVALID, UVM_ALL_ON)
        `uvm_field_int(S3_AWREADY, UVM_ALL_ON)
        
        // Write Data Channel
        `uvm_field_int(S3_WDATA, UVM_ALL_ON)
        `uvm_field_int(S3_WSTRB, UVM_ALL_ON)
        `uvm_field_int(S3_WLAST, UVM_ALL_ON)
        `uvm_field_int(S3_WVALID, UVM_ALL_ON)
        `uvm_field_int(S3_WREADY, UVM_ALL_ON)
        
        // Write Response Channel
        `uvm_field_int(S3_BID, UVM_ALL_ON)
        `uvm_field_int(S3_BRESP, UVM_ALL_ON)
        `uvm_field_int(S3_BVALID, UVM_ALL_ON)
        `uvm_field_int(S3_BREADY, UVM_ALL_ON)
        
        // Read Address Channel
        `uvm_field_int(S3_ARID, UVM_ALL_ON)
        `uvm_field_int(S3_ARADDR, UVM_ALL_ON)
        `uvm_field_int(S3_ARLEN, UVM_ALL_ON)
        `uvm_field_int(S3_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(S3_ARSIZE, UVM_ALL_ON)
        `uvm_field_int(S3_ARBURST, UVM_ALL_ON)
        `uvm_field_int(S3_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(S3_ARPROT, UVM_ALL_ON)
        `uvm_field_int(S3_ARQOS, UVM_ALL_ON)
        `uvm_field_int(S3_ARREGION, UVM_ALL_ON)
        `uvm_field_int(S3_ARVALID, UVM_ALL_ON)
        `uvm_field_int(S3_ARREADY, UVM_ALL_ON)
        
        // Read Data Channel
        `uvm_field_int(S3_RID, UVM_ALL_ON)
        `uvm_field_int(S3_RDATA, UVM_ALL_ON)
        `uvm_field_int(S3_RRESP, UVM_ALL_ON)
        `uvm_field_int(S3_RLAST, UVM_ALL_ON)
        `uvm_field_int(S3_RVALID, UVM_ALL_ON)
        `uvm_field_int(S3_RREADY, UVM_ALL_ON)
        
        // Arrays
        `uvm_field_array_int(burst_data, UVM_ALL_ON)
        `uvm_field_array_int(burst_strobe, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : S3_seq_item
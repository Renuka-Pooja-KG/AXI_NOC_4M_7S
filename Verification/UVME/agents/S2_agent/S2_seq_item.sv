//=============================================================================
// S2 Agent Sequence Item Class
//=============================================================================
// Simple sequence item for Slave 2 with AXI slave interface

class S2_seq_item extends uvm_sequence_item;
    
    // S2-specific transaction identification
    rand int unsigned s2_transaction_id;  // Unique transaction ID for S2
    rand axi_master_id_e master_id;       // Source master (0-3)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S2 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S2_AWID;           // Write address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S2_AWADDR;         // Write address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S2_AWLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S2_AWLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S2_AWSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S2_AWBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S2_AWCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S2_AWPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S2_AWQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S2_AWREGION;       // Region identifier (from master)
    bit [0:0]                  S2_AWUSER;         // Write address user path (from master)
    bit                        S2_AWVALID;        // Write address valid (from master)
    rand bit                   S2_AWREADY;        // Write address ready (S2 drives this)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S2 receives these signals from masters
    bit [AXI_DATA_WIDTH-1:0]   S2_WDATA;          // Write data (from master)
    bit [AXI_STRB_WIDTH-1:0]   S2_WSTRB;          // Write strobes (from master)
    bit                        S2_WLAST;          // Write last (from master)
    bit                        S2_WVALID;         // Write valid (from master)
    rand bit                   S2_WREADY;         // Write ready (S2 drives this)
    bit [0:0]                  S2_WUSER;          // Write data user path (from master)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S2 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S2_BID;           // Write response ID (S2 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S2_BRESP;       // Write response (S2 drives this)
    rand bit                    S2_BVALID;         // Write response valid (S2 drives this)
    bit                         S2_BREADY;         // Write response ready (from master)
    rand bit [0:0]             S2_BUSER;          // Write response user path (S2 drives this)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S2 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S2_ARID;           // Read address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S2_ARADDR;         // Read address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S2_ARLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S2_ARLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S2_ARSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S2_ARBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S2_ARCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S2_ARPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S2_ARQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S2_ARREGION;       // Region identifier (from master)
    bit [0:0]                  S2_ARUSER;         // Read address user path (from master)
    bit                        S2_ARVALID;        // Read address valid (from master)
    rand bit                   S2_ARREADY;        // Read address ready (S2 drives this)
    
    // ===== READ DATA CHANNEL (R) =====
    // S2 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S2_RID;           // Read ID (S2 drives this)
    rand bit [AXI_DATA_WIDTH-1:0] S2_RDATA;       // Read data (S2 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S2_RRESP;       // Read response (S2 drives this)
    rand bit                    S2_RLAST;          // Read last (S2 drives this)
    rand bit                    S2_RVALID;         // Read valid (S2 drives this)
    bit                         S2_RREADY;         // Read ready (from master)
    rand bit [0:0]             S2_RUSER;          // Read data user path (S2 drives this)
    
    // ===== BURST DATA ARRAYS =====
    rand bit [AXI_DATA_WIDTH-1:0]   burst_data[];   // Array for burst data
    rand bit [AXI_STRB_WIDTH-1:0]   burst_strobe[]; // Array for burst strobes
    
    // ===== STATUS AND TIMING =====
    bit                             transaction_complete;
    time                            start_time;
    time                            end_time;
    
    // Constraints
    constraint master_id_c {
        master_id inside {AXI_MASTER_0, AXI_MASTER_1, AXI_MASTER_2, AXI_MASTER_3};
    }
    
    constraint s2_awid_c {
        S2_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s2_arid_c {
        S2_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s2_awlen_c {
        S2_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s2_arlen_c {
        S2_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s2_awsize_c {
        S2_AWSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s2_arsize_c {
        S2_ARSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s2_awburst_c {
        S2_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s2_arburst_c {
        S2_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s2_awlock_c {
        S2_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s2_arlock_c {
        S2_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s2_awcache_c {
        S2_AWCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s2_arcache_c {
        S2_ARCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s2_awprot_c {
        S2_AWPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s2_arprot_c {
        S2_ARPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s2_awqos_c {
        S2_AWQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s2_arqos_c {
        S2_ARQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s2_awregion_c {
        S2_AWREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s2_arregion_c {
        S2_ARREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s2_bresp_c {
        S2_BRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint s2_rresp_c {
        S2_RRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint burst_data_c {
        burst_data.size() == (S2_AWLEN + 1);
        burst_strobe.size() == (S2_AWLEN + 1);
    }
    
    // Constructor
    function new(string name = "S2_seq_item");
        super.new(name);
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
        // Initialize timing
        start_time = 0;
        end_time = 0;
        transaction_complete = 0;
    endfunction
    
    // Start transaction timing
    function void start_transaction();
        start_time = $realtime;
        transaction_complete = 0;
    endfunction
    
    // End transaction timing
    function void end_transaction();
        end_time = $realtime;
        transaction_complete = 1;
    endfunction
    
    // UVM field macros for automation
    `uvm_object_utils_begin(S2_seq_item)
        `uvm_field_int(s2_transaction_id, UVM_ALL_ON)
        `uvm_field_enum(axi_master_id_e, master_id, UVM_ALL_ON)
        `uvm_field_enum(axi_trans_type_e, trans_type, UVM_ALL_ON)
        
        // Write Address Channel
        `uvm_field_int(S2_AWID, UVM_ALL_ON)
        `uvm_field_int(S2_AWADDR, UVM_ALL_ON)
        `uvm_field_int(S2_AWLEN, UVM_ALL_ON)
        `uvm_field_int(S2_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(S2_AWSIZE, UVM_ALL_ON)
        `uvm_field_int(S2_AWBURST, UVM_ALL_ON)
        `uvm_field_int(S2_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(S2_AWPROT, UVM_ALL_ON)
        `uvm_field_int(S2_AWQOS, UVM_ALL_ON)
        `uvm_field_int(S2_AWREGION, UVM_ALL_ON)
        `uvm_field_int(S2_AWUSER, UVM_ALL_ON)
        `uvm_field_int(S2_AWVALID, UVM_ALL_ON)
        `uvm_field_int(S2_AWREADY, UVM_ALL_ON)
        
        // Write Data Channel
        `uvm_field_int(S2_WDATA, UVM_ALL_ON)
        `uvm_field_int(S2_WSTRB, UVM_ALL_ON)
        `uvm_field_int(S2_WLAST, UVM_ALL_ON)
        `uvm_field_int(S2_WVALID, UVM_ALL_ON)
        `uvm_field_int(S2_WREADY, UVM_ALL_ON)
        `uvm_field_int(S2_WUSER, UVM_ALL_ON)
        
        // Write Response Channel
        `uvm_field_int(S2_BID, UVM_ALL_ON)
        `uvm_field_int(S2_BRESP, UVM_ALL_ON)
        `uvm_field_int(S2_BVALID, UVM_ALL_ON)
        `uvm_field_int(S2_BREADY, UVM_ALL_ON)
        `uvm_field_int(S2_BUSER, UVM_ALL_ON)
        
        // Read Address Channel
        `uvm_field_int(S2_ARID, UVM_ALL_ON)
        `uvm_field_int(S2_ARADDR, UVM_ALL_ON)
        `uvm_field_int(S2_ARLEN, UVM_ALL_ON)
        `uvm_field_int(S2_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(S2_ARSIZE, UVM_ALL_ON)
        `uvm_field_int(S2_ARBURST, UVM_ALL_ON)
        `uvm_field_int(S2_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(S2_ARPROT, UVM_ALL_ON)
        `uvm_field_int(S2_ARQOS, UVM_ALL_ON)
        `uvm_field_int(S2_ARREGION, UVM_ALL_ON)
        `uvm_field_int(S2_ARUSER, UVM_ALL_ON)
        `uvm_field_int(S2_ARVALID, UVM_ALL_ON)
        `uvm_field_int(S2_ARREADY, UVM_ALL_ON)
        
        // Read Data Channel
        `uvm_field_int(S2_RID, UVM_ALL_ON)
        `uvm_field_int(S2_RDATA, UVM_ALL_ON)
        `uvm_field_int(S2_RRESP, UVM_ALL_ON)
        `uvm_field_int(S2_RLAST, UVM_ALL_ON)
        `uvm_field_int(S2_RVALID, UVM_ALL_ON)
        `uvm_field_int(S2_RREADY, UVM_ALL_ON)
        `uvm_field_int(S2_RUSER, UVM_ALL_ON)
        
        // Arrays
        `uvm_field_sarray_int(burst_data, UVM_ALL_ON)
        `uvm_field_sarray_int(burst_strobe, UVM_ALL_ON)
        
        // Status and timing
        `uvm_field_int(transaction_complete, UVM_ALL_ON)
        `uvm_field_time(start_time, UVM_ALL_ON)
        `uvm_field_time(end_time, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : S2_seq_item
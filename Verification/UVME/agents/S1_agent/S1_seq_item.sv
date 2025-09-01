//=============================================================================
// S1 Agent Sequence Item Class
//=============================================================================
// Simple sequence item for Slave 1 with AXI slave interface

class S1_seq_item extends uvm_sequence_item;
    
    // S1-specific transaction identification
    rand int unsigned s1_transaction_id;  // Unique transaction ID for S1
    rand axi_master_id_e master_id;       // Source master (0-3)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S1 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S1_AWID;           // Write address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S1_AWADDR;         // Write address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S1_AWLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S1_AWLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S1_AWSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S1_AWBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S1_AWCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S1_AWPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S1_AWQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S1_AWREGION;       // Region identifier (from master)
    bit [0:0]                  S1_AWUSER;         // Write address user path (from master)
    bit                        S1_AWVALID;        // Write address valid (from master)
    rand bit                   S1_AWREADY;        // Write address ready (S1 drives this)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S1 receives these signals from masters
    bit [AXI_DATA_WIDTH-1:0]   S1_WDATA;          // Write data (from master)
    bit [AXI_STRB_WIDTH-1:0]   S1_WSTRB;          // Write strobes (from master)
    bit                        S1_WLAST;          // Write last (from master)
    bit                        S1_WVALID;         // Write valid (from master)
    rand bit                   S1_WREADY;         // Write ready (S1 drives this)
    bit [0:0]                  S1_WUSER;          // Write data user path (from master)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S1 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S1_BID;           // Write response ID (S1 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S1_BRESP;       // Write response (S1 drives this)
    rand bit                    S1_BVALID;         // Write response valid (S1 drives this)
    bit                         S1_BREADY;         // Write response ready (from master)
    rand bit [0:0]             S1_BUSER;          // Write response user path (S1 drives this)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S1 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S1_ARID;           // Read address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S1_ARADDR;         // Read address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S1_ARLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S1_ARLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S1_ARSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S1_ARBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S1_ARCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S1_ARPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S1_ARQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S1_ARREGION;       // Region identifier (from master)
    bit [0:0]                  S1_ARUSER;         // Read address user path (from master)
    bit                        S1_ARVALID;        // Read address valid (from master)
    rand bit                   S1_ARREADY;        // Read address ready (S1 drives this)
    
    // ===== READ DATA CHANNEL (R) =====
    // S1 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S1_RID;           // Read ID (S1 drives this)
    rand bit [AXI_DATA_WIDTH-1:0] S1_RDATA;       // Read data (S1 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S1_RRESP;       // Read response (S1 drives this)
    rand bit                    S1_RLAST;          // Read last (S1 drives this)
    rand bit                    S1_RVALID;         // Read valid (S1 drives this)
    bit                         S1_RREADY;         // Read ready (from master)
    rand bit [0:0]             S1_RUSER;          // Read data user path (S1 drives this)
    
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
    
    constraint s1_awid_c {
        S1_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s1_arid_c {
        S1_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s1_awlen_c {
        S1_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s1_arlen_c {
        S1_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s1_awsize_c {
        S1_AWSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s1_arsize_c {
        S1_ARSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s1_awburst_c {
        S1_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s1_arburst_c {
        S1_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s1_awlock_c {
        S1_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s1_arlock_c {
        S1_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s1_awcache_c {
        S1_AWCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s1_arcache_c {
        S1_ARCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s1_awprot_c {
        S1_AWPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s1_arprot_c {
        S1_ARPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s1_awqos_c {
        S1_AWQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s1_arqos_c {
        S1_ARQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s1_awregion_c {
        S1_AWREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s1_arregion_c {
        S1_ARREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s1_bresp_c {
        S1_BRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint s1_rresp_c {
        S1_RRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint burst_data_c {
        burst_data.size() == (S1_AWLEN + 1);
        burst_strobe.size() == (S1_AWLEN + 1);
    }
    
    // Constructor
    function new(string name = "S1_seq_item");
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
    `uvm_object_utils_begin(S1_seq_item)
        `uvm_field_int(s1_transaction_id, UVM_ALL_ON)
        `uvm_field_enum(axi_master_id_e, master_id, UVM_ALL_ON)
        `uvm_field_enum(axi_trans_type_e, trans_type, UVM_ALL_ON)
        
        // Write Address Channel
        `uvm_field_int(S1_AWID, UVM_ALL_ON)
        `uvm_field_int(S1_AWADDR, UVM_ALL_ON)
        `uvm_field_int(S1_AWLEN, UVM_ALL_ON)
        `uvm_field_int(S1_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(S1_AWSIZE, UVM_ALL_ON)
        `uvm_field_int(S1_AWBURST, UVM_ALL_ON)
        `uvm_field_int(S1_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(S1_AWPROT, UVM_ALL_ON)
        `uvm_field_int(S1_AWQOS, UVM_ALL_ON)
        `uvm_field_int(S1_AWREGION, UVM_ALL_ON)
        `uvm_field_int(S1_AWUSER, UVM_ALL_ON)
        `uvm_field_int(S1_AWVALID, UVM_ALL_ON)
        `uvm_field_int(S1_AWREADY, UVM_ALL_ON)
        
        // Write Data Channel
        `uvm_field_int(S1_WDATA, UVM_ALL_ON)
        `uvm_field_int(S1_WSTRB, UVM_ALL_ON)
        `uvm_field_int(S1_WLAST, UVM_ALL_ON)
        `uvm_field_int(S1_WVALID, UVM_ALL_ON)
        `uvm_field_int(S1_WREADY, UVM_ALL_ON)
        `uvm_field_int(S1_WUSER, UVM_ALL_ON)
        
        // Write Response Channel
        `uvm_field_int(S1_BID, UVM_ALL_ON)
        `uvm_field_int(S1_BRESP, UVM_ALL_ON)
        `uvm_field_int(S1_BVALID, UVM_ALL_ON)
        `uvm_field_int(S1_BREADY, UVM_ALL_ON)
        `uvm_field_int(S1_BUSER, UVM_ALL_ON)
        
        // Read Address Channel
        `uvm_field_int(S1_ARID, UVM_ALL_ON)
        `uvm_field_int(S1_ARADDR, UVM_ALL_ON)
        `uvm_field_int(S1_ARLEN, UVM_ALL_ON)
        `uvm_field_int(S1_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(S1_ARSIZE, UVM_ALL_ON)
        `uvm_field_int(S1_ARBURST, UVM_ALL_ON)
        `uvm_field_int(S1_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(S1_ARPROT, UVM_ALL_ON)
        `uvm_field_int(S1_ARQOS, UVM_ALL_ON)
        `uvm_field_int(S1_ARREGION, UVM_ALL_ON)
        `uvm_field_int(S1_ARUSER, UVM_ALL_ON)
        `uvm_field_int(S1_ARVALID, UVM_ALL_ON)
        `uvm_field_int(S1_ARREADY, UVM_ALL_ON)
        
        // Read Data Channel
        `uvm_field_int(S1_RID, UVM_ALL_ON)
        `uvm_field_int(S1_RDATA, UVM_ALL_ON)
        `uvm_field_int(S1_RRESP, UVM_ALL_ON)
        `uvm_field_int(S1_RLAST, UVM_ALL_ON)
        `uvm_field_int(S1_RVALID, UVM_ALL_ON)
        `uvm_field_int(S1_RREADY, UVM_ALL_ON)
        `uvm_field_int(S1_RUSER, UVM_ALL_ON)
        
        // Arrays
        `uvm_field_sarray_int(burst_data, UVM_ALL_ON)
        `uvm_field_sarray_int(burst_strobe, UVM_ALL_ON)
        
        // Status and timing
        `uvm_field_int(transaction_complete, UVM_ALL_ON)
        `uvm_field_int(start_time, UVM_ALL_ON)
        `uvm_field_int(end_time, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : S1_seq_item
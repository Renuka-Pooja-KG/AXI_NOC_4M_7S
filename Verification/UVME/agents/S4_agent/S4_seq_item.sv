//=============================================================================
// S4 Agent Sequence Item Class
//=============================================================================
// Simple sequence item for Slave 4 with AXI slave interface

class S4_seq_item extends uvm_sequence_item;
    
    // S4-specific transaction identification
    rand int unsigned s4_transaction_id;  // Unique transaction ID for S4
    rand axi_master_id_e master_id;       // Source master (0-3)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S4 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S4_AWID;           // Write address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S4_AWADDR;         // Write address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S4_AWLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S4_AWLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S4_AWSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S4_AWBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S4_AWCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S4_AWPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S4_AWQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S4_AWREGION;       // Region identifier (from master)
    bit [0:0]                  S4_AWUSER;         // Write address user path (from master)
    bit                        S4_AWVALID;        // Write address valid (from master)
    rand bit                   S4_AWREADY;        // Write address ready (S4 drives this)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S4 receives these signals from masters
    bit [AXI_DATA_WIDTH-1:0]   S4_WDATA;          // Write data (from master)
    bit [AXI_STRB_WIDTH-1:0]   S4_WSTRB;          // Write strobes (from master)
    bit                        S4_WLAST;          // Write last (from master)
    bit                        S4_WVALID;         // Write valid (from master)
    rand bit                   S4_WREADY;         // Write ready (S4 drives this)
    bit [0:0]                  S4_WUSER;          // Write data user path (from master)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S4 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S4_BID;           // Write response ID (S4 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S4_BRESP;       // Write response (S4 drives this)
    rand bit                    S4_BVALID;         // Write response valid (S4 drives this)
    bit                         S4_BREADY;         // Write response ready (from master)
    rand bit [0:0]             S4_BUSER;          // Write response user path (S4 drives this)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S4 receives these signals from masters
    bit [AXI_ID_WIDTH-1:0]     S4_ARID;           // Read address ID (from master)
    bit [AXI_ADDR_WIDTH-1:0]   S4_ARADDR;         // Read address (from master)
    bit [AXI_LEN_WIDTH-1:0]    S4_ARLEN;          // Burst length (from master)
    bit [AXI_LOCK_WIDTH-1:0]   S4_ARLOCK;         // Lock type (from master)
    bit [AXI_SIZE_WIDTH-1:0]   S4_ARSIZE;         // Burst size (from master)
    bit [AXI_BURST_WIDTH-1:0]  S4_ARBURST;        // Burst type (from master)
    bit [AXI_CACHE_WIDTH-1:0]  S4_ARCACHE;        // Cache attributes (from master)
    bit [AXI_PROT_WIDTH-1:0]   S4_ARPROT;         // Protection attributes (from master)
    bit [AXI_QOS_WIDTH-1:0]    S4_ARQOS;          // Quality of service (from master)
    bit [AXI_REGION_WIDTH-1:0] S4_ARREGION;       // Region identifier (from master)
    bit [0:0]                  S4_ARUSER;         // Read address user path (from master)
    bit                        S4_ARVALID;        // Read address valid (from master)
    rand bit                   S4_ARREADY;        // Read address ready (S4 drives this)
    
    // ===== READ DATA CHANNEL (R) =====
    // S4 drives these signals to masters
    rand bit [AXI_ID_WIDTH-1:0] S4_RID;           // Read ID (S4 drives this)
    rand bit [AXI_DATA_WIDTH-1:0] S4_RDATA;       // Read data (S4 drives this)
    rand bit [AXI_RESP_WIDTH-1:0] S4_RRESP;       // Read response (S4 drives this)
    rand bit                    S4_RLAST;          // Read last (S4 drives this)
    rand bit                    S4_RVALID;         // Read valid (S4 drives this)
    bit                         S4_RREADY;         // Read ready (from master)
    rand bit [0:0]             S4_RUSER;          // Read data user path (S4 drives this)
    
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
    
    constraint s4_awid_c {
        S4_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s4_arid_c {
        S4_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};
    }
    
    constraint s4_awlen_c {
        S4_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s4_arlen_c {
        S4_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};
    }
    
    constraint s4_awsize_c {
        S4_AWSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s4_arsize_c {
        S4_ARSIZE inside {AXI_SIZE_1BYTE, AXI_SIZE_2BYTE, AXI_SIZE_4BYTE, AXI_SIZE_8BYTE};
    }
    
    constraint s4_awburst_c {
        S4_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s4_arburst_c {
        S4_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};
    }
    
    constraint s4_awlock_c {
        S4_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s4_arlock_c {
        S4_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};
    }
    
    constraint s4_awcache_c {
        S4_AWCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s4_arcache_c {
        S4_ARCACHE inside {AXI_CACHE_NONCACHEABLE, AXI_CACHE_BUFFERABLE, AXI_CACHE_CACHEABLE, 
                          AXI_CACHE_WRITETHROUGH, AXI_CACHE_WRITEBACK};
    }
    
    constraint s4_awprot_c {
        S4_AWPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s4_arprot_c {
        S4_ARPROT inside {AXI_PROT_NORMAL, AXI_PROT_PRIVILEGED, AXI_PROT_SECURE, AXI_PROT_NONSECURE,
                          AXI_PROT_INSTRUCTION, AXI_PROT_DATA, AXI_PROT_USER, AXI_PROT_SUPERVISOR};
    }
    
    constraint s4_awqos_c {
        S4_AWQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s4_arqos_c {
        S4_ARQOS inside {AXI_QOS_LEVEL_0, AXI_QOS_LEVEL_1, AXI_QOS_LEVEL_2, AXI_QOS_LEVEL_3,
                         AXI_QOS_LEVEL_4, AXI_QOS_LEVEL_5, AXI_QOS_LEVEL_6, AXI_QOS_LEVEL_7};
    }
    
    constraint s4_awregion_c {
        S4_AWREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s4_arregion_c {
        S4_ARREGION inside {AXI_REGION_0, AXI_REGION_1, AXI_REGION_2, AXI_REGION_3,
                           AXI_REGION_4, AXI_REGION_5, AXI_REGION_6, AXI_REGION_7};
    }
    
    constraint s4_bresp_c {
        S4_BRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint s4_rresp_c {
        S4_RRESP inside {AXI_OKAY, AXI_EXOKAY, AXI_SLVERR, AXI_DECERR};
    }
    
    constraint burst_data_c {
        burst_data.size() == (S4_AWLEN + 1);
        burst_strobe.size() == (S4_AWLEN + 1);
    }
    
    // Constructor
    function new(string name = "S4_seq_item");
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
    `uvm_object_utils_begin(S4_seq_item)
        `uvm_field_int(s4_transaction_id, UVM_ALL_ON)
        `uvm_field_enum(axi_master_id_e, master_id, UVM_ALL_ON)
        `uvm_field_enum(axi_trans_type_e, trans_type, UVM_ALL_ON)
        
        // Write Address Channel
        `uvm_field_int(S4_AWID, UVM_ALL_ON)
        `uvm_field_int(S4_AWADDR, UVM_ALL_ON)
        `uvm_field_int(S4_AWLEN, UVM_ALL_ON)
        `uvm_field_int(S4_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(S4_AWSIZE, UVM_ALL_ON)
        `uvm_field_int(S4_AWBURST, UVM_ALL_ON)
        `uvm_field_int(S4_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(S4_AWPROT, UVM_ALL_ON)
        `uvm_field_int(S4_AWQOS, UVM_ALL_ON)
        `uvm_field_int(S4_AWREGION, UVM_ALL_ON)
        `uvm_field_int(S4_AWUSER, UVM_ALL_ON)
        `uvm_field_int(S4_AWVALID, UVM_ALL_ON)
        `uvm_field_int(S4_AWREADY, UVM_ALL_ON)
        
        // Write Data Channel
        `uvm_field_int(S4_WDATA, UVM_ALL_ON)
        `uvm_field_int(S4_WSTRB, UVM_ALL_ON)
        `uvm_field_int(S4_WLAST, UVM_ALL_ON)
        `uvm_field_int(S4_WVALID, UVM_ALL_ON)
        `uvm_field_int(S4_WREADY, UVM_ALL_ON)
        `uvm_field_int(S4_WUSER, UVM_ALL_ON)
        
        // Write Response Channel
        `uvm_field_int(S4_BID, UVM_ALL_ON)
        `uvm_field_int(S4_BRESP, UVM_ALL_ON)
        `uvm_field_int(S4_BVALID, UVM_ALL_ON)
        `uvm_field_int(S4_BREADY, UVM_ALL_ON)
        `uvm_field_int(S4_BUSER, UVM_ALL_ON)
        
        // Read Address Channel
        `uvm_field_int(S4_ARID, UVM_ALL_ON)
        `uvm_field_int(S4_ARADDR, UVM_ALL_ON)
        `uvm_field_int(S4_ARLEN, UVM_ALL_ON)
        `uvm_field_int(S4_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(S4_ARSIZE, UVM_ALL_ON)
        `uvm_field_int(S4_ARBURST, UVM_ALL_ON)
        `uvm_field_int(S4_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(S4_ARPROT, UVM_ALL_ON)
        `uvm_field_int(S4_ARQOS, UVM_ALL_ON)
        `uvm_field_int(S4_ARREGION, UVM_ALL_ON)
        `uvm_field_int(S4_ARUSER, UVM_ALL_ON)
        `uvm_field_int(S4_ARVALID, UVM_ALL_ON)
        `uvm_field_int(S4_ARREADY, UVM_ALL_ON)
        
        // Read Data Channel
        `uvm_field_int(S4_RID, UVM_ALL_ON)
        `uvm_field_int(S4_RDATA, UVM_ALL_ON)
        `uvm_field_int(S4_RRESP, UVM_ALL_ON)
        `uvm_field_int(S4_RLAST, UVM_ALL_ON)
        `uvm_field_int(S4_RVALID, UVM_ALL_ON)
        `uvm_field_int(S4_RREADY, UVM_ALL_ON)
        `uvm_field_int(S4_RUSER, UVM_ALL_ON)
        
        // Arrays
        `uvm_field_sarray_int(burst_data, UVM_ALL_ON)
        `uvm_field_sarray_int(burst_strobe, UVM_ALL_ON)
        
        // Status and timing
        `uvm_field_int(transaction_complete, UVM_ALL_ON)
        `uvm_field_time(start_time, UVM_ALL_ON)
        `uvm_field_time(end_time, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : S4_seq_item
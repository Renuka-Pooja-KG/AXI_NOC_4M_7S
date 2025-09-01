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
    
    // ===== STATUS AND TIMING =====
    bit                             transaction_complete;
    time                            start_time;
    time                            end_time;
    
    // M0-specific transaction statistics
    int unsigned m0_total_transactions;
    int unsigned m0_write_transactions;
    int unsigned m0_read_transactions;
    int unsigned m0_burst_transactions;
    int unsigned m0_single_transactions;
    
    // M0-specific performance metrics
    time m0_avg_response_time;
    time m0_min_response_time;
    time m0_max_response_time;
    
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
        m0_transaction_id = 0;
        m0_total_transactions = 0;
        m0_write_transactions = 0;
        m0_read_transactions = 0;
        m0_burst_transactions = 0;
        m0_single_transactions = 0;
        m0_avg_response_time = 0;
        m0_min_response_time = 0;
        m0_max_response_time = 0;
        transaction_complete = 0;
        start_time = 0;
        end_time = 0;
        
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
    endfunction
    
    // M0-specific methods
    
    // Set M0 transaction ID
    function void set_m0_transaction_id(int id);
        m0_transaction_id = id;
    endfunction
    
    // Get M0 transaction ID
    function int get_m0_transaction_id();
        return m0_transaction_id;
    endfunction
    
    // Set slave ID
    function void set_slave_id(axi_slave_id_e id);
        slave_id = id;
    endfunction
    
    // Set transaction type
    function void set_transaction_type(axi_trans_type_e type);
        trans_type = type;
        if (type == AXI_WRITE) 
            m0_write_transactions++;
        else 
            m0_read_transactions++;
        m0_total_transactions++;
    endfunction
    
    // M0-specific slave selection methods
    function void set_random_slave();
        randcase
            1: slave_id = AXI_SLAVE_0;  // S0
            1: slave_id = AXI_SLAVE_1;  // S1
            1: slave_id = AXI_SLAVE_2;  // S2
            1: slave_id = AXI_SLAVE_3;  // S3
            1: slave_id = AXI_SLAVE_4;  // S4
            1: slave_id = AXI_SLAVE_5;  // S5
            1: slave_id = AXI_SLAVE_6;  // S6
        endcase
    endfunction
    
    // Set burst parameters using package constants
    function void set_burst_parameters(int length, axi_burst_type_e burst, int size);
        if (trans_type == AXI_WRITE) {
            M0_AWLEN = set_axi_length(length);  // Use package function
            M0_AWBURST = burst;
            M0_AWSIZE = $clog2(size);
        } else {
            M0_ARLEN = set_axi_length(length);  // Use package function
            M0_ARBURST = burst;
            M0_ARSIZE = $clog2(size);
        }
        
        // Resize arrays
        if (trans_type == AXI_WRITE) {
            burst_data = new[length];
            burst_strobe = new[length];
        } else {
            burst_data = new[length];
        }
    endfunction
    
    // Set address
    function void set_address(bit [AXI_ADDR_WIDTH-1:0] addr);
        if (trans_type == AXI_WRITE) 
            M0_AWADDR = addr;
        else 
            M0_ARADDR = addr;
    endfunction
    
    // Set burst data
    function void set_burst_data(int index, bit [AXI_DATA_WIDTH-1:0] data);
        if (index < burst_data.size()) 
            burst_data[index] = data;
    endfunction
    
    // Set burst strobe
    function void set_burst_strobe(int index, bit [AXI_STRB_WIDTH-1:0] strobe);
        if (index < burst_strobe.size()) 
            burst_strobe[index] = strobe;
    endfunction
    
    // M0-specific transaction type methods
    function void set_write_transaction();
        set_transaction_type(AXI_WRITE);
    endfunction
    
    function void set_read_transaction();
        set_transaction_type(AXI_READ);
    endfunction
    
    // M0-specific burst configuration methods
    function void set_single_transfer();
        if (trans_type == AXI_WRITE) {
            M0_AWLEN = 0;  // Single transfer
            M0_AWBURST = AXI_INCR;
        } else {
            M0_ARLEN = 0;  // Single transfer
            M0_ARBURST = AXI_INCR;
        }
        m0_single_transactions++;
    endfunction
    
    function void set_burst_transfer(int length, axi_burst_type_e burst_type);
        if (length > 1) {
            set_burst_parameters(length, burst_type, 4); // Default 4-byte transfers
            m0_burst_transactions++;
        } else {
            set_single_transfer();
        }
    endfunction
    
    // M0-specific address generation methods using package constants
    function void set_random_address_in_slave_range(axi_slave_id_e slave);
        set_slave_id(slave);
        if (slave == AXI_SLAVE_0) {
            if (trans_type == AXI_WRITE) M0_AWADDR = $urandom_range(SLAVE_0_BASE_ADDR, SLAVE_0_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M0_ARADDR = $urandom_range(SLAVE_0_BASE_ADDR, SLAVE_0_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        } else if (slave == AXI_SLAVE_1) {
            if (trans_type == AXI_WRITE) M0_AWADDR = $urandom_range(SLAVE_1_BASE_ADDR, SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M0_ARADDR = $urandom_range(SLAVE_1_BASE_ADDR, SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        } else if (slave == AXI_SLAVE_2) {
            if (trans_type == AXI_WRITE) M0_AWADDR = $urandom_range(SLAVE_2_BASE_ADDR, SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M0_ARADDR = $urandom_range(SLAVE_2_BASE_ADDR, SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        } else if (slave == AXI_SLAVE_3) {
            if (trans_type == AXI_WRITE) M0_AWADDR = $urandom_range(SLAVE_3_BASE_ADDR, SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M0_ARADDR = $urandom_range(SLAVE_3_BASE_ADDR, SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        } else if (slave == AXI_SLAVE_4) {
            if (trans_type == AXI_WRITE) M0_AWADDR = $urandom_range(SLAVE_4_BASE_ADDR, SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M0_ARADDR = $urandom_range(SLAVE_4_BASE_ADDR, SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        } else if (slave == AXI_SLAVE_5) {
            if (trans_type == AXI_WRITE) M0_AWADDR = $urandom_range(SLAVE_5_BASE_ADDR, SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M0_ARADDR = $urandom_range(SLAVE_5_BASE_ADDR, SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        } else if (slave == AXI_SLAVE_6) {
            if (trans_type == AXI_WRITE) M0_AWADDR = $urandom_range(SLAVE_6_BASE_ADDR, SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M0_ARADDR = $urandom_range(SLAVE_6_BASE_ADDR, SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        }
    endfunction
    
    // Check if transaction is complete
    function bit is_complete();
        return transaction_complete;
    endfunction
    
    // Mark transaction as complete
    function void mark_complete();
        transaction_complete = 1;
        end_time = $time;
    endfunction
    
    // Get transaction duration
    function time get_duration();
        return end_time - start_time;
    endfunction
    
    // M0-specific performance tracking
    function void update_performance_metrics(time response_time);
        if (m0_min_response_time == 0 || response_time < m0_min_response_time) 
            m0_min_response_time = response_time;
        if (response_time > m0_max_response_time) 
            m0_max_response_time = response_time;
        m0_avg_response_time = ((m0_avg_response_time * (m0_total_transactions - 1)) + response_time) / m0_total_transactions;
    endfunction
    
    // M0-specific transaction validation using package functions
    function bit is_valid_m0_transaction();
        // Check if slave ID is valid
        if (slave_id < AXI_SLAVE_0 || slave_id > AXI_SLAVE_6) return 0;
        
        // Check address alignment using package function
        if (trans_type == AXI_WRITE) {
            if (!is_address_aligned(M0_AWADDR, M0_AWSIZE)) return 0;
        } else {
            if (!is_address_aligned(M0_ARADDR, M0_ARSIZE)) return 0;
        }
        
        // Check burst length
        if (trans_type == AXI_WRITE) {
            if (M0_AWLEN < 0 || M0_AWLEN >= AXI_MAX_BURST_LENGTH) return 0;
        } else {
            if (M0_ARLEN < 0 || M0_ARLEN >= AXI_MAX_BURST_LENGTH) return 0;
        }
        
        return 1;
    endfunction
    
    // Get transaction info string
    function string get_transaction_info();
        if (trans_type == AXI_WRITE) 
            return $sformatf("M0->S%0d WRITE ID=%0d Len=%0d Addr=0x%08x Burst=%s", 
                            slave_id, M0_AWID, get_burst_length(M0_AWLEN), M0_AWADDR, 
                            M0_AWBURST.name());
        else 
            return $sformatf("M0->S%0d READ ID=%0d Len=%0d Addr=0x%08x Burst=%s", 
                            slave_id, M0_ARID, get_burst_length(M0_ARLEN), M0_ARADDR, 
                            M0_ARBURST.name());
    endfunction
    
    // M0-specific transaction info
    function string get_m0_transaction_info();
        string info = $sformatf("M0_TX%0d: ", m0_transaction_id);
        info = {info, get_transaction_info()};
        info = {info, $sformatf(" | Stats: W=%0d, R=%0d, Total=%0d", 
                                m0_write_transactions, m0_read_transactions, m0_total_transactions)};
        return info;
    endfunction
    
    // M0-specific statistics summary
    function string get_m0_statistics_summary();
        return $sformatf("M0 Statistics: Total=%0d, Writes=%0d, Reads=%0d, Bursts=%0d, Singles=%0d, Avg_Response=%0t, Min_Response=%0t, Max_Response=%0t",
                        m0_total_transactions, m0_write_transactions, m0_read_transactions, 
                        m0_burst_transactions, m0_single_transactions,
                        m0_avg_response_time, m0_min_response_time, m0_max_response_time);
    endfunction
    
    // UVM Field Macros for automatic copy, compare, print, etc.
    `uvm_object_utils_begin(M0_seq_item)
        `uvm_field_int(m0_transaction_id, UVM_ALL_ON)
        `uvm_field_enum(slave_id, axi_slave_id_e, UVM_ALL_ON)
        `uvm_field_enum(trans_type, axi_trans_type_e, UVM_ALL_ON)
        `uvm_field_int(M0_AWID, UVM_ALL_ON)
        `uvm_field_int(M0_AWADDR, UVM_ALL_ON)
        `uvm_field_int(M0_AWLEN, UVM_ALL_ON)
        `uvm_field_int(M0_AWSIZE, UVM_ALL_ON)
        `uvm_field_enum(M0_AWBURST, axi_burst_type_e, UVM_ALL_ON)
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
        `uvm_field_enum(M0_ARBURST, axi_burst_type_e, UVM_ALL_ON)
        `uvm_field_int(M0_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(M0_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(M0_ARPROT, UVM_ALL_ON)
        `uvm_field_int(M0_ARQOS, UVM_ALL_ON)
        `uvm_field_int(M0_ARREGION, UVM_ALL_ON)
        `uvm_field_int(M0_ARVALID, UVM_ALL_ON)
        `uvm_field_array_int(burst_data, UVM_ALL_ON)
        `uvm_field_array_int(burst_strobe, UVM_ALL_ON)
        `uvm_field_int(transaction_complete, UVM_ALL_ON)
        `uvm_field_int(start_time, UVM_ALL_ON)
        `uvm_field_int(end_time, UVM_ALL_ON)
        `uvm_field_int(m0_total_transactions, UVM_ALL_ON)
        `uvm_field_int(m0_write_transactions, UVM_ALL_ON)
        `uvm_field_int(m0_read_transactions, UVM_ALL_ON)
        `uvm_field_int(m0_burst_transactions, UVM_ALL_ON)
        `uvm_field_int(m0_single_transactions, UVM_ALL_ON)
        `uvm_field_int(m0_avg_response_time, UVM_ALL_ON)
        `uvm_field_int(m0_min_response_time, UVM_ALL_ON)
        `uvm_field_int(m0_max_response_time, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : M0_seq_item

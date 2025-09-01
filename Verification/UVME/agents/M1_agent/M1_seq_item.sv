//=============================================================================
// M1 Agent Sequence Item Class
//=============================================================================
// Standalone sequence item for Master 1 with full access to all slaves
// Extends uvm_sequence_item directly


import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the common AXI types package
import axi_common_types_pkg::*;

class M1_seq_item extends uvm_sequence_item;
    
    // M1-specific transaction identification
    rand int unsigned m1_transaction_id;  // Unique transaction ID for M1
    rand axi_slave_id_e slave_id;         // Target slave (0-6)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    rand bit [AXI_ID_WIDTH-1:0]     M1_AWID;           // Write address ID
    rand bit [AXI_ADDR_WIDTH-1:0]   M1_AWADDR;         // Write address
    rand bit [AXI_LEN_WIDTH-1:0]    M1_AWLEN;          // Burst length (0-15)
    rand bit [AXI_SIZE_WIDTH-1:0]   M1_AWSIZE;         // Burst size
    rand bit [AXI_BURST_WIDTH-1:0]  M1_AWBURST;        // Burst type
    rand bit [AXI_LOCK_WIDTH-1:0]   M1_AWLOCK;          // Lock type
    rand bit [AXI_CACHE_WIDTH-1:0]  M1_AWCACHE;        // Cache attributes
    rand bit [AXI_PROT_WIDTH-1:0]   M1_AWPROT;         // Protection attributes
    rand bit [AXI_QOS_WIDTH-1:0]    M1_AWQOS;          // Quality of service
    rand bit [AXI_REGION_WIDTH-1:0] M1_AWREGION;       // Region identifier
    rand bit                        M1_AWVALID;         // Write address valid
    bit                             M1_AWREADY;         // Write address ready (from slave)
    
    // ===== WRITE DATA CHANNEL (W) =====
    rand bit [AXI_DATA_WIDTH-1:0]   M1_WDATA;          // Write data
    rand bit [AXI_STRB_WIDTH-1:0]   M1_WSTRB;          // Write strobes
    rand bit                        M1_WLAST;          // Write last
    rand bit                        M1_WVALID;         // Write valid
    bit                             M1_WREADY;         // Write ready (from slave)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    bit [AXI_ID_WIDTH-1:0]          M1_BID;            // Write response ID (from slave)
    bit [AXI_RESP_WIDTH-1:0]        M1_BRESP;          // Write response (from slave)
    bit                             M1_BVALID;         // Write response valid (from slave)
    rand bit                        M1_BREADY;         // Write response ready
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    rand bit [AXI_ID_WIDTH-1:0]     M1_ARID;           // Read address ID
    rand bit [AXI_ADDR_WIDTH-1:0]   M1_ARADDR;         // Read address
    rand bit [AXI_LEN_WIDTH-1:0]    M1_ARLEN;          // Burst length (0-15)
    rand bit [AXI_SIZE_WIDTH-1:0]   M1_ARSIZE;         // Burst size
    rand bit [AXI_BURST_WIDTH-1:0]  M1_ARBURST;        // Burst type
    rand bit [AXI_LOCK_WIDTH-1:0]   M1_ARLOCK;          // Lock type
    rand bit [AXI_CACHE_WIDTH-1:0]  M1_ARCACHE;        // Cache attributes
    rand bit [AXI_PROT_WIDTH-1:0]   M1_ARPROT;         // Protection attributes
    rand bit [AXI_QOS_WIDTH-1:0]    M1_ARQOS;          // Quality of service
    rand bit [AXI_REGION_WIDTH-1:0] M1_ARREGION;       // Region identifier
    rand bit                        M1_ARVALID;         // Read address valid
    bit                             M1_ARREADY;         // Read address ready (from slave)
    
    // ===== READ DATA CHANNEL (R) =====
    bit [AXI_ID_WIDTH-1:0]          M1_RID;            // Read ID (from slave)
    bit [AXI_DATA_WIDTH-1:0]        M1_RDATA;          // Read data (from slave)
    bit [AXI_RESP_WIDTH-1:0]        M1_RRESP;          // Read response (from slave)
    bit                             M1_RLAST;          // Read last (from slave)
    bit                             M1_RVALID;         // Read valid (from slave)
    rand bit                        M1_RREADY;         // Read ready
    
    // ===== BURST DATA ARRAYS =====
    rand bit [AXI_DATA_WIDTH-1:0]   burst_data[];   // Array for burst data
    rand bit [AXI_STRB_WIDTH-1:0]   burst_strobe[]; // Array for burst strobes
    
    // ===== STATUS AND TIMING =====
    bit                             transaction_complete;
    time                            start_time;
    time                            end_time;
    
    // M1-specific transaction statistics
    int unsigned m1_total_transactions;
    int unsigned m1_write_transactions;
    int unsigned m1_read_transactions;
    int unsigned m1_burst_transactions;
    int unsigned m1_single_transactions;
    
    // M1-specific performance metrics
    time m1_avg_response_time;
    time m1_min_response_time;
    time m1_max_response_time;
    
    // Constraints
    constraint slave_id_c {
        slave_id inside {AXI_SLAVE_0, AXI_SLAVE_1, AXI_SLAVE_2, AXI_SLAVE_3, 
                        AXI_SLAVE_4, AXI_SLAVE_5, AXI_SLAVE_6};  // M1 can access all slaves
    }
    
    constraint M1_awid_c {
        M1_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};  // Full ID range
    }
    
    constraint M1_arid_c {
        M1_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};  // Full ID range
    }
    
    constraint M1_awlen_c {
        M1_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};  // Burst length 1-16
    }
    
    constraint M1_arlen_c {
        M1_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};  // Burst length 1-16
    }
    
    constraint M1_awsize_c {
        M1_AWSIZE inside {[0:AXI_SIZE_WIDTH-1]};  // Transfer size 1, 2, 4, 8, 16, 32, 64, 128 bytes
    }
    
    constraint M1_arsize_c {
        M1_ARSIZE inside {[0:AXI_SIZE_WIDTH-1]};  // Transfer size 1, 2, 4, 8, 16, 32, 64, 128 bytes
    }
    
    constraint M1_awburst_c {
        M1_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};  // All burst types
    }
    
    constraint M1_arburst_c {
        M1_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};  // All burst types
    }
    
    constraint M1_awlock_c {
        M1_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};  // All lock types
    }
    
    constraint M1_arlock_c {
        M1_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};  // All lock types
    }
    
    constraint M1_awcache_c {
        M1_AWCACHE inside {[0:(1<<AXI_CACHE_WIDTH)-1]}; // All cache combinations
    }
    
    constraint M1_arcache_c {
        M1_ARCACHE inside {[0:(1<<AXI_CACHE_WIDTH)-1]}; // All cache combinations
    }
    
    constraint M1_awprot_c {
        M1_AWPROT inside {[0:(1<<AXI_PROT_WIDTH)-1]};  // All protection combinations
    }
    
    constraint M1_arprot_c {
        M1_ARPROT inside {[0:(1<<AXI_PROT_WIDTH)-1]};  // All protection combinations
    }
    
    constraint M1_awqos_c {
        M1_AWQOS inside {[0:(1<<AXI_QOS_WIDTH)-1]};  // All QoS levels
    }
    
    constraint M1_arqos_c {
        M1_ARQOS inside {[0:(1<<AXI_QOS_WIDTH)-1]};  // All QoS levels
    }
    
    constraint M1_awregion_c {
        M1_AWREGION inside {[0:(1<<AXI_REGION_WIDTH)-1]}; // All region identifiers
    }
    
    constraint M1_arregion_c {
        M1_ARREGION inside {[0:(1<<AXI_REGION_WIDTH)-1]}; // All region identifiers
    }
    
    // Address range constraints based on slave using package constants
    constraint address_range_c {
        if (slave_id == AXI_SLAVE_0) {
            if (trans_type == AXI_WRITE) {
                M1_AWADDR inside {[SLAVE_0_BASE_ADDR:SLAVE_0_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M1_ARADDR inside {[SLAVE_0_BASE_ADDR:SLAVE_0_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_1) {
            if (trans_type == AXI_WRITE) {
                M1_AWADDR inside {[SLAVE_1_BASE_ADDR:SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M1_ARADDR inside {[SLAVE_1_BASE_ADDR:SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_2) {
            if (trans_type == AXI_WRITE) {
                M1_AWADDR inside {[SLAVE_2_BASE_ADDR:SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M1_ARADDR inside {[SLAVE_2_BASE_ADDR:SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_3) {
            if (trans_type == AXI_WRITE) {
                M1_AWADDR inside {[SLAVE_3_BASE_ADDR:SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M1_ARADDR inside {[SLAVE_3_BASE_ADDR:SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_4) {
            if (trans_type == AXI_WRITE) {
                M1_AWADDR inside {[SLAVE_4_BASE_ADDR:SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M1_ARADDR inside {[SLAVE_4_BASE_ADDR:SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_5) {
            if (trans_type == AXI_WRITE) {
                M1_AWADDR inside {[SLAVE_5_BASE_ADDR:SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M1_ARADDR inside {[SLAVE_5_BASE_ADDR:SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        } else if (slave_id == AXI_SLAVE_6) {
            if (trans_type == AXI_WRITE) {
                M1_AWADDR inside {[SLAVE_6_BASE_ADDR:SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            } else {
                M1_ARADDR inside {[SLAVE_6_BASE_ADDR:SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            }
        }
    }
    
    // Address alignment constraints using package function
    constraint address_alignment_c {
        if (trans_type == AXI_WRITE) {
            M1_AWADDR % (1 << M1_AWSIZE) == 0;
        } else {
            M1_ARADDR % (1 << M1_ARSIZE) == 0;
        }
    }
    
    // Burst data array size constraint
    constraint burst_data_size_c {
        if (trans_type == AXI_WRITE) {
            burst_data.size() == get_burst_length(M1_AWLEN);
            burst_strobe.size() == get_burst_length(M1_AWLEN);
        } else {
            burst_data.size() == get_burst_length(M1_ARLEN);
        }
    }
    
    // Constructor
    function new(string name = "M1_seq_item");
        super.new(name);
        m1_transaction_id = 0;
        m1_total_transactions = 0;
        m1_write_transactions = 0;
        m1_read_transactions = 0;
        m1_burst_transactions = 0;
        m1_single_transactions = 0;
        m1_avg_response_time = 0;
        m1_min_response_time = 0;
        m1_max_response_time = 0;
        transaction_complete = 0;
        start_time = 0;
        end_time = 0;
        
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
    endfunction
    
    // M1-specific methods
    
    // Set M1 transaction ID
    function void set_m1_transaction_id(int id);
        m1_transaction_id = id;
    endfunction
    
    // Get M1 transaction ID
    function int get_m1_transaction_id();
        return m1_transaction_id;
    endfunction
    
    // Set slave ID
    function void set_slave_id(axi_slave_id_e id);
        slave_id = id;
    endfunction
    
    // Set transaction type
    function void set_transaction_type(axi_trans_type_e type);
        trans_type = type;
        if (type == AXI_WRITE) begin
            m1_write_transactions++;
        end else begin
            m1_read_transactions++;
        end
        m1_total_transactions++;
    endfunction
    
    // M1-specific slave selection methods
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
        if (trans_type == AXI_WRITE) begin
            M1_AWLEN = set_axi_length(length);  // Use package function
            M1_AWBURST = burst;
            M1_AWSIZE = $clog2(size);
        end else begin
            M1_ARLEN = set_axi_length(length);  // Use package function
            M1_ARBURST = burst;
            M1_ARSIZE = $clog2(size);
        end
        
        // Resize arrays
        if (trans_type == AXI_WRITE) begin
            burst_data = new[length];
            burst_strobe = new[length];
        end else begin
            burst_data = new[length];
        end
    endfunction
    
    // Set address
    function void set_address(bit [AXI_ADDR_WIDTH-1:0] addr);
        if (trans_type == AXI_WRITE) begin
            M1_AWADDR = addr;
        end else begin
            M1_ARADDR = addr;
        end
    endfunction
    
    // Set burst data
    function void set_burst_data(int index, bit [AXI_DATA_WIDTH-1:0] data);
        if (index < burst_data.size()) begin
            burst_data[index] = data;
        end
    endfunction
    
    // Set burst strobe
    function void set_burst_strobe(int index, bit [AXI_STRB_WIDTH-1:0] strobe);
        if (index < burst_strobe.size()) begin
            burst_strobe[index] = strobe;
        end
    endfunction
    
    // M1-specific transaction type methods
    function void set_write_transaction();
        set_transaction_type(AXI_WRITE);
    endfunction
    
    function void set_read_transaction();
        set_transaction_type(AXI_READ);
    endfunction
    
    // M1-specific burst configuration methods
    function void set_single_transfer();
        if (trans_type == AXI_WRITE) begin
            M1_AWLEN = 0;  // Single transfer
            M1_AWBURST = AXI_INCR;
        end else begin
            M1_ARLEN = 0;  // Single transfer
            M1_ARBURST = AXI_INCR;
        end
        m1_single_transactions++;
    endfunction
    
    function void set_burst_transfer(int length, axi_burst_type_e burst_type);
        if (length > 1) begin
            set_burst_parameters(length, burst_type, 4); // Default 4-byte transfers
            m1_burst_transactions++;
        end else begin
            set_single_transfer();
        end
    endfunction
    
    // M1-specific address generation methods using package constants
    function void set_random_address_in_slave_range(axi_slave_id_e slave);
        set_slave_id(slave);
        if (slave == AXI_SLAVE_0) begin
            if (trans_type == AXI_WRITE) M1_AWADDR = $urandom_range(SLAVE_0_BASE_ADDR, SLAVE_0_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M1_ARADDR = $urandom_range(SLAVE_0_BASE_ADDR, SLAVE_0_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end else if (slave == AXI_SLAVE_1) begin
            if (trans_type == AXI_WRITE) M1_AWADDR = $urandom_range(SLAVE_1_BASE_ADDR, SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M1_ARADDR = $urandom_range(SLAVE_1_BASE_ADDR, SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end else if (slave == AXI_SLAVE_2) begin
            if (trans_type == AXI_WRITE) M1_AWADDR = $urandom_range(SLAVE_2_BASE_ADDR, SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M1_ARADDR = $urandom_range(SLAVE_2_BASE_ADDR, SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end else if (slave == AXI_SLAVE_3) begin
            if (trans_type == AXI_WRITE) M1_AWADDR = $urandom_range(SLAVE_3_BASE_ADDR, SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M1_ARADDR = $urandom_range(SLAVE_3_BASE_ADDR, SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end else if (slave == AXI_SLAVE_4) begin
            if (trans_type == AXI_WRITE) M1_AWADDR = $urandom_range(SLAVE_4_BASE_ADDR, SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M1_ARADDR = $urandom_range(SLAVE_4_BASE_ADDR, SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end else if (slave == AXI_SLAVE_5) begin
            if (trans_type == AXI_WRITE) M1_AWADDR = $urandom_range(SLAVE_5_BASE_ADDR, SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M1_ARADDR = $urandom_range(SLAVE_5_BASE_ADDR, SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end else if (slave == AXI_SLAVE_6) begin
            if (trans_type == AXI_WRITE) M1_AWADDR = $urandom_range(SLAVE_6_BASE_ADDR, SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M1_ARADDR = $urandom_range(SLAVE_6_BASE_ADDR, SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end
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
    
    // M1-specific performance tracking
    function void update_performance_metrics(time response_time);
        if (m1_min_response_time == 0 || response_time < m1_min_response_time) begin
            m1_min_response_time = response_time;
        end
        if (response_time > m1_max_response_time) begin
            m1_max_response_time = response_time;
        end
        m1_avg_response_time = ((m1_avg_response_time * (m1_total_transactions - 1)) + response_time) / m1_total_transactions;
    endfunction
    
    // M1-specific transaction validation using package functions
    function bit is_valid_m1_transaction();
        // Check if slave ID is valid
        if (slave_id < AXI_SLAVE_0 || slave_id > AXI_SLAVE_6) return 0;
        
        // Check address alignment using package function
        if (trans_type == AXI_WRITE) begin
            if (!is_address_aligned(M1_AWADDR, M1_AWSIZE)) return 0;
        end else begin
            if (!is_address_aligned(M1_ARADDR, M1_ARSIZE)) return 0;
        end
        
        // Check burst length
        if (trans_type == AXI_WRITE) begin
            if (M1_AWLEN < 0 || M1_AWLEN >= AXI_MAX_BURST_LENGTH) return 0;
        end else begin
            if (M1_ARLEN < 0 || M1_ARLEN >= AXI_MAX_BURST_LENGTH) return 0;
        end
        
        return 1;
    endfunction
    
    // Get transaction info string
    function string get_transaction_info();
        if (trans_type == AXI_WRITE) begin
            return $sformatf("M1->S%0d WRITE ID=%0d Len=%0d Addr=0x%08x Burst=%s", 
                            slave_id, M1_AWID, get_burst_length(M1_AWLEN), M1_AWADDR, 
                            M1_AWBURST.name());
        end else begin
            return $sformatf("M1->S%0d READ ID=%0d Len=%0d Addr=0x%08x Burst=%s", 
                            slave_id, M1_ARID, get_burst_length(M1_ARLEN), M1_ARADDR, 
                            M1_ARBURST.name());
        end
    endfunction
    
    // M1-specific transaction info
    function string get_m1_transaction_info();
        string info = $sformatf("M1_TX%0d: ", m1_transaction_id);
        info = {info, get_transaction_info()};
        info = {info, $sformatf(" | Stats: W=%0d, R=%0d, Total=%0d", 
                                m1_write_transactions, m1_read_transactions, m1_total_transactions)};
        return info;
    endfunction
    
    // M1-specific statistics summary
    function string get_m1_statistics_summary();
        return $sformatf("M1 Statistics: Total=%0d, Writes=%0d, Reads=%0d, Bursts=%0d, Singles=%0d, Avg_Response=%0t, Min_Response=%0t, Max_Response=%0t",
                        m1_total_transactions, m1_write_transactions, m1_read_transactions, 
                        m1_burst_transactions, m1_single_transactions,
                        m1_avg_response_time, m1_min_response_time, m1_max_response_time);
    endfunction
    
    // UVM Field Macros for automatic copy, compare, print, etc.
    `uvm_object_utils_begin(M1_seq_item)
        `uvm_field_int(m1_transaction_id, UVM_ALL_ON)
        `uvm_field_enum(slave_id, axi_slave_id_e, UVM_ALL_ON)
        `uvm_field_enum(trans_type, axi_trans_type_e, UVM_ALL_ON)
        `uvm_field_int(M1_AWID, UVM_ALL_ON)
        `uvm_field_int(M1_AWADDR, UVM_ALL_ON)
        `uvm_field_int(M1_AWLEN, UVM_ALL_ON)
        `uvm_field_int(M1_AWSIZE, UVM_ALL_ON)
        `uvm_field_enum(M1_AWBURST, axi_burst_type_e, UVM_ALL_ON)
        `uvm_field_int(M1_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(M1_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(M1_AWPROT, UVM_ALL_ON)
        `uvm_field_int(M1_AWQOS, UVM_ALL_ON)
        `uvm_field_int(M1_AWREGION, UVM_ALL_ON)
        `uvm_field_int(M1_AWVALID, UVM_ALL_ON)
        `uvm_field_int(M1_WDATA, UVM_ALL_ON)
        `uvm_field_int(M1_WSTRB, UVM_ALL_ON)
        `uvm_field_int(M1_WLAST, UVM_ALL_ON)
        `uvm_field_int(M1_WVALID, UVM_ALL_ON)
        `uvm_field_int(M1_ARID, UVM_ALL_ON)
        `uvm_field_int(M1_ARADDR, UVM_ALL_ON)
        `uvm_field_int(M1_ARLEN, UVM_ALL_ON)
        `uvm_field_int(M1_ARSIZE, UVM_ALL_ON)
        `uvm_field_enum(M1_ARBURST, axi_burst_type_e, UVM_ALL_ON)
        `uvm_field_int(M1_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(M1_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(M1_ARPROT, UVM_ALL_ON)
        `uvm_field_int(M1_ARQOS, UVM_ALL_ON)
        `uvm_field_int(M1_ARREGION, UVM_ALL_ON)
        `uvm_field_int(M1_ARVALID, UVM_ALL_ON)
        `uvm_field_array_int(burst_data, UVM_ALL_ON)
        `uvm_field_array_int(burst_strobe, UVM_ALL_ON)
        `uvm_field_int(transaction_complete, UVM_ALL_ON)
        `uvm_field_int(start_time, UVM_ALL_ON)
        `uvm_field_int(end_time, UVM_ALL_ON)
        `uvm_field_int(m1_total_transactions, UVM_ALL_ON)
        `uvm_field_int(m1_write_transactions, UVM_ALL_ON)
        `uvm_field_int(m1_read_transactions, UVM_ALL_ON)
        `uvm_field_int(m1_burst_transactions, UVM_ALL_ON)
        `uvm_field_int(m1_single_transactions, UVM_ALL_ON)
        `uvm_field_int(m1_avg_response_time, UVM_ALL_ON)
        `uvm_field_int(m1_min_response_time, UVM_ALL_ON)
        `uvm_field_int(m1_max_response_time, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : M1_seq_item

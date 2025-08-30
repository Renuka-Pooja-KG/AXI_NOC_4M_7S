//=============================================================================
// M2 Agent Sequence Item Class
//=============================================================================
// Standalone sequence item for Master 2 with full access to all slaves
// Extends uvm_sequence_item directly


import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the common AXI types package
import axi_common_types_pkg::*;

class M2_seq_item extends uvm_sequence_item;
    
    // M2-specific transaction identification
    rand int unsigned m2_transaction_id;  // Unique transaction ID for M2
    rand axi_slave_id_e slave_id;         // Target slave (0-6)
    
    // Transaction type
    rand axi_trans_type_e trans_type;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    rand bit [AXI_ID_WIDTH-1:0]     M2_AWID;           // Write address ID
    rand bit [AXI_ADDR_WIDTH-1:0]   M2_AWADDR;         // Write address
    rand bit [AXI_LEN_WIDTH-1:0]    M2_AWLEN;          // Burst length (0-15)
    rand bit [AXI_SIZE_WIDTH-1:0]   M2_AWSIZE;         // Burst size
    rand bit [AXI_BURST_WIDTH-1:0]  M2_AWBURST;        // Burst type
    rand bit [AXI_LOCK_WIDTH-1:0]   M2_AWLOCK;          // Lock type
    rand bit [AXI_CACHE_WIDTH-1:0]  M2_AWCACHE;        // Cache attributes
    rand bit [AXI_PROT_WIDTH-1:0]   M2_AWPROT;         // Protection attributes
    rand bit [AXI_QOS_WIDTH-1:0]    M2_AWQOS;          // Quality of service
    rand bit [AXI_REGION_WIDTH-1:0] M2_AWREGION;       // Region identifier
    rand bit                        M2_AWVALID;         // Write address valid
    bit                             M2_AWREADY;         // Write address ready (from slave)
    
    // ===== WRITE DATA CHANNEL (W) =====
    rand bit [AXI_DATA_WIDTH-1:0]   M2_WDATA;          // Write data
    rand bit [AXI_STRB_WIDTH-1:0]   M2_WSTRB;          // Write strobes
    rand bit                        M2_WLAST;          // Write last
    rand bit                        M2_WVALID;         // Write valid
    bit                             M2_WREADY;         // Write ready (from slave)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    bit [AXI_ID_WIDTH-1:0]          M2_BID;            // Write response ID (from slave)
    bit [AXI_RESP_WIDTH-1:0]        M2_BRESP;          // Write response (from slave)
    bit                             M2_BVALID;         // Write response valid (from slave)
    rand bit                        M2_BREADY;         // Write response ready
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    rand bit [AXI_ID_WIDTH-1:0]     M2_ARID;           // Read address ID
    rand bit [AXI_ADDR_WIDTH-1:0]   M2_ARADDR;         // Read address
    rand bit [AXI_LEN_WIDTH-1:0]    M2_ARLEN;          // Burst length (0-15)
    rand bit [AXI_SIZE_WIDTH-1:0]   M2_ARSIZE;         // Burst size
    rand bit [AXI_BURST_WIDTH-1:0]  M2_ARBURST;        // Burst type
    rand bit [AXI_LOCK_WIDTH-1:0]   M2_ARLOCK;          // Lock type
    rand bit [AXI_CACHE_WIDTH-1:0]  M2_ARCACHE;        // Cache attributes
    rand bit [AXI_PROT_WIDTH-1:0]   M2_ARPROT;         // Protection attributes
    rand bit [AXI_QOS_WIDTH-1:0]    M2_ARQOS;          // Quality of service
    rand bit [AXI_REGION_WIDTH-1:0] M2_ARREGION;       // Region identifier
    rand bit                        M2_ARVALID;         // Read address valid
    bit                             M2_ARREADY;         // Read address ready (from slave)
    
    // ===== READ DATA CHANNEL (R) =====
    bit [AXI_ID_WIDTH-1:0]          M2_RID;            // Read ID (from slave)
    bit [AXI_DATA_WIDTH-1:0]        M2_RDATA;          // Read data (from slave)
    bit [AXI_RESP_WIDTH-1:0]        M2_RRESP;          // Read response (from slave)
    bit                             M2_RLAST;          // Read last (from slave)
    bit                             M2_RVALID;         // Read valid (from slave)
    rand bit                        M2_RREADY;         // Read ready
    
    // ===== BURST DATA ARRAYS =====
    rand bit [AXI_DATA_WIDTH-1:0]   burst_data[];   // Array for burst data
    rand bit [AXI_STRB_WIDTH-1:0]   burst_strobe[]; // Array for burst strobes
    
    // ===== STATUS AND TIMING =====
    bit                             transaction_complete;
    time                            start_time;
    time                            end_time;
    
    // M2-specific transaction statistics
    int unsigned m2_total_transactions;
    int unsigned m2_write_transactions;
    int unsigned m2_read_transactions;
    int unsigned m2_burst_transactions;
    int unsigned m2_single_transactions;
    
    // M2-specific performance metrics
    time m2_avg_response_time;
    time m2_min_response_time;
    time m2_max_response_time;
    
    // Constraints
    constraint slave_id_c {
        slave_id inside {AXI_SLAVE_0, AXI_SLAVE_1, AXI_SLAVE_2, AXI_SLAVE_3, 
                        AXI_SLAVE_4, AXI_SLAVE_5, AXI_SLAVE_6};  // M2 can access all slaves
    }
    
    constraint M2_awid_c {
        M2_AWID inside {[0:(1<<AXI_ID_WIDTH)-1]};  // Full ID range
    }
    
    constraint M2_arid_c {
        M2_ARID inside {[0:(1<<AXI_ID_WIDTH)-1]};  // Full ID range
    }
    
    constraint M2_awlen_c {
        M2_AWLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};  // Burst length 1-16
    }
    
    constraint M2_arlen_c {
        M2_ARLEN inside {[0:AXI_MAX_BURST_LENGTH-1]};  // Burst length 1-16
    }
    
    constraint M2_awsize_c {
        M2_AWSIZE inside {[0:AXI_SIZE_WIDTH-1]};  // Transfer size 1, 2, 4, 8, 16, 32, 64, 128 bytes
    }
    
    constraint M2_arsize_c {
        M2_ARSIZE inside {[0:AXI_SIZE_WIDTH-1]};  // Transfer size 1, 2, 4, 8, 16, 32, 64, 128 bytes
    }
    
    constraint M2_awburst_c {
        M2_AWBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};  // All burst types
    }
    
    constraint M2_arburst_c {
        M2_ARBURST inside {AXI_FIXED, AXI_INCR, AXI_WRAP};  // All burst types
    }
    
    constraint M2_awlock_c {
        M2_AWLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};  // All lock types
    }
    
    constraint M2_arlock_c {
        M2_ARLOCK inside {AXI_NORMAL, AXI_EXCLUSIVE};  // All lock types
    }
    
    constraint M2_awcache_c {
        M2_AWCACHE inside {[0:(1<<AXI_CACHE_WIDTH)-1]}; // All cache combinations
    }
    
    constraint M2_arcache_c {
        M2_ARCACHE inside {[0:(1<<AXI_CACHE_WIDTH)-1]}; // All cache combinations
    }
    
    constraint M2_awprot_c {
        M2_AWPROT inside {[0:(1<<AXI_PROT_WIDTH)-1]};  // All protection combinations
    }
    
    constraint M2_arprot_c {
        M2_ARPROT inside {[0:(1<<AXI_PROT_WIDTH)-1]};  // All protection combinations
    }
    
    constraint M2_awqos_c {
        M2_AWQOS inside {[0:(1<<AXI_QOS_WIDTH)-1]};  // All QoS levels
    }
    
    constraint M2_arqos_c {
        M2_ARQOS inside {[0:(1<<AXI_QOS_WIDTH)-1]};  // All QoS levels
    }
    
    constraint M2_awregion_c {
        M2_AWREGION inside {[0:(1<<AXI_REGION_WIDTH)-1]}; // All region identifiers
    }
    
    constraint M2_arregion_c {
        M2_ARREGION inside {[0:(1<<AXI_REGION_WIDTH)-1]}; // All region identifiers
    }
    
    // Address range constraints based on slave using package constants
    constraint address_range_c {
        if (slave_id == AXI_SLAVE_0) begin
            if (trans_type == AXI_WRITE) M2_AWADDR inside {[SLAVE_0_BASE_ADDR:SLAVE_0_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            else M2_ARADDR inside {[SLAVE_0_BASE_ADDR:SLAVE_0_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
        end else if (slave_id == AXI_SLAVE_1) begin
            if (trans_type == AXI_WRITE) M2_AWADDR inside {[SLAVE_1_BASE_ADDR:SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            else M2_ARADDR inside {[SLAVE_1_BASE_ADDR:SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
        end else if (slave_id == AXI_SLAVE_2) begin
            if (trans_type == AXI_WRITE) M2_AWADDR inside {[SLAVE_2_BASE_ADDR:SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            else M2_ARADDR inside {[SLAVE_2_BASE_ADDR:SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
        end else if (slave_id == AXI_SLAVE_3) begin
            if (trans_type == AXI_WRITE) M2_AWADDR inside {[SLAVE_3_BASE_ADDR:SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            else M2_ARADDR inside {[SLAVE_3_BASE_ADDR:SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
        end else if (slave_id == AXI_SLAVE_4) begin
            if (trans_type == AXI_WRITE) M2_AWADDR inside {[SLAVE_4_BASE_ADDR:SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            else M2_ARADDR inside {[SLAVE_4_BASE_ADDR:SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
        end else if (slave_id == AXI_SLAVE_5) begin
            if (trans_type == AXI_WRITE) M2_AWADDR inside {[SLAVE_5_BASE_ADDR:SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            else M2_ARADDR inside {[SLAVE_5_BASE_ADDR:SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
        end else if (slave_id == AXI_SLAVE_6) begin
            if (trans_type == AXI_WRITE) M2_AWADDR inside {[SLAVE_6_BASE_ADDR:SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
            else M2_ARADDR inside {[SLAVE_6_BASE_ADDR:SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1]};
        end
    }
    
    // Address alignment constraints using package function
    constraint address_alignment_c {
        if (trans_type == AXI_WRITE) begin
            M2_AWADDR % (1 << M2_AWSIZE) == 0;
        end else begin
            M2_ARADDR % (1 << M2_ARSIZE) == 0;
        end
    }
    
    // Burst data array size constraint
    constraint burst_data_size_c {
        if (trans_type == AXI_WRITE) begin
            burst_data.size() == get_burst_length(M2_AWLEN);
            burst_strobe.size() == get_burst_length(M2_AWLEN);
        end else begin
            burst_data.size() == get_burst_length(M2_ARLEN);
        end
    }
    
    // Constructor
    function new(string name = "M2_seq_item");
        super.new(name);
        m2_transaction_id = 0;
        m2_total_transactions = 0;
        m2_write_transactions = 0;
        m2_read_transactions = 0;
        m2_burst_transactions = 0;
        m2_single_transactions = 0;
        m2_avg_response_time = 0;
        m2_min_response_time = 0;
        m2_max_response_time = 0;
        transaction_complete = 0;
        start_time = 0;
        end_time = 0;
        
        // Initialize arrays
        burst_data = new[1];
        burst_strobe = new[1];
    endfunction
    
    // M2-specific methods
    
    // Set M2 transaction ID
    function void set_m2_transaction_id(int id);
        m2_transaction_id = id;
    endfunction
    
    // Get M2 transaction ID
    function int get_m2_transaction_id();
        return m2_transaction_id;
    endfunction
    
    // Set slave ID
    function void set_slave_id(axi_slave_id_e id);
        slave_id = id;
    endfunction
    
    // Set transaction type
    function void set_transaction_type(axi_trans_type_e type);
        trans_type = type;
        if (type == AXI_WRITE) begin
            m2_write_transactions++;
        end else begin
            m2_read_transactions++;
        end
        m2_total_transactions++;
    endfunction
    
    // M2-specific slave selection methods
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
            M2_AWLEN = set_axi_length(length);  // Use package function
            M2_AWBURST = burst;
            M2_AWSIZE = $clog2(size);
        end else begin
            M2_ARLEN = set_axi_length(length);  // Use package function
            M2_ARBURST = burst;
            M2_ARSIZE = $clog2(size);
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
            M2_AWADDR = addr;
        end else begin
            M2_ARADDR = addr;
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
    
    // M2-specific transaction type methods
    function void set_write_transaction();
        set_transaction_type(AXI_WRITE);
    endfunction
    
    function void set_read_transaction();
        set_transaction_type(AXI_READ);
    endfunction
    
    // M2-specific burst configuration methods
    function void set_single_transfer();
        if (trans_type == AXI_WRITE) begin
            M2_AWLEN = 0;  // Single transfer
            M2_AWBURST = AXI_INCR;
        end else begin
            M2_ARLEN = 0;  // Single transfer
            M2_ARBURST = AXI_INCR;
        end
        m2_single_transactions++;
    endfunction
    
    function void set_burst_transfer(int length, axi_burst_type_e burst_type);
        if (length > 1) begin
            set_burst_parameters(length, burst_type, 4); // Default 4-byte transfers
            m2_burst_transactions++;
        end else begin
            set_single_transfer();
        end
    endfunction
    
    // M2-specific address generation methods using package constants
    function void set_random_address_in_slave_range(axi_slave_id_e slave);
        set_slave_id(slave);
        if (slave == AXI_SLAVE_0) begin
            if (trans_type == AXI_WRITE) M2_AWADDR = $urandom_range(SLAVE_0_BASE_ADDR, SLAVE_0_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M2_ARADDR = $urandom_range(SLAVE_0_BASE_ADDR, SLAVE_0_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end else if (slave == AXI_SLAVE_1) begin
            if (trans_type == AXI_WRITE) M2_AWADDR = $urandom_range(SLAVE_1_BASE_ADDR, SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M2_ARADDR = $urandom_range(SLAVE_1_BASE_ADDR, SLAVE_1_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end else if (slave == AXI_SLAVE_2) begin
            if (trans_type == AXI_WRITE) M2_AWADDR = $urandom_range(SLAVE_2_BASE_ADDR, SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M2_ARADDR = $urandom_range(SLAVE_2_BASE_ADDR, SLAVE_2_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end else if (slave == AXI_SLAVE_3) begin
            if (trans_type == AXI_WRITE) M2_AWADDR = $urandom_range(SLAVE_3_BASE_ADDR, SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M2_ARADDR = $urandom_range(SLAVE_3_BASE_ADDR, SLAVE_3_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end else if (slave == AXI_SLAVE_4) begin
            if (trans_type == AXI_WRITE) M2_AWADDR = $urandom_range(SLAVE_4_BASE_ADDR, SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M2_ARADDR = $urandom_range(SLAVE_4_BASE_ADDR, SLAVE_4_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end else if (slave == AXI_SLAVE_5) begin
            if (trans_type == AXI_WRITE) M2_AWADDR = $urandom_range(SLAVE_5_BASE_ADDR, SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M2_ARADDR = $urandom_range(SLAVE_5_BASE_ADDR, SLAVE_5_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
        end else if (slave == AXI_SLAVE_6) begin
            if (trans_type == AXI_WRITE) M2_AWADDR = $urandom_range(SLAVE_6_BASE_ADDR, SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
            else M2_ARADDR = $urandom_range(SLAVE_6_BASE_ADDR, SLAVE_6_BASE_ADDR+SLAVE_ADDR_RANGE_SIZE-1);
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
    
    // M2-specific performance tracking
    function void update_performance_metrics(time response_time);
        if (m2_min_response_time == 0 || response_time < m2_min_response_time) begin
            m2_min_response_time = response_time;
        end
        if (response_time > m2_max_response_time) begin
            m2_max_response_time = response_time;
        end
        m2_avg_response_time = ((m2_avg_response_time * (m2_total_transactions - 1)) + response_time) / m2_total_transactions;
    endfunction
    
    // M2-specific transaction validation using package functions
    function bit is_valid_m2_transaction();
        // Check if slave ID is valid
        if (slave_id < AXI_SLAVE_0 || slave_id > AXI_SLAVE_6) return 0;
        
        // Check address alignment using package function
        if (trans_type == AXI_WRITE) begin
            if (!is_address_aligned(M2_AWADDR, M2_AWSIZE)) return 0;
        end else begin
            if (!is_address_aligned(M2_ARADDR, M2_ARSIZE)) return 0;
        end
        
        // Check burst length
        if (trans_type == AXI_WRITE) begin
            if (M2_AWLEN < 0 || M2_AWLEN >= AXI_MAX_BURST_LENGTH) return 0;
        end else begin
            if (M2_ARLEN < 0 || M2_ARLEN >= AXI_MAX_BURST_LENGTH) return 0;
        end
        
        return 1;
    endfunction
    
    // Get transaction info string
    function string get_transaction_info();
        if (trans_type == AXI_WRITE) begin
            return $sformatf("M2->S%0d WRITE ID=%0d Len=%0d Addr=0x%08x Burst=%s", 
                            slave_id, M2_AWID, get_burst_length(M2_AWLEN), M2_AWADDR, 
                            M2_AWBURST.name());
        end else begin
            return $sformatf("M2->S%0d READ ID=%0d Len=%0d Addr=0x%08x Burst=%s", 
                            slave_id, M2_ARID, get_burst_length(M2_ARLEN), M2_ARADDR, 
                            M2_ARBURST.name());
        end
    endfunction
    
    // M2-specific transaction info
    function string get_m2_transaction_info();
        string info = $sformatf("M2_TX%0d: ", m2_transaction_id);
        info = {info, get_transaction_info()};
        info = {info, $sformatf(" | Stats: W=%0d, R=%0d, Total=%0d", 
                                m2_write_transactions, m2_read_transactions, m2_total_transactions)};
        return info;
    endfunction
    
    // M2-specific statistics summary
    function string get_m2_statistics_summary();
        return $sformatf("M2 Statistics: Total=%0d, Writes=%0d, Reads=%0d, Bursts=%0d, Singles=%0d, Avg_Response=%0t, Min_Response=%0t, Max_Response=%0t",
                        m2_total_transactions, m2_write_transactions, m2_read_transactions, 
                        m2_burst_transactions, m2_single_transactions,
                        m2_avg_response_time, m2_min_response_time, m2_max_response_time);
    endfunction
    
    // UVM Field Macros for automatic copy, compare, print, etc.
    `uvm_object_utils_begin(M2_seq_item)
        `uvm_field_int(m2_transaction_id, UVM_ALL_ON)
        `uvm_field_enum(slave_id, axi_slave_id_e, UVM_ALL_ON)
        `uvm_field_enum(trans_type, axi_trans_type_e, UVM_ALL_ON)
        `uvm_field_int(M2_AWID, UVM_ALL_ON)
        `uvm_field_int(M2_AWADDR, UVM_ALL_ON)
        `uvm_field_int(M2_AWLEN, UVM_ALL_ON)
        `uvm_field_int(M2_AWSIZE, UVM_ALL_ON)
        `uvm_field_enum(M2_AWBURST, axi_burst_type_e, UVM_ALL_ON)
        `uvm_field_int(M2_AWLOCK, UVM_ALL_ON)
        `uvm_field_int(M2_AWCACHE, UVM_ALL_ON)
        `uvm_field_int(M2_AWPROT, UVM_ALL_ON)
        `uvm_field_int(M2_AWQOS, UVM_ALL_ON)
        `uvm_field_int(M2_AWREGION, UVM_ALL_ON)
        `uvm_field_int(M2_AWVALID, UVM_ALL_ON)
        `uvm_field_int(M2_WDATA, UVM_ALL_ON)
        `uvm_field_int(M2_WSTRB, UVM_ALL_ON)
        `uvm_field_int(M2_WLAST, UVM_ALL_ON)
        `uvm_field_int(M2_WVALID, UVM_ALL_ON)
        `uvm_field_int(M2_ARID, UVM_ALL_ON)
        `uvm_field_int(M2_ARADDR, UVM_ALL_ON)
        `uvm_field_int(M2_ARLEN, UVM_ALL_ON)
        `uvm_field_int(M2_ARSIZE, UVM_ALL_ON)
        `uvm_field_enum(M2_ARBURST, axi_burst_type_e, UVM_ALL_ON)
        `uvm_field_int(M2_ARLOCK, UVM_ALL_ON)
        `uvm_field_int(M2_ARCACHE, UVM_ALL_ON)
        `uvm_field_int(M2_ARPROT, UVM_ALL_ON)
        `uvm_field_int(M2_ARQOS, UVM_ALL_ON)
        `uvm_field_int(M2_ARREGION, UVM_ALL_ON)
        `uvm_field_int(M2_ARVALID, UVM_ALL_ON)
        `uvm_field_array_int(burst_data, UVM_ALL_ON)
        `uvm_field_array_int(burst_strobe, UVM_ALL_ON)
        `uvm_field_int(transaction_complete, UVM_ALL_ON)
        `uvm_field_time(start_time, UVM_ALL_ON)
        `uvm_field_time(end_time, UVM_ALL_ON)
        `uvm_field_int(m2_total_transactions, UVM_ALL_ON)
        `uvm_field_int(m2_write_transactions, UVM_ALL_ON)
        `uvm_field_int(m2_read_transactions, UVM_ALL_ON)
        `uvm_field_int(m2_burst_transactions, UVM_ALL_ON)
        `uvm_field_int(m2_single_transactions, UVM_ALL_ON)
        `uvm_field_time(m2_avg_response_time, UVM_ALL_ON)
        `uvm_field_time(m2_min_response_time, UVM_ALL_ON)
        `uvm_field_time(m2_max_response_time, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass : M2_seq_item

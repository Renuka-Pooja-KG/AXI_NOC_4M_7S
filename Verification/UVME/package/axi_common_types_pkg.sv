//=============================================================================
// AXI Common Types Package
//=============================================================================
// Contains all common AXI type definitions, enums, and constants
// This package can be imported by all AXI verification components

`ifndef AXI_COMMON_TYPES_PKG_SV
`define AXI_COMMON_TYPES_PKG_SV

package axi_common_types_pkg;

    // Import UVM package
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // ===== AXI TRANSACTION TYPES =====
    typedef enum bit [1:0] {
        AXI_WRITE = 2'b00,
        AXI_READ  = 2'b01
    } axi_trans_type_e;

    // ===== AXI BURST TYPES =====
    typedef enum bit [1:0] {
        AXI_FIXED = 2'b00,    // Fixed burst
        AXI_INCR  = 2'b01,    // Incrementing burst
        AXI_WRAP  = 2'b10     // Wrapping burst
    } axi_burst_type_e;

    // ===== AXI LOCK TYPES =====
    typedef enum bit {
        AXI_NORMAL = 1'b0,    // Normal access
        AXI_EXCLUSIVE = 1'b1  // Exclusive access
    } axi_lock_type_e;

    // ===== AXI RESPONSE TYPES =====
    typedef enum bit [1:0] {
        AXI_OKAY    = 2'b00,  // Normal successful access
        AXI_EXOKAY  = 2'b01,  // Exclusive access successful
        AXI_SLVERR  = 2'b10,  // Slave error
        AXI_DECERR  = 2'b11   // Decode error
    } axi_response_type_e;

    // ===== AXI TRANSFER SIZES =====
    typedef enum bit [2:0] {
        AXI_SIZE_1BYTE   = 3'b000,  // 1 byte
        AXI_SIZE_2BYTE   = 3'b001,  // 2 bytes
        AXI_SIZE_4BYTE   = 3'b010,  // 4 bytes
        AXI_SIZE_8BYTE   = 3'b011,  // 8 bytes
        AXI_SIZE_16BYTE  = 3'b100,  // 16 bytes
        AXI_SIZE_32BYTE  = 3'b101,  // 32 bytes
        AXI_SIZE_64BYTE  = 3'b110,  // 64 bytes
        AXI_SIZE_128BYTE = 3'b111   // 128 bytes
    } axi_size_e;

    // ===== AXI PROTECTION TYPES =====
    typedef enum bit [2:0] {
        AXI_PROT_NORMAL     = 3'b000,  // Normal access
        AXI_PROT_PRIVILEGED = 3'b001,  // Privileged access
        AXI_PROT_SECURE     = 3'b010,  // Secure access
        AXI_PROT_NONSECURE  = 3'b011,  // Non-secure access
        AXI_PROT_INSTRUCTION = 3'b100, // Instruction access
        AXI_PROT_DATA       = 3'b101,  // Data access
        AXI_PROT_USER       = 3'b110,  // User access
        AXI_PROT_SUPERVISOR = 3'b111   // Supervisor access
    } axi_prot_type_e;

    // ===== AXI CACHE ATTRIBUTES =====
    typedef enum bit [3:0] {
        AXI_CACHE_NONCACHEABLE = 4'b0000,  // Non-cacheable
        AXI_CACHE_BUFFERABLE   = 4'b0001,  // Bufferable
        AXI_CACHE_CACHEABLE    = 4'b0010,  // Cacheable
        AXI_CACHE_WRITETHROUGH = 4'b0100,  // Write-through
        AXI_CACHE_WRITEBACK    = 4'b1000   // Write-back
    } axi_cache_type_e;

    // ===== AXI QoS LEVELS =====
    typedef enum bit [3:0] {
        AXI_QOS_LEVEL_0 = 4'b0000,  // Lowest priority
        AXI_QOS_LEVEL_1 = 4'b0001,  // Low priority
        AXI_QOS_LEVEL_2 = 4'b0010,  // Medium priority
        AXI_QOS_LEVEL_3 = 4'b0011,  // High priority
        AXI_QOS_LEVEL_4 = 4'b0100,  // Very high priority
        AXI_QOS_LEVEL_5 = 4'b0101,  // Critical priority
        AXI_QOS_LEVEL_6 = 4'b0110,  // Emergency priority
        AXI_QOS_LEVEL_7 = 4'b0111,  // Highest priority
        AXI_QOS_LEVEL_8 = 4'b1000,  // Reserved
        AXI_QOS_LEVEL_9 = 4'b1001,  // Reserved
        AXI_QOS_LEVEL_A = 4'b1010,  // Reserved
        AXI_QOS_LEVEL_B = 4'b1011,  // Reserved
        AXI_QOS_LEVEL_C = 4'b1100,  // Reserved
        AXI_QOS_LEVEL_D = 4'b1101,  // Reserved
        AXI_QOS_LEVEL_E = 4'b1110,  // Reserved
        AXI_QOS_LEVEL_F = 4'b1111   // Reserved
    } axi_qos_level_e;

    // ===== AXI REGION IDENTIFIERS =====
    typedef enum bit [3:0] {
        AXI_REGION_0 = 4'b0000,  // Region 0
        AXI_REGION_1 = 4'b0001,  // Region 1
        AXI_REGION_2 = 4'b0010,  // Region 2
        AXI_REGION_3 = 4'b0011,  // Region 3
        AXI_REGION_4 = 4'b0100,  // Region 4
        AXI_REGION_5 = 4'b0101,  // Region 5
        AXI_REGION_6 = 4'b0110,  // Region 6
        AXI_REGION_7 = 4'b0111,  // Region 7
        AXI_REGION_8 = 4'b1000,  // Region 8
        AXI_REGION_9 = 4'b1001,  // Region 9
        AXI_REGION_A = 4'b1010,  // Region A
        AXI_REGION_B = 4'b1011,  // Region B
        AXI_REGION_C = 4'b1100,  // Region C
        AXI_REGION_D = 4'b1101,  // Region D
        AXI_REGION_E = 4'b1110,  // Region E
        AXI_REGION_F = 4'b1111   // Region F
    } axi_region_e;

    // ===== AXI MASTER IDENTIFIERS =====
    typedef enum bit [1:0] {
        AXI_MASTER_0 = 2'b00,  // Master 0
        AXI_MASTER_1 = 2'b01,  // Master 1
        AXI_MASTER_2 = 2'b10,  // Master 2
        AXI_MASTER_3 = 2'b11   // Master 3
    } axi_master_id_e;

    // ===== AXI SLAVE IDENTIFIERS =====
    typedef enum bit [2:0] {
        AXI_SLAVE_0 = 3'b000,  // Slave 0
        AXI_SLAVE_1 = 3'b001,  // Slave 1
        AXI_SLAVE_2 = 3'b010,  // Slave 2
        AXI_SLAVE_3 = 3'b011,  // Slave 3
        AXI_SLAVE_4 = 3'b100,  // Slave 4
        AXI_SLAVE_5 = 3'b101,  // Slave 5
        AXI_SLAVE_6 = 3'b110   // Slave 6
    } axi_slave_id_e;

    // ===== AXI ADDRESS RANGES =====
    // Base addresses for each slave
    parameter bit [31:0] SLAVE_0_BASE_ADDR = 32'h0000_0000;
    parameter bit [31:0] SLAVE_1_BASE_ADDR = 32'h0000_2000;
    parameter bit [31:0] SLAVE_2_BASE_ADDR = 32'h0000_4000;
    parameter bit [31:0] SLAVE_3_BASE_ADDR = 32'h0000_6000;
    parameter bit [31:0] SLAVE_4_BASE_ADDR = 32'h0000_8000;
    parameter bit [31:0] SLAVE_5_BASE_ADDR = 32'h0000_A000;
    parameter bit [31:0] SLAVE_6_BASE_ADDR = 32'h0000_C000;

    // Address range size (4KB per slave)
    parameter bit [31:0] SLAVE_ADDR_RANGE_SIZE = 32'h0000_1000;

    // ===== AXI SIGNAL WIDTHS =====
    parameter int AXI_ID_WIDTH     = 4;    // ID width in bits
    parameter int AXI_SID_WIDTH    = 6;    // Slave ID width in bits
    parameter int AXI_ADDR_WIDTH   = 32;   // Address width in bits
    parameter int AXI_DATA_WIDTH   = 32;   // Data width in bits
    parameter int AXI_STRB_WIDTH   = 4;    // Strobe width in bits
    parameter int AXI_LEN_WIDTH    = 8;    // Burst length width
    parameter int AXI_SIZE_WIDTH   = 3;    // Transfer size width
    parameter int AXI_BURST_WIDTH  = 2;    // Burst type width
    parameter int AXI_LOCK_WIDTH   = 1;    // Lock type width
    parameter int AXI_CACHE_WIDTH  = 4;    // Cache attributes width
    parameter int AXI_PROT_WIDTH   = 3;    // Protection attributes width
    parameter int AXI_QOS_WIDTH    = 4;    // Quality of service width
    parameter int AXI_REGION_WIDTH = 4;    // Region identifier width
    parameter int AXI_RESP_WIDTH   = 2;    // Response width

    // ===== AXI CONSTANTS =====
    parameter int AXI_MAX_BURST_LENGTH = 16;  // Maximum burst length
    parameter int AXI_MIN_BURST_LENGTH = 1;   // Minimum burst length

    // ===== AXI ACCESS CONTROL MATRIX =====
    // Master 0: Full access to all slaves
    // LSB is S0, MSB is S6
    parameter bit [6:0] MASTER_0_ACCESS = 7'b111_1111;  // Can access S0-S6
    
    // Master 1: Limited access to S1, S3, S4
    // LSB is S0, MSB is S6
    parameter bit [6:0] MASTER_1_ACCESS = 7'b001_1010;  // Can access S1, S3, S4
    
    // Master 2: Limited access to S1, S2, S4
    // LSB is S0, MSB is S6
    parameter bit [6:0] MASTER_2_ACCESS = 7'b001_0110;  // Can access S1, S2, S4
    
    // Master 3: Limited access to S1, S5, S6
    // LSB is S0, MSB is S6
    parameter bit [6:0] MASTER_3_ACCESS = 7'b110_0010;  // Can access S1, S5, S6

    // ===== UTILITY FUNCTIONS =====
    
    // Function to check if a master can access a specific slave
    function automatic bit can_master_access_slave(axi_master_id_e master, axi_slave_id_e slave);
        case (master)
            AXI_MASTER_0: return MASTER_0_ACCESS[slave];
            AXI_MASTER_1: return MASTER_1_ACCESS[slave];
            AXI_MASTER_2: return MASTER_2_ACCESS[slave];
            AXI_MASTER_3: return MASTER_3_ACCESS[slave];
            default: return 1'b0;
        endcase
    endfunction

    // Function to get slave base address
    function automatic bit [31:0] get_slave_base_addr(axi_slave_id_e slave);
        case (slave)
            AXI_SLAVE_0: return SLAVE_0_BASE_ADDR;
            AXI_SLAVE_1: return SLAVE_1_BASE_ADDR;
            AXI_SLAVE_2: return SLAVE_2_BASE_ADDR;
            AXI_SLAVE_3: return SLAVE_3_BASE_ADDR;
            AXI_SLAVE_4: return SLAVE_4_BASE_ADDR;
            AXI_SLAVE_5: return SLAVE_5_BASE_ADDR;
            AXI_SLAVE_6: return SLAVE_6_BASE_ADDR;
            default: return 32'h0000_0000;
        endcase
    endfunction

    // Function to check if address is within slave range
    function automatic bit is_address_in_slave_range(bit [31:0] addr, axi_slave_id_e slave);
        bit [31:0] base_addr = get_slave_base_addr(slave);
        return (addr >= base_addr) && (addr < (base_addr + SLAVE_ADDR_RANGE_SIZE));
    endfunction

    // Function to get slave ID from address
    function automatic axi_slave_id_e get_slave_from_address(bit [31:0] addr);
        if (is_address_in_slave_range(addr, AXI_SLAVE_0)) return AXI_SLAVE_0;
        if (is_address_in_slave_range(addr, AXI_SLAVE_1)) return AXI_SLAVE_1;
        if (is_address_in_slave_range(addr, AXI_SLAVE_2)) return AXI_SLAVE_2;
        if (is_address_in_slave_range(addr, AXI_SLAVE_3)) return AXI_SLAVE_3;
        if (is_address_in_slave_range(addr, AXI_SLAVE_4)) return AXI_SLAVE_4;
        if (is_address_in_slave_range(addr, AXI_SLAVE_5)) return AXI_SLAVE_5;
        if (is_address_in_slave_range(addr, AXI_SLAVE_6)) return AXI_SLAVE_6;
        return AXI_SLAVE_0; // Default return
    endfunction

    // Function to check address alignment
    function automatic bit is_address_aligned(bit [31:0] addr, bit [2:0] size);
        return (addr % (1 << size)) == 0;
    endfunction

    // Function to get burst length from AXI length field
    function automatic int get_burst_length(bit [7:0] axlen);
        return axlen + 1; // AXI length is 0-based
    endfunction

    // Function to set AXI length field from burst length
    function automatic bit [7:0] set_axi_length(int burst_length);
        return burst_length - 1; // Convert to 0-based
    endfunction

endpackage : axi_common_types_pkg

`endif // AXI_COMMON_TYPES_PKG_SV

//=============================================================================
// AXI Slave VIP Package
//=============================================================================
// Complete verification IP for AXI slave functionality

`ifndef AXI_SLAVE_VIP_PKG_SV
`define AXI_SLAVE_VIP_PKG_SV

package axi_slave_vip_pkg;

import uvm_pkg::*;
`include "uvm_macros.svh"

// Forward declarations
typedef class axi_slave_transaction;
typedef class axi_slave_agent;
typedef class axi_slave_driver;
typedef class axi_slave_monitor;
typedef class axi_slave_sequencer;
typedef class axi_slave_config;

// Transaction class
class axi_slave_transaction extends uvm_sequence_item;
    
    // Transaction properties
    rand bit [3:0]  slave_id;       // Slave identifier (0-6)
    rand bit [3:0]  master_id;      // Source master (0-3)
    rand bit [31:0] address;        // Transaction address
    rand bit [7:0]  burst_length;   // Burst length (0-255)
    rand bit [2:0]  burst_size;     // Burst size (1,2,4,8,16,32,64,128 bytes)
    rand bit [1:0]  burst_type;     // 00:FIXED, 01:INCR, 10:WRAP
    rand bit [3:0]  id;             // Transaction ID
    rand bit [1:0]  lock;           // Lock type
    rand bit [2:0]  prot;           // Protection type
    rand bit [3:0]  qos;            // Quality of service
    rand bit [3:0]  region;         // Region identifier
    rand bit [31:0] data[];         // Write data array
    rand bit [3:0]  strb[];         // Write strobe array
    rand bit        is_read;        // 1: Read, 0: Write
    
    // Response fields
    rand bit [1:0]  response;       // Response code (00:OKAY, 01:EXOKAY, 10:SLVERR, 11:DECERR)
    rand bit [31:0] read_data[];    // Read data array
    rand int        response_delay;  // Response delay in clock cycles
    bit             transaction_done; // Transaction completion flag
    
    // Timing
    time start_time;
    time end_time;
    
    // Constraints
    constraint valid_burst_length { burst_length >= 0; burst_length <= 15; }  // AXI4 limit
    constraint valid_burst_size { burst_size inside {0,1,2,3,4,5,6,7}; }
    constraint valid_burst_type { burst_type inside {2'b00, 2'b01, 2'b10}; }
    constraint valid_slave_id { slave_id >= 0; slave_id <= 6; }
    constraint valid_master_id { master_id >= 0; master_id <= 3; }
    constraint valid_id { id >= 0; id <= 15; }
    constraint valid_response { response inside {2'b00, 2'b01, 2'b10, 2'b11}; }
    constraint valid_response_delay { response_delay >= 0; response_delay <= 5; }
    constraint data_array_size { data.size() == burst_length + 1; }
    constraint strb_array_size { strb.size() == burst_length + 1; }
    constraint read_data_array_size { read_data.size() == burst_length + 1; }
    
    // Constructor
    function new(string name = "axi_slave_transaction");
        super.new(name);
    endfunction
    
    // UVM field macros
    `uvm_object_utils_begin(axi_slave_transaction)
        `uvm_field_int(slave_id, UVM_ALL_ON)
        `uvm_field_int(master_id, UVM_ALL_ON)
        `uvm_field_int(address, UVM_ALL_ON)
        `uvm_field_int(burst_length, UVM_ALL_ON)
        `uvm_field_int(burst_size, UVM_ALL_ON)
        `uvm_field_int(burst_type, UVM_ALL_ON)
        `uvm_field_int(id, UVM_ALL_ON)
        `uvm_field_int(lock, UVM_ALL_ON)
        `uvm_field_int(prot, UVM_ALL_ON)
        `uvm_field_int(qos, UVM_ALL_ON)
        `uvm_field_int(region, UVM_ALL_ON)
        `uvm_field_array_int(data, UVM_ALL_ON)
        `uvm_field_array_int(strb, UVM_ALL_ON)
        `uvm_field_int(is_read, UVM_ALL_ON)
        `uvm_field_int(response, UVM_ALL_ON)
        `uvm_field_array_int(read_data, UVM_ALL_ON)
        `uvm_field_int(response_delay, UVM_ALL_ON)
        `uvm_field_int(transaction_done, UVM_ALL_ON)
        `uvm_field_time(start_time, UVM_ALL_ON)
        `uvm_field_time(end_time, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass

// Configuration class
class axi_slave_config extends uvm_object;
    
    // Interface configuration
    virtual axi_slave_interface vif;
    
    // Agent configuration
    bit is_active = UVM_ACTIVE;
    bit has_coverage = 1;
    bit has_checks = 1;
    
    // Slave behavior configuration
    bit [1:0] default_response = 2'b00;  // Default response (OKAY)
    int min_response_delay = 0;
    int max_response_delay = 3;
    
    // Slave identification
    bit [2:0] slave_id = 0;  // Which slave this agent represents (0-6)
    
    // Error injection configuration
    bit inject_errors = 0;
    real error_probability = 0.01;  // 1% error probability
    
    // Constructor
    function new(string name = "axi_slave_config");
        super.new(name);
    endfunction
    
    // UVM field macros
    `uvm_object_utils_begin(axi_slave_config)
        `uvm_field_int(is_active, UVM_ALL_ON)
        `uvm_field_int(has_coverage, UVM_ALL_ON)
        `uvm_field_int(has_checks, UVM_ALL_ON)
        `uvm_field_int(default_response, UVM_ALL_ON)
        `uvm_field_int(min_response_delay, UVM_ALL_ON)
        `uvm_field_int(max_response_delay, UVM_ALL_ON)
        `uvm_field_int(slave_id, UVM_ALL_ON)
        `uvm_field_int(inject_errors, UVM_ALL_ON)
        `uvm_field_real(error_probability, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass

// Monitor class
class axi_slave_monitor extends uvm_monitor;
    
    // Configuration
    axi_slave_config cfg;
    
    // Analysis port
    uvm_analysis_port #(axi_slave_transaction) ap;
    
    // Virtual interface
    virtual axi_slave_interface vif;
    
    // Constructor
    function new(string name = "axi_slave_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db #(axi_slave_config)::get(this, "", "cfg", cfg))
            `uvm_fatal("NOCONFIG", "Configuration not found")
        vif = cfg.vif;
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk);
            if (vif.resetn) begin
                monitor_transaction();
            end
        end
    endtask
    
    // Monitor transaction
    task monitor_transaction();
        axi_slave_transaction trans;
        
        // Monitor write address channel
        if (vif.awvalid && vif.awready) begin
            trans = axi_slave_transaction::type_id::create("trans");
            trans.address = vif.awaddr;
            trans.burst_length = vif.awlen;
            trans.burst_size = vif.awsize;
            trans.burst_type = vif.awburst;
            trans.id = vif.awid;
            trans.lock = vif.awlock;
            trans.prot = vif.awprot;
            trans.qos = vif.awqos;
            trans.region = vif.awregion;
            trans.is_read = 0;
            trans.start_time = $time;
            
            // Monitor write data channel
            monitor_write_data(trans);
            
            // Monitor write response
            monitor_write_response(trans);
            
            ap.write(trans);
        end
        
        // Monitor read address channel
        if (vif.arvalid && vif.arready) begin
            trans = axi_slave_transaction::type_id::create("trans");
            trans.address = vif.araddr;
            trans.burst_length = vif.arlen;
            trans.burst_size = vif.arsize;
            trans.burst_type = vif.arburst;
            trans.id = vif.arid;
            trans.lock = vif.arlock;
            trans.prot = vif.arprot;
            trans.qos = vif.arqos;
            trans.region = vif.arregion;
            trans.is_read = 1;
            trans.start_time = $time;
            
            // Monitor read data
            monitor_read_data(trans);
            
            ap.write(trans);
        end
    endtask
    
    // Monitor write data
    task monitor_write_data(axi_slave_transaction trans);
        int count = 0;
        trans.data = new[trans.burst_length + 1];
        trans.strb = new[trans.burst_length + 1];
        
        while (count <= trans.burst_length) begin
            @(posedge vif.clk);
            if (vif.wvalid && vif.wready) begin
                trans.data[count] = vif.wdata;
                trans.strb[count] = vif.wstrb;
                count++;
            end
        end
    endtask
    
    // Monitor write response
    task monitor_write_response(axi_slave_transaction trans);
        @(posedge vif.clk);
        if (vif.bvalid && vif.bready) begin
            trans.response = vif.bresp;
            trans.end_time = $time;
            trans.transaction_done = 1;
        end
    endtask
    
    // Monitor read data
    task monitor_read_data(axi_slave_transaction trans);
        int count = 0;
        trans.read_data = new[trans.burst_length + 1];
        
        while (count <= trans.burst_length) begin
            @(posedge vif.clk);
            if (vif.rvalid && vif.rready) begin
                trans.read_data[count] = vif.rdata;
                if (vif.rlast) begin
                    trans.response = vif.rresp;
                    trans.end_time = $time;
                    trans.transaction_done = 1;
                    break;
                end
                count++;
            end
        end
    endtask
    
endclass

// Driver class
class axi_slave_driver extends uvm_driver #(axi_slave_transaction);
    
    // Configuration
    axi_slave_config cfg;
    
    // Virtual interface
    virtual axi_slave_interface vif;
    
    // Internal memory for slave behavior
    bit [31:0] memory[bit [31:0]];
    
    // Constructor
    function new(string name = "axi_slave_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db #(axi_slave_config)::get(this, "", "cfg", cfg))
            `uvm_fatal("NOCONFIG", "Configuration not found")
        vif = cfg.vif;
        
        // Initialize memory
        initialize_memory();
    endfunction
    
    // Initialize memory - Dynamic approach
    function void initialize_memory();
        // Calculate the actual end address for this slave
        bit [31:0] end_address;
        
        case (cfg.slave_id)
            0: end_address = 32'h0000_0FFF;
            1: end_address = 32'h0000_2FFF;
            2: end_address = 32'h0000_4FFF;
            3: end_address = 32'h0000_6FFF;
            4: end_address = 32'h0000_8FFF;
            5: end_address = 32'h0000_AFFF;
            6: end_address = 32'h0000_CFFF;
            default: end_address = 32'h0000_0FFF;
        endcase
        
        // Initialize all addresses in the range
        for (bit [31:0] addr = cfg.base_address; addr <= end_address; addr = addr + 4) begin
            memory[addr] = addr[31:0];  // Use address as default value
        end
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            handle_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    // Handle transaction
    task handle_transaction(axi_slave_transaction trans);
        if (trans.is_read) begin
            handle_read_transaction(trans);
        end else begin
            handle_write_transaction(trans);
        end
    endtask
    
    // Handle write transaction
    task handle_write_transaction(axi_slave_transaction trans);
        // Accept write address
        accept_write_address(trans);
        
        // Accept write data
        accept_write_data(trans);
        
        // Send write response
        send_write_response(trans);
    endtask
    
    // Accept write address
    task accept_write_address(axi_slave_transaction trans);
        // Wait for address valid
        do @(posedge vif.clk); while (!vif.awvalid);
        
        // Drive ready signal
        vif.awready <= 1;
        @(posedge vif.clk);
        vif.awready <= 0;
    endtask
    
    // Accept write data
    task accept_write_data(axi_slave_transaction trans);
        for (int i = 0; i <= trans.burst_length; i++) begin
            // Wait for data valid
            do @(posedge vif.clk); while (!vif.wvalid);
            
            // Drive ready signal
            vif.wready <= 1;
            
            // Store data in memory
            if (vif.wstrb[0]) memory[vif.awaddr + (i * 4)] = vif.wdata[7:0];
            if (vif.wstrb[1]) memory[vif.awaddr + (i * 4) + 1] = vif.wdata[15:8];
            if (vif.wstrb[2]) memory[vif.awaddr + (i * 4) + 2] = vif.wdata[23:16];
            if (vif.wstrb[3]) memory[vif.awaddr + (i * 4) + 3] = vif.wdata[31:24];
            
            @(posedge vif.clk);
            vif.wready <= 0;
        end
    endtask
    
    // Send write response
    task send_write_response(axi_slave_transaction trans);
        // Add response delay
        repeat(trans.response_delay) @(posedge vif.clk);
        
        // Drive response - MUST match the actual request
        vif.bid <= vif.awid;  // Critical: ID must match request ID
        
        // Determine response based on emulated slave behavior
        vif.bresp <= determine_emulated_response(trans);
        vif.bvalid <= 1;
        
        // Wait for handshake
        do @(posedge vif.clk); while (!vif.bready);
        vif.bvalid <= 0;
    endtask
    
    // Enhanced response determination with proper error codes
    function bit [1:0] determine_emulated_response(axi_slave_transaction trans);
        // First check: Is this slave responsible for this address?
        if (!should_accept_transaction(trans)) begin
            return 2'b11;  // DECERR - address not mapped to this slave
        end
        
        // Second check: Does the master have permission to access this slave?
        if (!has_access_permission(trans)) begin
            return 2'b10;  // SLVERR - access denied (master not allowed)
        end
        
        // Additional checks for realistic slave behavior
        if (!is_valid_burst_combination(trans)) begin
            return 2'b10;  // SLVERR - invalid burst configuration
        end
        
        if (!is_address_aligned(trans)) begin
            return 2'b10;  // SLVERR - address alignment violation
        end
        
        // All checks passed - successful transaction
        return 2'b00;  // OKAY
    endfunction
    
    // Check if this slave should accept the transaction based on address range
    function bit should_accept_transaction(axi_slave_transaction trans);
        // Check if address falls within this slave's range
        case (cfg.slave_id)
            0: return (trans.address >= 32'h0000_0000 && trans.address <= 32'h0000_0FFF);
            1: return (trans.address >= 32'h0000_2000 && trans.address <= 32'h0000_2FFF);
            2: return (trans.address >= 32'h0000_4000 && trans.address <= 32'h0000_4FFF);
            3: return (trans.address >= 32'h0000_6000 && trans.address <= 32'h0000_6FFF);
            4: return (trans.address >= 32'h0000_8000 && trans.address <= 32'h0000_8FFF);
            5: return (trans.address >= 32'h0000_A000 && trans.address <= 32'h0000_AFFF);
            6: return (trans.address >= 32'h0000_C000 && trans.address <= 32'h0000_CFFF);
            default: return 0;
        endcase
    endfunction
    
    // Check if the master has permission to access this slave
    function bit has_access_permission(axi_slave_transaction trans);
        // Master access control matrix from README
        case (cfg.slave_id)
            0: begin  // Slave 0
                // Only Master 0 has access to Slave 0
                return (trans.master_id == 0);
            end
            
            1: begin  // Slave 1
                // Masters 0, 1, 2, 3 all have access to Slave 1
                return (trans.master_id >= 0 && trans.master_id <= 3);
            end
            
            2: begin  // Slave 2
                // Only Masters 0 and 2 have access to Slave 2
                return (trans.master_id == 0 || trans.master_id == 2);
            end
            
            3: begin  // Slave 3
                // Only Masters 0 and 1 have access to Slave 3
                return (trans.master_id == 0 || trans.master_id == 1);
            end
            
            4: begin  // Slave 4
                // Only Masters 0, 1, and 2 have access to Slave 4
                return (trans.master_id >= 0 && trans.master_id <= 2);
            end
            
            5: begin  // Slave 5
                // Only Masters 0 and 3 have access to Slave 5
                return (trans.master_id == 0 || trans.master_id == 3);
            end
            
            6: begin  // Slave 6
                // Only Masters 0 and 3 have access to Slave 6
                return (trans.master_id == 0 || trans.master_id == 3);
            end
            
            default: return 0;
        endcase
    endfunction
    
    // Check if burst configuration is valid for this slave
    function bit is_valid_burst_combination(axi_slave_transaction trans);
        // Check burst size alignment
        bit [31:0] aligned_address;
        aligned_address = trans.address & ~((1 << trans.burst_size) - 1);
        
        if (aligned_address != trans.address) begin
            return 0;  // Address not aligned with burst size
        end
        
        // Check burst length constraints
        if (trans.burst_length > 15) begin  // AXI4 limit
            return 0;
        end
        
        // Check if burst would exceed slave address range
        bit [31:0] end_address;
        end_address = trans.address + (trans.burst_length * (1 << trans.burst_size));
        
        case (cfg.slave_id)
            0: return (end_address <= 32'h0000_0FFF);
            1: return (end_address <= 32'h0000_2FFF);
            2: return (end_address <= 32'h0000_4FFF);
            3: return (end_address <= 32'h0000_6FFF);
            4: return (end_address <= 32'h0000_8FFF);
            5: return (end_address <= 32'h0000_AFFF);
            6: return (end_address <= 32'h0000_CFFF);
            default: return 0;
        endcase
    endfunction
    
    // Check if address is properly aligned
    function bit is_address_aligned(axi_slave_transaction trans);
        // Address must be aligned according to burst size
        bit [31:0] alignment_mask;
        alignment_mask = (1 << trans.burst_size) - 1;
        
        return ((trans.address & alignment_mask) == 0);
    endfunction
    
    // Handle read transaction
    task handle_read_transaction(axi_slave_transaction trans);
        // Accept read address
        accept_read_address(trans);
        
        // Send read data
        send_read_data(trans);
    endtask
    
    // Accept read address
    task accept_read_address(axi_slave_transaction trans);
        // Wait for address valid
        do @(posedge vif.clk); while (!vif.arvalid);
        
        // Drive ready signal
        vif.arready <= 1;
        @(posedge vif.clk);
        vif.arready <= 0;
    endtask
    
    // Send read data
    task send_read_data(axi_slave_transaction trans);
        for (int i = 0; i <= trans.burst_length; i++) begin
            // Add response delay
            repeat(trans.response_delay) @(posedge vif.clk);
            
            // Drive data
            vif.rid <= vif.arid;  // Use actual request ID
            vif.rdata <= memory[trans.address + (i * 4)];
            vif.rresp <= determine_emulated_response(trans);
            vif.rlast <= (i == trans.burst_length);
            vif.rvalid <= 1;
            
            // Wait for handshake
            do @(posedge vif.clk); while (!vif.rready);
            vif.rvalid <= 0;
        end
    endtask
    
endclass

// Sequencer class
class axi_slave_sequencer extends uvm_sequencer #(axi_slave_transaction);
    
    // Constructor
    function new(string name = "axi_slave_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
endclass

// Agent class
class axi_slave_agent extends uvm_agent;
    
    // Components
    axi_slave_driver driver;
    axi_slave_monitor monitor;
    axi_slave_sequencer sequencer;
    
    // Configuration
    axi_slave_config cfg;
    
    // Constructor
    function new(string name = "axi_slave_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(axi_slave_config)::get(this, "", "cfg", cfg))
            `uvm_fatal("NOCONFIG", "Configuration not found")
        
        monitor = axi_slave_monitor::type_id::create("monitor", this);
        
        if (cfg.is_active == UVM_ACTIVE) begin
            driver = axi_slave_driver::type_id::create("driver", this);
            sequencer = axi_slave_sequencer::type_id::create("sequencer", this);
        end
    endfunction
    
    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if (cfg.is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
    
endclass

endpackage
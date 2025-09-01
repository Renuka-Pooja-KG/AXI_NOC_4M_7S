//=============================================================================
// AXI Master VIP Package
//=============================================================================
// Complete verification IP for AXI master functionality

`ifndef AXI_MASTER_VIP_PKG_SV
`define AXI_MASTER_VIP_PKG_SV

package axi_master_vip_pkg;

import uvm_pkg::*;
`include "uvm_macros.svh"

// Forward declarations
typedef class axi_master_transaction;
typedef class axi_master_agent;
typedef class axi_master_driver;
typedef class axi_master_monitor;
typedef class axi_master_sequencer;
typedef class axi_master_config;

// Transaction class
class axi_master_transaction extends uvm_sequence_item;
    
    // Transaction properties
    rand bit [3:0]  master_id;      // Master identifier (0-3)
    rand bit [2:0]  slave_id;       // Target slave (0-6)
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
    bit [1:0]  response;            // Response code
    bit [31:0] read_data[];         // Read data array
    bit        transaction_done;     // Transaction completion flag
    
    // Timing
    time start_time;
    time end_time;
    
    // Constraints
    constraint valid_burst_length { burst_length >= 0; burst_length <= 255; }
    constraint valid_burst_size { burst_size inside {0,1,2,3,4,5,6,7}; }
    constraint valid_burst_type { burst_type inside {2'b00, 2'b01, 2'b10}; }
    constraint valid_slave_id { slave_id >= 0; slave_id <= 6; }
    constraint valid_master_id { master_id >= 0; master_id <= 3; }
    constraint valid_id { id >= 0; id <= 15; }
    constraint data_array_size { data.size() == burst_length + 1; }
    constraint strb_array_size { strb.size() == burst_length + 1; }
    
    // Constructor
    function new(string name = "axi_master_transaction");
        super.new(name);
    endfunction
    
    // UVM field macros
    `uvm_object_utils_begin(axi_master_transaction)
        `uvm_field_int(master_id, UVM_ALL_ON)
        `uvm_field_int(slave_id, UVM_ALL_ON)
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
        `uvm_field_int(transaction_done, UVM_ALL_ON)
        `uvm_field_int(start_time, UVM_ALL_ON)
        `uvm_field_int(end_time, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass

// Configuration class
class axi_master_config extends uvm_object;
    
    // Interface configuration
    virtual axi_master_interface vif;
    
    // Agent configuration
    bit is_active = UVM_ACTIVE;
    bit has_coverage = 1;
    bit has_checks = 1;
    
    // Timing configuration
    int min_delay = 0;
    int max_delay = 10;
    
    // Transaction configuration
    int max_burst_length = 15;
    int max_concurrent_transactions = 4;
    
    // Constructor
    function new(string name = "axi_master_config");
        super.new(name);
    endfunction
    
    // UVM field macros
    `uvm_object_utils_begin(axi_master_config)
        `uvm_field_int(is_active, UVM_ALL_ON)
        `uvm_field_int(has_coverage, UVM_ALL_ON)
        `uvm_field_int(has_checks, UVM_ALL_ON)
        `uvm_field_int(min_delay, UVM_ALL_ON)
        `uvm_field_int(max_delay, UVM_ALL_ON)
        `uvm_field_int(max_burst_length, UVM_ALL_ON)
        `uvm_field_int(max_concurrent_transactions, UVM_ALL_ON)
    `uvm_object_utils_end
    
endclass

// Monitor class
class axi_master_monitor extends uvm_monitor;
    
    // Configuration
    axi_master_config cfg;
    
    // Analysis port
    uvm_analysis_port #(axi_master_transaction) ap;
    
    // Virtual interface
    virtual axi_master_interface vif;
    
    // Constructor
    function new(string name = "axi_master_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db #(axi_master_config)::get(this, "", "cfg", cfg))
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
        axi_master_transaction trans;
        
        // Monitor write address channel
        if (vif.awvalid && vif.awready) begin
            trans = axi_master_transaction::type_id::create("trans");
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
            trans = axi_master_transaction::type_id::create("trans");
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
    task monitor_write_data(axi_master_transaction trans);
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
    task monitor_write_response(axi_master_transaction trans);
        @(posedge vif.clk);
        if (vif.bvalid && vif.bready) begin
            trans.response = vif.bresp;
            trans.end_time = $time;
            trans.transaction_done = 1;
        end
    endtask
    
    // Monitor read data
    task monitor_read_data(axi_master_transaction trans);
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
class axi_master_driver extends uvm_driver #(axi_master_transaction);
    
    // Configuration
    axi_master_config cfg;
    
    // Virtual interface
    virtual axi_master_interface vif;
    
    // Constructor
    function new(string name = "axi_master_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db #(axi_master_config)::get(this, "", "cfg", cfg))
            `uvm_fatal("NOCONFIG", "Configuration not found")
        vif = cfg.vif;
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    // Drive transaction
    task drive_transaction(axi_master_transaction trans);
        if (trans.is_read) begin
            drive_read_transaction(trans);
        end else begin
            drive_write_transaction(trans);
        end
    endtask
    
    // Drive write transaction
    task drive_write_transaction(axi_master_transaction trans);
        // Drive write address
        drive_write_address(trans);
        
        // Drive write data
        drive_write_data(trans);
        
        // Wait for write response
        wait_write_response(trans);
    endtask
    
    // Drive write address
    task drive_write_address(axi_master_transaction trans);
        @(posedge vif.clk);
        vif.awid <= trans.id;
        vif.awaddr <= trans.address;
        vif.awlen <= trans.burst_length;
        vif.awsize <= trans.burst_size;
        vif.awburst <= trans.burst_type;
        vif.awlock <= trans.lock;
        vif.awprot <= trans.prot;
        vif.awqos <= trans.qos;
        vif.awregion <= trans.region;
        vif.awvalid <= 1;
        
        // Wait for handshake
        do @(posedge vif.clk); while (!vif.awready);
        vif.awvalid <= 0;
    endtask
    
    // Drive write data
    task drive_write_data(axi_master_transaction trans);
        for (int i = 0; i <= trans.burst_length; i++) begin
            @(posedge vif.clk);
            vif.wdata <= trans.data[i];
            vif.wstrb <= trans.strb[i];
            vif.wlast <= (i == trans.burst_length);
            vif.wvalid <= 1;
            
            // Wait for handshake
            do @(posedge vif.clk); while (!vif.wready);
            vif.wvalid <= 0;
        end
    endtask
    
    // Wait for write response
    task wait_write_response(axi_master_transaction trans);
        @(posedge vif.clk);
        vif.bready <= 1;
        
        // Wait for response
        do @(posedge vif.clk); while (!vif.bvalid);
        vif.bready <= 0;
    endtask
    
    // Drive read transaction
    task drive_read_transaction(axi_master_transaction trans);
        // Drive read address
        drive_read_address(trans);
        
        // Wait for read data
        wait_read_data(trans);
    endtask
    
    // Drive read address
    task drive_read_address(axi_master_transaction trans);
        @(posedge vif.clk);
        vif.arid <= trans.id;
        vif.araddr <= trans.address;
        vif.arlen <= trans.burst_length;
        vif.arsize <= trans.burst_size;
        vif.arburst <= trans.burst_type;
        vif.arlock <= trans.lock;
        vif.arprot <= trans.prot;
        vif.arqos <= trans.qos;
        vif.arregion <= trans.region;
        vif.arvalid <= 1;
        
        // Wait for handshake
        do @(posedge vif.clk); while (!vif.arready);
        vif.arvalid <= 0;
    endtask
    
    // Wait for read data
    task wait_read_data(axi_master_transaction trans);
        @(posedge vif.clk);
        vif.rready <= 1;
        
        // Wait for all data
        for (int i = 0; i <= trans.burst_length; i++) begin
            do @(posedge vif.clk); while (!vif.rvalid);
            if (vif.rlast) break;
        end
        vif.rready <= 0;
    endtask
    
endclass

// Sequencer class
class axi_master_sequencer extends uvm_sequencer #(axi_master_transaction);
    
    // Constructor
    function new(string name = "axi_master_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
endclass

// Agent class
class axi_master_agent extends uvm_agent;
    
    // Components
    axi_master_driver driver;
    axi_master_monitor monitor;
    axi_master_sequencer sequencer;
    
    // Configuration
    axi_master_config cfg;
    
    // Constructor
    function new(string name = "axi_master_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if(!uvm_config_db #(axi_master_config)::get(this, "", "cfg", cfg))
            `uvm_fatal("NOCONFIG", "Configuration not found")
        
        monitor = axi_master_monitor::type_id::create("monitor", this);
        
        if (cfg.is_active == UVM_ACTIVE) begin
            driver = axi_master_driver::type_id::create("driver", this);
            sequencer = axi_master_sequencer::type_id::create("sequencer", this);
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
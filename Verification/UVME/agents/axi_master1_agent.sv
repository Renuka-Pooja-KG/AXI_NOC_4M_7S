//=============================================================================
// AXI Master 1 Agent
//=============================================================================
// This file contains the Master 1 UVM agent with driver, monitor, sequencer,
// and agent components for the NOC verification environment. Master 1 has
// restricted access to only slaves S1, S3, and S4.

`ifndef AXI_MASTER1_AGENT_SV
`define AXI_MASTER1_AGENT_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

`include "axi_interfaces_pkg.sv"
`include "axi_transactions_pkg.sv"

//=============================================================================
// AXI Master 1 Driver
//=============================================================================
class axi_master1_driver extends uvm_driver #(axi_master1_transaction);
    
    // UVM Factory Registration
    `uvm_component_utils(axi_master1_driver)
    
    // Virtual interface
    virtual axi_master1_if vif;
    
    // Configuration
    axi_master1_config cfg;
    
    // Constructor
    function new(string name = "axi_master1_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db #(axi_master1_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("CFG_ERROR", "axi_master1_config not found in config_db")
        end
        
        // Get virtual interface
        if (!uvm_config_db #(virtual axi_master1_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("VIF_ERROR", "axi_master1_if not found in config_db")
        end
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        // Initialize interface signals
        vif.master1.m1_awvalid = 0;
        vif.master1.m1_wvalid = 0;
        vif.master1.m1_bready = 0;
        vif.master1.m1_arvalid = 0;
        vif.master1.m1_rready = 0;
        
        // Wait for reset
        wait(vif.rstn);
        
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    // Drive transaction task
    task drive_transaction(axi_master1_transaction trans);
        // Check access control before driving
        if (!check_access_control(trans)) begin
            `uvm_error("DRIVER_ERROR", $sformatf("Master 1 access denied to slave %0d", trans.slave_id))
            return;
        end
        
        case(trans.trans_type)
            AXI_WRITE: drive_write_transaction(trans);
            AXI_READ:  drive_read_transaction(trans);
            default:   `uvm_error("DRIVER_ERROR", "Unknown transaction type")
        endcase
    endtask
    
    // Check access control for Master 1
    function bit check_access_control(axi_master1_transaction trans);
        // Master 1 can only access S1, S3, S4
        case(trans.slave_id)
            1, 3, 4: return 1; // Allowed slaves
            default:  return 0; // Denied slaves
        endcase
    endfunction
    
    // Drive write transaction
    task drive_write_transaction(axi_master1_transaction trans);
        // Write Address Phase
        @(posedge vif.clk);
        vif.master1.m1_awid = trans.awid;
        vif.master1.m1_awaddr = trans.addr;
        vif.master1.m1_awlen = trans.len;
        vif.master1.m1_awsize = trans.size;
        vif.master1.m1_awburst = trans.burst;
        vif.master1.m1_awlock = trans.lock;
        vif.master1.m1_awcache = trans.cache;
        vif.master1.m1_awprot = trans.prot;
        vif.master1.m1_awqos = trans.qos;
        vif.master1.m1_awregion = trans.region;
        vif.master1.m1_awvalid = 1;
        
        // Wait for AWREADY
        wait(vif.master1.m1_awready);
        @(posedge vif.clk);
        vif.master1.m1_awvalid = 0;
        
        // Write Data Phase
        for (int i = 0; i <= trans.len; i++) begin
            @(posedge vif.clk);
            vif.master1.m1_wdata = trans.data[i];
            vif.master1.m1_wstrb = trans.strb[i];
            vif.master1.m1_wlast = (i == trans.len) ? 1 : 0;
            vif.master1.m1_wvalid = 1;
            
            // Wait for WREADY
            wait(vif.master1.m1_wready);
            @(posedge vif.clk);
            vif.master1.m1_wvalid = 0;
        end
        
        // Write Response Phase
        vif.master1.m1_bready = 1;
        wait(vif.master1.m1_bvalid);
        @(posedge vif.clk);
        vif.master1.m1_bready = 0;
        
        // Update transaction with response
        trans.bid = vif.master1.m1_bid;
        trans.resp = vif.master1.m1_bresp;
        trans.set_end_time();
        
        `uvm_info("DRIVER", $sformatf("Master 1 Write completed: Addr=0x%08X, Slave=%0d, Resp=%s", 
                                     trans.addr, trans.slave_id, trans.resp.name()), UVM_MEDIUM)
    endtask
    
    // Drive read transaction
    task drive_read_transaction(axi_master1_transaction trans);
        // Read Address Phase
        @(posedge vif.clk);
        vif.master1.m1_arid = trans.arid;
        vif.master1.m1_araddr = trans.addr;
        vif.master1.m1_arlen = trans.len;
        vif.master1.m1_arsize = trans.size;
        vif.master1.m1_arburst = trans.arburst;
        vif.master1.m1_arlock = trans.arlock;
        vif.master1.m1_arcache = trans.arcache;
        vif.master1.m1_arprot = trans.arprot;
        vif.master1.m1_arqos = trans.arqos;
        vif.master1.m1_arregion = trans.arregion;
        vif.master1.m1_arvalid = 1;
        
        // Wait for ARREADY
        wait(vif.master1.m1_arready);
        @(posedge vif.clk);
        vif.master1.m1_arvalid = 0;
        
        // Read Data Phase
        vif.master1.m1_rready = 1;
        for (int i = 0; i <= trans.len; i++) begin
            wait(vif.master1.m1_rvalid);
            trans.data[i] = vif.master1.m1_rdata;
            trans.rid = vif.master1.m1_rid;
            trans.rresp = vif.master1.m1_rresp;
            trans.rlast = vif.master1.m1_rlast;
            @(posedge vif.clk);
        end
        vif.master1.m1_rready = 0;
        
        // Update transaction
        trans.set_end_time();
        
        `uvm_info("DRIVER", $sformatf("Master 1 Read completed: Addr=0x%08X, Slave=%0d, Data=0x%08X", 
                                     trans.addr, trans.slave_id, trans.data[0]), UVM_MEDIUM)
    endtask
    
endclass : axi_master1_driver

//=============================================================================
// AXI Master 1 Monitor
//=============================================================================
class axi_master1_monitor extends uvm_monitor;
    
    // UVM Factory Registration
    `uvm_component_utils(axi_master1_monitor)
    
    // Virtual interface
    virtual axi_master1_if vif;
    
    // Analysis port
    uvm_analysis_port #(axi_master1_transaction) ap;
    
    // Configuration
    axi_master1_config cfg;
    
    // Constructor
    function new(string name = "axi_master1_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db #(axi_master1_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("CFG_ERROR", "axi_master1_config not found in config_db")
        end
        
        // Get virtual interface
        if (!uvm_config_db #(virtual axi_master1_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("VIF_ERROR", "axi_master1_if not found in config_db")
        end
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        // Wait for reset
        wait(vif.rstn);
        
        // Monitor transactions
        fork
            monitor_write_transactions();
            monitor_read_transactions();
        join
    endtask
    
    // Monitor write transactions
    task monitor_write_transactions();
        axi_master1_transaction trans;
        
        forever begin
            // Wait for write address
            wait(vif.master1.m1_awvalid && vif.master1.m1_awready);
            
            trans = axi_master1_transaction::type_id::create("trans");
            trans.trans_type = AXI_WRITE;
            trans.awid = vif.master1.m1_awid;
            trans.addr = vif.master1.m1_awaddr;
            trans.len = vif.master1.m1_awlen;
            trans.size = vif.master1.m1_awsize;
            trans.burst = vif.master1.m1_awburst;
            trans.lock = vif.master1.m1_awlock;
            trans.cache = vif.master1.m1_awcache;
            trans.prot = vif.master1.m1_awprot;
            trans.qos = vif.master1.m1_awqos;
            trans.region = vif.master1.m1_awregion;
            trans.set_start_time();
            
            // Determine slave ID from address
            trans.slave_id = get_slave_id_from_addr(trans.addr);
            
            // Monitor write data
            for (int i = 0; i <= trans.len; i++) begin
                wait(vif.master1.m1_wvalid && vif.master1.m1_wready);
                trans.data[i] = vif.master1.m1_wdata;
                trans.strb[i] = vif.master1.m1_wstrb;
                trans.wlast = vif.master1.m1_wlast;
                @(posedge vif.clk);
            end
            
            // Monitor write response
            wait(vif.master1.m1_bvalid && vif.master1.m1_bready);
            trans.bid = vif.master1.m1_bid;
            trans.resp = vif.master1.m1_bresp;
            trans.set_end_time();
            
            // Send to analysis port
            ap.write(trans);
            
            `uvm_info("MONITOR", $sformatf("Master 1 Write monitored: Addr=0x%08X, Slave=%0d, Resp=%s", 
                                          trans.addr, trans.slave_id, trans.resp.name()), UVM_MEDIUM)
        end
    endtask
    
    // Monitor read transactions
    task monitor_read_transactions();
        axi_master1_transaction trans;
        
        forever begin
            // Wait for read address
            wait(vif.master1.m1_arvalid && vif.master1.m1_arready);
            
            trans = axi_master1_transaction::type_id::create("trans");
            trans.trans_type = AXI_READ;
            trans.arid = vif.master1.m1_arid;
            trans.addr = vif.master1.m1_araddr;
            trans.len = vif.master1.m1_arlen;
            trans.size = vif.master1.m1_arsize;
            trans.arburst = vif.master1.m1_arburst;
            trans.arlock = vif.master1.m1_arlock;
            trans.arcache = vif.master1.m1_arcache;
            trans.arprot = vif.master1.m1_arprot;
            trans.arqos = vif.master1.m1_arqos;
            trans.arregion = vif.master1.m1_arregion;
            trans.set_start_time();
            
            // Determine slave ID from address
            trans.slave_id = get_slave_id_from_addr(trans.addr);
            
            // Monitor read data
            for (int i = 0; i <= trans.len; i++) begin
                wait(vif.master1.m1_rvalid && vif.master1.m1_rready);
                trans.data[i] = vif.master1.m1_rdata;
                trans.rid = vif.master1.m1_rid;
                trans.rresp = vif.master1.m1_rresp;
                trans.rlast = vif.master1.m1_rlast;
                @(posedge vif.clk);
            end
            
            trans.set_end_time();
            
            // Send to analysis port
            ap.write(trans);
            
            `uvm_info("MONITOR", $sformatf("Master 1 Read monitored: Addr=0x%08X, Slave=%0d, Data=0x%08X", 
                                          trans.addr, trans.slave_id, trans.data[0]), UVM_MEDIUM)
        end
    endtask
    
    // Get slave ID from address
    function int get_slave_id_from_addr(input [31:0] addr);
        case(1)
            (addr >= 32'h0000_2000 && addr <= 32'h0000_2FFF): return 1; // S1
            (addr >= 32'h0000_6000 && addr <= 32'h0000_6FFF): return 3; // S3
            (addr >= 32'h0000_8000 && addr <= 32'h0000_8FFF): return 4; // S4
            default: return -1; // Invalid address
        endcase
    endfunction
    
endclass : axi_master1_monitor

//=============================================================================
// AXI Master 1 Sequencer
//=============================================================================
class axi_master1_sequencer extends uvm_sequencer #(axi_master1_transaction);
    
    // UVM Factory Registration
    `uvm_component_utils(axi_master1_sequencer)
    
    // Constructor
    function new(string name = "axi_master1_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
endclass : axi_master1_sequencer

//=============================================================================
// AXI Master 1 Agent
//=============================================================================
class axi_master1_agent extends uvm_agent;
    
    // UVM Factory Registration
    `uvm_component_utils(axi_master1_agent)
    
    // Agent components
    axi_master1_driver    driver;
    axi_master1_monitor   monitor;
    axi_master1_sequencer sequencer;
    
    // Configuration
    axi_master1_config cfg;
    
    // Agent type (active or passive)
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    
    // Constructor
    function new(string name = "axi_master1_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db #(axi_master1_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("CFG_ERROR", "axi_master1_config not found in config_db")
        end
        
        // Create monitor (always created)
        monitor = axi_master1_monitor::type_id::create("monitor", this);
        
        // Create active components if agent is active
        if (is_active == UVM_ACTIVE) begin
            sequencer = axi_master1_sequencer::type_id::create("sequencer", this);
            driver = axi_master1_driver::type_id::create("driver", this);
        end
    endfunction
    
    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver to sequencer if active
        if (is_active == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
    
endclass : axi_master1_agent

//=============================================================================
// AXI Master 1 Configuration
//=============================================================================
class axi_master1_config extends uvm_object;
    
    // UVM Factory Registration
    `uvm_object_utils(axi_master1_config)
    
    // Configuration parameters
    int unsigned master_id = 1;
    int unsigned timeout = 1000;
    bit enable_coverage = 1;
    bit enable_checks = 1;
    
    // Access control parameters
    int unsigned allowed_slaves[] = '{1, 3, 4}; // S1, S3, S4
    
    // Constructor
    function new(string name = "axi_master1_config");
        super.new(name);
    endfunction
    
    // Check if slave is allowed
    function bit is_slave_allowed(input int unsigned slave_id);
        foreach(allowed_slaves[i]) begin
            if (allowed_slaves[i] == slave_id) return 1;
        end
        return 0;
    endfunction
    
endclass : axi_master1_config

`endif // AXI_MASTER1_AGENT_SV


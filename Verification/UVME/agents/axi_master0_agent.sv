//=============================================================================
// AXI Master 0 Agent
//=============================================================================
// This file contains the Master 0 UVM agent with driver, monitor, sequencer,
// and agent components for the NOC verification environment.

`ifndef AXI_MASTER0_AGENT_SV
`define AXI_MASTER0_AGENT_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

`include "axi_interfaces_pkg.sv"
`include "axi_transactions_pkg.sv"

//=============================================================================
// AXI Master 0 Driver
//=============================================================================
class axi_master0_driver extends uvm_driver #(axi_master0_transaction);
    
    // UVM Factory Registration
    `uvm_component_utils(axi_master0_driver)
    
    // Virtual interface
    virtual axi_master0_if vif;
    
    // Configuration
    axi_master0_config cfg;
    
    // Constructor
    function new(string name = "axi_master0_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db #(axi_master0_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("CFG_ERROR", "axi_master0_config not found in config_db")
        end
        
        // Get virtual interface
        if (!uvm_config_db #(virtual axi_master0_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("VIF_ERROR", "axi_master0_if not found in config_db")
        end
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        // Initialize interface signals
        vif.master0.m0_awvalid = 0;
        vif.master0.m0_wvalid = 0;
        vif.master0.m0_bready = 0;
        vif.master0.m0_arvalid = 0;
        vif.master0.m0_rready = 0;
        
        // Wait for reset
        wait(vif.rstn);
        
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    // Drive transaction task
    task drive_transaction(axi_master0_transaction trans);
        case(trans.trans_type)
            AXI_WRITE: drive_write_transaction(trans);
            AXI_READ:  drive_read_transaction(trans);
            default:   `uvm_error("DRIVER_ERROR", "Unknown transaction type")
        endcase
    endtask
    
    // Drive write transaction
    task drive_write_transaction(axi_master0_transaction trans);
        // Write Address Phase
        @(posedge vif.clk);
        vif.master0.m0_awid = trans.awid;
        vif.master0.m0_awaddr = trans.addr;
        vif.master0.m0_awlen = trans.len;
        vif.master0.m0_awsize = trans.size;
        vif.master0.m0_awburst = trans.burst;
        vif.master0.m0_awlock = trans.lock;
        vif.master0.m0_awcache = trans.cache;
        vif.master0.m0_awprot = trans.prot;
        vif.master0.m0_awqos = trans.qos;
        vif.master0.m0_awregion = trans.region;
        vif.master0.m0_awvalid = 1;
        
        // Wait for AWREADY
        wait(vif.master0.m0_awready);
        @(posedge vif.clk);
        vif.master0.m0_awvalid = 0;
        
        // Write Data Phase
        for (int i = 0; i <= trans.len; i++) begin
            @(posedge vif.clk);
            vif.master0.m0_wdata = trans.data[i];
            vif.master0.m0_wstrb = trans.strb[i];
            vif.master0.m0_wlast = (i == trans.len) ? 1 : 0;
            vif.master0.m0_wvalid = 1;
            
            // Wait for WREADY
            wait(vif.master0.m0_wready);
            @(posedge vif.clk);
            vif.master0.m0_wvalid = 0;
        end
        
        // Write Response Phase
        vif.master0.m0_bready = 1;
        wait(vif.master0.m0_bvalid);
        @(posedge vif.clk);
        vif.master0.m0_bready = 0;
        
        // Update transaction with response
        trans.bid = vif.master0.m0_bid;
        trans.resp = vif.master0.m0_bresp;
        trans.set_end_time();
        
        `uvm_info("DRIVER", $sformatf("Master 0 Write completed: Addr=0x%08X, Resp=%s", 
                                     trans.addr, trans.resp.name()), UVM_MEDIUM)
    endtask
    
    // Drive read transaction
    task drive_read_transaction(axi_master0_transaction trans);
        // Read Address Phase
        @(posedge vif.clk);
        vif.master0.m0_arid = trans.arid;
        vif.master0.m0_araddr = trans.addr;
        vif.master0.m0_arlen = trans.len;
        vif.master0.m0_arsize = trans.size;
        vif.master0.m0_arburst = trans.arburst;
        vif.master0.m0_arlock = trans.arlock;
        vif.master0.m0_arcache = trans.arcache;
        vif.master0.m0_arprot = trans.arprot;
        vif.master0.m0_arqos = trans.arqos;
        vif.master0.m0_arregion = trans.arregion;
        vif.master0.m0_arvalid = 1;
        
        // Wait for ARREADY
        wait(vif.master0.m0_arready);
        @(posedge vif.clk);
        vif.master0.m0_arvalid = 0;
        
        // Read Data Phase
        vif.master0.m0_rready = 1;
        for (int i = 0; i <= trans.len; i++) begin
            wait(vif.master0.m0_rvalid);
            trans.data[i] = vif.master0.m0_rdata;
            trans.rid = vif.master0.m0_rid;
            trans.rresp = vif.master0.m0_rresp;
            trans.rlast = vif.master0.m0_rlast;
            @(posedge vif.clk);
        end
        vif.master0.m0_rready = 0;
        
        // Update transaction
        trans.set_end_time();
        
        `uvm_info("DRIVER", $sformatf("Master 0 Read completed: Addr=0x%08X, Data=0x%08X", 
                                     trans.addr, trans.data[0]), UVM_MEDIUM)
    endtask
    
endclass : axi_master0_driver

//=============================================================================
// AXI Master 0 Monitor
//=============================================================================
class axi_master0_monitor extends uvm_monitor;
    
    // UVM Factory Registration
    `uvm_component_utils(axi_master0_monitor)
    
    // Virtual interface
    virtual axi_master0_if vif;
    
    // Analysis port
    uvm_analysis_port #(axi_master0_transaction) ap;
    
    // Configuration
    axi_master0_config cfg;
    
    // Constructor
    function new(string name = "axi_master0_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db #(axi_master0_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("CFG_ERROR", "axi_master0_config not found in config_db")
        end
        
        // Get virtual interface
        if (!uvm_config_db #(virtual axi_master0_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("VIF_ERROR", "axi_master0_if not found in config_db")
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
        axi_master0_transaction trans;
        
        forever begin
            // Wait for write address
            wait(vif.master0.m0_awvalid && vif.master0.m0_awready);
            
            trans = axi_master0_transaction::type_id::create("trans");
            trans.trans_type = AXI_WRITE;
            trans.awid = vif.master0.m0_awid;
            trans.addr = vif.master0.m0_awaddr;
            trans.len = vif.master0.m0_awlen;
            trans.size = vif.master0.m0_awsize;
            trans.burst = vif.master0.m0_awburst;
            trans.lock = vif.master0.m0_awlock;
            trans.cache = vif.master0.m0_awcache;
            trans.prot = vif.master0.m0_awprot;
            trans.qos = vif.master0.m0_awqos;
            trans.region = vif.master0.m0_awregion;
            trans.set_start_time();
            
            // Monitor write data
            for (int i = 0; i <= trans.len; i++) begin
                wait(vif.master0.m0_wvalid && vif.master0.m0_wready);
                trans.data[i] = vif.master0.m0_wdata;
                trans.strb[i] = vif.master0.m0_wstrb;
                trans.wlast = vif.master0.m0_wlast;
                @(posedge vif.clk);
            end
            
            // Monitor write response
            wait(vif.master0.m0_bvalid && vif.master0.m0_bready);
            trans.bid = vif.master0.m0_bid;
            trans.resp = vif.master0.m0_bresp;
            trans.set_end_time();
            
            // Send to analysis port
            ap.write(trans);
            
            `uvm_info("MONITOR", $sformatf("Master 0 Write monitored: Addr=0x%08X, Resp=%s", 
                                          trans.addr, trans.resp.name()), UVM_MEDIUM)
        end
    endtask
    
    // Monitor read transactions
    task monitor_read_transactions();
        axi_master0_transaction trans;
        
        forever begin
            // Wait for read address
            wait(vif.master0.m0_arvalid && vif.master0.m0_arready);
            
            trans = axi_master0_transaction::type_id::create("trans");
            trans.trans_type = AXI_READ;
            trans.arid = vif.master0.m0_arid;
            trans.addr = vif.master0.m0_araddr;
            trans.len = vif.master0.m0_arlen;
            trans.size = vif.master0.m0_arsize;
            trans.arburst = vif.master0.m0_arburst;
            trans.arlock = vif.master0.m0_arlock;
            trans.arcache = vif.master0.m0_arcache;
            trans.arprot = vif.master0.m0_arprot;
            trans.arqos = vif.master0.m0_arqos;
            trans.arregion = vif.master0.m0_arregion;
            trans.set_start_time();
            
            // Monitor read data
            for (int i = 0; i <= trans.len; i++) begin
                wait(vif.master0.m0_rvalid && vif.master0.m0_rready);
                trans.data[i] = vif.master0.m0_rdata;
                trans.rid = vif.master0.m0_rid;
                trans.rresp = vif.master0.m0_rresp;
                trans.rlast = vif.master0.m0_rlast;
                @(posedge vif.clk);
            end
            
            trans.set_end_time();
            
            // Send to analysis port
            ap.write(trans);
            
            `uvm_info("MONITOR", $sformatf("Master 0 Read monitored: Addr=0x%08X, Data=0x%08X", 
                                          trans.addr, trans.data[0]), UVM_MEDIUM)
        end
    endtask
    
endclass : axi_master0_monitor

//=============================================================================
// AXI Master 0 Sequencer
//=============================================================================
class axi_master0_sequencer extends uvm_sequencer #(axi_master0_transaction);
    
    // UVM Factory Registration
    `uvm_component_utils(axi_master0_sequencer)
    
    // Constructor
    function new(string name = "axi_master0_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
endclass : axi_master0_sequencer

//=============================================================================
// AXI Master 0 Agent
//=============================================================================
class axi_master0_agent extends uvm_agent;
    
    // UVM Factory Registration
    `uvm_component_utils(axi_master0_agent)
    
    // Agent components
    axi_master0_driver    driver;
    axi_master0_monitor   monitor;
    axi_master0_sequencer sequencer;
    
    // Configuration
    axi_master0_config cfg;
    
    // Agent type (active or passive)
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    
    // Constructor
    function new(string name = "axi_master0_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db #(axi_master0_config)::get(this, "", "cfg", cfg)) begin
            `uvm_fatal("CFG_ERROR", "axi_master0_config not found in config_db")
        end
        
        // Create monitor (always created)
        monitor = axi_master0_monitor::type_id::create("monitor", this);
        
        // Create active components if agent is active
        if (is_active == UVM_ACTIVE) begin
            sequencer = axi_master0_sequencer::type_id::create("sequencer", this);
            driver = axi_master0_driver::type_id::create("driver", this);
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
    
endclass : axi_master0_agent

//=============================================================================
// AXI Master 0 Configuration
//=============================================================================
class axi_master0_config extends uvm_object;
    
    // UVM Factory Registration
    `uvm_object_utils(axi_master0_config)
    
    // Configuration parameters
    int unsigned master_id = 0;
    int unsigned timeout = 1000;
    bit enable_coverage = 1;
    bit enable_checks = 1;
    
    // Constructor
    function new(string name = "axi_master0_config");
        super.new(name);
    endfunction
    
endclass : axi_master0_config

`endif // AXI_MASTER0_AGENT_SV


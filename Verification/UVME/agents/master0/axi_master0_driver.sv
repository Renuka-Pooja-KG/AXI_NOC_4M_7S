//=============================================================================
// AXI Master 0 Driver
//=============================================================================
// This file contains the Master 0 UVM driver component for the NOC verification
// environment. It drives AXI transactions on the Master 0 interface.

`ifndef AXI_MASTER0_DRIVER_SV
`define AXI_MASTER0_DRIVER_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

`include "axi_interfaces_pkg.sv"
`include "axi_transactions_pkg.sv"

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

`endif // AXI_MASTER0_DRIVER_SV


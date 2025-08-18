//=============================================================================
// AXI Master 0 Monitor
//=============================================================================
// This file contains the Master 0 UVM monitor component for the NOC verification
// environment. It monitors and captures AXI transactions on the Master 0 interface.

`ifndef AXI_MASTER0_MONITOR_SV
`define AXI_MASTER0_MONITOR_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

`include "axi_interfaces_pkg.sv"
`include "axi_transactions_pkg.sv"

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
            
            // Determine slave ID from address
            trans.slave_id = get_slave_id_from_addr(trans.addr);
            
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
            
            `uvm_info("MONITOR", $sformatf("Master 0 Write monitored: Addr=0x%08X, Slave=%0d, Resp=%s", 
                                          trans.addr, trans.slave_id, trans.resp.name()), UVM_MEDIUM)
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
            
            // Determine slave ID from address
            trans.slave_id = get_slave_id_from_addr(trans.addr);
            
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
            
            `uvm_info("MONITOR", $sformatf("Master 0 Read monitored: Addr=0x%08X, Slave=%0d, Data=0x%08X", 
                                          trans.addr, trans.slave_id, trans.data[0]), UVM_MEDIUM)
        end
    endtask
    
    // Get slave ID from address
    function int get_slave_id_from_addr(input [31:0] addr);
        case(1)
            (addr >= 32'h0000_0000 && addr <= 32'h0000_0FFF): return 0; // S0
            (addr >= 32'h0000_2000 && addr <= 32'h0000_2FFF): return 1; // S1
            (addr >= 32'h0000_4000 && addr <= 32'h0000_4FFF): return 2; // S2
            (addr >= 32'h0000_6000 && addr <= 32'h0000_6FFF): return 3; // S3
            (addr >= 32'h0000_8000 && addr <= 32'h0000_8FFF): return 4; // S4
            (addr >= 32'h0000_A000 && addr <= 32'h0000_AFFF): return 5; // S5
            (addr >= 32'h0000_C000 && addr <= 32'h0000_CFFF): return 6; // S6
            default: return -1; // Invalid address
        endcase
    endfunction
    
endclass : axi_master0_monitor

`endif // AXI_MASTER0_MONITOR_SV


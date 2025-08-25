//=============================================================================
// AXI Slave Coverage
//=============================================================================
// Separate coverage file for slave interface

`ifndef AXI_SLAVE_COVERAGE_SV
`define AXI_SLAVE_COVERAGE_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

class axi_slave_coverage extends uvm_component;
    `uvm_component_utils(axi_slave_coverage)

    // Virtual interface
    virtual axi_slave_interface.slave_modport vif;

    // Coverage groups
    covergroup aw_channel_cg @(posedge vif.clk);
        awid_cp: coverpoint vif.awid {
            bins low_id = {[0:7]};
            bins high_id = {[8:15]};
        }
        
        awaddr_cp: coverpoint vif.awaddr {
            bins low_addr = {[0:32'h3FFF_FFFF]};
            bins high_addr = {[32'h4000_0000:32'h7FFF_FFFF]};
            bins very_high_addr = {[32'h8000_0000:32'hFFFF_FFFF]};
        }
        
        awburst_cp: coverpoint vif.awburst {
            bins fixed = {2'b00};
            bins incr  = {2'b01};
            bins wrap  = {2'b10};
            bins reserved = {2'b11};
        }
        
        awlen_cp: coverpoint vif.awlen {
            bins single = {0};
            bins small_burst = {[1:7]};
            bins medium_burst = {[8:15]};
            bins large_burst = {[16:255]};
        }
        
        awsize_cp: coverpoint vif.awsize {
            bins byte = {0};
            bins halfword = {1};
            bins word = {2};
            bins doubleword = {3};
        }
        
        // Cross coverage
        awburst_awlen_cross: cross awburst_cp, awlen_cp;
        awsize_awlen_cross: cross awsize_cp, awlen_cp;
    endgroup

    covergroup w_channel_cg @(posedge vif.clk);
        wstrb_cp: coverpoint vif.wstrb {
            bins byte0 = {4'b0001};
            bins byte1 = {4'b0010};
            bins byte2 = {4'b0100};
            bins byte3 = {4'b1000};
            bins halfword_lower = {4'b0011};
            bins halfword_upper = {4'b1100};
            bins full_word = {4'b1111};
        }
        
        wlast_cp: coverpoint vif.wlast;
    endgroup

    covergroup ar_channel_cg @(posedge vif.clk);
        arid_cp: coverpoint vif.arid;
        araddr_cp: coverpoint vif.araddr;
        arburst_cp: coverpoint vif.arburst;
        arlen_cp: coverpoint vif.arlen;
        arsize_cp: coverpoint vif.arsize;
        
        // Cross coverage
        arburst_arlen_cross: cross arburst_cp, arlen_cp;
    endgroup

    covergroup response_cg @(posedge vif.clk);
        bresp_cp: coverpoint vif.bresp {
            bins okay = {2'b00};
            bins exokay = {2'b01};
            bins slverr = {2'b10};
            bins decerr = {2'b11};
        }
        
        rresp_cp: coverpoint vif.rresp {
            bins okay = {2'b00};
            bins exokay = {2'b01};
            bins slverr = {2'b10};
            bins decerr = {2'b11};
        }
    endgroup

    // Constructor
    function new(string name = "axi_slave_coverage", uvm_component parent = null);
        super.new(name, parent);
        
        // Create coverage groups
        aw_channel_cg = new();
        w_channel_cg = new();
        ar_channel_cg = new();
        response_cg = new();
    endfunction

    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(virtual axi_slave_interface.slave_modport)::get(this, "", "vif", vif)) begin
            `uvm_fatal("COVERAGE", "Virtual interface not found")
        end
    endfunction

endclass

`endif // AXI_SLAVE_COVERAGE_SV
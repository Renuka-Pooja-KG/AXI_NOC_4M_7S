//=============================================================================
// AXI Master Coverage
//=============================================================================
// Separate coverage file for master interface

`ifndef AXI_MASTER_COVERAGE_SV
`define AXI_MASTER_COVERAGE_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

class axi_master_coverage extends uvm_component;
    `uvm_component_utils(axi_master_coverage)

    // Virtual interface
    virtual axi_master_interface.monitor vif;

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
        
        awlock_cp: coverpoint vif.awlock {
            bins normal = {0};
            bins exclusive = {1};
        }
        
        awcache_cp: coverpoint vif.awcache {
            bins bufferable = {[0,1,4,5,8,9,12,13]};
            bins cacheable = {[2,3,6,7,10,11,14,15]};
        }
        
        awprot_cp: coverpoint vif.awprot {
            bins unprivileged = {[0,2,4,6]};
            bins privileged = {[1,3,5,7]};
        }
        
        awqos_cp: coverpoint vif.awqos;
        awregion_cp: coverpoint vif.awregion;
        
        // Cross coverage
        awburst_awlen_cross: cross awburst_cp, awlen_cp;
        awsize_awlen_cross: cross awsize_cp, awlen_cp;
        awburst_awsize_cross: cross awburst_cp, awsize_cp;
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
            bins partial_word = {4'b0101, 4'b1010, 4'b1101, 4'b0111, 4'b1011, 4'b1110};
        }
        
        wlast_cp: coverpoint vif.wlast;
        wvalid_cp: coverpoint vif.wvalid;
    endgroup

    covergroup ar_channel_cg @(posedge vif.clk);
        arid_cp: coverpoint vif.arid {
            bins low_id = {[0:7]};
            bins high_id = {[8:15]};
        }
        
        araddr_cp: coverpoint vif.araddr {
            bins low_addr = {[0:32'h3FFF_FFFF]};
            bins high_addr = {[32'h4000_0000:32'h7FFF_FFFF]};
            bins very_high_addr = {[32'h8000_0000:32'hFFFF_FFFF]};
        }
        
        arburst_cp: coverpoint vif.arburst {
            bins fixed = {2'b00};
            bins incr  = {2'b01};
            bins wrap  = {2'b10};
            bins reserved = {2'b11};
        }
        
        arlen_cp: coverpoint vif.arlen {
            bins single = {0};
            bins small_burst = {[1:7]};
            bins medium_burst = {[8:15]};
            bins large_burst = {[16:255]};
        }
        
        arsize_cp: coverpoint vif.arsize {
            bins byte = {0};
            bins halfword = {1};
            bins word = {2};
            bins doubleword = {3};
        }
        
        arlock_cp: coverpoint vif.arlock {
            bins normal = {0};
            bins exclusive = {1};
        }
        
        arcache_cp: coverpoint vif.arcache;
        arprot_cp: coverpoint vif.arprot;
        arqos_cp: coverpoint vif.arqos;
        arregion_cp: coverpoint vif.arregion;
        
        // Cross coverage
        arburst_arlen_cross: cross arburst_cp, arlen_cp;
        arsize_arlen_cross: cross arsize_cp, arlen_cp;
        arburst_arsize_cross: cross arburst_cp, arsize_cp;
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
        
        bid_cp: coverpoint vif.bid;
        rid_cp: coverpoint vif.rid;
        rlast_cp: coverpoint vif.rlast;
    endgroup

    covergroup handshake_cg @(posedge vif.clk);
        // Write address handshake
        aw_handshake_cp: coverpoint {vif.awvalid, vif.awready} {
            bins idle = {2'b00};
            bins wait_ready = {2'b10};
            bins transfer = {2'b11};
        }
        
        // Write data handshake
        w_handshake_cp: coverpoint {vif.wvalid, vif.wready} {
            bins idle = {2'b00};
            bins wait_ready = {2'b10};
            bins transfer = {2'b11};
        }
        
        // Write response handshake
        b_handshake_cp: coverpoint {vif.bvalid, vif.bready} {
            bins idle = {2'b00};
            bins wait_ready = {2'b01};
            bins transfer = {2'b11};
        }
        
        // Read address handshake
        ar_handshake_cp: coverpoint {vif.arvalid, vif.arready} {
            bins idle = {2'b00};
            bins wait_ready = {2'b10};
            bins transfer = {2'b11};
        }
        
        // Read data handshake
        r_handshake_cp: coverpoint {vif.rvalid, vif.rready} {
            bins idle = {2'b00};
            bins wait_ready = {2'b01};
            bins transfer = {2'b11};
        }
    endgroup

    // Constructor
    function new(string name = "axi_master_coverage", uvm_component parent = null);
        super.new(name, parent);
        
        // Create coverage groups
        aw_channel_cg = new();
        w_channel_cg = new();
        ar_channel_cg = new();
        response_cg = new();
        handshake_cg = new();
    endfunction

    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(virtual axi_master_interface.monitor)::get(this, "", "vif", vif)) begin
            `uvm_fatal("COVERAGE", "Virtual interface not found")
        end
    endfunction

    // Run phase - optional additional coverage logic
    task run_phase(uvm_phase phase);
        super.run_phase(phase);
        
        // Monitor for specific coverage scenarios
        forever begin
            @(posedge vif.clk);
            
            // Cover burst completion
            if (vif.wvalid && vif.wready && vif.wlast) begin
                // Burst write completed
            end
            
            if (vif.rvalid && vif.rready && vif.rlast) begin
                // Burst read completed
            end
        end
    endtask

endclass

`endif // AXI_MASTER_COVERAGE_SV
//=============================================================================
// AXI Master 0 Agent
//=============================================================================
// This file contains the Master 0 UVM agent component for the NOC verification
// environment. It orchestrates the driver, monitor, and sequencer components.

`ifndef AXI_MASTER0_AGENT_SV
`define AXI_MASTER0_AGENT_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

`include "axi_master0_driver.sv"
`include "axi_master0_monitor.sv"
`include "axi_master0_sequencer.sv"
`include "axi_master0_config.sv"

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
    
    // Set agent type (active or passive)
    function void set_agent_type(input uvm_active_passive_enum agent_type);
        is_active = agent_type;
    endfunction
    
    // Get agent type
    function uvm_active_passive_enum get_agent_type();
        return is_active;
    endfunction
    
    // Get monitor reference
    function axi_master0_monitor get_monitor();
        return monitor;
    endfunction
    
    // Get driver reference (if active)
    function axi_master0_driver get_driver();
        if (is_active == UVM_ACTIVE) return driver;
        else return null;
    endfunction
    
    // Get sequencer reference (if active)
    function axi_master0_sequencer get_sequencer();
        if (is_active == UVM_ACTIVE) return sequencer;
        else return null;
    endfunction
    
endclass : axi_master0_agent

`endif // AXI_MASTER0_AGENT_SV

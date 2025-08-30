//=============================================================================
// S6 Agent Class
//=============================================================================
// Agent for Slave 6 that instantiates and connects S6 driver, monitor, and sequencer
// Extends uvm_agent to provide complete S6 verification functionality

`ifndef S6_AGENT_SV
`define S6_AGENT_SV

// Note: All imports and includes will be handled by define_files_package

class S6_agent extends uvm_agent;
    `uvm_component_utils(S6_agent)

    S6_monitor s6_monitor;
    S6_driver s6_driver;
    S6_sequencer s6_sequencer;
    
    // Agent configuration
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S6_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== BUILD PHASE =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Build monitor (always built)
        s6_monitor = S6_monitor::type_id::create("s6_monitor", this);
        
        // Build driver and sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s6_driver = S6_driver::type_id::create("s6_driver", this);
            s6_sequencer = S6_sequencer::type_id::create("s6_sequencer", this);
        end
    endfunction
    
    // ===== CONNECT PHASE =====
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver to sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s6_driver.seq_item_port.connect(s6_sequencer.seq_item_export);
        end
        
        // Monitor analysis port connections will be handled at environment level
        // s6_monitor.item_collected_port.connect(...);
    endfunction
    
endclass
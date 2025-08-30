//=============================================================================
// S0 Agent Class
//=============================================================================
// Agent for Slave 0 that instantiates and connects S0 driver, monitor, and sequencer
// Extends uvm_agent to provide complete S0 verification functionality

`ifndef S0_AGENT_SV
`define S0_AGENT_SV

// Note: All imports and includes will be handled by define_files_package

class S0_agent extends uvm_agent;
    `uvm_component_utils(S0_agent)

    S0_monitor s0_monitor;
    S0_driver s0_driver;
    S0_sequencer s0_sequencer;
    
    // Agent configuration
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S0_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== BUILD PHASE =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Build monitor (always built)
        s0_monitor = S0_monitor::type_id::create("s0_monitor", this);
        
        // Build driver and sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s0_driver = S0_driver::type_id::create("s0_driver", this);
            s0_sequencer = S0_sequencer::type_id::create("s0_sequencer", this);
        end
    endfunction
    
    // ===== CONNECT PHASE =====
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver to sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s0_driver.seq_item_port.connect(s0_sequencer.seq_item_export);
        end
        
        // Monitor analysis port connections will be handled at environment level
        // s0_monitor.item_collected_port.connect(...);
    endfunction
    
endclass
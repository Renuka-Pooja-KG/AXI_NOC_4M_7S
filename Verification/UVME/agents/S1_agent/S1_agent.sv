//=============================================================================
// S1 Agent Class
//=============================================================================
// Agent for Slave 1 that instantiates and connects S1 driver, monitor, and sequencer
// Extends uvm_agent to provide complete S1 verification functionality

`ifndef S1_AGENT_SV
`define S1_AGENT_SV

// Note: All imports and includes will be handled by define_files_package

class S1_agent extends uvm_agent;
    `uvm_component_utils(S1_agent)

    S1_monitor s1_monitor;
    S1_driver s1_driver;
    S1_sequencer s1_sequencer;
    
    // Agent configuration
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S1_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== BUILD PHASE =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Build monitor (always built)
        s1_monitor = S1_monitor::type_id::create("s1_monitor", this);
        
        // Build driver and sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s1_driver = S1_driver::type_id::create("s1_driver", this);
            s1_sequencer = S1_sequencer::type_id::create("s1_sequencer", this);
        end
    endfunction
    
    // ===== CONNECT PHASE =====
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver to sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s1_driver.seq_item_port.connect(s1_sequencer.seq_item_export);
        end
        
        // Monitor analysis port connections will be handled at environment level
        // s1_monitor.item_collected_port.connect(...);
    endfunction
    
endclass
//=============================================================================
// S2 Agent Class
//=============================================================================
// Agent for Slave 2 that instantiates and connects S2 driver, monitor, and sequencer
// Extends uvm_agent to provide complete S2 verification functionality

`ifndef S2_AGENT_SV
`define S2_AGENT_SV

// Note: All imports and includes will be handled by define_files_package

class S2_agent extends uvm_agent;
    `uvm_component_utils(S2_agent)

    S2_monitor s2_monitor;
    S2_driver s2_driver;
    S2_sequencer s2_sequencer;
    
    // Agent configuration
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S2_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== BUILD PHASE =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Build monitor (always built)
        s2_monitor = S2_monitor::type_id::create("s2_monitor", this);
        
        // Build driver and sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s2_driver = S2_driver::type_id::create("s2_driver", this);
            s2_sequencer = S2_sequencer::type_id::create("s2_sequencer", this);
        end
    endfunction
    
    // ===== CONNECT PHASE =====
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver to sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s2_driver.seq_item_port.connect(s2_sequencer.seq_item_export);
        end
        
        // Monitor analysis port connections will be handled at environment level
        // s2_monitor.item_collected_port.connect(...);
    endfunction
    
endclass

`endif // S2_AGENT_SV
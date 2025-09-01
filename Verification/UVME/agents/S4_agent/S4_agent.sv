//=============================================================================
// S4 Agent Class
//=============================================================================
// Agent for Slave 4 that instantiates and connects S4 driver, monitor, and sequencer
// Extends uvm_agent to provide complete S4 verification functionality

`ifndef S4_AGENT_SV
`define S4_AGENT_SV

// Note: All imports and includes will be handled by define_files_package

class S4_agent extends uvm_agent;
    `uvm_component_utils(S4_agent)

    S4_monitor s4_monitor;
    S4_driver s4_driver;
    S4_sequencer s4_sequencer;
    
    // Agent configuration
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S4_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== BUILD PHASE =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Build monitor (always built)
        s4_monitor = S4_monitor::type_id::create("s4_monitor", this);
        
        // Build driver and sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s4_driver = S4_driver::type_id::create("s4_driver", this);
            s4_sequencer = S4_sequencer::type_id::create("s4_sequencer", this);
        end
    endfunction
    
    // ===== CONNECT PHASE =====
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver to sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s4_driver.seq_item_port.connect(s4_sequencer.seq_item_export);
        end
        
        // Monitor analysis port connections will be handled at environment level
        // s4_monitor.item_collected_port.connect(...);
    endfunction
    
endclass

`endif // S4_AGENT_SV
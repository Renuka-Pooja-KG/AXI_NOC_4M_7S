//=============================================================================
// S5 Agent Class
//=============================================================================
// Agent for Slave 5 that instantiates and connects S5 driver, monitor, and sequencer
// Extends uvm_agent to provide complete S5 verification functionality

`ifndef S5_AGENT_SV
`define S5_AGENT_SV

// Note: All imports and includes will be handled by define_files_package

class S5_agent extends uvm_agent;
    `uvm_component_utils(S5_agent)

    S5_monitor s5_monitor;
    S5_driver s5_driver;
    S5_sequencer s5_sequencer;
    
    // Agent configuration
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S5_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== BUILD PHASE =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Build monitor (always built)
        s5_monitor = S5_monitor::type_id::create("s5_monitor", this);
        
        // Build driver and sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s5_driver = S5_driver::type_id::create("s5_driver", this);
            s5_sequencer = S5_sequencer::type_id::create("s5_sequencer", this);
        end
    endfunction
    
    // ===== CONNECT PHASE =====
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver to sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s5_driver.seq_item_port.connect(s5_sequencer.seq_item_export);
        end
        
        // Monitor analysis port connections will be handled at environment level
        // s5_monitor.item_collected_port.connect(...);
    endfunction
    
endclass
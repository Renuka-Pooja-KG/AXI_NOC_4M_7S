//=============================================================================
// S3 Agent Class
//=============================================================================
// Agent for Slave 3 that instantiates and connects S3 driver, monitor, and sequencer
// Extends uvm_agent to provide complete S3 verification functionality

`ifndef S3_AGENT_SV
`define S3_AGENT_SV

// Note: All imports and includes will be handled by define_files_package

class S3_agent extends uvm_agent;
    `uvm_component_utils(S3_agent)

    S3_monitor s3_monitor;
    S3_driver s3_driver;
    S3_sequencer s3_sequencer;
    
    // Agent configuration
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S3_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== BUILD PHASE =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Build monitor (always built)
        s3_monitor = S3_monitor::type_id::create("s3_monitor", this);
        
        // Build driver and sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s3_driver = S3_driver::type_id::create("s3_driver", this);
            s3_sequencer = S3_sequencer::type_id::create("s3_sequencer", this);
        end
    endfunction
    
    // ===== CONNECT PHASE =====
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect driver to sequencer only if agent is active
        if (is_active == UVM_ACTIVE) begin
            s3_driver.seq_item_port.connect(s3_sequencer.seq_item_export);
        end
        
        // Monitor analysis port connections will be handled at environment level
        // s3_monitor.item_collected_port.connect(...);
    endfunction
    
endclass
class M0_agent extends uvm_agent;
    `uvm_component_utils(M0_agent)

    M0_monitor m0_monitor;
    M0_driver m0_driver;
    M0_sequencer m0_sequencer;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        m0_monitor = M0_monitor::type_id::create("m0_monitor", this);
        m0_driver = M0_driver::type_id::create("m0_driver", this);
        m0_sequencer = M0_sequencer::type_id::create("m0_sequencer", this);
        `uvm_info("M0_AGENT", "M0_agent build_phase completed", UVM_LOW)
        `uvm_info("M0_AGENT", $sformatf("M0_monitor created successfully: %p", m0_monitor), UVM_LOW)
        `uvm_info("M0_AGENT", $sformatf("M0_driver created successfully: %p", m0_driver), UVM_LOW)
        `uvm_info("M0_AGENT", $sformatf("M0_sequencer created successfully: %p", m0_sequencer), UVM_LOW)
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        `uvm_info("M0_AGENT", "M0_agent connect_phase started", UVM_LOW)
        m0_driver.seq_item_port.connect(m0_sequencer.seq_item_export);
    endfunction
    
    
endclass
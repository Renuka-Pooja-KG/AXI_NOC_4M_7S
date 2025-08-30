class M2_agent extends uvm_agent;
    `uvm_component_utils(M2_agent)

    M2_monitor m2_monitor;
    M2_driver m2_driver;
    M2_sequencer m2_sequencer;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        m2_monitor = M2_monitor::type_id::create("m2_monitor", this);
        m2_driver = M2_driver::type_id::create("m2_driver", this);
        m2_sequencer = M2_sequencer::type_id::create("m2_sequencer", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        m2_driver.seq_item_port.connect(m2_sequencer.seq_item_export);
    endfunction
    
    
endclass
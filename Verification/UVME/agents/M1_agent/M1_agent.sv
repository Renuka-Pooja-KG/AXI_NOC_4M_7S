class M1_agent extends uvm_agent;
    `uvm_component_utils(M1_agent)

    M1_monitor m1_monitor;
    M1_driver m1_driver;
    M1_sequencer m1_sequencer;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        m1_monitor = M1_monitor::type_id::create("m1_monitor", this);
        m1_driver = M1_driver::type_id::create("m1_driver", this);
        m1_sequencer = M1_sequencer::type_id::create("m1_sequencer", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        m1_driver.seq_item_port.connect(m1_sequencer.seq_item_export);
    endfunction
    
    
endclass
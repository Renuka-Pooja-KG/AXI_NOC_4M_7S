class M3_agent extends uvm_agent;
    `uvm_component_utils(M3_agent)

    M3_monitor m3_monitor;
    M3_driver m3_driver;
    M3_sequencer m3_sequencer;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        m3_monitor = M3_monitor::type_id::create("m3_monitor", this);
        m3_driver = M3_driver::type_id::create("m3_driver", this);
        m3_sequencer = M3_sequencer::type_id::create("m3_sequencer", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        m3_driver.seq_item_port.connect(m3_sequencer.seq_item_export);
    endfunction
    
    
endclass
//=============================================================================
// S2 Agent Sequencer Class
//=============================================================================
// Simple sequencer for Slave 2 that manages sequence execution
// Extends uvm_sequencer to handle S2 sequence items

`ifndef S2_SEQUENCER_SV
`define S2_SEQUENCER_SV

// Note: All imports and includes will be handled by define_files_package

class S2_sequencer extends uvm_sequencer #(S2_seq_item);
    
    // UVM component utilities
    `uvm_component_utils(S2_sequencer)
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S2_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== UVM PHASES =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
endclass

`endif // S2_SEQUENCER_SV
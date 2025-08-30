//=============================================================================
// S5 Agent Sequencer Class
//=============================================================================
// Simple sequencer for Slave 5 that manages sequence execution
// Extends uvm_sequencer to handle S5 sequence items

`ifndef S5_SEQUENCER_SV
`define S5_SEQUENCER_SV

// Note: All imports and includes will be handled by define_files_package

class S5_sequencer extends uvm_sequencer #(S5_seq_item);
    
    // UVM component utilities
    `uvm_component_utils(S5_sequencer)
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S5_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== UVM PHASES =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
endclass
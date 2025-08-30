//=============================================================================
// S1 Agent Sequencer Class
//=============================================================================
// Simple sequencer for Slave 1 that manages sequence execution
// Extends uvm_sequencer to handle S1 sequence items

`ifndef S1_SEQUENCER_SV
`define S1_SEQUENCER_SV

// Note: All imports and includes will be handled by define_files_package

class S1_sequencer extends uvm_sequencer #(S1_seq_item);
    
    // UVM component utilities
    `uvm_component_utils(S1_sequencer)
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S1_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== UVM PHASES =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
endclass
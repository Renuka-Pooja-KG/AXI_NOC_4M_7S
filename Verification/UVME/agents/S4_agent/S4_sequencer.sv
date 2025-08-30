//=============================================================================
// S4 Agent Sequencer Class
//=============================================================================
// Simple sequencer for Slave 4 that manages sequence execution
// Extends uvm_sequencer to handle S4 sequence items

`ifndef S4_SEQUENCER_SV
`define S4_SEQUENCER_SV

// Note: All imports and includes will be handled by define_files_package

class S4_sequencer extends uvm_sequencer #(S4_seq_item);
    
    // UVM component utilities
    `uvm_component_utils(S4_sequencer)
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S4_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== UVM PHASES =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
endclass
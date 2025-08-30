//=============================================================================
// S6 Agent Sequencer Class
//=============================================================================
// Simple sequencer for Slave 6 that manages sequence execution
// Extends uvm_sequencer to handle S6 sequence items

`ifndef S6_SEQUENCER_SV
`define S6_SEQUENCER_SV

// Note: All imports and includes will be handled by define_files_package

class S6_sequencer extends uvm_sequencer #(S6_seq_item);
    
    // UVM component utilities
    `uvm_component_utils(S6_sequencer)
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S6_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== UVM PHASES =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
endclass
//=============================================================================
// S3 Agent Sequencer Class
//=============================================================================
// Simple sequencer for Slave 3 that manages sequence execution
// Extends uvm_sequencer to handle S3 sequence items

`ifndef S3_SEQUENCER_SV
`define S3_SEQUENCER_SV

// Note: All imports and includes will be handled by define_files_package

class S3_sequencer extends uvm_sequencer #(S3_seq_item);
    
    // UVM component utilities
    `uvm_component_utils(S3_sequencer)
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S3_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== UVM PHASES =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
endclass
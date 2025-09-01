//=============================================================================
// S0 Agent Sequencer Class
//=============================================================================
// Simple sequencer for Slave 0 that manages sequence execution
// Extends uvm_sequencer to handle S0 sequence items

`ifndef S0_SEQUENCER_SV
`define S0_SEQUENCER_SV

// Note: All imports and includes will be handled by define_files_package

class S0_sequencer extends uvm_sequencer #(S0_seq_item);
    
    // UVM component utilities
    `uvm_component_utils(S0_sequencer)
    
    // ===== CONSTRUCTOR =====
    function new(string name = "S0_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== UVM PHASES =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
endclass

`endif // S0_SEQUENCER_SV
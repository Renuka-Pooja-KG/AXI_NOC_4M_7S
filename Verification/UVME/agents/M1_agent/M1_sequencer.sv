//=============================================================================
// M1 Agent Basic Sequencer Class
//=============================================================================
// Simple sequencer for Master 1 - designed to work with virtual sequencer
// Extends uvm_sequencer to handle M1 sequence items

`ifndef M1_SEQUENCER_SV
`define M1_SEQUENCER_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the M1 sequence item
import axi_common_types_pkg::*;

class M1_sequencer extends uvm_sequencer#(M1_seq_item);
    `uvm_component_utils(M1_sequencer)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
endclass

`endif // M1_SEQUENCER_SV
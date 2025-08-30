//=============================================================================
// M2 Agent Basic Sequencer Class
//=============================================================================
// Simple sequencer for Master 2 - designed to work with virtual sequencer
// Extends uvm_sequencer to handle M2 sequence items

`ifndef M2_SEQUENCER_SV
`define M2_SEQUENCER_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the M2 sequence item
import axi_common_types_pkg::*;

class M2_sequencer extends uvm_sequencer#(M2_seq_item);
    `uvm_component_utils(M2_sequencer)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
endclass

`endif // M2_SEQUENCER_SV
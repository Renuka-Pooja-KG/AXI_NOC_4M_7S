//=============================================================================
// M3 Agent Basic Sequencer Class
//=============================================================================
// Simple sequencer for Master 3 - designed to work with virtual sequencer
// Extends uvm_sequencer to handle M3 sequence items

`ifndef M3_SEQUENCER_SV
`define M3_SEQUENCER_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the M3 sequence item
import axi_common_types_pkg::*;

class M3_sequencer extends uvm_sequencer#(M3_seq_item);
    `uvm_component_utils(M3_sequencer)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
endclass

`endif // M3_SEQUENCER_SV
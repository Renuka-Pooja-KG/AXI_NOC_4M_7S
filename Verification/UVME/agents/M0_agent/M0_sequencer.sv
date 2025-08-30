//=============================================================================
// M0 Agent Basic Sequencer Class
//=============================================================================
// Simple sequencer for Master 0 - designed to work with virtual sequencer
// Extends uvm_sequencer to handle M0 sequence items

`ifndef M0_SEQUENCER_SV
`define M0_SEQUENCER_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

// Import the M0 sequence item
import axi_common_types_pkg::*;

class M0_sequencer extends uvm_sequencer#(M0_seq_item);
    `uvm_component_utils(M0_sequencer)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
endclass

`endif // M0_SEQUENCER_SV
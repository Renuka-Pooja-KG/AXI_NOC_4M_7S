//=============================================================================
// AXI Master 0 Sequencer
//=============================================================================
// This file contains the Master 0 UVM sequencer component for the NOC verification
// environment. It manages transaction sequences for Master 0.

`ifndef AXI_MASTER0_SEQUENCER_SV
`define AXI_MASTER0_SEQUENCER_SV

import uvm_pkg::*;
`include "uvm_macros.svh"

`include "axi_transactions_pkg.sv"

class axi_master0_sequencer extends uvm_sequencer #(axi_master0_transaction);
    
    // UVM Factory Registration
    `uvm_component_utils(axi_master0_sequencer)
    
    // Constructor
    function new(string name = "axi_master0_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
endclass : axi_master0_sequencer

`endif // AXI_MASTER0_SEQUENCER_SV


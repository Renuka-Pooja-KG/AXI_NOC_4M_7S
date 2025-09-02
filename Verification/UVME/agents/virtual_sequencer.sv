//=============================================================================
// Virtual Sequencer Class
//=============================================================================
// Coordinates sequences across all master and slave agents
// Manages sub-sequencers for M0, M1, M2, M3 and S0, S1, S2, S3, S4, S5, S6

`ifndef VIRTUAL_SEQUENCER_SV
`define VIRTUAL_SEQUENCER_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class virtual_sequencer extends uvm_sequencer;
    
    //--- Factory Registration -------//
    `uvm_component_utils(virtual_sequencer)
    
    //--- Sub-sequencer Declarations -------//
    // Master sequencers
    M0_sequencer M0_seqr;
    M1_sequencer M1_seqr;
    M2_sequencer M2_seqr;
    M3_sequencer M3_seqr;
    
    // Slave sequencers
    S0_sequencer S0_seqr;
    S1_sequencer S1_seqr;
    S2_sequencer S2_seqr;
    S3_sequencer S3_seqr;
    S4_sequencer S4_seqr;
    S5_sequencer S5_seqr;
    S6_sequencer S6_seqr;
    
    //--- Constructor -------//
    function new(string name = "virtual_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    //--- Build Phase -------//
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
    //--- Connect Phase -------//
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Get references to sub-sequencers from config database
        if (!uvm_config_db#(M0_sequencer)::get(this.get_parent(), "virtual_seqr", "m0_sequencer", M0_seqr))
            `uvm_fatal("VIRTUAL_SEQ", "M0_sequencer not found")
            
        if (!uvm_config_db#(M1_sequencer)::get(this.get_parent(), "virtual_seqr", "m1_sequencer", M1_seqr))
            `uvm_fatal("VIRTUAL_SEQ", "M1_sequencer not found")
            
        if (!uvm_config_db#(M2_sequencer)::get(this.get_parent(), "virtual_seqr", "m2_sequencer", M2_seqr))
            `uvm_fatal("VIRTUAL_SEQ", "M2_sequencer not found")
            
        if (!uvm_config_db#(M3_sequencer)::get(this.get_parent(), "virtual_seqr", "m3_sequencer", M3_seqr))
            `uvm_fatal("VIRTUAL_SEQ", "M3_sequencer not found")
            
        if (!uvm_config_db#(S0_sequencer)::get(this.get_parent(), "virtual_seqr", "s0_sequencer", S0_seqr))
            `uvm_fatal("VIRTUAL_SEQ", "S0_sequencer not found")
            
        if (!uvm_config_db#(S1_sequencer)::get(this.get_parent(), "virtual_seqr", "s1_sequencer", S1_seqr))
            `uvm_fatal("VIRTUAL_SEQ", "S1_sequencer not found")
            
        if (!uvm_config_db#(S2_sequencer)::get(this.get_parent(), "virtual_seqr", "s2_sequencer", S2_seqr))
            `uvm_fatal("VIRTUAL_SEQ", "S2_sequencer not found")
            
        if (!uvm_config_db#(S3_sequencer)::get(this.get_parent(), "virtual_seqr", "s3_sequencer", S3_seqr))
            `uvm_fatal("VIRTUAL_SEQ", "S3_sequencer not found")
            
        if (!uvm_config_db#(S4_sequencer)::get(this.get_parent(), "virtual_seqr", "s4_sequencer", S4_seqr))
            `uvm_fatal("VIRTUAL_SEQ", "S4_sequencer not found")
            
        if (!uvm_config_db#(S5_sequencer)::get(this.get_parent(), "virtual_seqr", "s5_sequencer", S5_seqr))
            `uvm_fatal("VIRTUAL_SEQ", "S5_sequencer not found")
            
        if (!uvm_config_db#(S6_sequencer)::get(this.get_parent(), "virtual_seqr", "s6_sequencer", S6_seqr))
            `uvm_fatal("VIRTUAL_SEQ", "S6_sequencer not found")
            
        `uvm_info("VIRTUAL_SEQ", "All sub-sequencers connected successfully", UVM_LOW)
    endfunction
    
endclass

`endif // VIRTUAL_SEQUENCER_SV
//=============================================================================
// AXI NoC Virtual Sequence Class
//=============================================================================
// Coordinates sequences across all masters and slaves
// Simplified version with just reset scenario

`ifndef AXI_NOC_VIRTUAL_SEQ_SV
`define AXI_NOC_VIRTUAL_SEQ_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class axi_noc_virtual_seq extends uvm_sequence;
    `uvm_object_utils(axi_noc_virtual_seq)
    
    //--- P-Sequencer Declaration -------//
    `uvm_declare_p_sequencer(virtual_sequencer)
    
    //--- Sequence Configuration -------//
    string seq_type;
    
    //--- Sequence Handles -------//
    // Master sequences
    M0_seq M0_seqh;
    M1_seq M1_seqh;
    M2_seq M2_seqh;
    M3_seq M3_seqh;
    
    // Slave sequences
    S0_seq S0_seqh;
    S1_seq S1_seqh;
    S2_seq S2_seqh;
    S3_seq S3_seqh;
    S4_seq S4_seqh;
    S5_seq S5_seqh;
    S6_seq S6_seqh;
    
    //--- Constructor -------//
    function new(string name = "axi_noc_virtual_seq");
        super.new(name);
    endfunction
    
    //--- Body Task -------//
    virtual task body();
        case (seq_type)
            "rst": begin
                // Reset scenario - start reset sequences on all agents
                `uvm_info(get_type_name(), "Starting reset scenario", UVM_LOW)
                
                // Create and start reset sequences on all masters
                M0_seqh = M0_seq::type_id::create("M0_seqh");
                M0_seqh.scenario = 1;
                M0_seqh.start(p_sequencer.M0_seqr);
                
                M1_seqh = M1_seq::type_id::create("M1_seqh");
                M1_seqh.scenario = 1;
                M1_seqh.start(p_sequencer.M1_seqr);
                
                M2_seqh = M2_seq::type_id::create("M2_seqh");
                M2_seqh.scenario = 1;
                M2_seqh.start(p_sequencer.M2_seqr);
                
                M3_seqh = M3_seq::type_id::create("M3_seqh");
                M3_seqh.scenario = 1;
                M3_seqh.start(p_sequencer.M3_seqr);
                
                // Create and start reset sequences on all slaves
                S0_seqh = S0_seq::type_id::create("S0_seqh");
                S0_seqh.scenario = 1;
                S0_seqh.start(p_sequencer.S0_seqr);
                
                S1_seqh = S1_seq::type_id::create("S1_seqh");
                S1_seqh.scenario = 1;
                S1_seqh.start(p_sequencer.S1_seqr);
                
                S2_seqh = S2_seq::type_id::create("S2_seqh");
                S2_seqh.scenario = 1;
                S2_seqh.start(p_sequencer.S2_seqr);
                
                S3_seqh = S3_seq::type_id::create("S3_seqh");
                S3_seqh.scenario = 1;
                S3_seqh.start(p_sequencer.S3_seqr);
                
                S4_seqh = S4_seq::type_id::create("S4_seqh");
                S4_seqh.scenario = 1;
                S4_seqh.start(p_sequencer.S4_seqr);
                
                S5_seqh = S5_seq::type_id::create("S5_seqh");
                S5_seqh.scenario = 1;
                S5_seqh.start(p_sequencer.S5_seqr);
                
                S6_seqh = S6_seq::type_id::create("S6_seqh");
                S6_seqh.scenario = 1;
                S6_seqh.start(p_sequencer.S6_seqr);
                
                `uvm_info(get_type_name(), "Reset scenario completed", UVM_LOW)
            end
            
            default: begin
                `uvm_error(get_full_name(), $sformatf("Unknown seq_type: %s", seq_type))
            end
        endcase
    endtask
    
endclass

`endif // AXI_NOC_VIRTUAL_SEQ_SV
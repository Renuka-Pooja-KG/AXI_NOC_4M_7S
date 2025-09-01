//=============================================================================
// S2_seq Class
//=============================================================================
// Slave 2 specific sequence implementing different scenarios including reset

`ifndef S2_SEQ_SV
`define S2_SEQ_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class S2_seq extends uvm_sequence #(S2_seq_item);
    `uvm_object_utils(S2_seq)
    
    //--- Sequence Item Instance -------//
    S2_seq_item S2_seqi_inst;
    
    //--- Virtual Interface -------//
    virtual S2_interface S2_intf;
    
    //--- Scenario Variable -------//
    int scenario;
    
    //--- Constructor -------//
    function new(string name = "S2_seq");
        super.new(name);
    endfunction
    
    //--- Body Task -------//
    virtual task body();
        `uvm_info(get_type_name(), "base seq: inside body", UVM_LOW)
        
        // Reset scenario
        if (scenario == 1) begin
            S2_seqi_inst = S2_seq_item::type_id::create("S2_seqi_inst");
            start_item(S2_seqi_inst);
            
            // Set reset values
            S2_seqi_inst.S2_AWREADY = 1'b1;
            S2_seqi_inst.S2_WREADY = 1'b1;
            S2_seqi_inst.S2_BID = 0;
            S2_seqi_inst.S2_BRESP = 0;
            S2_seqi_inst.S2_BVALID = 1'b0;
            S2_seqi_inst.S2_ARREADY = 1'b1;
            S2_seqi_inst.S2_RID = 0;
            S2_seqi_inst.S2_RDATA = 0;
            S2_seqi_inst.S2_RRESP = 0;
            S2_seqi_inst.S2_RLAST = 0;
            S2_seqi_inst.S2_RVALID = 1'b0;
            
            finish_item(S2_seqi_inst);
        end
        
        else begin
            `uvm_error(get_full_name(), $sformatf("Unknown scenario: %0d", scenario))
        end
    endtask
    
endclass

`endif // S2_SEQ_SV
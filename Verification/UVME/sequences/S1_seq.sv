//=============================================================================
// S1_seq Class
//=============================================================================
// Slave 1 specific sequence implementing different scenarios including reset

`ifndef S1_SEQ_SV
`define S1_SEQ_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class S1_seq extends uvm_sequence #(S1_seq_item);
    `uvm_object_utils(S1_seq)
    
    //--- Sequence Item Instance -------//
    S1_seq_item S1_seqi_inst;
    
    //--- Virtual Interface -------//
    virtual S1_interface S1_intf;
    
    //--- Scenario Variable -------//
    int scenario;
    
    //--- Constructor -------//
    function new(string name = "S1_seq");
        super.new(name);
    endfunction
    
    //--- Body Task -------//
    virtual task body();
        `uvm_info(get_type_name(), "base seq: inside body", UVM_LOW)
        
        // Reset scenario
        if (scenario == 1) begin
            S1_seqi_inst = S1_seq_item::type_id::create("S1_seqi_inst");
            start_item(S1_seqi_inst);
            
            // Set reset values
            S1_seqi_inst.S1_AWREADY = 1'b1;
            S1_seqi_inst.S1_WREADY = 1'b1;
            S1_seqi_inst.S1_BID = 0;
            S1_seqi_inst.S1_BRESP = 0;
            S1_seqi_inst.S1_BVALID = 1'b0;
            S1_seqi_inst.S1_ARREADY = 1'b1;
            S1_seqi_inst.S1_RID = 0;
            S1_seqi_inst.S1_RDATA = 0;
            S1_seqi_inst.S1_RRESP = 0;
            S1_seqi_inst.S1_RLAST = 0;
            S1_seqi_inst.S1_RVALID = 1'b0;
            
            finish_item(S1_seqi_inst);
        end
        
        else begin
            `uvm_error(get_full_name(), $sformatf("Unknown scenario: %0d", scenario))
        end
    endtask
    
endclass

`endif // S1_SEQ_SV
//=============================================================================
// S6_seq Class
//=============================================================================
// Slave 6 specific sequence implementing different scenarios including reset

`ifndef S6_SEQ_SV
`define S6_SEQ_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class S6_seq extends uvm_sequence #(S6_seq_item);
    `uvm_object_utils(S6_seq)
    
    //--- Sequence Item Instance -------//
    S6_seq_item S6_seqi_inst;
    
    //--- Virtual Interface -------//
    virtual S6_interface S6_intf;
    
    //--- Scenario Variable -------//
    int scenario;
    
    //--- Constructor -------//
    function new(string name = "S6_seq");
        super.new(name);
    endfunction
    
    //--- Body Task -------//
    virtual task body();
        `uvm_info(get_type_name(), "base seq: inside body", UVM_LOW)
        
        // Reset scenario
        if (scenario == 1) begin
            S6_seqi_inst = S6_seq_item::type_id::create("S6_seqi_inst");
            start_item(S6_seqi_inst);
            
            // Set reset values
            S6_seqi_inst.S6_AWREADY = 1'b1;
            S6_seqi_inst.S6_WREADY = 1'b1;
            S6_seqi_inst.S6_BID = 0;
            S6_seqi_inst.S6_BRESP = 0;
            S6_seqi_inst.S6_BVALID = 1'b0;
            S6_seqi_inst.S6_ARREADY = 1'b1;
            S6_seqi_inst.S6_RID = 0;
            S6_seqi_inst.S6_RDATA = 0;
            S6_seqi_inst.S6_RRESP = 0;
            S6_seqi_inst.S6_RLAST = 0;
            S6_seqi_inst.S6_RVALID = 1'b0;
            
            finish_item(S6_seqi_inst);
        end
        
        else begin
            `uvm_error(get_full_name(), $sformatf("Unknown scenario: %0d", scenario))
        end
    endtask
    
endclass

`endif // S6_SEQ_SV
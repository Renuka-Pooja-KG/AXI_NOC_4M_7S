//=============================================================================
// S0_seq Class
//=============================================================================
// Slave 0 specific sequence implementing different scenarios including reset

`ifndef S0_SEQ_SV
`define S0_SEQ_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class S0_seq extends uvm_sequence #(S0_seq_item);
    `uvm_object_utils(S0_seq)
    
    //--- Sequence Item Instance -------//
    S0_seq_item S0_seqi_inst;
    
    //--- Virtual Interface -------//
    virtual S0_interface S0_intf;
    
    //--- Scenario Variable -------//
    int scenario;
    
    //--- Constructor -------//
    function new(string name = "S0_seq");
        super.new(name);
    endfunction
    
    //--- Body Task -------//
    virtual task body();
        `uvm_info(get_type_name(), "base seq: inside body", UVM_LOW)
        
        // Reset scenario
        if (scenario == 1) begin
            S0_seqi_inst = S0_seq_item::type_id::create("S0_seqi_inst");
            start_item(S0_seqi_inst);
            
            // Set reset values
            S0_seqi_inst.S0_AWREADY = 1'b1;
            S0_seqi_inst.S0_WREADY = 1'b1;
            S0_seqi_inst.S0_BID = 0;
            S0_seqi_inst.S0_BRESP = 0;
            S0_seqi_inst.S0_BVALID = 1'b0;
            S0_seqi_inst.S0_BUSER = 0;
            S0_seqi_inst.S0_ARREADY = 1'b1;
            S0_seqi_inst.S0_RID = 0;
            S0_seqi_inst.S0_RDATA = 0;
            S0_seqi_inst.S0_RRESP = 0;
            S0_seqi_inst.S0_RLAST = 0;
            S0_seqi_inst.S0_RVALID = 1'b0;
            S0_seqi_inst.S0_RUSER = 0;
            
            finish_item(S0_seqi_inst);
        end
        
        else begin
            `uvm_error(get_full_name(), $sformatf("Unknown scenario: %0d", scenario))
        end
    endtask
    
endclass

`endif // S0_SEQ_SV
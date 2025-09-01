//=============================================================================
// S5_seq Class
//=============================================================================
// Slave 5 specific sequence implementing different scenarios including reset

`ifndef S5_SEQ_SV
`define S5_SEQ_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class S5_seq extends uvm_sequence #(S5_seq_item);
    `uvm_object_utils(S5_seq)
    
    //--- Sequence Item Instance -------//
    S5_seq_item S5_seqi_inst;
    
    //--- Virtual Interface -------//
    virtual S5_interface S5_intf;
    
    //--- Scenario Variable -------//
    int scenario;
    
    //--- Constructor -------//
    function new(string name = "S5_seq");
        super.new(name);
    endfunction
    
    //--- Body Task -------//
    virtual task body();
        `uvm_info(get_type_name(), "base seq: inside body", UVM_LOW)
        
        // Reset scenario
        if (scenario == 1) begin
            S5_seqi_inst = S5_seq_item::type_id::create("S5_seqi_inst");
            start_item(S5_seqi_inst);
            
            // Set reset values
            S5_seqi_inst.S5_AWREADY = 1'b1;
            S5_seqi_inst.S5_WREADY = 1'b1;
            S5_seqi_inst.S5_BID = 0;
            S5_seqi_inst.S5_BRESP = 0;
            S5_seqi_inst.S5_BVALID = 1'b0;
            S5_seqi_inst.S5_ARREADY = 1'b1;
            S5_seqi_inst.S5_RID = 0;
            S5_seqi_inst.S5_RDATA = 0;
            S5_seqi_inst.S5_RRESP = 0;
            S5_seqi_inst.S5_RLAST = 0;
            S5_seqi_inst.S5_RVALID = 1'b0;
            
            finish_item(S5_seqi_inst);
        end
        
        else begin
            `uvm_error(get_full_name(), $sformatf("Unknown scenario: %0d", scenario))
        end
    endtask
    
endclass

`endif // S5_SEQ_SV
//=============================================================================
// S3_seq Class
//=============================================================================
// Slave 3 specific sequence implementing different scenarios including reset

`ifndef S3_SEQ_SV
`define S3_SEQ_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class S3_seq extends uvm_sequence #(S3_seq_item);
    `uvm_object_utils(S3_seq)
    
    //--- Sequence Item Instance -------//
    S3_seq_item S3_seqi_inst;
    
    //--- Virtual Interface -------//
    virtual S3_interface S3_intf;
    
    //--- Scenario Variable -------//
    int scenario;
    
    //--- Constructor -------//
    function new(string name = "S3_seq");
        super.new(name);
    endfunction
    
    //--- Body Task -------//
    virtual task body();
        `uvm_info(get_type_name(), "base seq: inside body", UVM_LOW)
        
        // Reset scenario
        if (scenario == 1) begin
            S3_seqi_inst = S3_seq_item::type_id::create("S3_seqi_inst");
            start_item(S3_seqi_inst);
            
            // Set reset values
            S3_seqi_inst.S3_AWREADY = 1'b1;
            S3_seqi_inst.S3_WREADY = 1'b1;
            S3_seqi_inst.S3_BID = 0;
            S3_seqi_inst.S3_BRESP = 0;
            S3_seqi_inst.S3_BVALID = 1'b0;
            S3_seqi_inst.S3_ARREADY = 1'b1;
            S3_seqi_inst.S3_RID = 0;
            S3_seqi_inst.S3_RDATA = 0;
            S3_seqi_inst.S3_RRESP = 0;
            S3_seqi_inst.S3_RLAST = 0;
            S3_seqi_inst.S3_RVALID = 1'b0;
            
            finish_item(S3_seqi_inst);
        end
        
        else begin
            `uvm_error(get_full_name(), $sformatf("Unknown scenario: %0d", scenario))
        end
    endtask
    
endclass

`endif // S3_SEQ_SV
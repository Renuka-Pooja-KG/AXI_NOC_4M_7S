//=============================================================================
// S4_seq Class
//=============================================================================
// Slave 4 specific sequence implementing different scenarios including reset

`ifndef S4_SEQ_SV
`define S4_SEQ_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class S4_seq extends uvm_sequence #(S4_seq_item);
    `uvm_object_utils(S4_seq)
    
    //--- Sequence Item Instance -------//
    S4_seq_item S4_seqi_inst;
    
    //--- Virtual Interface -------//
    virtual S4_interface S4_intf;
    
    //--- Scenario Variable -------//
    int scenario;
    
    //--- Constructor -------//
    function new(string name = "S4_seq");
        super.new(name);
    endfunction
    
    //--- Body Task -------//
    virtual task body();
        `uvm_info(get_type_name(), "base seq: inside body", UVM_LOW)
        
        // Reset scenario
        if (scenario == 1) begin
            S4_seqi_inst = S4_seq_item::type_id::create("S4_seqi_inst");
            start_item(S4_seqi_inst);
            
            // Set reset values
            S4_seqi_inst.S4_AWREADY = 1'b1;
            S4_seqi_inst.S4_WREADY = 1'b1;
            S4_seqi_inst.S4_BID = 0;
            S4_seqi_inst.S4_BRESP = 0;
            S4_seqi_inst.S4_BVALID = 1'b0;
            S4_seqi_inst.S4_BUSER = 0;
            S4_seqi_inst.S4_ARREADY = 1'b1;
            S4_seqi_inst.S4_RID = 0;
            S4_seqi_inst.S4_RDATA = 0;
            S4_seqi_inst.S4_RRESP = 0;
            S4_seqi_inst.S4_RLAST = 0;
            S4_seqi_inst.S4_RVALID = 1'b0;
            S4_seqi_inst.S4_RUSER = 0;
            
            finish_item(S4_seqi_inst);
        end
        
        else begin
            `uvm_error(get_full_name(), $sformatf("Unknown scenario: %0d", scenario))
        end
    endtask
    
endclass

`endif // S4_SEQ_SV
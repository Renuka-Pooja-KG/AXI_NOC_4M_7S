//=============================================================================
// M1_seq Class
//=============================================================================
// Master 1 specific sequence implementing different scenarios including reset

`ifndef M1_SEQ_SV
`define M1_SEQ_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class M1_seq extends uvm_sequence #(M1_seq_item);
    `uvm_object_utils(M1_seq)
    
    //--- Sequence Item Instance -------//
    M1_seq_item M1_seqi_inst;
    
    //--- Virtual Interface -------//
    virtual M1_interface M1_intf;
    
    //--- Scenario Variable -------//
    int scenario;
    
    //--- Constructor -------//
    function new(string name = "M1_seq");
        super.new(name);
    endfunction
    
    //--- Body Task -------//
    virtual task body();
        `uvm_info(get_type_name(), "base seq: inside body", UVM_LOW)
        
        // Reset scenario
        if (scenario == 1) begin
            M1_seqi_inst = M1_seq_item::type_id::create("M1_seqi_inst");
            start_item(M1_seqi_inst);
            
            // Set reset values
            M1_seqi_inst.M1_AWADDR = 32'h00000010;
            M1_seqi_inst.M1_AWVALID = 1'b0;
            M1_seqi_inst.M1_WVALID = 1'b0;
            M1_seqi_inst.M1_WDATA = 32'h00000000;
            M1_seqi_inst.M1_AWID = 0;
            M1_seqi_inst.M1_AWLEN = 0;
            M1_seqi_inst.M1_AWSIZE = 0;
            M1_seqi_inst.M1_AWBURST = 0;
            M1_seqi_inst.M1_AWLOCK = 0;
            M1_seqi_inst.M1_AWCACHE = 0;
            M1_seqi_inst.M1_AWPROT = 0;
            M1_seqi_inst.M1_AWQOS = 0;
            M1_seqi_inst.M1_AWREGION = 0;
            M1_seqi_inst.M1_WSTRB = 0;
            M1_seqi_inst.M1_WLAST = 0;
            M1_seqi_inst.M1_BREADY = 1'b1;
            M1_seqi_inst.M1_ARID = 0;
            M1_seqi_inst.M1_ARADDR = 0;
            M1_seqi_inst.M1_ARLEN = 0;
            M1_seqi_inst.M1_ARSIZE = 0;
            M1_seqi_inst.M1_ARBURST = 0;
            M1_seqi_inst.M1_ARLOCK = 0;
            M1_seqi_inst.M1_ARCACHE = 0;
            M1_seqi_inst.M1_ARPROT = 0;
            M1_seqi_inst.M1_ARQOS = 0;
            M1_seqi_inst.M1_ARREGION = 0;
            M1_seqi_inst.M1_ARVALID = 1'b0;
            M1_seqi_inst.M1_RREADY = 1'b1;
            
            finish_item(M1_seqi_inst);
        end
        
        else begin
            `uvm_error(get_full_name(), $sformatf("Unknown scenario: %0d", scenario))
        end
    endtask
    
endclass

`endif // M1_SEQ_SV
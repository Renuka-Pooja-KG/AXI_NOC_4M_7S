//=============================================================================
// M2_seq Class
//=============================================================================
// Master 2 specific sequence implementing different scenarios including reset

`ifndef M2_SEQ_SV
`define M2_SEQ_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class M2_seq extends uvm_sequence #(M2_seq_item);
    `uvm_object_utils(M2_seq)
    
    //--- Sequence Item Instance -------//
    M2_seq_item M2_seqi_inst;
    
    //--- Virtual Interface -------//
    virtual M2_interface M2_intf;
    
    //--- Scenario Variable -------//
    int scenario;
    
    //--- Constructor -------//
    function new(string name = "M2_seq");
        super.new(name);
    endfunction
    
    //--- Body Task -------//
    virtual task body();
        `uvm_info(get_type_name(), "base seq: inside body", UVM_LOW)
        
        // Reset scenario
        if (scenario == 1) begin
            M2_seqi_inst = M2_seq_item::type_id::create("M2_seqi_inst");
            start_item(M2_seqi_inst);
            
            // Set reset values
            M2_seqi_inst.M2_AWADDR = 32'h00000010;
            M2_seqi_inst.M2_AWVALID = 1'b0;
            M2_seqi_inst.M2_WVALID = 1'b0;
            M2_seqi_inst.M2_WDATA = 32'h00000000;
            M2_seqi_inst.M2_AWID = 0;
            M2_seqi_inst.M2_AWLEN = 0;
            M2_seqi_inst.M2_AWSIZE = 0;
            M2_seqi_inst.M2_AWBURST = 0;
            M2_seqi_inst.M2_AWLOCK = 0;
            M2_seqi_inst.M2_AWCACHE = 0;
            M2_seqi_inst.M2_AWPROT = 0;
            M2_seqi_inst.M2_AWQOS = 0;
            M2_seqi_inst.M2_AWREGION = 0;
            M2_seqi_inst.M2_WSTRB = 0;
            M2_seqi_inst.M2_WLAST = 0;
            M2_seqi_inst.M2_BREADY = 1'b1;
            M2_seqi_inst.M2_ARID = 0;
            M2_seqi_inst.M2_ARADDR = 0;
            M2_seqi_inst.M2_ARLEN = 0;
            M2_seqi_inst.M2_ARSIZE = 0;
            M2_seqi_inst.M2_ARBURST = 0;
            M2_seqi_inst.M2_ARLOCK = 0;
            M2_seqi_inst.M2_ARCACHE = 0;
            M2_seqi_inst.M2_ARPROT = 0;
            M2_seqi_inst.M2_ARQOS = 0;
            M2_seqi_inst.M2_ARREGION = 0;
            M2_seqi_inst.M2_ARVALID = 1'b0;
            M2_seqi_inst.M2_RREADY = 1'b1;
            
            finish_item(M2_seqi_inst);
        end
        
        else begin
            `uvm_error(get_full_name(), $sformatf("Unknown scenario: %0d", scenario))
        end
    endtask
    
endclass

`endif // M2_SEQ_SV
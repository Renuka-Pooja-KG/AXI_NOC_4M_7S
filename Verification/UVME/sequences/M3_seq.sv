//=============================================================================
// M3_seq Class
//=============================================================================
// Master 3 specific sequence implementing different scenarios including reset

`ifndef M3_SEQ_SV
`define M3_SEQ_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class M3_seq extends uvm_sequence #(M3_seq_item);
    `uvm_object_utils(M3_seq)
    
    //--- Sequence Item Instance -------//
    M3_seq_item M3_seqi_inst;
    
    //--- Virtual Interface -------//
    virtual M3_interface M3_intf;
    
    //--- Scenario Variable -------//
    int scenario;
    
    //--- Constructor -------//
    function new(string name = "M3_seq");
        super.new(name);
    endfunction
    
    //--- Body Task -------//
    virtual task body();
        `uvm_info(get_type_name(), "base seq: inside body", UVM_LOW)
        
        // Reset scenario
        if (scenario == 1) begin
            M3_seqi_inst = M3_seq_item::type_id::create("M3_seqi_inst");
            start_item(M3_seqi_inst);
            
            // Set reset values
            M3_seqi_inst.M3_AWADDR = 32'h00000010;
            M3_seqi_inst.M3_AWVALID = 1'b0;
            M3_seqi_inst.M3_WVALID = 1'b0;
            M3_seqi_inst.M3_WDATA = 32'h00000000;
            M3_seqi_inst.M3_AWID = 0;
            M3_seqi_inst.M3_AWLEN = 0;
            M3_seqi_inst.M3_AWSIZE = 0;
            M3_seqi_inst.M3_AWBURST = 0;
            M3_seqi_inst.M3_AWLOCK = 0;
            M3_seqi_inst.M3_AWCACHE = 0;
            M3_seqi_inst.M3_AWPROT = 0;
            M3_seqi_inst.M3_AWQOS = 0;
            M3_seqi_inst.M3_AWREGION = 0;
            M3_seqi_inst.M3_WSTRB = 0;
            M3_seqi_inst.M3_WLAST = 0;
            M3_seqi_inst.M3_BREADY = 1'b1;
            M3_seqi_inst.M3_ARID = 0;
            M3_seqi_inst.M3_ARADDR = 0;
            M3_seqi_inst.M3_ARLEN = 0;
            M3_seqi_inst.M3_ARSIZE = 0;
            M3_seqi_inst.M3_ARBURST = 0;
            M3_seqi_inst.M3_ARLOCK = 0;
            M3_seqi_inst.M3_ARCACHE = 0;
            M3_seqi_inst.M3_ARPROT = 0;
            M3_seqi_inst.M3_ARQOS = 0;
            M3_seqi_inst.M3_ARREGION = 0;
            M3_seqi_inst.M3_ARVALID = 1'b0;
            M3_seqi_inst.M3_RREADY = 1'b1;
            
            finish_item(M3_seqi_inst);
        end
        
        else begin
            `uvm_error(get_full_name(), $sformatf("Unknown scenario: %0d", scenario))
        end
    endtask
    
endclass

`endif // M3_SEQ_SV
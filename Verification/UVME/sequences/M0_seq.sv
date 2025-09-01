//=============================================================================
// M0_seq Class
//=============================================================================
// Master 0 specific sequence implementing different scenarios including reset

`ifndef M0_SEQ_SV
`define M0_SEQ_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class M0_seq extends uvm_sequence #(M0_seq_item);
    `uvm_object_utils(M0_seq)
    
    //--- Sequence Item Instance -------//
    M0_seq_item M0_seqi_inst;
    
    //--- Virtual Interface -------//
    virtual M0_interface M0_intf;
    
    //--- Scenario Variable -------//
    int scenario;
    
    //--- Constructor -------//
    function new(string name = "M0_seq");
        super.new(name);
    endfunction
    
    //--- Body Task -------//
    virtual task body();
        `uvm_info(get_type_name(), "base seq: inside body", UVM_LOW)
        
        // Reset scenario
        if (scenario == 1) begin
            // Reset scenario - commented out as shown in screenshot
            // uvm_do_with(M0_seqi_inst, {M0_seqi_inst.M0_AWADDR == 32'h00000010; 
            //                              M0_seqi_inst.M0_AWVALID == 1'b0;
            //                              M0_seqi_inst.M0_WVALID == 1'b0;
            //                              M0_seqi_inst.M0_WDATA == 32'h00000000;});
            // uvm_do(M0_seqi_inst);
            
            // Create and send reset transaction
            M0_seqi_inst = M0_seq_item::type_id::create("M0_seqi_inst");
            start_item(M0_seqi_inst);
            
            // Set reset values
            M0_seqi_inst.M0_AWADDR = 32'h00000010;
            M0_seqi_inst.M0_AWVALID = 1'b0;
            M0_seqi_inst.M0_WVALID = 1'b0;
            M0_seqi_inst.M0_WDATA = 32'h00000000;
            M0_seqi_inst.M0_AWID = 0;
            M0_seqi_inst.M0_AWLEN = 0;
            M0_seqi_inst.M0_AWSIZE = 0;
            M0_seqi_inst.M0_AWBURST = 0;
            M0_seqi_inst.M0_AWLOCK = 0;
            M0_seqi_inst.M0_AWCACHE = 0;
            M0_seqi_inst.M0_AWPROT = 0;
            M0_seqi_inst.M0_AWQOS = 0;
            M0_seqi_inst.M0_AWREGION = 0;
            M0_seqi_inst.M0_WSTRB = 0;
            M0_seqi_inst.M0_WLAST = 0;
            M0_seqi_inst.M0_BREADY = 1'b1;
            M0_seqi_inst.M0_ARID = 0;
            M0_seqi_inst.M0_ARADDR = 0;
            M0_seqi_inst.M0_ARLEN = 0;
            M0_seqi_inst.M0_ARSIZE = 0;
            M0_seqi_inst.M0_ARBURST = 0;
            M0_seqi_inst.M0_ARLOCK = 0;
            M0_seqi_inst.M0_ARCACHE = 0;
            M0_seqi_inst.M0_ARPROT = 0;
            M0_seqi_inst.M0_ARQOS = 0;
            M0_seqi_inst.M0_ARREGION = 0;
            M0_seqi_inst.M0_ARVALID = 1'b0;
            M0_seqi_inst.M0_RREADY = 1'b1;
            
            finish_item(M0_seqi_inst);
        end
        
        else begin
            `uvm_error(get_full_name(), $sformatf("Unknown scenario: %0d", scenario))
        end
    endtask
    
endclass

`endif // M0_SEQ_SV
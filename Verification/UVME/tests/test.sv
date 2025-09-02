//=============================================================================
// Basic AXI NoC Test Class
//=============================================================================
// Basic test that instantiates the environment and runs a virtual sequence
// Demonstrates the basic UVM test structure for AXI NoC verification

`ifndef TEST_SV
`define TEST_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class test extends uvm_test;
    
    //--- Factory Registration -------//
    `uvm_component_utils(test)
    
    //--- Component Handles -------//
    axi_noc_env env_top;
    axi_noc_virtual_seq v_seq;
    
    //--- Test Configuration -------//
    string seq_type;
    
    //--- Constructor -------//
    function new(string name = "test", uvm_component parent = null);
        super.new(name, parent);
        `uvm_info(get_type_name(), "TEST CONSTRUCTOR CALLED", UVM_LOW)
    endfunction
    
    //--- Build Phase -------//
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        `uvm_info(get_type_name(), "TEST BUILD PHASE STARTED", UVM_LOW)
        
        // Create environment instance
        env_top = axi_noc_env::type_id::create("env_top", this);
        `uvm_info(get_type_name(), "Environment created", UVM_LOW)
        
        // Create virtual sequence instance
        v_seq = axi_noc_virtual_seq::type_id::create("v_seq", this);
        `uvm_info(get_type_name(), "Virtual sequence created", UVM_LOW)
        
        `uvm_info(get_type_name(), "Test build phase completed", UVM_LOW)
    endfunction
    
    //--- Run Phase -------//
    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        
        `uvm_info(get_full_name(), "BASE TEST START", UVM_MEDIUM)
        
        // Raise objection to prevent phase from ending prematurely
        phase.raise_objection(this);
        
        `uvm_info(get_full_name(), "INSIDE BASE TEST", UVM_MEDIUM)
        
        begin
            // Set sequence type to "rst" for reset sequence
            v_seq.seq_type = "rst";
            
            // Start the virtual sequence on the environment's virtual sequencer
            v_seq.start(env_top.virtual_seqr);
        end
        
        `uvm_info(get_full_name(), "END OF BASE TEST", UVM_MEDIUM)
        
        // Drop objection to allow phase to complete
        phase.drop_objection(this);
        
        // Set drain time to allow remaining transactions to complete
        uvm_test_done.set_drain_time(this, 4);
        
    endtask
    
endclass

`endif // TEST_SV
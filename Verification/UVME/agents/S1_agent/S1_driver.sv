//=============================================================================
// S1 Agent Driver Class
//=============================================================================
// Basic driver for Slave 1 that responds to master write and read requests
// Extends uvm_driver to drive S1 sequence items
// Uses S1_interface.driver modport with synchronized clocking block access

`ifndef S1_DRIVER_SV
`define S1_DRIVER_SV

// Note: All imports and includes will be handled by define_files_package

class S1_driver extends uvm_driver #(S1_seq_item);
    
    // Virtual interface for S1 AXI signals using driver modport
    virtual S1_interface.driver s1_vif;
    
    // S1 sequence item handle
    S1_seq_item req;
    
    // Driver configuration
    int unsigned s1_driver_id;
    string s1_driver_name;
    
    // Driver statistics
    int unsigned s1_total_transactions;
    int unsigned s1_write_transactions;
    int unsigned s1_read_transactions;
    
    // Driver control
    bit s1_driver_enabled;
    
    // Constructor
    function new(string name = "S1_driver", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize driver
        s1_driver_id = 0;
        s1_driver_name = name;
        
        // Initialize statistics
        s1_total_transactions = 0;
        s1_write_transactions = 0;
        s1_read_transactions = 0;
        
        // Initialize control
        s1_driver_enabled = 1;
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S1_interface.driver)::get(this, "", "s1_vif", s1_vif)) begin
            `uvm_fatal("S1_DRIVER", "Virtual interface not found for S1 driver")
        end
    endfunction
    
    // Run phase - main driver loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S1_DRIVER", $sformatf("S1 Driver %0d starting run phase", s1_driver_id), UVM_LOW)
        
        // Initialize S1 interface signals
        init_s1_signals();
        
        // Main driver loop
        forever begin
            // Get sequence item from sequencer
            seq_item_port.get_next_item(req);
            
            // Process the transaction
            if (s1_driver_enabled) begin
                if (req.trans_type == AXI_WRITE) begin
                    rsp_to_write(req);
                end else begin
                    rsp_to_read(req);
                end
            end
            
            // Signal completion
            seq_item_port.item_done();
        end
    endtask
    
    // Initialize S1 interface signals
    virtual task init_s1_signals();
        // Initialize all S1-driven signals to safe defaults
        s1_vif.s1_cb.S1_AWREADY <= 1'b0;
        s1_vif.s1_cb.S1_WREADY <= 1'b0;
        s1_vif.s1_cb.S1_BID <= '0;
        s1_vif.s1_cb.S1_BRESP <= '0;
        s1_vif.s1_cb.S1_BVALID <= 1'b0;
        s1_vif.s1_cb.S1_ARREADY <= 1'b0;
        s1_vif.s1_cb.S1_RID <= '0;
        s1_vif.s1_cb.S1_RDATA <= '0;
        s1_vif.s1_cb.S1_RRESP <= '0;
        s1_vif.s1_cb.S1_RLAST <= 1'b0;
        s1_vif.s1_cb.S1_RVALID <= 1'b0;
        
        `uvm_info("S1_DRIVER", "S1 interface signals initialized", UVM_LOW)
    endtask
    
    // Respond to write transaction (AW + W + B channels)
    virtual task rsp_to_write(S1_seq_item s1_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S1_DRIVER", "S1 responding to WRITE transaction", UVM_LOW)
        
        // Phase 1: Write Address Channel (AW) - S1 receives AW, drives AWREADY
        wait(s1_vif.s1_cb.S1_AWVALID);  // Wait for master to assert AWVALID
        b_len = s1_vif.s1_cb.S1_AWLEN + 1;  // Calculate burst length
        
        @(posedge s1_vif.ACLK);
        s1_vif.s1_cb.S1_AWREADY <= s1_seqi_inst.S1_AWREADY;  // Assert AWREADY
        @(posedge s1_vif.ACLK);
        s1_vif.s1_cb.S1_AWREADY <= 1'b0;  // Deassert AWREADY
        
        // Phase 2: Write Data Channel (W) - S1 receives W, drives WREADY
        wait(s1_vif.s1_cb.S1_WVALID);  // Wait for master to assert WVALID
        
        // Handle burst write data
        for (i = 0; i < b_len; i++) begin
            s1_vif.s1_cb.S1_WREADY <= s1_seqi_inst.S1_WREADY;  // Assert WREADY
            @(negedge s1_vif.ACLK);  // Wait for negative edge
        end
        
        // Phase 3: Write Response Channel (B) - S1 drives B, receives BREADY
        @(posedge s1_vif.ACLK);
        s1_vif.s1_cb.S1_WREADY <= 1'b0;  // Deassert WREADY
        
        // Set write response signals
        s1_vif.s1_cb.S1_BID <= s1_seqi_inst.S1_BID;
        s1_vif.s1_cb.S1_BRESP <= s1_seqi_inst.S1_BRESP;
        s1_vif.s1_cb.S1_BVALID <= s1_seqi_inst.S1_BVALID;
        
        // Handle write strobe for response
        if (s1_vif.s1_cb.S1_WSTRB == 4'hF) begin
            s1_vif.s1_cb.S1_BRESP <= s1_seqi_inst.S1_BRESP;
        end else begin
            s1_vif.s1_cb.S1_BRESP <= 2'b10;  // SLVERR if strobe not all 1's
        end
        
        @(posedge s1_vif.ACLK);
        s1_vif.s1_cb.S1_BVALID <= s1_seqi_inst.S1_BVALID;  // Assert BVALID
        
        wait(s1_vif.s1_cb.S1_BREADY);  // Wait for master to assert BREADY
        
        // Clear response signals
        s1_vif.s1_cb.S1_BVALID <= 1'b0;
        s1_vif.s1_cb.S1_BRESP <= 2'b00;
        
        // Update statistics
        s1_total_transactions++;
        s1_write_transactions++;
        
        `uvm_info("S1_DRIVER", "S1 WRITE transaction completed", UVM_LOW)
    endtask
    
    // Respond to read transaction (AR + R channels)
    virtual task rsp_to_read(S1_seq_item s1_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S1_DRIVER", "S1 responding to READ transaction", UVM_LOW)
        
        // Phase 1: Read Address Channel (AR) - S1 receives AR, drives ARREADY
        wait(s1_vif.s1_cb.S1_ARVALID);  // Wait for master to assert ARVALID
        b_len = s1_vif.s1_cb.S1_ARLEN + 1;  // Calculate burst length
        
        @(posedge s1_vif.ACLK);
        s1_vif.s1_cb.S1_ARREADY <= s1_seqi_inst.S1_ARREADY;  // Assert ARREADY
        
        wait(!s1_vif.s1_cb.S1_ARVALID);  // Wait for master to deassert ARVALID
        s1_vif.s1_cb.S1_ARREADY <= 1'b0;  // Deassert ARREADY
        
        // Phase 2: Read Data Channel (R) - S1 drives R, receives RREADY
        for (i = 0; i < b_len; i++) begin
            // Set read data signals
            s1_vif.s1_cb.S1_RID <= s1_seqi_inst.S1_RID;
            s1_vif.s1_cb.S1_RVALID <= s1_seqi_inst.S1_RVALID;
            s1_vif.s1_cb.S1_RDATA <= $random;  // Generate random read data
            s1_vif.s1_cb.S1_RLAST <= (i == b_len - 1) ? 1'b1 : 1'b0;  // Set RLAST for final beat
            s1_vif.s1_cb.S1_RRESP <= s1_seqi_inst.S1_RRESP;
            
            @(posedge s1_vif.ACLK);  // Synchronize to clock edge
        end
        
        // Wait for master to deassert RREADY and clear RVALID
        wait(!s1_vif.s1_cb.S1_RREADY);
        s1_vif.s1_cb.S1_RVALID <= 1'b0;
        s1_vif.s1_cb.S1_RDATA <= '0;
        s1_vif.s1_cb.S1_RLAST <= 1'b0;
        s1_vif.s1_cb.S1_RRESP <= 2'b00;
        
        // Update statistics
        s1_total_transactions++;
        s1_read_transactions++;
        
        `uvm_info("S1_DRIVER", "S1 READ transaction completed", UVM_LOW)
    endtask
    
    // Driver control methods
    
    // Enable driver
    virtual function void enable_driver();
        s1_driver_enabled = 1;
        `uvm_info("S1_DRIVER", $sformatf("S1 Driver %0d enabled", s1_driver_id), UVM_LOW)
    endfunction
    
    // Disable driver
    virtual function void disable_driver();
        s1_driver_enabled = 0;
        `uvm_info("S1_DRIVER", $sformatf("S1 Driver %0d disabled", s1_driver_id), UVM_LOW)
    endfunction
    
    // Check if driver is enabled
    virtual function bit is_driver_enabled();
        return s1_driver_enabled;
    endfunction
    
    // Get driver statistics
    virtual function string get_driver_statistics();
        return $sformatf("S1 Driver %0d Statistics: Total=%0d, Writes=%0d, Reads=%0d",
                        s1_driver_id, s1_total_transactions, s1_write_transactions, s1_read_transactions);
    endfunction
    
    // Reset driver statistics
    virtual function void reset_driver_statistics();
        s1_total_transactions = 0;
        s1_write_transactions = 0;
        s1_read_transactions = 0;
        `uvm_info("S1_DRIVER", $sformatf("S1 Driver %0d statistics reset", s1_driver_id), UVM_LOW)
    endfunction
    
    // UVM Field Macros
    `uvm_component_utils_begin(S1_driver)
        `uvm_field_int(s1_driver_id, UVM_ALL_ON)
        `uvm_field_string(s1_driver_name, UVM_ALL_ON)
        `uvm_field_int(s1_total_transactions, UVM_ALL_ON)
        `uvm_field_int(s1_write_transactions, UVM_ALL_ON)
        `uvm_field_int(s1_read_transactions, UVM_ALL_ON)
        `uvm_field_int(s1_driver_enabled, UVM_ALL_ON)
    `uvm_component_utils_end
    
endclass : S1_driver

`endif // S1_DRIVER_SV

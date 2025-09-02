//=============================================================================
// S3 Agent Driver Class
//=============================================================================
// Basic driver for Slave 3 that responds to master write and read requests
// Extends uvm_driver to drive S3 sequence items
// Uses S3_interface.driver modport with synchronized clocking block access

`ifndef S3_DRIVER_SV
`define S3_DRIVER_SV

// Note: All imports and includes will be handled by define_files_package

class S3_driver extends uvm_driver #(S3_seq_item);
    
    // Virtual interface for S3 AXI signals using driver modport
    virtual S3_interface.driver s3_vif;
    
    // S3 sequence item handle
    S3_seq_item req;
    
    // Driver configuration
    int unsigned s3_driver_id;
    string s3_driver_name;
    
    // Driver statistics
    int unsigned s3_total_transactions;
    int unsigned s3_write_transactions;
    int unsigned s3_read_transactions;
    
    // Driver control
    bit s3_driver_enabled;
    
    // Constructor
    function new(string name = "S3_driver", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize driver
        s3_driver_id = 0;
        s3_driver_name = name;
        
        // Initialize statistics
        s3_total_transactions = 0;
        s3_write_transactions = 0;
        s3_read_transactions = 0;
        
        // Initialize control
        s3_driver_enabled = 1;
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S3_interface)::get(this, "", "s3_vif", s3_vif)) begin
            `uvm_fatal("S3_DRIVER", "Virtual interface not found for S3 driver")
        end
    endfunction
    
    // Run phase - main driver loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S3_DRIVER", $sformatf("S3 Driver %0d starting run phase", s3_driver_id), UVM_LOW)
        
        // Initialize S3 interface signals
        init_s3_signals();
        
        // Main driver loop
        forever begin
            // Get sequence item from sequencer
            seq_item_port.get_next_item(req);
            
            // Process the transaction
            if (s3_driver_enabled) begin
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
    
    // Initialize S3 interface signals
    virtual task init_s3_signals();
        // Initialize all S3-driven signals to safe defaults
        s3_vif.s3_cb.S3_AWREADY <= 1'b0;
        s3_vif.s3_cb.S3_WREADY <= 1'b0;
        s3_vif.s3_cb.S3_BID <= '0;
        s3_vif.s3_cb.S3_BRESP <= '0;
        s3_vif.s3_cb.S3_BVALID <= 1'b0;
        s3_vif.s3_cb.S3_ARREADY <= 1'b0;
        s3_vif.s3_cb.S3_RID <= '0;
        s3_vif.s3_cb.S3_RDATA <= '0;
        s3_vif.s3_cb.S3_RRESP <= '0;
        s3_vif.s3_cb.S3_RLAST <= 1'b0;
        s3_vif.s3_cb.S3_RVALID <= 1'b0;
        
        `uvm_info("S3_DRIVER", "S3 interface signals initialized", UVM_LOW)
    endtask
    
    // Respond to write transaction (AW + W + B channels)
    virtual task rsp_to_write(S3_seq_item s3_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S3_DRIVER", "S3 responding to WRITE transaction", UVM_LOW)
        
        // Phase 1: Write Address Channel (AW) - S3 receives AW, drives AWREADY
        wait(s3_vif.s3_cb.S3_AWVALID);  // Wait for master to assert AWVALID
        b_len = s3_vif.s3_cb.S3_AWLEN + 1;  // Calculate burst length
        
        @(posedge s3_vif.ACLK);
        s3_vif.s3_cb.S3_AWREADY <= s3_seqi_inst.S3_AWREADY;  // Assert AWREADY
        @(posedge s3_vif.ACLK);
        s3_vif.s3_cb.S3_AWREADY <= 1'b0;  // Deassert AWREADY
        
        // Phase 2: Write Data Channel (W) - S3 receives W, drives WREADY
        wait(s3_vif.s3_cb.S3_WVALID);  // Wait for master to assert WVALID
        
        // Handle burst write data
        for (i = 0; i < b_len; i++) begin
            s3_vif.s3_cb.S3_WREADY <= s3_seqi_inst.S3_WREADY;  // Assert WREADY
            @(negedge s3_vif.ACLK);  // Wait for negative edge
        end
        
        // Phase 3: Write Response Channel (B) - S3 drives B, receives BREADY
        @(posedge s3_vif.ACLK);
        s3_vif.s3_cb.S3_WREADY <= 1'b0;  // Deassert WREADY
        
        // Set write response signals
        s3_vif.s3_cb.S3_BID <= s3_seqi_inst.S3_BID;
        s3_vif.s3_cb.S3_BRESP <= s3_seqi_inst.S3_BRESP;
        
        // Handle write strobe for response
        if (s3_vif.s3_cb.S3_WSTRB == 4'hF) begin
            s3_vif.s3_cb.S3_BRESP <= s3_seqi_inst.S3_BRESP;
        end else begin
            s3_vif.s3_cb.S3_BRESP <= 2'b10;  // SLVERR if strobe not all 1's
        end
        
        @(posedge s3_vif.ACLK);
        s3_vif.s3_cb.S3_BVALID <= s3_seqi_inst.S3_BVALID;  // Assert BVALID
        
        wait(s3_vif.s3_cb.S3_BREADY);  // Wait for master to assert BREADY
        
        // Clear response signals
        s3_vif.s3_cb.S3_BVALID <= 1'b0;
        s3_vif.s3_cb.S3_BRESP <= 2'b00;
        
        // Update statistics
        s3_total_transactions++;
        s3_write_transactions++;
        
        `uvm_info("S3_DRIVER", "S3 WRITE transaction completed", UVM_LOW)
    endtask
    
    // Respond to read transaction (AR + R channels)
    virtual task rsp_to_read(S3_seq_item s3_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S3_DRIVER", "S3 responding to READ transaction", UVM_LOW)
        
        // Phase 1: Read Address Channel (AR) - S3 receives AR, drives ARREADY
        wait(s3_vif.s3_cb.S3_ARVALID);  // Wait for master to assert ARVALID
        b_len = s3_vif.s3_cb.S3_ARLEN + 1;  // Calculate burst length
        
        @(posedge s3_vif.ACLK);
        s3_vif.s3_cb.S3_ARREADY <= s3_seqi_inst.S3_ARREADY;  // Assert ARREADY
        
        wait(!s3_vif.s3_cb.S3_ARVALID);  // Wait for master to deassert ARVALID
        s3_vif.s3_cb.S3_ARREADY <= 1'b0;  // Deassert ARREADY
        
        // Phase 2: Read Data Channel (R) - S3 drives R, receives RREADY
        for (i = 0; i < b_len; i++) begin
            // Set read data signals
            s3_vif.s3_cb.S3_RID <= s3_seqi_inst.S3_RID;
            s3_vif.s3_cb.S3_RVALID <= s3_seqi_inst.S3_RVALID;
            s3_vif.s3_cb.S3_RDATA <= $random;  // Generate random read data
            s3_vif.s3_cb.S3_RLAST <= (i == b_len - 1) ? 1'b1 : 1'b0;  // Set RLAST for final beat
            s3_vif.s3_cb.S3_RRESP <= s3_seqi_inst.S3_RRESP;
            
            @(posedge s3_vif.ACLK);  // Synchronize to clock edge
        end
        
        // Wait for master to deassert RREADY and clear RVALID
        wait(!s3_vif.s3_cb.S3_RREADY);
        s3_vif.s3_cb.S3_RVALID <= 1'b0;
        s3_vif.s3_cb.S3_RDATA <= '0;
        s3_vif.s3_cb.S3_RLAST <= 1'b0;
        s3_vif.s3_cb.S3_RRESP <= 2'b00;
        
        // Update statistics
        s3_total_transactions++;
        s3_read_transactions++;
        
        `uvm_info("S3_DRIVER", "S3 READ transaction completed", UVM_LOW)
    endtask
    
    // Driver control methods
    
    // Enable driver
    virtual function void enable_driver();
        s3_driver_enabled = 1;
        `uvm_info("S3_DRIVER", $sformatf("S3 Driver %0d enabled", s3_driver_id), UVM_LOW)
    endfunction
    
    // Disable driver
    virtual function void disable_driver();
        s3_driver_enabled = 0;
        `uvm_info("S3_DRIVER", $sformatf("S3 Driver %0d disabled", s3_driver_id), UVM_LOW)
    endfunction
    
    // Check if driver is enabled
    virtual function bit is_driver_enabled();
        return s3_driver_enabled;
    endfunction
    
    // Get driver statistics
    virtual function string get_driver_statistics();
        return $sformatf("S3 Driver %0d Statistics: Total=%0d, Writes=%0d, Reads=%0d",
                        s3_driver_id, s3_total_transactions, s3_write_transactions, s3_read_transactions);
    endfunction
    
    // Reset driver statistics
    virtual function void reset_driver_statistics();
        s3_total_transactions = 0;
        s3_write_transactions = 0;
        s3_read_transactions = 0;
        `uvm_info("S3_DRIVER", $sformatf("S3 Driver %0d statistics reset", s3_driver_id), UVM_LOW)
    endfunction
    
    // UVM Field Macros
    `uvm_component_utils_begin(S3_driver)
        `uvm_field_int(s3_driver_id, UVM_ALL_ON)
        `uvm_field_string(s3_driver_name, UVM_ALL_ON)
        `uvm_field_int(s3_total_transactions, UVM_ALL_ON)
        `uvm_field_int(s3_write_transactions, UVM_ALL_ON)
        `uvm_field_int(s3_read_transactions, UVM_ALL_ON)
        `uvm_field_int(s3_driver_enabled, UVM_ALL_ON)
    `uvm_component_utils_end
    
endclass : S3_driver

`endif // S3_DRIVER_SV

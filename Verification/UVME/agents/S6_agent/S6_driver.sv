//=============================================================================
// S6 Agent Driver Class
//=============================================================================
// Basic driver for Slave 6 that responds to master write and read requests
// Extends uvm_driver to drive S6 sequence items
// Uses S6_interface.driver modport with synchronized clocking block access

`ifndef S6_DRIVER_SV
`define S6_DRIVER_SV

// Note: All imports and includes will be handled by define_files_package

class S6_driver extends uvm_driver #(S6_seq_item);
    
    // Virtual interface for S6 AXI signals using driver modport
    virtual S6_interface.driver s6_vif;
    
    // S6 sequence item handle
    S6_seq_item req;
    
    // Driver configuration
    int unsigned s6_driver_id;
    string s6_driver_name;
    
    // Driver statistics
    int unsigned s6_total_transactions;
    int unsigned s6_write_transactions;
    int unsigned s6_read_transactions;
    
    // Driver control
    bit s6_driver_enabled;
    
    // Constructor
    function new(string name = "S6_driver", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize driver
        s6_driver_id = 0;
        s6_driver_name = name;
        
        // Initialize statistics
        s6_total_transactions = 0;
        s6_write_transactions = 0;
        s6_read_transactions = 0;
        
        // Initialize control
        s6_driver_enabled = 1;
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S6_interface.driver)::get(this, "", "s6_vif", s6_vif)) begin
            `uvm_fatal("S6_DRIVER", "Virtual interface not found for S6 driver")
        end
    endfunction
    
    // Run phase - main driver loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S6_DRIVER", $sformatf("S6 Driver %0d starting run phase", s6_driver_id), UVM_LOW)
        
        // Initialize S6 interface signals
        init_s6_signals();
        
        // Main driver loop
        forever begin
            // Get sequence item from sequencer
            seq_item_port.get_next_item(req);
            
            // Process the transaction
            if (s6_driver_enabled) begin
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
    
    // Initialize S6 interface signals
    virtual task init_s6_signals();
        // Initialize all S6-driven signals to safe defaults
        s6_vif.s6_cb.S6_AWREADY <= 1'b0;
        s6_vif.s6_cb.S6_WREADY <= 1'b0;
        s6_vif.s6_cb.S6_BID <= '0;
        s6_vif.s6_cb.S6_BRESP <= '0;
        s6_vif.s6_cb.S6_BVALID <= 1'b0;
        s6_vif.s6_cb.S6_BUSER <= '0;
        s6_vif.s6_cb.S6_ARREADY <= 1'b0;
        s6_vif.s6_cb.S6_RID <= '0;
        s6_vif.s6_cb.S6_RDATA <= '0;
        s6_vif.s6_cb.S6_RRESP <= '0;
        s6_vif.s6_cb.S6_RLAST <= 1'b0;
        s6_vif.s6_cb.S6_RVALID <= 1'b0;
        s6_vif.s6_cb.S6_RUSER <= '0;
        
        `uvm_info("S6_DRIVER", "S6 interface signals initialized", UVM_LOW)
    endtask
    
    // Respond to write transaction (AW + W + B channels)
    virtual task rsp_to_write(S6_seq_item s6_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S6_DRIVER", "S6 responding to WRITE transaction", UVM_LOW)
        
        // Phase 1: Write Address Channel (AW) - S6 receives AW, drives AWREADY
        wait(s6_vif.s6_cb.S6_AWVALID);  // Wait for master to assert AWVALID
        b_len = s6_vif.s6_cb.S6_AWLEN + 1;  // Calculate burst length
        
        @(posedge s6_vif.ACLK);
        s6_vif.s6_cb.S6_AWREADY <= s6_seqi_inst.S6_AWREADY;  // Assert AWREADY
        @(posedge s6_vif.ACLK);
        s6_vif.s6_cb.S6_AWREADY <= 1'b0;  // Deassert AWREADY
        
        // Phase 2: Write Data Channel (W) - S6 receives W, drives WREADY
        wait(s6_vif.s6_cb.S6_WVALID);  // Wait for master to assert WVALID
        
        // Handle burst write data
        for (i = 0; i < b_len; i++) begin
            s6_vif.s6_cb.S6_WREADY <= s6_seqi_inst.S6_WREADY;  // Assert WREADY
            @(negedge s6_vif.ACLK);  // Wait for negative edge
        end
        
        // Phase 3: Write Response Channel (B) - S6 drives B, receives BREADY
        @(posedge s6_vif.ACLK);
        s6_vif.s6_cb.S6_WREADY <= 1'b0;  // Deassert WREADY
        
        // Set write response signals
        s6_vif.s6_cb.S6_BID <= s6_seqi_inst.S6_BID;
        s6_vif.s6_cb.S6_BRESP <= s6_seqi_inst.S6_BRESP;
        s6_vif.s6_cb.S6_BUSER <= s6_seqi_inst.S6_BUSER;
        
        // Handle write strobe for response
        if (s6_vif.s6_cb.S6_WSTRB == 4'hF) begin
            s6_vif.s6_cb.S6_BRESP <= s6_seqi_inst.S6_BRESP;
        end else begin
            s6_vif.s6_cb.S6_BRESP <= 2'b10;  // SLVERR if strobe not all 1's
        end
        
        @(posedge s6_vif.ACLK);
        s6_vif.s6_cb.S6_BVALID <= s6_seqi_inst.S6_BVALID;  // Assert BVALID
        
        wait(s6_vif.s6_cb.S6_BREADY);  // Wait for master to assert BREADY
        
        // Clear response signals
        s6_vif.s6_cb.S6_BVALID <= 1'b0;
        s6_vif.s6_cb.S6_BRESP <= 2'b00;
        
        // Update statistics
        s6_total_transactions++;
        s6_write_transactions++;
        
        `uvm_info("S6_DRIVER", "S6 WRITE transaction completed", UVM_LOW)
    endtask
    
    // Respond to read transaction (AR + R channels)
    virtual task rsp_to_read(S6_seq_item s6_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S6_DRIVER", "S6 responding to READ transaction", UVM_LOW)
        
        // Phase 1: Read Address Channel (AR) - S6 receives AR, drives ARREADY
        wait(s6_vif.s6_cb.S6_ARVALID);  // Wait for master to assert ARVALID
        b_len = s6_vif.s6_cb.S6_ARLEN + 1;  // Calculate burst length
        
        @(posedge s6_vif.ACLK);
        s6_vif.s6_cb.S6_ARREADY <= s6_seqi_inst.S6_ARREADY;  // Assert ARREADY
        
        wait(!s6_vif.s6_cb.S6_ARVALID);  // Wait for master to deassert ARVALID
        s6_vif.s6_cb.S6_ARREADY <= 1'b0;  // Deassert ARREADY
        
        // Phase 2: Read Data Channel (R) - S6 drives R, receives RREADY
        for (i = 0; i < b_len; i++) begin
            // Set read data signals
            s6_vif.s6_cb.S6_RID <= s6_seqi_inst.S6_RID;
            s6_vif.s6_cb.S6_RVALID <= s6_seqi_inst.S6_RVALID;
            s6_vif.s6_cb.S6_RDATA <= $random;  // Generate random read data
            s6_vif.s6_cb.S6_RLAST <= (i == b_len - 1) ? 1'b1 : 1'b0;  // Set RLAST for final beat
            s6_vif.s6_cb.S6_RRESP <= s6_seqi_inst.S6_RRESP;
            s6_vif.s6_cb.S6_RUSER <= s6_seqi_inst.S6_RUSER;
            
            @(posedge s6_vif.ACLK);  // Synchronize to clock edge
        end
        
        // Wait for master to deassert RREADY and clear RVALID
        wait(!s6_vif.s6_cb.S6_RREADY);
        s6_vif.s6_cb.S6_RVALID <= 1'b0;
        s6_vif.s6_cb.S6_RDATA <= '0;
        s6_vif.s6_cb.S6_RLAST <= 1'b0;
        s6_vif.s6_cb.S6_RRESP <= 2'b00;
        
        // Update statistics
        s6_total_transactions++;
        s6_read_transactions++;
        
        `uvm_info("S6_DRIVER", "S6 READ transaction completed", UVM_LOW)
    endtask
    
    // Driver control methods
    
    // Enable driver
    virtual function void enable_driver();
        s6_driver_enabled = 1;
        `uvm_info("S6_DRIVER", $sformatf("S6 Driver %0d enabled", s6_driver_id), UVM_LOW)
    endfunction
    
    // Disable driver
    virtual function void disable_driver();
        s6_driver_enabled = 0;
        `uvm_info("S6_DRIVER", $sformatf("S6 Driver %0d disabled", s6_driver_id), UVM_LOW)
    endfunction
    
    // Check if driver is enabled
    virtual function bit is_driver_enabled();
        return s6_driver_enabled;
    endfunction
    
    // Get driver statistics
    virtual function string get_driver_statistics();
        return $sformatf("S6 Driver %0d Statistics: Total=%0d, Writes=%0d, Reads=%0d",
                        s6_driver_id, s6_total_transactions, s6_write_transactions, s6_read_transactions);
    endfunction
    
    // Reset driver statistics
    virtual function void reset_driver_statistics();
        s6_total_transactions = 0;
        s6_write_transactions = 0;
        s6_read_transactions = 0;
        `uvm_info("S6_DRIVER", $sformatf("S6 Driver %0d statistics reset", s6_driver_id), UVM_LOW)
    endfunction
    
    // UVM Field Macros
    `uvm_component_utils_begin(S6_driver)
        `uvm_field_int(s6_driver_id, UVM_ALL_ON)
        `uvm_field_string(s6_driver_name, UVM_ALL_ON)
        `uvm_field_int(s6_total_transactions, UVM_ALL_ON)
        `uvm_field_int(s6_write_transactions, UVM_ALL_ON)
        `uvm_field_int(s6_read_transactions, UVM_ALL_ON)
        `uvm_field_int(s6_driver_enabled, UVM_ALL_ON)
    `uvm_component_utils_end
    
endclass : S6_driver

`endif // S6_DRIVER_SV

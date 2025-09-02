//=============================================================================
// S2 Agent Driver Class
//=============================================================================
// Basic driver for Slave 2 that responds to master write and read requests
// Extends uvm_driver to drive S2 sequence items
// Uses S2_interface.driver modport with synchronized clocking block access

`ifndef S2_DRIVER_SV
`define S2_DRIVER_SV

// Note: All imports and includes will be handled by define_files_package

class S2_driver extends uvm_driver #(S2_seq_item);
    
    // Virtual interface for S2 AXI signals using driver modport
    virtual S2_interface.driver s2_vif;
    
    // S2 sequence item handle
    S2_seq_item req;
    
    // Driver configuration
    int unsigned s2_driver_id;
    string s2_driver_name;
    
    // Driver statistics
    int unsigned s2_total_transactions;
    int unsigned s2_write_transactions;
    int unsigned s2_read_transactions;
    
    // Driver control
    bit s2_driver_enabled;
    
    // Constructor
    function new(string name = "S2_driver", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize driver
        s2_driver_id = 0;
        s2_driver_name = name;
        
        // Initialize statistics
        s2_total_transactions = 0;
        s2_write_transactions = 0;
        s2_read_transactions = 0;
        
        // Initialize control
        s2_driver_enabled = 1;
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S2_interface)::get(this, "", "s2_vif", s2_vif)) begin
            `uvm_fatal("S2_DRIVER", "Virtual interface not found for S2 driver")
        end
    endfunction
    
    // Run phase - main driver loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S2_DRIVER", $sformatf("S2 Driver %0d starting run phase", s2_driver_id), UVM_LOW)
        
        // Initialize S2 interface signals
        init_s2_signals();
        
        // Main driver loop
        forever begin
            // Get sequence item from sequencer
            seq_item_port.get_next_item(req);
            
            // Process the transaction
            if (s2_driver_enabled) begin
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
    
    // Initialize S2 interface signals
    virtual task init_s2_signals();
        // Initialize all S2-driven signals to safe defaults
        s2_vif.s2_cb.S2_AWREADY <= 1'b0;
        s2_vif.s2_cb.S2_WREADY <= 1'b0;
        s2_vif.s2_cb.S2_BID <= '0;
        s2_vif.s2_cb.S2_BRESP <= '0;
        s2_vif.s2_cb.S2_BVALID <= 1'b0;
        s2_vif.s2_cb.S2_ARREADY <= 1'b0;
        s2_vif.s2_cb.S2_RID <= '0;
        s2_vif.s2_cb.S2_RDATA <= '0;
        s2_vif.s2_cb.S2_RRESP <= '0;
        s2_vif.s2_cb.S2_RLAST <= 1'b0;
        s2_vif.s2_cb.S2_RVALID <= 1'b0;
        
        `uvm_info("S2_DRIVER", "S2 interface signals initialized", UVM_LOW)
    endtask
    
    // Respond to write transaction (AW + W + B channels)
    virtual task rsp_to_write(S2_seq_item s2_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S2_DRIVER", "S2 responding to WRITE transaction", UVM_LOW)
        
        // Phase 1: Write Address Channel (AW) - S2 receives AW, drives AWREADY
        wait(s2_vif.s2_cb.S2_AWVALID);  // Wait for master to assert AWVALID
        b_len = s2_vif.s2_cb.S2_AWLEN + 1;  // Calculate burst length
        
        @(posedge s2_vif.ACLK);
        s2_vif.s2_cb.S2_AWREADY <= s2_seqi_inst.S2_AWREADY;  // Assert AWREADY
        @(posedge s2_vif.ACLK);
        s2_vif.s2_cb.S2_AWREADY <= 1'b0;  // Deassert AWREADY
        
        // Phase 2: Write Data Channel (W) - S2 receives W, drives WREADY
        wait(s2_vif.s2_cb.S2_WVALID);  // Wait for master to assert WVALID
        
        // Handle burst write data
        for (i = 0; i < b_len; i++) begin
            s2_vif.s2_cb.S2_WREADY <= s2_seqi_inst.S2_WREADY;  // Assert WREADY
            @(negedge s2_vif.ACLK);  // Wait for negative edge
        end
        
        // Phase 3: Write Response Channel (B) - S2 drives B, receives BREADY
        @(posedge s2_vif.ACLK);
        s2_vif.s2_cb.S2_WREADY <= 1'b0;  // Deassert WREADY
        
        // Set write response signals
        s2_vif.s2_cb.S2_BID <= s2_seqi_inst.S2_BID;
        s2_vif.s2_cb.S2_BRESP <= s2_seqi_inst.S2_BRESP;
        s2_vif.s2_cb.S2_BVALID <= s2_seqi_inst.S2_BVALID;
        
        // Handle write strobe for response
        if (s2_vif.s2_cb.S2_WSTRB == 4'hF) begin
            s2_vif.s2_cb.S2_BRESP <= s2_seqi_inst.S2_BRESP;
        end else begin
            s2_vif.s2_cb.S2_BRESP <= 2'b10;  // SLVERR if strobe not all 1's
        end
        
        @(posedge s2_vif.ACLK);
        s2_vif.s2_cb.S2_BVALID <= s2_seqi_inst.S2_BVALID;  // Assert BVALID
        
        wait(s2_vif.s2_cb.S2_BREADY);  // Wait for master to assert BREADY
        
        // Clear response signals
        s2_vif.s2_cb.S2_BVALID <= 1'b0;
        s2_vif.s2_cb.S2_BRESP <= 2'b00;
        
        // Update statistics
        s2_total_transactions++;
        s2_write_transactions++;
        
        `uvm_info("S2_DRIVER", "S2 WRITE transaction completed", UVM_LOW)
    endtask
    
    // Respond to read transaction (AR + R channels)
    virtual task rsp_to_read(S2_seq_item s2_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S2_DRIVER", "S2 responding to READ transaction", UVM_LOW)
        
        // Phase 1: Read Address Channel (AR) - S2 receives AR, drives ARREADY
        wait(s2_vif.s2_cb.S2_ARVALID);  // Wait for master to assert ARVALID
        b_len = s2_vif.s2_cb.S2_ARLEN + 1;  // Calculate burst length
        
        @(posedge s2_vif.ACLK);
        s2_vif.s2_cb.S2_ARREADY <= s2_seqi_inst.S2_ARREADY;  // Assert ARREADY
        
        wait(!s2_vif.s2_cb.S2_ARVALID);  // Wait for master to deassert ARVALID
        s2_vif.s2_cb.S2_ARREADY <= 1'b0;  // Deassert ARREADY
        
        // Phase 2: Read Data Channel (R) - S2 drives R, receives RREADY
        for (i = 0; i < b_len; i++) begin
            // Set read data signals
            s2_vif.s2_cb.S2_RID <= s2_seqi_inst.S2_RID;
            s2_vif.s2_cb.S2_RVALID <= s2_seqi_inst.S2_RVALID;
            s2_vif.s2_cb.S2_RDATA <= $random;  // Generate random read data
            s2_vif.s2_cb.S2_RLAST <= (i == b_len - 1) ? 1'b1 : 1'b0;  // Set RLAST for final beat
            s2_vif.s2_cb.S2_RRESP <= s2_seqi_inst.S2_RRESP;
            
            @(posedge s2_vif.ACLK);  // Synchronize to clock edge
        end
        
        // Wait for master to deassert RREADY and clear RVALID
        wait(!s2_vif.s2_cb.S2_RREADY);
        s2_vif.s2_cb.S2_RVALID <= 1'b0;
        s2_vif.s2_cb.S2_RDATA <= '0;
        s2_vif.s2_cb.S2_RLAST <= 1'b0;
        s2_vif.s2_cb.S2_RRESP <= 2'b00;
        
        // Update statistics
        s2_total_transactions++;
        s2_read_transactions++;
        
        `uvm_info("S2_DRIVER", "S2 READ transaction completed", UVM_LOW)
    endtask
    
    // Driver control methods
    
    // Enable driver
    virtual function void enable_driver();
        s2_driver_enabled = 1;
        `uvm_info("S2_DRIVER", $sformatf("S2 Driver %0d enabled", s2_driver_id), UVM_LOW)
    endfunction
    
    // Disable driver
    virtual function void disable_driver();
        s2_driver_enabled = 0;
        `uvm_info("S2_DRIVER", $sformatf("S2 Driver %0d disabled", s2_driver_id), UVM_LOW)
    endfunction
    
    // Check if driver is enabled
    virtual function bit is_driver_enabled();
        return s2_driver_enabled;
    endfunction
    
    // Get driver statistics
    virtual function string get_driver_statistics();
        return $sformatf("S2 Driver %0d Statistics: Total=%0d, Writes=%0d, Reads=%0d",
                        s2_driver_id, s2_total_transactions, s2_write_transactions, s2_read_transactions);
    endfunction
    
    // Reset driver statistics
    virtual function void reset_driver_statistics();
        s2_total_transactions = 0;
        s2_write_transactions = 0;
        s2_read_transactions = 0;
        `uvm_info("S2_DRIVER", $sformatf("S2 Driver %0d statistics reset", s2_driver_id), UVM_LOW)
    endfunction
    
    // UVM Field Macros
    `uvm_component_utils_begin(S2_driver)
        `uvm_field_int(s2_driver_id, UVM_ALL_ON)
        `uvm_field_string(s2_driver_name, UVM_ALL_ON)
        `uvm_field_int(s2_total_transactions, UVM_ALL_ON)
        `uvm_field_int(s2_write_transactions, UVM_ALL_ON)
        `uvm_field_int(s2_read_transactions, UVM_ALL_ON)
        `uvm_field_int(s2_driver_enabled, UVM_ALL_ON)
    `uvm_component_utils_end
    
endclass : S2_driver

`endif // S2_DRIVER_SV

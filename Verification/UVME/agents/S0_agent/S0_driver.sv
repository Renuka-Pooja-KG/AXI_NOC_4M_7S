//=============================================================================
// S0 Agent Driver Class
//=============================================================================
// Basic driver for Slave 0 that responds to master write and read requests
// Extends uvm_driver to drive S0 sequence items
// Uses S0_interface.driver modport with synchronized clocking block access

`ifndef S0_DRIVER_SV
`define S0_DRIVER_SV

// Note: All imports and includes will be handled by define_files_package

class S0_driver extends uvm_driver #(S0_seq_item);
    
    // Virtual interface for S0 AXI signals using driver modport
    virtual S0_interface s0_vif;
    
    // S0 sequence item handle
    S0_seq_item req;
    
    // Driver configuration
    int unsigned s0_driver_id;
    string s0_driver_name;
    
    // Driver statistics
    int unsigned s0_total_transactions;
    int unsigned s0_write_transactions;
    int unsigned s0_read_transactions;
    
    // Driver control
    bit s0_driver_enabled;
    
    // Constructor
    function new(string name = "S0_driver", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize driver
        s0_driver_id = 0;
        s0_driver_name = name;
        
        // Initialize statistics
        s0_total_transactions = 0;
        s0_write_transactions = 0;
        s0_read_transactions = 0;
        
        // Initialize control
        s0_driver_enabled = 1;
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S0_interface)::get(this, "", "s0_vif", s0_vif)) begin
            `uvm_fatal("S0_DRIVER", "Virtual interface not found for S0 driver")
        end
    endfunction
    
    // Run phase - main driver loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S0_DRIVER", $sformatf("S0 Driver %0d starting run phase", s0_driver_id), UVM_LOW)
        
        // Initialize S0 interface signals
        init_s0_signals();
        
        // Main driver loop
        forever begin
            // Get sequence item from sequencer
            seq_item_port.get_next_item(req);
            
            // Process the transaction
            if (s0_driver_enabled) begin
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
    
    // Initialize S0 interface signals
    virtual task init_s0_signals();
        // Initialize all S0-driven signals to safe defaults
        s0_vif.s0_cb.S0_AWREADY <= 1'b0;
        s0_vif.s0_cb.S0_WREADY <= 1'b0;
        s0_vif.s0_cb.S0_BID <= '0;
        s0_vif.s0_cb.S0_BRESP <= '0;
        s0_vif.s0_cb.S0_BVALID <= 1'b0;
        s0_vif.s0_cb.S0_ARREADY <= 1'b0;
        s0_vif.s0_cb.S0_RID <= '0;
        s0_vif.s0_cb.S0_RDATA <= '0;
        s0_vif.s0_cb.S0_RRESP <= '0;
        s0_vif.s0_cb.S0_RLAST <= 1'b0;
        s0_vif.s0_cb.S0_RVALID <= 1'b0;
        
        `uvm_info("S0_DRIVER", "S0 interface signals initialized", UVM_LOW)
    endtask
    
    // Respond to write transaction (AW + W + B channels)
    virtual task rsp_to_write(S0_seq_item s0_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S0_DRIVER", "S0 responding to WRITE transaction", UVM_LOW)
        
        // Phase 1: Write Address Channel (AW) - S0 receives AW, drives AWREADY
        wait(s0_vif.s0_cb.S0_AWVALID);  // Wait for master to assert AWVALID
        b_len = s0_vif.s0_cb.S0_AWLEN + 1;  // Calculate burst length
        
        @(posedge s0_vif.ACLK);
        s0_vif.s0_cb.S0_AWREADY <= s0_seqi_inst.S0_AWREADY;  // Assert AWREADY
        @(posedge s0_vif.ACLK);
        s0_vif.s0_cb.S0_AWREADY <= 1'b0;  // Deassert AWREADY
        
        // Phase 2: Write Data Channel (W) - S0 receives W, drives WREADY
        wait(s0_vif.s0_cb.S0_WVALID);  // Wait for master to assert WVALID
        
        // Handle burst write data
        for (i = 0; i < b_len; i++) begin
            s0_vif.s0_cb.S0_WREADY <= s0_seqi_inst.S0_WREADY;  // Assert WREADY
            @(negedge s0_vif.ACLK);  // Wait for negative edge
        end
        
        // Phase 3: Write Response Channel (B) - S0 drives B, receives BREADY
        @(posedge s0_vif.ACLK);
        s0_vif.s0_cb.S0_WREADY <= 1'b0;  // Deassert WREADY
        
        // Set write response signals
        s0_vif.s0_cb.S0_BID <= s0_seqi_inst.S0_BID;
        s0_vif.s0_cb.S0_BRESP <= s0_seqi_inst.S0_BRESP;
        
        // Handle write strobe for response
        if (s0_vif.s0_cb.S0_WSTRB == 4'hF) begin
            s0_vif.s0_cb.S0_BRESP <= s0_seqi_inst.S0_BRESP;
        end else begin
            s0_vif.s0_cb.S0_BRESP <= 2'b10;  // SLVERR if strobe not all 1's
        end
        
        @(posedge s0_vif.ACLK);
        s0_vif.s0_cb.S0_BVALID <= s0_seqi_inst.S0_BVALID;  // Assert BVALID
        
        wait(s0_vif.s0_cb.S0_BREADY);  // Wait for master to assert BREADY
        
        // Clear response signals
        s0_vif.s0_cb.S0_BVALID <= 1'b0;
        s0_vif.s0_cb.S0_BRESP <= 2'b00;
        
        // Update statistics
        s0_total_transactions++;
        s0_write_transactions++;
        
        `uvm_info("S0_DRIVER", "S0 WRITE transaction completed", UVM_LOW)
    endtask
    
    // Respond to read transaction (AR + R channels)
    virtual task rsp_to_read(S0_seq_item s0_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S0_DRIVER", "S0 responding to READ transaction", UVM_LOW)
        
        // Phase 1: Read Address Channel (AR) - S0 receives AR, drives ARREADY
        wait(s0_vif.s0_cb.S0_ARVALID);  // Wait for master to assert ARVALID
        b_len = s0_vif.s0_cb.S0_ARLEN + 1;  // Calculate burst length
        
        @(posedge s0_vif.ACLK);
        s0_vif.s0_cb.S0_ARREADY <= s0_seqi_inst.S0_ARREADY;  // Assert ARREADY
        
        wait(!s0_vif.s0_cb.S0_ARVALID);  // Wait for master to deassert ARVALID
        s0_vif.s0_cb.S0_ARREADY <= 1'b0;  // Deassert ARREADY
        
        // Phase 2: Read Data Channel (R) - S0 drives R, receives RREADY
        for (i = 0; i < b_len; i++) begin
            // Set read data signals
            s0_vif.s0_cb.S0_RID <= s0_seqi_inst.S0_RID;
            s0_vif.s0_cb.S0_RVALID <= s0_seqi_inst.S0_RVALID;
            s0_vif.s0_cb.S0_RDATA <= $random;  // Generate random read data
            s0_vif.s0_cb.S0_RLAST <= (i == b_len - 1) ? 1'b1 : 1'b0;  // Set RLAST for final beat
            s0_vif.s0_cb.S0_RRESP <= s0_seqi_inst.S0_RRESP;
            
            @(posedge s0_vif.ACLK);  // Synchronize to clock edge
        end
        
        // Wait for master to deassert RREADY and clear RVALID
        wait(!s0_vif.s0_cb.S0_RREADY);
        s0_vif.s0_cb.S0_RVALID <= 1'b0;
        s0_vif.s0_cb.S0_RDATA <= '0;
        s0_vif.s0_cb.S0_RLAST <= 1'b0;
        s0_vif.s0_cb.S0_RRESP <= 2'b00;
        
        // Update statistics
        s0_total_transactions++;
        s0_read_transactions++;
        
        `uvm_info("S0_DRIVER", "S0 READ transaction completed", UVM_LOW)
    endtask
    
    // Driver control methods
    
    // Enable driver
    virtual function void enable_driver();
        s0_driver_enabled = 1;
        `uvm_info("S0_DRIVER", $sformatf("S0 Driver %0d enabled", s0_driver_id), UVM_LOW)
    endfunction
    
    // Disable driver
    virtual function void disable_driver();
        s0_driver_enabled = 0;
        `uvm_info("S0_DRIVER", $sformatf("S0 Driver %0d disabled", s0_driver_id), UVM_LOW)
    endfunction
    
    // Check if driver is enabled
    virtual function bit is_driver_enabled();
        return s0_driver_enabled;
    endfunction
    
    // Get driver statistics
    virtual function string get_driver_statistics();
        return $sformatf("S0 Driver %0d Statistics: Total=%0d, Writes=%0d, Reads=%0d",
                        s0_driver_id, s0_total_transactions, s0_write_transactions, s0_read_transactions);
    endfunction
    
    // Reset driver statistics
    virtual function void reset_driver_statistics();
        s0_total_transactions = 0;
        s0_write_transactions = 0;
        s0_read_transactions = 0;
        `uvm_info("S0_DRIVER", $sformatf("S0 Driver %0d statistics reset", s0_driver_id), UVM_LOW)
    endfunction
    
    // UVM Field Macros
    `uvm_component_utils_begin(S0_driver)
        `uvm_field_int(s0_driver_id, UVM_ALL_ON)
        `uvm_field_string(s0_driver_name, UVM_ALL_ON)
        `uvm_field_int(s0_total_transactions, UVM_ALL_ON)
        `uvm_field_int(s0_write_transactions, UVM_ALL_ON)
        `uvm_field_int(s0_read_transactions, UVM_ALL_ON)
        `uvm_field_int(s0_driver_enabled, UVM_ALL_ON)
    `uvm_component_utils_end
    
endclass : S0_driver

`endif // S0_DRIVER_SV

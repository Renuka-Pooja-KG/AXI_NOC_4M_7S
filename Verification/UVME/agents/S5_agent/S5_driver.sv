//=============================================================================
// S5 Agent Driver Class
//=============================================================================
// Basic driver for Slave 5 that responds to master write and read requests
// Extends uvm_driver to drive S5 sequence items
// Uses S5_interface.driver modport with synchronized clocking block access

`ifndef S5_DRIVER_SV
`define S5_DRIVER_SV

// Note: All imports and includes will be handled by define_files_package

class S5_driver extends uvm_driver #(S5_seq_item);
    
    // Virtual interface for S5 AXI signals using driver modport
    virtual S5_interface s5_vif;
    
    // S5 sequence item handle
    S5_seq_item req;
    
    // Driver configuration
    int unsigned s5_driver_id;
    string s5_driver_name;
    
    // Driver statistics
    int unsigned s5_total_transactions;
    int unsigned s5_write_transactions;
    int unsigned s5_read_transactions;
    
    // Driver control
    bit s5_driver_enabled;
    
    // Constructor
    function new(string name = "S5_driver", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize driver
        s5_driver_id = 0;
        s5_driver_name = name;
        
        // Initialize statistics
        s5_total_transactions = 0;
        s5_write_transactions = 0;
        s5_read_transactions = 0;
        
        // Initialize control
        s5_driver_enabled = 1;
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S5_interface)::get(this, "", "s5_vif", s5_vif)) begin
            `uvm_fatal("S5_DRIVER", "Virtual interface not found for S5 driver")
        end
    endfunction
    
    // Run phase - main driver loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S5_DRIVER", $sformatf("S5 Driver %0d starting run phase", s5_driver_id), UVM_LOW)
        
        // Initialize S5 interface signals
        init_s5_signals();
        
        // Main driver loop
        forever begin
            // Get sequence item from sequencer
            seq_item_port.get_next_item(req);
            
            // Process the transaction
            if (s5_driver_enabled) begin
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
    
    // Initialize S5 interface signals
    virtual task init_s5_signals();
        // Initialize all S5-driven signals to safe defaults
        s5_vif.s5_cb.S5_AWREADY <= 1'b0;
        s5_vif.s5_cb.S5_WREADY <= 1'b0;
        s5_vif.s5_cb.S5_BID <= '0;
        s5_vif.s5_cb.S5_BRESP <= '0;
        s5_vif.s5_cb.S5_BVALID <= 1'b0;
        s5_vif.s5_cb.S5_ARREADY <= 1'b0;
        s5_vif.s5_cb.S5_RID <= '0;
        s5_vif.s5_cb.S5_RDATA <= '0;
        s5_vif.s5_cb.S5_RRESP <= '0;
        s5_vif.s5_cb.S5_RLAST <= 1'b0;
        s5_vif.s5_cb.S5_RVALID <= 1'b0;
        
        `uvm_info("S5_DRIVER", "S5 interface signals initialized", UVM_LOW)
    endtask
    
    // Respond to write transaction (AW + W + B channels)
    virtual task rsp_to_write(S5_seq_item s5_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S5_DRIVER", "S5 responding to WRITE transaction", UVM_LOW)
        
        // Phase 1: Write Address Channel (AW) - S5 receives AW, drives AWREADY
        wait(s5_vif.s5_cb.S5_AWVALID);  // Wait for master to assert AWVALID
        b_len = s5_vif.s5_cb.S5_AWLEN + 1;  // Calculate burst length
        
        @(posedge s5_vif.ACLK);
        s5_vif.s5_cb.S5_AWREADY <= s5_seqi_inst.S5_AWREADY;  // Assert AWREADY
        @(posedge s5_vif.ACLK);
        s5_vif.s5_cb.S5_AWREADY <= 1'b0;  // Deassert AWREADY
        
        // Phase 2: Write Data Channel (W) - S5 receives W, drives WREADY
        wait(s5_vif.s5_cb.S5_WVALID);  // Wait for master to assert WVALID
        
        // Handle burst write data
        for (i = 0; i < b_len; i++) begin
            s5_vif.s5_cb.S5_WREADY <= s5_seqi_inst.S5_WREADY;  // Assert WREADY
            @(negedge s5_vif.ACLK);  // Wait for negative edge
        end
        
        // Phase 3: Write Response Channel (B) - S5 drives B, receives BREADY
        @(posedge s5_vif.ACLK);
        s5_vif.s5_cb.S5_WREADY <= 1'b0;  // Deassert WREADY
        
        // Set write response signals
        s5_vif.s5_cb.S5_BID <= s5_seqi_inst.S5_BID;
        s5_vif.s5_cb.S5_BRESP <= s5_seqi_inst.S5_BRESP;
        
        // Handle write strobe for response
        if (s5_vif.s5_cb.S5_WSTRB == 4'hF) begin
            s5_vif.s5_cb.S5_BRESP <= s5_seqi_inst.S5_BRESP;
        end else begin
            s5_vif.s5_cb.S5_BRESP <= 2'b10;  // SLVERR if strobe not all 1's
        end
        
        @(posedge s5_vif.ACLK);
        s5_vif.s5_cb.S5_BVALID <= s5_seqi_inst.S5_BVALID;  // Assert BVALID
        
        wait(s5_vif.s5_cb.S5_BREADY);  // Wait for master to assert BREADY
        
        // Clear response signals
        s5_vif.s5_cb.S5_BVALID <= 1'b0;
        s5_vif.s5_cb.S5_BRESP <= 2'b00;
        
        // Update statistics
        s5_total_transactions++;
        s5_write_transactions++;
        
        `uvm_info("S5_DRIVER", "S5 WRITE transaction completed", UVM_LOW)
    endtask
    
    // Respond to read transaction (AR + R channels)
    virtual task rsp_to_read(S5_seq_item s5_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S5_DRIVER", "S5 responding to READ transaction", UVM_LOW)
        
        // Phase 1: Read Address Channel (AR) - S5 receives AR, drives ARREADY
        wait(s5_vif.s5_cb.S5_ARVALID);  // Wait for master to assert ARVALID
        b_len = s5_vif.s5_cb.S5_ARLEN + 1;  // Calculate burst length
        
        @(posedge s5_vif.ACLK);
        s5_vif.s5_cb.S5_ARREADY <= s5_seqi_inst.S5_ARREADY;  // Assert ARREADY
        
        wait(!s5_vif.s5_cb.S5_ARVALID);  // Wait for master to deassert ARVALID
        s5_vif.s5_cb.S5_ARREADY <= 1'b0;  // Deassert ARREADY
        
        // Phase 2: Read Data Channel (R) - S5 drives R, receives RREADY
        for (i = 0; i < b_len; i++) begin
            // Set read data signals
            s5_vif.s5_cb.S5_RID <= s5_seqi_inst.S5_RID;
            s5_vif.s5_cb.S5_RVALID <= s5_seqi_inst.S5_RVALID;
            s5_vif.s5_cb.S5_RDATA <= $random;  // Generate random read data
            s5_vif.s5_cb.S5_RLAST <= (i == b_len - 1) ? 1'b1 : 1'b0;  // Set RLAST for final beat
            s5_vif.s5_cb.S5_RRESP <= s5_seqi_inst.S5_RRESP;
            
            @(posedge s5_vif.ACLK);  // Synchronize to clock edge
        end
        
        // Wait for master to deassert RREADY and clear RVALID
        wait(!s5_vif.s5_cb.S5_RREADY);
        s5_vif.s5_cb.S5_RVALID <= 1'b0;
        s5_vif.s5_cb.S5_RDATA <= '0;
        s5_vif.s5_cb.S5_RLAST <= 1'b0;
        s5_vif.s5_cb.S5_RRESP <= 2'b00;
        
        // Update statistics
        s5_total_transactions++;
        s5_read_transactions++;
        
        `uvm_info("S5_DRIVER", "S5 READ transaction completed", UVM_LOW)
    endtask
    
    // Driver control methods
    
    // Enable driver
    virtual function void enable_driver();
        s5_driver_enabled = 1;
        `uvm_info("S5_DRIVER", $sformatf("S5 Driver %0d enabled", s5_driver_id), UVM_LOW)
    endfunction
    
    // Disable driver
    virtual function void disable_driver();
        s5_driver_enabled = 0;
        `uvm_info("S5_DRIVER", $sformatf("S5 Driver %0d disabled", s5_driver_id), UVM_LOW)
    endfunction
    
    // Check if driver is enabled
    virtual function bit is_driver_enabled();
        return s5_driver_enabled;
    endfunction
    
    // Get driver statistics
    virtual function string get_driver_statistics();
        return $sformatf("S5 Driver %0d Statistics: Total=%0d, Writes=%0d, Reads=%0d",
                        s5_driver_id, s5_total_transactions, s5_write_transactions, s5_read_transactions);
    endfunction
    
    // Reset driver statistics
    virtual function void reset_driver_statistics();
        s5_total_transactions = 0;
        s5_write_transactions = 0;
        s5_read_transactions = 0;
        `uvm_info("S5_DRIVER", $sformatf("S5 Driver %0d statistics reset", s5_driver_id), UVM_LOW)
    endfunction
    
    // UVM Field Macros
    `uvm_component_utils_begin(S5_driver)
        `uvm_field_int(s5_driver_id, UVM_ALL_ON)
        `uvm_field_string(s5_driver_name, UVM_ALL_ON)
        `uvm_field_int(s5_total_transactions, UVM_ALL_ON)
        `uvm_field_int(s5_write_transactions, UVM_ALL_ON)
        `uvm_field_int(s5_read_transactions, UVM_ALL_ON)
        `uvm_field_int(s5_driver_enabled, UVM_ALL_ON)
    `uvm_component_utils_end
    
endclass : S5_driver

`endif // S5_DRIVER_SV

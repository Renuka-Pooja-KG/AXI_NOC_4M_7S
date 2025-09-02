//=============================================================================
// S4 Agent Driver Class
//=============================================================================
// Basic driver for Slave 4 that responds to master write and read requests
// Extends uvm_driver to drive S4 sequence items
// Uses S4_interface.driver modport with synchronized clocking block access

`ifndef S4_DRIVER_SV
`define S4_DRIVER_SV

// Note: All imports and includes will be handled by define_files_package

class S4_driver extends uvm_driver #(S4_seq_item);
    
    // Virtual interface for S4 AXI signals using driver modport
    virtual S4_interface s4_vif;
    
    // S4 sequence item handle
    S4_seq_item req;
    
    // Driver configuration
    int unsigned s4_driver_id;
    string s4_driver_name;
    
    // Driver statistics
    int unsigned s4_total_transactions;
    int unsigned s4_write_transactions;
    int unsigned s4_read_transactions;
    
    // Driver control
    bit s4_driver_enabled;
    
    // Constructor
    function new(string name = "S4_driver", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize driver
        s4_driver_id = 0;
        s4_driver_name = name;
        
        // Initialize statistics
        s4_total_transactions = 0;
        s4_write_transactions = 0;
        s4_read_transactions = 0;
        
        // Initialize control
        s4_driver_enabled = 1;
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S4_interface)::get(this, "", "s4_vif", s4_vif)) begin
            `uvm_fatal("S4_DRIVER", "Virtual interface not found for S4 driver")
        end
    endfunction
    
    // Run phase - main driver loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S4_DRIVER", $sformatf("S4 Driver %0d starting run phase", s4_driver_id), UVM_LOW)
        
        // Initialize S4 interface signals
        init_s4_signals();
        
        // Main driver loop
        forever begin
            // Get sequence item from sequencer
            seq_item_port.get_next_item(req);
            
            // Process the transaction
            if (s4_driver_enabled) begin
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
    
    // Initialize S4 interface signals
    virtual task init_s4_signals();
        // Initialize all S4-driven signals to safe defaults
        s4_vif.s4_cb.S4_AWREADY <= 1'b0;
        s4_vif.s4_cb.S4_WREADY <= 1'b0;
        s4_vif.s4_cb.S4_BID <= '0;
        s4_vif.s4_cb.S4_BRESP <= '0;
        s4_vif.s4_cb.S4_BVALID <= 1'b0;
        s4_vif.s4_cb.S4_ARREADY <= 1'b0;
        s4_vif.s4_cb.S4_RID <= '0;
        s4_vif.s4_cb.S4_RDATA <= '0;
        s4_vif.s4_cb.S4_RRESP <= '0;
        s4_vif.s4_cb.S4_RLAST <= 1'b0;
        s4_vif.s4_cb.S4_RVALID <= 1'b0;
        
        `uvm_info("S4_DRIVER", "S4 interface signals initialized", UVM_LOW)
    endtask
    
    // Respond to write transaction (AW + W + B channels)
    virtual task rsp_to_write(S4_seq_item s4_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S4_DRIVER", "S4 responding to WRITE transaction", UVM_LOW)
        
        // Phase 1: Write Address Channel (AW) - S4 receives AW, drives AWREADY
        wait(s4_vif.s4_cb.S4_AWVALID);  // Wait for master to assert AWVALID
        b_len = s4_vif.s4_cb.S4_AWLEN + 1;  // Calculate burst length
        
        @(posedge s4_vif.ACLK);
        s4_vif.s4_cb.S4_AWREADY <= s4_seqi_inst.S4_AWREADY;  // Assert AWREADY
        @(posedge s4_vif.ACLK);
        s4_vif.s4_cb.S4_AWREADY <= 1'b0;  // Deassert AWREADY
        
        // Phase 2: Write Data Channel (W) - S4 receives W, drives WREADY
        wait(s4_vif.s4_cb.S4_WVALID);  // Wait for master to assert WVALID
        
        // Handle burst write data
        for (i = 0; i < b_len; i++) begin
            s4_vif.s4_cb.S4_WREADY <= s4_seqi_inst.S4_WREADY;  // Assert WREADY
            @(negedge s4_vif.ACLK);  // Wait for negative edge
        end
        
        // Phase 3: Write Response Channel (B) - S4 drives B, receives BREADY
        @(posedge s4_vif.ACLK);
        s4_vif.s4_cb.S4_WREADY <= 1'b0;  // Deassert WREADY
        
        // Set write response signals
        s4_vif.s4_cb.S4_BID <= s4_seqi_inst.S4_BID;
        s4_vif.s4_cb.S4_BRESP <= s4_seqi_inst.S4_BRESP;
        s4_vif.s4_cb.S4_BVALID <= s4_seqi_inst.S4_BVALID;
        
        // Handle write strobe for response
        if (s4_vif.s4_cb.S4_WSTRB == 4'hF) begin
            s4_vif.s4_cb.S4_BRESP <= s4_seqi_inst.S4_BRESP;
        end else begin
            s4_vif.s4_cb.S4_BRESP <= 2'b10;  // SLVERR if strobe not all 1's
        end
        
        @(posedge s4_vif.ACLK);
        s4_vif.s4_cb.S4_BVALID <= s4_seqi_inst.S4_BVALID;  // Assert BVALID
        
        wait(s4_vif.s4_cb.S4_BREADY);  // Wait for master to assert BREADY
        
        // Clear response signals
        s4_vif.s4_cb.S4_BVALID <= 1'b0;
        s4_vif.s4_cb.S4_BRESP <= 2'b00;
        
        // Update statistics
        s4_total_transactions++;
        s4_write_transactions++;
        
        `uvm_info("S4_DRIVER", "S4 WRITE transaction completed", UVM_LOW)
    endtask
    
    // Respond to read transaction (AR + R channels)
    virtual task rsp_to_read(S4_seq_item s4_seqi_inst);
        int i;
        int b_len;
        
        `uvm_info("S4_DRIVER", "S4 responding to READ transaction", UVM_LOW)
        
        // Phase 1: Read Address Channel (AR) - S4 receives AR, drives ARREADY
        wait(s4_vif.s4_cb.S4_ARVALID);  // Wait for master to assert ARVALID
        b_len = s4_vif.s4_cb.S4_ARLEN + 1;  // Calculate burst length
        
        @(posedge s4_vif.ACLK);
        s4_vif.s4_cb.S4_ARREADY <= s4_seqi_inst.S4_ARREADY;  // Assert ARREADY
        
        wait(!s4_vif.s4_cb.S4_ARVALID);  // Wait for master to deassert ARVALID
        s4_vif.s4_cb.S4_ARREADY <= 1'b0;  // Deassert ARREADY
        
        // Phase 2: Read Data Channel (R) - S4 drives R, receives RREADY
        for (i = 0; i < b_len; i++) begin
            // Set read data signals
            s4_vif.s4_cb.S4_RID <= s4_seqi_inst.S4_RID;
            s4_vif.s4_cb.S4_RVALID <= s4_seqi_inst.S4_RVALID;
            s4_vif.s4_cb.S4_RDATA <= $random;  // Generate random read data
            s4_vif.s4_cb.S4_RLAST <= (i == b_len - 1) ? 1'b1 : 1'b0;  // Set RLAST for final beat
            s4_vif.s4_cb.S4_RRESP <= s4_seqi_inst.S4_RRESP;
            
            @(posedge s4_vif.ACLK);  // Synchronize to clock edge
        end
        
        // Wait for master to deassert RREADY and clear RVALID
        wait(!s4_vif.s4_cb.S4_RREADY);
        s4_vif.s4_cb.S4_RVALID <= 1'b0;
        s4_vif.s4_cb.S4_RDATA <= '0;
        s4_vif.s4_cb.S4_RLAST <= 1'b0;
        s4_vif.s4_cb.S4_RRESP <= 2'b00;
        
        // Update statistics
        s4_total_transactions++;
        s4_read_transactions++;
        
        `uvm_info("S4_DRIVER", "S4 READ transaction completed", UVM_LOW)
    endtask
    
    // Driver control methods
    
    // Enable driver
    virtual function void enable_driver();
        s4_driver_enabled = 1;
        `uvm_info("S4_DRIVER", $sformatf("S4 Driver %0d enabled", s4_driver_id), UVM_LOW)
    endfunction
    
    // Disable driver
    virtual function void disable_driver();
        s4_driver_enabled = 0;
        `uvm_info("S4_DRIVER", $sformatf("S4 Driver %0d disabled", s4_driver_id), UVM_LOW)
    endfunction
    
    // Check if driver is enabled
    virtual function bit is_driver_enabled();
        return s4_driver_enabled;
    endfunction
    
    // Get driver statistics
    virtual function string get_driver_statistics();
        return $sformatf("S4 Driver %0d Statistics: Total=%0d, Writes=%0d, Reads=%0d",
                        s4_driver_id, s4_total_transactions, s4_write_transactions, s4_read_transactions);
    endfunction
    
    // Reset driver statistics
    virtual function void reset_driver_statistics();
        s4_total_transactions = 0;
        s4_write_transactions = 0;
        s4_read_transactions = 0;
        `uvm_info("S4_DRIVER", $sformatf("S4 Driver %0d statistics reset", s4_driver_id), UVM_LOW)
    endfunction
    
    // UVM Field Macros
    `uvm_component_utils_begin(S4_driver)
        `uvm_field_int(s4_driver_id, UVM_ALL_ON)
        `uvm_field_string(s4_driver_name, UVM_ALL_ON)
        `uvm_field_int(s4_total_transactions, UVM_ALL_ON)
        `uvm_field_int(s4_write_transactions, UVM_ALL_ON)
        `uvm_field_int(s4_read_transactions, UVM_ALL_ON)
        `uvm_field_int(s4_driver_enabled, UVM_ALL_ON)
    `uvm_component_utils_end
    
endclass : S4_driver

`endif // S4_DRIVER_SV

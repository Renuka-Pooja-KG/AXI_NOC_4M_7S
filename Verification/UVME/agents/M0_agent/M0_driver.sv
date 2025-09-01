//=============================================================================
// M0 Agent Driver Class
//=============================================================================
// Basic driver for Master 0 that handles write and read sequences
// Extends uvm_driver to drive M0 sequence items
// Uses M0_interface.driver modport with synchronized clocking block access

`ifndef M0_DRIVER_SV
`define M0_DRIVER_SV

// Note: All imports and includes will be handled by define_files_package

class M0_driver extends uvm_driver #(M0_seq_item);
    
    // Virtual interface for M0 AXI signals using driver modport
    virtual M0_interface.driver m0_vif;
    
    //M0_seq_item
    M0_seq_item req;
    
    // Driver configuration
    int unsigned m0_driver_id;
    string m0_driver_name;
    
    // Driver statistics
    int unsigned m0_total_transactions;
    int unsigned m0_write_transactions;
    int unsigned m0_read_transactions;
    
    // Driver control
    bit m0_driver_enabled;

    int unsigned burst_length;
    
    // Constructor
    function new(string name = "M0_driver", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize driver
        m0_driver_id = 0;
        m0_driver_name = name;
        
        // Initialize statistics
        m0_total_transactions = 0;
        m0_write_transactions = 0;
        m0_read_transactions = 0;
        
        // Initialize control
        m0_driver_enabled = 1;
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual M0_interface.driver)::get(this, "", "m0_vif", m0_vif)) begin
            `uvm_fatal("M0_DRIVER", "Virtual interface not found for M0 driver")
        end
    endfunction
    
    // Run phase - main driver loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("M0_DRIVER", $sformatf("M0 Driver %0d starting run phase", m0_driver_id), UVM_LOW)
        
        // Main driver loop
        forever begin
            // Get sequence item from sequencer
            seq_item_port.get_next_item(req);
            
            // Process the transaction
            if (m0_driver_enabled) begin
                drive_transaction(req);
            end
            
            // Signal completion
            seq_item_port.item_done();
        end
    endtask
    
    // Drive transaction based on type
    virtual task drive_transaction(M0_seq_item item);
        `uvm_info("M0_DRIVER", $sformatf("M0 Driver %0d driving transaction: Type=%s, Slave=%0d, ID=%0d", 
                                        m0_driver_id, item.trans_type.name(), item.slave_id, item.M0_AWID), UVM_LOW)
        
        case (item.trans_type)
            AXI_WRITE: drive_write_transaction(item);
            AXI_READ:  drive_read_transaction(item);
            default:   `uvm_error("M0_DRIVER", $sformatf("Unknown transaction type: %s", item.trans_type.name()))
        endcase
        
        // Update statistics
        update_driver_statistics(item);
    endtask
    
    // Drive write transaction
    virtual task drive_write_transaction(M0_seq_item item);
        `uvm_info("M0_DRIVER", $sformatf("M0 Driver %0d driving WRITE transaction to Slave %0d", 
                                        m0_driver_id, item.slave_id), UVM_LOW)
        
        // Phase 1: Write Address Channel (AW)
        drive_write_address_phase(item);
        
        // Phase 2: Write Data Channel (W)
        drive_write_data_phase(item);
        
        // Phase 3: Write Response Channel (B)
        drive_write_response_phase(item);
        
        `uvm_info("M0_DRIVER", $sformatf("M0 Driver %0d WRITE transaction completed", m0_driver_id), UVM_LOW)
    endtask
    
    // Drive read transaction
    virtual task drive_read_transaction(M0_seq_item item);
        `uvm_info("M0_DRIVER", $sformatf("M0 Driver %0d driving READ transaction from Slave %0d", 
                                        m0_driver_id, item.slave_id), UVM_LOW)
        
        // Phase 1: Read Address Channel (AR)
        drive_read_address_phase(item);
        
        // Phase 2: Read Data Channel (R)
        drive_read_data_phase(item);
        
        `uvm_info("M0_DRIVER", $sformatf("M0 Driver %0d READ transaction completed", m0_driver_id), UVM_LOW)
    endtask
    
    // Drive write address phase using clocking block
    virtual task drive_write_address_phase(M0_seq_item item);
        `uvm_info("M0_DRIVER", "Driving Write Address Phase", UVM_FULL)
        
         repeat (4) @(posedge m0_vif.ACLK);  // 4-clock delay before starting
           
        // Set address channel signals through clocking block for synchronization
        m0_vif.m0_cb.M0_AWID <= item.M0_AWID;
        m0_vif.m0_cb.M0_AWADDR <= item.M0_AWADDR;
        m0_vif.m0_cb.M0_AWLEN <= item.M0_AWLEN;
        m0_vif.m0_cb.M0_AWSIZE <= item.M0_AWSIZE;
        m0_vif.m0_cb.M0_AWBURST <= item.M0_AWBURST;
        m0_vif.m0_cb.M0_AWLOCK <= item.M0_AWLOCK;
        m0_vif.m0_cb.M0_AWCACHE <= item.M0_AWCACHE;
        m0_vif.m0_cb.M0_AWPROT <= item.M0_AWPROT;
        m0_vif.m0_cb.M0_AWQOS <= item.M0_AWQOS;
        m0_vif.m0_cb.M0_AWREGION <= item.M0_AWREGION;
        m0_vif.m0_cb.M0_AWVALID <= 1'b1;
        
        // Wait for slave ready using clocking block
        @(posedge m0_vif.ACLK);
        while (!m0_vif.m0_cb.M0_AWREADY) begin
            @(posedge m0_vif.ACLK);
        end
        
        // Clear valid signal through clocking block
        m0_vif.m0_cb.M0_AWVALID <= 1'b0;
        @(posedge m0_vif.ACLK);
    endtask
    
    // Drive write data phase using clocking block
    virtual task drive_write_data_phase(M0_seq_item item);
        `uvm_info("M0_DRIVER", "Driving Write Data Phase", UVM_FULL)
        
        burst_length = get_burst_length(item.M0_AWLEN);
        
        for (int i = 0; i < burst_length; i++) begin
            // Set data channel signals through clocking block
            m0_vif.m0_cb.M0_WDATA <= item.burst_data[i];
            m0_vif.m0_cb.M0_WSTRB <= item.burst_strobe[i];
            m0_vif.m0_cb.M0_WLAST <= (i == burst_length - 1) ? 1'b1 : 1'b0;
            m0_vif.m0_cb.M0_WVALID <= 1'b1;
            
            // Wait for slave ready using clocking block
            @(posedge m0_vif.ACLK);
            while (!m0_vif.m0_cb.M0_WREADY) begin
                @(posedge m0_vif.ACLK);
            end
            
            // Clear valid signal through clocking block
            m0_vif.m0_cb.M0_WVALID <= 1'b0;
            @(posedge m0_vif.ACLK);
        end
    endtask
    
    // Drive write response phase using clocking block
    virtual task drive_write_response_phase(M0_seq_item item);
        `uvm_info("M0_DRIVER", "Driving Write Response Phase", UVM_FULL)
         repeat (2) @(posedge m0_vif.ACLK);  // 2-clock delay before starting
           
        // Set response ready through clocking block
        m0_vif.m0_cb.M0_BREADY <= 1'b1;
        
        // Wait for response valid using clocking block
        @(posedge m0_vif.ACLK);
        while (!m0_vif.m0_cb.M0_BVALID) begin
            @(posedge m0_vif.ACLK);
        end
        
        // Capture response from clocking block
        item.M0_BID = m0_vif.m0_cb.M0_BID;
        item.M0_BRESP = m0_vif.m0_cb.M0_BRESP;
        
        // Clear ready signal through clocking block
        m0_vif.m0_cb.M0_BREADY <= 1'b0;
        @(posedge m0_vif.ACLK);
    endtask
    
    // Drive read address phase using clocking block
    virtual task drive_read_address_phase(M0_seq_item item);
        `uvm_info("M0_DRIVER", "Driving Read Address Phase", UVM_FULL)
        repeat (4) @(posedge m0_vif.ACLK);  // 4-clock delay before starting
           
        // Set address channel signals through clocking block
        m0_vif.m0_cb.M0_ARID <= item.M0_ARID;
        m0_vif.m0_cb.M0_ARADDR <= item.M0_ARADDR;
        m0_vif.m0_cb.M0_ARLEN <= item.M0_ARLEN;
        m0_vif.m0_cb.M0_ARSIZE <= item.M0_ARSIZE;
        m0_vif.m0_cb.M0_ARBURST <= item.M0_ARBURST;
        m0_vif.m0_cb.M0_ARLOCK <= item.M0_ARLOCK;
        m0_vif.m0_cb.M0_ARCACHE <= item.M0_ARCACHE;
        m0_vif.m0_cb.M0_ARPROT <= item.M0_ARPROT;
        m0_vif.m0_cb.M0_ARQOS <= item.M0_ARQOS;
        m0_vif.m0_cb.M0_ARREGION <= item.M0_ARREGION;
        m0_vif.m0_cb.M0_ARVALID <= 1'b1;
        
        // Wait for slave ready using clocking block
        @(posedge m0_vif.ACLK);
        while (!m0_vif.m0_cb.M0_ARREADY) begin
            @(posedge m0_vif.ACLK);
        end
        
        // Clear valid signal through clocking block
        m0_vif.m0_cb.M0_ARVALID <= 1'b0;
        @(posedge m0_vif.ACLK);
    endtask
    
    // Drive read data phase using clocking block
    virtual task drive_read_data_phase(M0_seq_item item);
        `uvm_info("M0_DRIVER", "Driving Read Data Phase", UVM_FULL)
        repeat (4) @(posedge m0_vif.ACLK);  // 4-clock delay before starting
        burst_length = get_burst_length(item.M0_ARLEN);
        
        for (int i = 0; i < burst_length; i++) begin
            // Set read ready through clocking block
            m0_vif.m0_cb.M0_RREADY <= 1'b1;
            
            // Wait for data valid using clocking block
            @(posedge m0_vif.ACLK);
            while (!m0_vif.m0_cb.M0_RVALID) begin
                @(posedge m0_vif.ACLK);
            end
            
            // Capture data from clocking block
            item.M0_RID = m0_vif.m0_cb.M0_RID;
            item.M0_RDATA = m0_vif.m0_cb.M0_RDATA;
            item.M0_RRESP = m0_vif.m0_cb.M0_RRESP;
            item.M0_RLAST = m0_vif.m0_cb.M0_RLAST;
            
            // Store in burst data array
            item.burst_data[i] = m0_vif.m0_cb.M0_RDATA;
            
            // Clear ready signal through clocking block
            m0_vif.m0_cb.M0_RREADY <= 1'b0;
            @(posedge m0_vif.ACLK);
        end
    endtask
    
    // Update driver statistics
    virtual function void update_driver_statistics(M0_seq_item item);
        m0_total_transactions++;
        
        if (item.trans_type == AXI_WRITE) begin
            m0_write_transactions++;
        end else begin
            m0_read_transactions++;
        end
        
        `uvm_info("M0_DRIVER", $sformatf("M0 Driver %0d stats: Total=%0d, W=%0d, R=%0d", 
                                        m0_driver_id, m0_total_transactions, 
                                        m0_write_transactions, m0_read_transactions), UVM_FULL)
    endfunction
    
    // Driver control methods
    
    // Enable driver
    virtual function void enable_driver();
        m0_driver_enabled = 1;
        `uvm_info("M0_DRIVER", $sformatf("M0 Driver %0d enabled", m0_driver_id), UVM_LOW)
    endfunction
    
    // Disable driver
    virtual function void disable_driver();
        m0_driver_enabled = 0;
        `uvm_info("M0_DRIVER", $sformatf("M0 Driver %0d disabled", m0_driver_id), UVM_LOW)
    endfunction
    
    // Check if driver is enabled
    virtual function bit is_driver_enabled();
        return m0_driver_enabled;
    endfunction
    
    // Get driver statistics
    virtual function string get_driver_statistics();
        return $sformatf("M0 Driver %0d Statistics: Total=%0d, Writes=%0d, Reads=%0d",
                        m0_driver_id, m0_total_transactions, m0_write_transactions, m0_read_transactions);
    endfunction
    
    // Reset driver statistics
    virtual function void reset_driver_statistics();
        m0_total_transactions = 0;
        m0_write_transactions = 0;
        m0_read_transactions = 0;
        `uvm_info("M0_DRIVER", $sformatf("M0 Driver %0d statistics reset", m0_driver_id), UVM_LOW)
    endfunction
    
    // UVM Field Macros
    `uvm_component_utils_begin(M0_driver)
        `uvm_field_int(m0_driver_id, UVM_ALL_ON)
        `uvm_field_string(m0_driver_name, UVM_ALL_ON)
        `uvm_field_int(m0_total_transactions, UVM_ALL_ON)
        `uvm_field_int(m0_write_transactions, UVM_ALL_ON)
        `uvm_field_int(m0_read_transactions, UVM_ALL_ON)
        `uvm_field_int(m0_driver_enabled, UVM_ALL_ON)
    `uvm_component_utils_end
    
endclass : M0_driver

`endif // M0_DRIVER_SV
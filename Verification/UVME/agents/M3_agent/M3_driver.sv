//=============================================================================
// M3 Agent Driver Class
//=============================================================================
// Basic driver for Master 3 that handles write and read sequences
// Extends uvm_driver to drive M3 sequence items
// Uses M3_interface.driver modport with synchronized clocking block access

`ifndef M3_DRIVER_SV
`define M3_DRIVER_SV

// Note: All imports and includes will be handled by define_files_package

class M3_driver extends uvm_driver #(M3_seq_item);
    
    // Virtual interface for M3 AXI signals using driver modport
    virtual M3_interface.driver m3_vif;
    
    //M3_seq_item
    M3_seq_item req;
    
    // Driver configuration
    int unsigned m3_driver_id;
    string m3_driver_name;
    
    // Driver statistics
    int unsigned m3_total_transactions;
    int unsigned m3_write_transactions;
    int unsigned m3_read_transactions;
    
    // Driver control
    bit m3_driver_enabled;
    
    // Constructor
    function new(string name = "M3_driver", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize driver
        m3_driver_id = 0;
        m3_driver_name = name;
        
        // Initialize statistics
        m3_total_transactions = 0;
        m3_write_transactions = 0;
        m3_read_transactions = 0;
        
        // Initialize control
        m3_driver_enabled = 1;
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual M3_interface.driver)::get(this, "", "m3_vif", m3_vif)) begin
            `uvm_fatal("M3_DRIVER", "Virtual interface not found for M3 driver")
        end
    endfunction
    
    // Run phase - main driver loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("M3_DRIVER", $sformatf("M3 Driver %0d starting run phase", m3_driver_id), UVM_LOW)
        
        // Main driver loop
        forever begin
            // Get sequence item from sequencer
            seq_item_port.get_next_item(req);
            
            // Process the transaction
            if (m3_driver_enabled) begin
                drive_transaction(req);
            end
            
            // Signal completion
            seq_item_port.item_done();
        end
    endtask
    
    // Drive transaction based on type
    virtual task drive_transaction(M3_seq_item item);
        `uvm_info("M3_DRIVER", $sformatf("M3 Driver %0d driving transaction: %s", 
                                        m3_driver_id, item.get_transaction_info()), UVM_LOW)
        
        case (item.trans_type)
            AXI_WRITE: drive_write_transaction(item);
            AXI_READ:  drive_read_transaction(item);
            default:   `uvm_error("M3_DRIVER", $sformatf("Unknown transaction type: %s", item.trans_type.name()))
        endcase
        
        // Update statistics
        update_driver_statistics(item);
    endtask
    
    // Drive write transaction
    virtual task drive_write_transaction(M3_seq_item item);
        `uvm_info("M3_DRIVER", $sformatf("M3 Driver %0d driving WRITE transaction to Slave %0d", 
                                        m3_driver_id, item.slave_id), UVM_LOW)
        
        // Phase 1: Write Address Channel (AW)
        drive_write_address_phase(item);
        
        // Phase 2: Write Data Channel (W)
        drive_write_data_phase(item);
        
        // Phase 3: Write Response Channel (B)
        drive_write_response_phase(item);
        
        `uvm_info("M3_DRIVER", $sformatf("M3 Driver %0d WRITE transaction completed", m3_driver_id), UVM_LOW)
    endtask
    
    // Drive read transaction
    virtual task drive_read_transaction(M3_seq_item item);
        `uvm_info("M3_DRIVER", $sformatf("M3 Driver %0d driving READ transaction from Slave %0d", 
                                        m3_driver_id, item.slave_id), UVM_LOW)
        
        // Phase 1: Read Address Channel (AR)
        drive_read_address_phase(item);
        
        // Phase 2: Read Data Channel (R)
        drive_read_data_phase(item);
        
        `uvm_info("M3_DRIVER", $sformatf("M3 Driver %0d READ transaction completed", m3_driver_id), UVM_LOW)
    endtask
    
    // Drive write address phase using clocking block
    virtual task drive_write_address_phase(M3_seq_item item);
        `uvm_info("M3_DRIVER", "Driving Write Address Phase", UVM_FULL)
        
         repeat (4) @(posedge m3_vif.ACLK);  // 4-clock delay before starting
           
        // Set address channel signals through clocking block for synchronization
        m3_vif.m3_cb.M3_AWID <= item.M3_AWID;
        m3_vif.m3_cb.M3_AWADDR <= item.M3_AWADDR;
        m3_vif.m3_cb.M3_AWLEN <= item.M3_AWLEN;
        m3_vif.m3_cb.M3_AWSIZE <= item.M3_AWSIZE;
        m3_vif.m3_cb.M3_AWBURST <= item.M3_AWBURST;
        m3_vif.m3_cb.M3_AWLOCK <= item.M3_AWLOCK;
        m3_vif.m3_cb.M3_AWCACHE <= item.M3_AWCACHE;
        m3_vif.m3_cb.M3_AWPROT <= item.M3_AWPROT;
        m3_vif.m3_cb.M3_AWQOS <= item.M3_AWQOS;
        m3_vif.m3_cb.M3_AWREGION <= item.M3_AWREGION;
        m3_vif.m3_cb.M3_AWVALID <= 1'b1;
        
        // Wait for slave ready using clocking block
        @(posedge m3_vif.ACLK);
        while (!m3_vif.m3_cb.M3_AWREADY) begin
            @(posedge m3_vif.ACLK);
        end
        
        // Clear valid signal through clocking block
        m3_vif.m3_cb.M3_AWVALID <= 1'b0;
        @(posedge m3_vif.ACLK);
    endtask
    
    // Drive write data phase using clocking block
    virtual task drive_write_data_phase(M3_seq_item item);
        `uvm_info("M3_DRIVER", "Driving Write Data Phase", UVM_FULL)
        
        int burst_length = get_burst_length(item.M3_AWLEN);
        
        for (int i = 0; i < burst_length; i++) begin
            // Set data channel signals through clocking block
            m3_vif.m3_cb.M3_WDATA <= item.burst_data[i];
            m3_vif.m3_cb.M3_WSTRB <= item.burst_strobe[i];
            m3_vif.m3_cb.M3_WLAST <= (i == burst_length - 1) ? 1'b1 : 1'b0;
            m3_vif.m3_cb.M3_WVALID <= 1'b1;
            
            // Wait for slave ready using clocking block
            @(posedge m3_vif.ACLK);
            while (!m3_vif.m3_cb.M3_WREADY) begin
                @(posedge m3_vif.ACLK);
            end
            
            // Clear valid signal through clocking block
            m3_vif.m3_cb.M3_WVALID <= 1'b0;
            @(posedge m3_vif.ACLK);
        end
    endtask
    
    // Drive write response phase using clocking block
    virtual task drive_write_response_phase(M3_seq_item item);
        `uvm_info("M3_DRIVER", "Driving Write Response Phase", UVM_FULL)
         repeat (2) @(posedge m3_vif.ACLK);  // 2-clock delay before starting
           
        // Set response ready through clocking block
        m3_vif.m3_cb.M3_BREADY <= 1'b1;
        
        // Wait for response valid using clocking block
        @(posedge m3_vif.ACLK);
        while (!m3_vif.m3_cb.M3_BVALID) begin
            @(posedge m3_vif.ACLK);
        end
        
        // Capture response from clocking block
        item.M3_BID = m3_vif.m3_cb.M3_BID;
        item.M3_BRESP = m3_vif.m3_cb.M3_BRESP;
        
        // Clear ready signal through clocking block
        m3_vif.m3_cb.M3_BREADY <= 1'b0;
        @(posedge m3_vif.ACLK);
    endtask
    
    // Drive read address phase using clocking block
    virtual task drive_read_address_phase(M3_seq_item item);
        `uvm_info("M3_DRIVER", "Driving Read Address Phase", UVM_FULL)
 repeat (4) @(posedge m3_vif.ACLK);  // 4-clock delay before starting
           
        // Set address channel signals through clocking block
        m3_vif.m3_cb.M3_ARID <= item.M3_ARID;
        m3_vif.m3_cb.M3_ARADDR <= item.M3_ARADDR;
        m3_vif.m3_cb.M3_ARLEN <= item.M3_ARLEN;
        m3_vif.m3_cb.M3_ARSIZE <= item.M3_ARSIZE;
        m3_vif.m3_cb.M3_ARBURST <= item.M3_ARBURST;
        m3_vif.m3_cb.M3_ARLOCK <= item.M3_ARLOCK;
        m3_vif.m3_cb.M3_ARCACHE <= item.M3_ARCACHE;
        m3_vif.m3_cb.M3_ARPROT <= item.M3_ARPROT;
        m3_vif.m3_cb.M3_ARQOS <= item.M3_ARQOS;
        m3_vif.m3_cb.M3_ARREGION <= item.M3_ARREGION;
        m3_vif.m3_cb.M3_ARVALID <= 1'b1;
        
        // Wait for slave ready using clocking block
        @(posedge m3_vif.ACLK);
        while (!m3_vif.m3_cb.M3_ARREADY) begin
            @(posedge m3_vif.ACLK);
        end
        
        // Clear valid signal through clocking block
        m3_vif.m3_cb.M3_ARVALID <= 1'b0;
        @(posedge m3_vif.ACLK);
    endtask
    
    // Drive read data phase using clocking block
    virtual task drive_read_data_phase(M3_seq_item item);
        `uvm_info("M3_DRIVER", "Driving Read Data Phase", UVM_FULL)
        repeat (4) @(posedge m3_vif.ACLK);  // 4-clock delay before starting
        int burst_length = get_burst_length(item.M3_ARLEN);
        
        for (int i = 0; i < burst_length; i++) begin
            // Set read ready through clocking block
            m3_vif.m3_cb.M3_RREADY <= 1'b1;
            
            // Wait for data valid using clocking block
            @(posedge m3_vif.ACLK);
            while (!m3_vif.m3_cb.M3_RVALID) begin
                @(posedge m3_vif.ACLK);
            end
            
            // Capture data from clocking block
            item.M3_RID = m3_vif.m3_cb.M3_RID;
            item.M3_RDATA = m3_vif.m3_cb.M3_RDATA;
            item.M3_RRESP = m3_vif.m3_cb.M3_RRESP;
            item.M3_RLAST = m3_vif.m3_cb.M3_RLAST;
            
            // Store in burst data array
            item.burst_data[i] = m3_vif.m3_cb.M3_RDATA;
            
            // Clear ready signal through clocking block
            m3_vif.m3_cb.M3_RREADY <= 1'b0;
            @(posedge m3_vif.ACLK);
        end
    endtask
    
    // Update driver statistics
    virtual function void update_driver_statistics(M3_seq_item item);
        m3_total_transactions++;
        
        if (item.trans_type == AXI_WRITE) begin
            m3_write_transactions++;
        end else begin
            m3_read_transactions++;
        end
        
        `uvm_info("M3_DRIVER", $sformatf("M3 Driver %0d stats: Total=%0d, W=%0d, R=%0d", 
                                        m3_driver_id, m3_total_transactions, 
                                        m3_write_transactions, m3_read_transactions), UVM_FULL)
    endfunction
    
    // Driver control methods
    
    // Enable driver
    virtual function void enable_driver();
        m3_driver_enabled = 1;
        `uvm_info("M3_DRIVER", $sformatf("M3 Driver %0d enabled", m3_driver_id), UVM_LOW)
    endfunction
    
    // Disable driver
    virtual function void disable_driver();
        m3_driver_enabled = 0;
        `uvm_info("M3_DRIVER", $sformatf("M3 Driver %0d disabled", m3_driver_id), UVM_LOW)
    endfunction
    
    // Check if driver is enabled
    virtual function bit is_driver_enabled();
        return m3_driver_enabled;
    endfunction
    
    // Get driver statistics
    virtual function string get_driver_statistics();
        return $sformatf("M3 Driver %0d Statistics: Total=%0d, Writes=%0d, Reads=%0d",
                        m3_driver_id, m3_total_transactions, m3_write_transactions, m3_read_transactions);
    endfunction
    
    // Reset driver statistics
    virtual function void reset_driver_statistics();
        m3_total_transactions = 0;
        m3_write_transactions = 0;
        m3_read_transactions = 0;
        `uvm_info("M3_DRIVER", $sformatf("M3 Driver %0d statistics reset", m3_driver_id), UVM_LOW)
    endfunction
    
    // UVM Field Macros
    `uvm_component_utils_begin(M3_driver)
        `uvm_field_int(m3_driver_id, UVM_ALL_ON)
        `uvm_field_string(m3_driver_name, UVM_ALL_ON)
        `uvm_field_int(m3_total_transactions, UVM_ALL_ON)
        `uvm_field_int(m3_write_transactions, UVM_ALL_ON)
        `uvm_field_int(m3_read_transactions, UVM_ALL_ON)
        `uvm_field_int(m3_driver_enabled, UVM_ALL_ON)
    `uvm_component_utils_end
    
endclass : M3_driver

`endif // M3_DRIVER_SV
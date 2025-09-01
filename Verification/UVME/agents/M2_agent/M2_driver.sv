//=============================================================================
// M2 Agent Driver Class
//=============================================================================
// Basic driver for Master 2 that handles write and read sequences
// Extends uvm_driver to drive M2 sequence items
// Uses M2_interface.driver modport with synchronized clocking block access

`ifndef M2_DRIVER_SV
`define M2_DRIVER_SV

// Note: All imports and includes will be handled by define_files_package

class M2_driver extends uvm_driver #(M2_seq_item);
    
    // Virtual interface for M2 AXI signals using driver modport
    virtual M2_interface.driver m2_vif;
    
    //M2_seq_item
    M2_seq_item req;
    
    // Driver configuration
    int unsigned m2_driver_id;
    string m2_driver_name;
    
    // Driver statistics
    int unsigned m2_total_transactions;
    int unsigned m2_write_transactions;
    int unsigned m2_read_transactions;
    
    // Driver control
    bit m2_driver_enabled;

    int unsigned burst_length;
    
    // Constructor
    function new(string name = "M2_driver", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize driver
        m2_driver_id = 0;
        m2_driver_name = name;
        
        // Initialize statistics
        m2_total_transactions = 0;
        m2_write_transactions = 0;
        m2_read_transactions = 0;
        
        // Initialize control
        m2_driver_enabled = 1;
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual M2_interface.driver)::get(this, "", "m2_vif", m2_vif)) begin
            `uvm_fatal("M2_DRIVER", "Virtual interface not found for M2 driver")
        end
    endfunction
    
    // Run phase - main driver loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("M2_DRIVER", $sformatf("M2 Driver %0d starting run phase", m2_driver_id), UVM_LOW)
        
        // Main driver loop
        forever begin
            // Get sequence item from sequencer
            seq_item_port.get_next_item(req);
            
            // Process the transaction
            if (m2_driver_enabled) begin
                drive_transaction(req);
            end
            
            // Signal completion
            seq_item_port.item_done();
        end
    endtask
    
    // Drive transaction based on type
    virtual task drive_transaction(M2_seq_item item);
        `uvm_info("M2_DRIVER", $sformatf("M2 Driver %0d driving transaction: Type=%s, Slave=%0d, ID=%0d", 
                                        m2_driver_id, item.trans_type.name(), item.slave_id, item.M2_AWID), UVM_LOW)
        
        case (item.trans_type)
            AXI_WRITE: drive_write_transaction(item);
            AXI_READ:  drive_read_transaction(item);
            default:   `uvm_error("M2_DRIVER", $sformatf("Unknown transaction type: %s", item.trans_type.name()))
        endcase
        
        // Update statistics
        update_driver_statistics(item);
    endtask
    
    // Drive write transaction
    virtual task drive_write_transaction(M2_seq_item item);
        `uvm_info("M2_DRIVER", $sformatf("M2 Driver %0d driving WRITE transaction to Slave %0d", 
                                        m2_driver_id, item.slave_id), UVM_LOW)
        
        // Phase 1: Write Address Channel (AW)
        drive_write_address_phase(item);
        
        // Phase 2: Write Data Channel (W)
        drive_write_data_phase(item);
        
        // Phase 3: Write Response Channel (B)
        drive_write_response_phase(item);
        
        `uvm_info("M2_DRIVER", $sformatf("M2 Driver %0d WRITE transaction completed", m2_driver_id), UVM_LOW)
    endtask
    
    // Drive read transaction
    virtual task drive_read_transaction(M2_seq_item item);
        `uvm_info("M2_DRIVER", $sformatf("M2 Driver %0d driving READ transaction from Slave %0d", 
                                        m2_driver_id, item.slave_id), UVM_LOW)
        
        // Phase 1: Read Address Channel (AR)
        drive_read_address_phase(item);
        
        // Phase 2: Read Data Channel (R)
        drive_read_data_phase(item);
        
        `uvm_info("M2_DRIVER", $sformatf("M2 Driver %0d READ transaction completed", m2_driver_id), UVM_LOW)
    endtask
    
    // Drive write address phase using clocking block
    virtual task drive_write_address_phase(M2_seq_item item);
        `uvm_info("M2_DRIVER", "Driving Write Address Phase", UVM_FULL)
        
         repeat (4) @(posedge m2_vif.ACLK);  // 4-clock delay before starting
           
        // Set address channel signals through clocking block for synchronization
        m2_vif.m2_cb.M2_AWID <= item.M2_AWID;
        m2_vif.m2_cb.M2_AWADDR <= item.M2_AWADDR;
        m2_vif.m2_cb.M2_AWLEN <= item.M2_AWLEN;
        m2_vif.m2_cb.M2_AWSIZE <= item.M2_AWSIZE;
        m2_vif.m2_cb.M2_AWBURST <= item.M2_AWBURST;
        m2_vif.m2_cb.M2_AWLOCK <= item.M2_AWLOCK;
        m2_vif.m2_cb.M2_AWCACHE <= item.M2_AWCACHE;
        m2_vif.m2_cb.M2_AWPROT <= item.M2_AWPROT;
        m2_vif.m2_cb.M2_AWQOS <= item.M2_AWQOS;
        m2_vif.m2_cb.M2_AWREGION <= item.M2_AWREGION;
        m2_vif.m2_cb.M2_AWVALID <= 1'b1;
        
        // Wait for slave ready using clocking block
        @(posedge m2_vif.ACLK);
        while (!m2_vif.m2_cb.M2_AWREADY) begin
            @(posedge m2_vif.ACLK);
        end
        
        // Clear valid signal through clocking block
        m2_vif.m2_cb.M2_AWVALID <= 1'b0;
        @(posedge m2_vif.ACLK);
    endtask
    
    // Drive write data phase using clocking block
    virtual task drive_write_data_phase(M2_seq_item item);
        `uvm_info("M2_DRIVER", "Driving Write Data Phase", UVM_FULL)
        
        burst_length = get_burst_length(item.M2_AWLEN);
        
        for (int i = 0; i < burst_length; i++) begin
            // Set data channel signals through clocking block
            m2_vif.m2_cb.M2_WDATA <= item.burst_data[i];
            m2_vif.m2_cb.M2_WSTRB <= item.burst_strobe[i];
            m2_vif.m2_cb.M2_WLAST <= (i == burst_length - 1) ? 1'b1 : 1'b0;
            m2_vif.m2_cb.M2_WVALID <= 1'b1;
            
            // Wait for slave ready using clocking block
            @(posedge m2_vif.ACLK);
            while (!m2_vif.m2_cb.M2_WREADY) begin
                @(posedge m2_vif.ACLK);
            end
            
            // Clear valid signal through clocking block
            m2_vif.m2_cb.M2_WVALID <= 1'b0;
            @(posedge m2_vif.ACLK);
        end
    endtask
    
    // Drive write response phase using clocking block
    virtual task drive_write_response_phase(M2_seq_item item);
        `uvm_info("M2_DRIVER", "Driving Write Response Phase", UVM_FULL)
         repeat (2) @(posedge m2_vif.ACLK);  // 2-clock delay before starting
           
        // Set response ready through clocking block
        m2_vif.m2_cb.M2_BREADY <= 1'b1;
        
        // Wait for response valid using clocking block
        @(posedge m2_vif.ACLK);
        while (!m2_vif.m2_cb.M2_BVALID) begin
            @(posedge m2_vif.ACLK);
        end
        
        // Capture response from clocking block
        item.M2_BID = m2_vif.m2_cb.M2_BID;
        item.M2_BRESP = m2_vif.m2_cb.M2_BRESP;
        
        // Clear ready signal through clocking block
        m2_vif.m2_cb.M2_BREADY <= 1'b0;
        @(posedge m2_vif.ACLK);
    endtask
    
    // Drive read address phase using clocking block
    virtual task drive_read_address_phase(M2_seq_item item);
        `uvm_info("M2_DRIVER", "Driving Read Address Phase", UVM_FULL)
 repeat (4) @(posedge m2_vif.ACLK);  // 4-clock delay before starting
           
        // Set address channel signals through clocking block
        m2_vif.m2_cb.M2_ARID <= item.M2_ARID;
        m2_vif.m2_cb.M2_ARADDR <= item.M2_ARADDR;
        m2_vif.m2_cb.M2_ARLEN <= item.M2_ARLEN;
        m2_vif.m2_cb.M2_ARSIZE <= item.M2_ARSIZE;
        m2_vif.m2_cb.M2_ARBURST <= item.M2_ARBURST;
        m2_vif.m2_cb.M2_ARLOCK <= item.M2_ARLOCK;
        m2_vif.m2_cb.M2_ARCACHE <= item.M2_ARCACHE;
        m2_vif.m2_cb.M2_ARPROT <= item.M2_ARPROT;
        m2_vif.m2_cb.M2_ARQOS <= item.M2_ARQOS;
        m2_vif.m2_cb.M2_ARREGION <= item.M2_ARREGION;
        m2_vif.m2_cb.M2_ARVALID <= 1'b1;
        
        // Wait for slave ready using clocking block
        @(posedge m2_vif.ACLK);
        while (!m2_vif.m2_cb.M2_ARREADY) begin
            @(posedge m2_vif.ACLK);
        end
        
        // Clear valid signal through clocking block
        m2_vif.m2_cb.M2_ARVALID <= 1'b0;
        @(posedge m2_vif.ACLK);
    endtask
    
    // Drive read data phase using clocking block
    virtual task drive_read_data_phase(M2_seq_item item);
        `uvm_info("M2_DRIVER", "Driving Read Data Phase", UVM_FULL)
        repeat (4) @(posedge m2_vif.ACLK);  // 4-clock delay before starting
        burst_length = get_burst_length(item.M2_ARLEN);
        
        for (int i = 0; i < burst_length; i++) begin
            // Set read ready through clocking block
            m2_vif.m2_cb.M2_RREADY <= 1'b1;
            
            // Wait for data valid using clocking block
            @(posedge m2_vif.ACLK);
            while (!m2_vif.m2_cb.M2_RVALID) begin
                @(posedge m2_vif.ACLK);
            end
            
            // Capture data from clocking block
            item.M2_RID = m2_vif.m2_cb.M2_RID;
            item.M2_RDATA = m2_vif.m2_cb.M2_RDATA;
            item.M2_RRESP = m2_vif.m2_cb.M2_RRESP;
            item.M2_RLAST = m2_vif.m2_cb.M2_RLAST;
            
            // Store in burst data array
            item.burst_data[i] = m2_vif.m2_cb.M2_RDATA;
            
            // Clear ready signal through clocking block
            m2_vif.m2_cb.M2_RREADY <= 1'b0;
            @(posedge m2_vif.ACLK);
        end
    endtask
    
    // Update driver statistics
    virtual function void update_driver_statistics(M2_seq_item item);
        m2_total_transactions++;
        
        if (item.trans_type == AXI_WRITE) begin
            m2_write_transactions++;
        end else begin
            m2_read_transactions++;
        end
        
        `uvm_info("M2_DRIVER", $sformatf("M2 Driver %0d stats: Total=%0d, W=%0d, R=%0d", 
                                        m2_driver_id, m2_total_transactions, 
                                        m2_write_transactions, m2_read_transactions), UVM_FULL)
    endfunction
    
    // Driver control methods
    
    // Enable driver
    virtual function void enable_driver();
        m2_driver_enabled = 1;
        `uvm_info("M2_DRIVER", $sformatf("M2 Driver %0d enabled", m2_driver_id), UVM_LOW)
    endfunction
    
    // Disable driver
    virtual function void disable_driver();
        m2_driver_enabled = 0;
        `uvm_info("M2_DRIVER", $sformatf("M2 Driver %0d disabled", m2_driver_id), UVM_LOW)
    endfunction
    
    // Check if driver is enabled
    virtual function bit is_driver_enabled();
        return m2_driver_enabled;
    endfunction
    
    // Get driver statistics
    virtual function string get_driver_statistics();
        return $sformatf("M2 Driver %0d Statistics: Total=%0d, Writes=%0d, Reads=%0d",
                        m2_driver_id, m2_total_transactions, m2_write_transactions, m2_read_transactions);
    endfunction
    
    // Reset driver statistics
    virtual function void reset_driver_statistics();
        m2_total_transactions = 0;
        m2_write_transactions = 0;
        m2_read_transactions = 0;
        `uvm_info("M2_DRIVER", $sformatf("M2 Driver %0d statistics reset", m2_driver_id), UVM_LOW)
    endfunction
    
    // UVM Field Macros
    `uvm_component_utils_begin(M2_driver)
        `uvm_field_int(m2_driver_id, UVM_ALL_ON)
        `uvm_field_string(m2_driver_name, UVM_ALL_ON)
        `uvm_field_int(m2_total_transactions, UVM_ALL_ON)
        `uvm_field_int(m2_write_transactions, UVM_ALL_ON)
        `uvm_field_int(m2_read_transactions, UVM_ALL_ON)
        `uvm_field_int(m2_driver_enabled, UVM_ALL_ON)
    `uvm_component_utils_end
    
endclass : M2_driver

`endif // M2_DRIVER_SV
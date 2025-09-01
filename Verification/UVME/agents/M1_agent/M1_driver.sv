//=============================================================================
// M1 Agent Driver Class
//=============================================================================
// Basic driver for Master 1 that handles write and read sequences
// Extends uvm_driver to drive M1 sequence items
// Uses M1_interface.driver modport with synchronized clocking block access

`ifndef M1_DRIVER_SV
`define M1_DRIVER_SV

// Note: All imports and includes will be handled by define_files_package

class M1_driver extends uvm_driver #(M1_seq_item);
    
    // Virtual interface for M1 AXI signals using driver modport
    virtual M1_interface.driver m1_vif;
    
    //M1_seq_item
    M1_seq_item req;
    
    // Driver configuration
    int unsigned m1_driver_id;
    string m1_driver_name;
    
    // Driver statistics
    int unsigned m1_total_transactions;
    int unsigned m1_write_transactions;
    int unsigned m1_read_transactions;
    
    // Driver control
    bit m1_driver_enabled;

    int unsigned burst_length;
    
    // Constructor
    function new(string name = "M1_driver", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize driver
        m1_driver_id = 0;
        m1_driver_name = name;
        
        // Initialize statistics
        m1_total_transactions = 0;
        m1_write_transactions = 0;
        m1_read_transactions = 0;
        
        // Initialize control
        m1_driver_enabled = 1;
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual M1_interface.driver)::get(this, "", "m1_vif", m1_vif)) begin
            `uvm_fatal("M1_DRIVER", "Virtual interface not found for M1 driver")
        end
    endfunction
    
    // Run phase - main driver loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("M1_DRIVER", $sformatf("M1 Driver %0d starting run phase", m1_driver_id), UVM_LOW)
        
        // Main driver loop
        forever begin
            // Get sequence item from sequencer
            seq_item_port.get_next_item(req);
            
            // Process the transaction
            if (m1_driver_enabled) begin
                drive_transaction(req);
            end
            
            // Signal completion
            seq_item_port.item_done();
        end
    endtask
    
    // Drive transaction based on type
    virtual task drive_transaction(M1_seq_item item);
        `uvm_info("M1_DRIVER", $sformatf("M1 Driver %0d driving transaction: Type=%s, Slave=%0d, ID=%0d", 
                                        m1_driver_id, item.trans_type.name(), item.slave_id, item.M1_AWID), UVM_LOW)
        
        case (item.trans_type)
            AXI_WRITE: drive_write_transaction(item);
            AXI_READ:  drive_read_transaction(item);
            default:   `uvm_error("M1_DRIVER", $sformatf("Unknown transaction type: %s", item.trans_type.name()))
        endcase
        
        // Update statistics
        update_driver_statistics(item);
    endtask
    
    // Drive write transaction
    virtual task drive_write_transaction(M1_seq_item item);
        `uvm_info("M1_DRIVER", $sformatf("M1 Driver %0d driving WRITE transaction to Slave %0d", 
                                        m1_driver_id, item.slave_id), UVM_LOW)
        
        // Phase 1: Write Address Channel (AW)
        drive_write_address_phase(item);
        
        // Phase 2: Write Data Channel (W)
        drive_write_data_phase(item);
        
        // Phase 3: Write Response Channel (B)
        drive_write_response_phase(item);
        
        `uvm_info("M1_DRIVER", $sformatf("M1 Driver %0d WRITE transaction completed", m1_driver_id), UVM_LOW)
    endtask
    
    // Drive read transaction
    virtual task drive_read_transaction(M1_seq_item item);
        `uvm_info("M1_DRIVER", $sformatf("M1 Driver %0d driving READ transaction from Slave %0d", 
                                        m1_driver_id, item.slave_id), UVM_LOW)
        
        // Phase 1: Read Address Channel (AR)
        drive_read_address_phase(item);
        
        // Phase 2: Read Data Channel (R)
        drive_read_data_phase(item);
        
        `uvm_info("M1_DRIVER", $sformatf("M1 Driver %0d READ transaction completed", m1_driver_id), UVM_LOW)
    endtask
    
    // Drive write address phase using clocking block
    virtual task drive_write_address_phase(M1_seq_item item);
        `uvm_info("M1_DRIVER", "Driving Write Address Phase", UVM_FULL)
        
         repeat (4) @(posedge m1_vif.ACLK);  // 4-clock delay before starting
           
        // Set address channel signals through clocking block for synchronization
        m1_vif.m1_cb.M1_AWID <= item.M1_AWID;
        m1_vif.m1_cb.M1_AWADDR <= item.M1_AWADDR;
        m1_vif.m1_cb.M1_AWLEN <= item.M1_AWLEN;
        m1_vif.m1_cb.M1_AWSIZE <= item.M1_AWSIZE;
        m1_vif.m1_cb.M1_AWBURST <= item.M1_AWBURST;
        m1_vif.m1_cb.M1_AWLOCK <= item.M1_AWLOCK;
        m1_vif.m1_cb.M1_AWCACHE <= item.M1_AWCACHE;
        m1_vif.m1_cb.M1_AWPROT <= item.M1_AWPROT;
        m1_vif.m1_cb.M1_AWQOS <= item.M1_AWQOS;
        m1_vif.m1_cb.M1_AWREGION <= item.M1_AWREGION;
        m1_vif.m1_cb.M1_AWVALID <= 1'b1;
        
        // Wait for slave ready using clocking block
        @(posedge m1_vif.ACLK);
        while (!m1_vif.m1_cb.M1_AWREADY) begin
            @(posedge m1_vif.ACLK);
        end
        
        // Clear valid signal through clocking block
        m1_vif.m1_cb.M1_AWVALID <= 1'b0;
        @(posedge m1_vif.ACLK);
    endtask
    
    // Drive write data phase using clocking block
    virtual task drive_write_data_phase(M1_seq_item item);
        `uvm_info("M1_DRIVER", "Driving Write Data Phase", UVM_FULL)
        
        burst_length = get_burst_length(item.M1_AWLEN);
        
        for (int i = 0; i < burst_length; i++) begin
            // Set data channel signals through clocking block
            m1_vif.m1_cb.M1_WDATA <= item.burst_data[i];
            m1_vif.m1_cb.M1_WSTRB <= item.burst_strobe[i];
            m1_vif.m1_cb.M1_WLAST <= (i == burst_length - 1) ? 1'b1 : 1'b0;
            m1_vif.m1_cb.M1_WVALID <= 1'b1;
            
            // Wait for slave ready using clocking block
            @(posedge m1_vif.ACLK);
            while (!m1_vif.m1_cb.M1_WREADY) begin
                @(posedge m1_vif.ACLK);
            end
            
            // Clear valid signal through clocking block
            m1_vif.m1_cb.M1_WVALID <= 1'b0;
            @(posedge m1_vif.ACLK);
        end
    endtask
    
    // Drive write response phase using clocking block
    virtual task drive_write_response_phase(M1_seq_item item);
        `uvm_info("M1_DRIVER", "Driving Write Response Phase", UVM_FULL)
         repeat (2) @(posedge m1_vif.ACLK);  // 2-clock delay before starting
           
        // Set response ready through clocking block
        m1_vif.m1_cb.M1_BREADY <= 1'b1;
        
        // Wait for response valid using clocking block
        @(posedge m1_vif.ACLK);
        while (!m1_vif.m1_cb.M1_BVALID) begin
            @(posedge m1_vif.ACLK);
        end
        
        // Capture response from clocking block
        item.M1_BID = m1_vif.m1_cb.M1_BID;
        item.M1_BRESP = m1_vif.m1_cb.M1_BRESP;
        
        // Clear ready signal through clocking block
        m1_vif.m1_cb.M1_BREADY <= 1'b0;
        @(posedge m1_vif.ACLK);
    endtask
    
    // Drive read address phase using clocking block
    virtual task drive_read_address_phase(M1_seq_item item);
        `uvm_info("M1_DRIVER", "Driving Read Address Phase", UVM_FULL)
 repeat (4) @(posedge m1_vif.ACLK);  // 4-clock delay before starting
           
        // Set address channel signals through clocking block
        m1_vif.m1_cb.M1_ARID <= item.M1_ARID;
        m1_vif.m1_cb.M1_ARADDR <= item.M1_ARADDR;
        m1_vif.m1_cb.M1_ARLEN <= item.M1_ARLEN;
        m1_vif.m1_cb.M1_ARSIZE <= item.M1_ARSIZE;
        m1_vif.m1_cb.M1_ARBURST <= item.M1_ARBURST;
        m1_vif.m1_cb.M1_ARLOCK <= item.M1_ARLOCK;
        m1_vif.m1_cb.M1_ARCACHE <= item.M1_ARCACHE;
        m1_vif.m1_cb.M1_ARPROT <= item.M1_ARPROT;
        m1_vif.m1_cb.M1_ARQOS <= item.M1_ARQOS;
        m1_vif.m1_cb.M1_ARREGION <= item.M1_ARREGION;
        m1_vif.m1_cb.M1_ARVALID <= 1'b1;
        
        // Wait for slave ready using clocking block
        @(posedge m1_vif.ACLK);
        while (!m1_vif.m1_cb.M1_ARREADY) begin
            @(posedge m1_vif.ACLK);
        end
        
        // Clear valid signal through clocking block
        m1_vif.m1_cb.M1_ARVALID <= 1'b0;
        @(posedge m1_vif.ACLK);
    endtask
    
    // Drive read data phase using clocking block
    virtual task drive_read_data_phase(M1_seq_item item);
        `uvm_info("M1_DRIVER", "Driving Read Data Phase", UVM_FULL)
        repeat (4) @(posedge m1_vif.ACLK);  // 4-clock delay before starting
        burst_length = get_burst_length(item.M1_ARLEN);
        
        for (int i = 0; i < burst_length; i++) begin
            // Set read ready through clocking block
            m1_vif.m1_cb.M1_RREADY <= 1'b1;
            
            // Wait for data valid using clocking block
            @(posedge m1_vif.ACLK);
            while (!m1_vif.m1_cb.M1_RVALID) begin
                @(posedge m1_vif.ACLK);
            end
            
            // Capture data from clocking block
            item.M1_RID = m1_vif.m1_cb.M1_RID;
            item.M1_RDATA = m1_vif.m1_cb.M1_RDATA;
            item.M1_RRESP = m1_vif.m1_cb.M1_RRESP;
            item.M1_RLAST = m1_vif.m1_cb.M1_RLAST;
            
            // Store in burst data array
            item.burst_data[i] = m1_vif.m1_cb.M1_RDATA;
            
            // Clear ready signal through clocking block
            m1_vif.m1_cb.M1_RREADY <= 1'b0;
            @(posedge m1_vif.ACLK);
        end
    endtask
    
    // Update driver statistics
    virtual function void update_driver_statistics(M1_seq_item item);
        m1_total_transactions++;
        
        if (item.trans_type == AXI_WRITE) begin
            m1_write_transactions++;
        end else begin
            m1_read_transactions++;
        end
        
        `uvm_info("M1_DRIVER", $sformatf("M1 Driver %0d stats: Total=%0d, W=%0d, R=%0d", 
                                        m1_driver_id, m1_total_transactions, 
                                        m1_write_transactions, m1_read_transactions), UVM_FULL)
    endfunction
    
    // Driver control methods
    
    // Enable driver
    virtual function void enable_driver();
        m1_driver_enabled = 1;
        `uvm_info("M1_DRIVER", $sformatf("M1 Driver %0d enabled", m1_driver_id), UVM_LOW)
    endfunction
    
    // Disable driver
    virtual function void disable_driver();
        m1_driver_enabled = 0;
        `uvm_info("M1_DRIVER", $sformatf("M1 Driver %0d disabled", m1_driver_id), UVM_LOW)
    endfunction
    
    // Check if driver is enabled
    virtual function bit is_driver_enabled();
        return m1_driver_enabled;
    endfunction
    
    // Get driver statistics
    virtual function string get_driver_statistics();
        return $sformatf("M1 Driver %0d Statistics: Total=%0d, Writes=%0d, Reads=%0d",
                        m1_driver_id, m1_total_transactions, m1_write_transactions, m1_read_transactions);
    endfunction
    
    // Reset driver statistics
    virtual function void reset_driver_statistics();
        m1_total_transactions = 0;
        m1_write_transactions = 0;
        m1_read_transactions = 0;
        `uvm_info("M1_DRIVER", $sformatf("M1 Driver %0d statistics reset", m1_driver_id), UVM_LOW)
    endfunction
    
    // UVM Field Macros
    `uvm_component_utils_begin(M1_driver)
        `uvm_field_int(m1_driver_id, UVM_ALL_ON)
        `uvm_field_string(m1_driver_name, UVM_ALL_ON)
        `uvm_field_int(m1_total_transactions, UVM_ALL_ON)
        `uvm_field_int(m1_write_transactions, UVM_ALL_ON)
        `uvm_field_int(m1_read_transactions, UVM_ALL_ON)
        `uvm_field_int(m1_driver_enabled, UVM_ALL_ON)
    `uvm_component_utils_end
    
endclass : M1_driver

`endif // M1_DRIVER_SV
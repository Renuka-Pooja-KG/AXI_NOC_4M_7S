//=============================================================================
// S3 Agent Monitor Class
//=============================================================================
// Simple passive monitor for Slave 3 that observes AXI transactions
// Uses S3_interface.monitor modport for synchronized signal sampling
// Only handles transaction observation and broadcasting - no coverage or protocol checking

`ifndef S3_MONITOR_SV
`define S3_MONITOR_SV

// Note: All imports and includes will be handled by define_files_package

class S3_monitor extends uvm_monitor;
    
    // Virtual interface for S3 AXI signals using monitor modport
    virtual S3_interface.monitor s3_vif;
    
    // Analysis port for transaction broadcasting
    uvm_analysis_port #(S3_seq_item) item_collect_port;
    
    // Single transaction item for reuse
    S3_seq_item mon_item;
    
    // UVM Factory registration
    `uvm_component_utils(S3_monitor)
    
    // Constructor
    function new(string name = "S3_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collect_port = new("item_collect_port", this);
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S3_interface)::get(this, "", "s3_vif", s3_vif)) begin
            `uvm_fatal("S3_MONITOR", "Virtual interface not found for S3 monitor")
        end
        
        // Create transaction item
        mon_item = S3_seq_item::type_id::create("mon_item");
    endfunction
    
    // Run phase - main monitoring loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S3_MONITOR", "S3 Monitor starting run phase", UVM_LOW)
        
        // Main monitoring loop
        collect_data();
    endtask
    
    // Simple data collection task - monitors all AXI channels
    virtual task collect_data();
        forever begin
            // Wait for clock edge
            @(posedge s3_vif.ACLK);
            
            // Collecting the address channel data
            mon_item.S3_AWVALID = s3_vif.s3_monitor_cb.S3_AWVALID;
            mon_item.S3_WVALID = s3_vif.s3_monitor_cb.S3_WVALID;
            
            // Check for write address handshake
            if (s3_vif.s3_monitor_cb.S3_AWVALID && s3_vif.s3_monitor_cb.S3_AWREADY) begin
                // Capture write address signals
                mon_item.S3_AWID = s3_vif.s3_monitor_cb.S3_AWID;
                mon_item.S3_AWREADY = s3_vif.s3_monitor_cb.S3_AWREADY;
                mon_item.S3_AWADDR = s3_vif.s3_monitor_cb.S3_AWADDR;
                mon_item.S3_AWLEN = s3_vif.s3_monitor_cb.S3_AWLEN;
                mon_item.S3_AWLOCK = s3_vif.s3_monitor_cb.S3_AWLOCK;
                mon_item.S3_AWSIZE = s3_vif.s3_monitor_cb.S3_AWSIZE;
                mon_item.S3_AWBURST = s3_vif.s3_monitor_cb.S3_AWBURST;
                mon_item.S3_AWCACHE = s3_vif.s3_monitor_cb.S3_AWCACHE;
                mon_item.S3_AWPROT = s3_vif.s3_monitor_cb.S3_AWPROT;
                mon_item.S3_AWQOS = s3_vif.s3_monitor_cb.S3_AWQOS;
                mon_item.S3_AWREGION = s3_vif.s3_monitor_cb.S3_AWREGION;
                
                // Log write address transaction
                `uvm_info("S3_MONITOR", $sformatf("Time: %0t, S3_AWVALID: %0b, S3_AWREADY: %0b, S3_AWID: 0x%0h, S3_AWADDR: 0x%0h, S3_AWLEN: %0d, S3_AWSIZE: %0d, S3_AWBURST: %0d, S3_AWLOCK: %0b, S3_AWCACHE: 0x%0h, S3_AWPROT: 0x%0h, S3_AWQOS: 0x%0h, S3_AWREGION: 0x%0h", 
                            $realtime, mon_item.S3_AWVALID, mon_item.S3_AWREADY, mon_item.S3_AWID, mon_item.S3_AWADDR, 
                            mon_item.S3_AWLEN, mon_item.S3_AWSIZE, mon_item.S3_AWBURST, mon_item.S3_AWLOCK, 
                            mon_item.S3_AWCACHE, mon_item.S3_AWPROT, mon_item.S3_AWQOS, mon_item.S3_AWREGION), UVM_LOW)
            end
            
            // Check for write data handshake
            if (s3_vif.s3_monitor_cb.S3_WVALID && s3_vif.s3_monitor_cb.S3_WREADY) begin
                // Capture write data signals
                mon_item.S3_WREADY = s3_vif.s3_monitor_cb.S3_WREADY;
                mon_item.S3_WDATA = s3_vif.s3_monitor_cb.S3_WDATA;
                mon_item.S3_WSTRB = s3_vif.s3_monitor_cb.S3_WSTRB;
                mon_item.S3_WLAST = s3_vif.s3_monitor_cb.S3_WLAST;
                
                // Log write data transaction
                `uvm_info("S3_MONITOR", $sformatf("Time: %0t, S3_WVALID: %0b, S3_WREADY: %0b, S3_WDATA: 0x%0h, S3_WSTRB: 0x%0h, S3_WLAST: %0b", 
                            $realtime, mon_item.S3_WVALID, mon_item.S3_WREADY, mon_item.S3_WDATA, 
                            mon_item.S3_WSTRB, mon_item.S3_WLAST), UVM_LOW)
            end
            
            // Check for write response handshake
            if (s3_vif.s3_monitor_cb.S3_BVALID && s3_vif.s3_monitor_cb.S3_BREADY) begin
                // Capture write response signals
                mon_item.S3_BID = s3_vif.s3_monitor_cb.S3_BID;
                mon_item.S3_BVALID = s3_vif.s3_monitor_cb.S3_BVALID;
                mon_item.S3_BREADY = s3_vif.s3_monitor_cb.S3_BREADY;
                mon_item.S3_BRESP = s3_vif.s3_monitor_cb.S3_BRESP;
                
                // Log write response transaction
                `uvm_info("S3_MONITOR", $sformatf("Time: %0t, S3_BVALID: %0b, S3_BREADY: %0b, S3_BID: 0x%0h, S3_BRESP: %0d", 
                            $realtime, mon_item.S3_BVALID, mon_item.S3_BREADY, mon_item.S3_BID, 
                            mon_item.S3_BRESP), UVM_LOW)
            end
            
            // Check for read address handshake
            if (s3_vif.s3_monitor_cb.S3_ARVALID && s3_vif.s3_monitor_cb.S3_ARREADY) begin
                // Capture read address signals
                mon_item.S3_ARID = s3_vif.s3_monitor_cb.S3_ARID;
                mon_item.S3_ARVALID = s3_vif.s3_monitor_cb.S3_ARVALID;
                mon_item.S3_ARREADY = s3_vif.s3_monitor_cb.S3_ARREADY;
                mon_item.S3_ARADDR = s3_vif.s3_monitor_cb.S3_ARADDR;
                mon_item.S3_ARLEN = s3_vif.s3_monitor_cb.S3_ARLEN;
                mon_item.S3_ARLOCK = s3_vif.s3_monitor_cb.S3_ARLOCK;
                mon_item.S3_ARSIZE = s3_vif.s3_monitor_cb.S3_ARSIZE;
                mon_item.S3_ARBURST = s3_vif.s3_monitor_cb.S3_ARBURST;
                mon_item.S3_ARCACHE = s3_vif.s3_monitor_cb.S3_ARCACHE;
                mon_item.S3_ARPROT = s3_vif.s3_monitor_cb.S3_ARPROT;
                mon_item.S3_ARQOS = s3_vif.s3_monitor_cb.S3_ARQOS;
                mon_item.S3_ARREGION = s3_vif.s3_monitor_cb.S3_ARREGION;
                
                // Log read address transaction
                `uvm_info("S3_MONITOR", $sformatf("Time: %0t, S3_ARVALID: %0b, S3_ARREADY: %0b, S3_ARID: 0x%0h, S3_ARADDR: 0x%0h, S3_ARLEN: %0d, S3_ARSIZE: %0d, S3_ARBURST: %0d, S3_ARLOCK: %0b, S3_ARCACHE: 0x%0h, S3_ARPROT: 0x%0h, S3_ARQOS: 0x%0h, S3_ARREGION: 0x%0h", 
                            $realtime, mon_item.S3_ARVALID, mon_item.S3_ARREADY, mon_item.S3_ARID, mon_item.S3_ARADDR, 
                            mon_item.S3_ARLEN, mon_item.S3_ARSIZE, mon_item.S3_ARBURST, mon_item.S3_ARLOCK, 
                            mon_item.S3_ARCACHE, mon_item.S3_ARPROT, mon_item.S3_ARQOS, mon_item.S3_ARREGION), UVM_LOW)
            end
            
            // Check for read data handshake
            if (s3_vif.s3_monitor_cb.S3_RVALID && s3_vif.s3_monitor_cb.S3_RREADY) begin
                // Capture read data signals
                mon_item.S3_RID = s3_vif.s3_monitor_cb.S3_RID;
                mon_item.S3_RVALID = s3_vif.s3_monitor_cb.S3_RVALID;
                mon_item.S3_RREADY = s3_vif.s3_monitor_cb.S3_RREADY;
                mon_item.S3_RDATA = s3_vif.s3_monitor_cb.S3_RDATA;
                mon_item.S3_RRESP = s3_vif.s3_monitor_cb.S3_RRESP;
                mon_item.S3_RLAST = s3_vif.s3_monitor_cb.S3_RLAST;
                
                // Log read data transaction
                `uvm_info("S3_MONITOR", $sformatf("Time: %0t, S3_RVALID: %0b, S3_RREADY: %0b, S3_RID: 0x%0h, S3_RDATA: 0x%0h, S3_RRESP: %0d, S3_RLAST: %0b", 
                            $realtime, mon_item.S3_RVALID, mon_item.S3_RREADY, mon_item.S3_RID, mon_item.S3_RDATA, 
                            mon_item.S3_RRESP, mon_item.S3_RLAST), UVM_LOW)
            end
            
            // End of monitor
            `uvm_info("S3_MONITOR", "End of Monitor", UVM_MEDIUM)
            
            // Broadcast the collected transaction
            item_collect_port.write(mon_item);
        end
    endtask
    
endclass : S3_monitor

`endif // S3_MONITOR_SV

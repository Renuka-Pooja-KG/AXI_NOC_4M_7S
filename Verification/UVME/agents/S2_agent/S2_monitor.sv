//=============================================================================
// S2 Agent Monitor Class
//=============================================================================
// Simple passive monitor for Slave 2 that observes AXI transactions
// Uses S2_interface.monitor modport for synchronized signal sampling
// Only handles transaction observation and broadcasting - no coverage or protocol checking

`ifndef S2_MONITOR_SV
`define S2_MONITOR_SV

// Note: All imports and includes will be handled by define_files_package

class S2_monitor extends uvm_monitor;
    
    // Virtual interface for S2 AXI signals using monitor modport
    virtual S2_interface.monitor s2_vif;
    
    // Analysis port for transaction broadcasting
    uvm_analysis_port #(S2_seq_item) item_collect_port;
    
    // Single transaction item for reuse
    S2_seq_item mon_item;
    
    // UVM Factory registration
    `uvm_component_utils(S2_monitor)
    
    // Constructor
    function new(string name = "S2_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collect_port = new("item_collect_port", this);
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S2_interface.monitor)::get(this, "", "s2_vif", s2_vif)) begin
            `uvm_fatal("S2_MONITOR", "Virtual interface not found for S2 monitor")
        end
        
        // Create transaction item
        mon_item = S2_seq_item::type_id::create("mon_item");
    endfunction
    
    // Run phase - main monitoring loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S2_MONITOR", "S2 Monitor starting run phase", UVM_LOW)
        
        // Main monitoring loop
        collect_data();
    endtask
    
    // Simple data collection task - monitors all AXI channels
    virtual task collect_data();
        forever begin
            // Wait for clock edge
            @(posedge s2_vif.ACLK);
            
            // Collecting the address channel data
            mon_item.S2_AWVALID = s2_vif.s2_monitor_cb.S2_AWVALID;
            mon_item.S2_WVALID = s2_vif.s2_monitor_cb.S2_WVALID;
            
            // Check for write address handshake
            if (s2_vif.s2_monitor_cb.S2_AWVALID && s2_vif.s2_monitor_cb.S2_AWREADY) begin
                // Capture write address signals
                mon_item.S2_AWID = s2_vif.s2_monitor_cb.S2_AWID;
                mon_item.S2_AWREADY = s2_vif.s2_monitor_cb.S2_AWREADY;
                mon_item.S2_AWADDR = s2_vif.s2_monitor_cb.S2_AWADDR;
                mon_item.S2_AWLEN = s2_vif.s2_monitor_cb.S2_AWLEN;
                mon_item.S2_AWLOCK = s2_vif.s2_monitor_cb.S2_AWLOCK;
                mon_item.S2_AWSIZE = s2_vif.s2_monitor_cb.S2_AWSIZE;
                mon_item.S2_AWBURST = s2_vif.s2_monitor_cb.S2_AWBURST;
                mon_item.S2_AWCACHE = s2_vif.s2_monitor_cb.S2_AWCACHE;
                mon_item.S2_AWPROT = s2_vif.s2_monitor_cb.S2_AWPROT;
                mon_item.S2_AWQOS = s2_vif.s2_monitor_cb.S2_AWQOS;
                mon_item.S2_AWREGION = s2_vif.s2_monitor_cb.S2_AWREGION;
                mon_item.S2_AWUSER = s2_vif.s2_monitor_cb.S2_AWUSER;
                
                // Log write address transaction
                `uvm_info("S2_MONITOR", $sformatf("Time: %0t, S2_AWVALID: %0b, S2_AWREADY: %0b, S2_AWID: 0x%0h, S2_AWADDR: 0x%0h, S2_AWLEN: %0d, S2_AWSIZE: %0d, S2_AWBURST: %0d, S2_AWLOCK: %0b, S2_AWCACHE: 0x%0h, S2_AWPROT: 0x%0h, S2_AWQOS: 0x%0h, S2_AWREGION: 0x%0h, S2_AWUSER: 0x%0h", 
                            $realtime, mon_item.S2_AWVALID, mon_item.S2_AWREADY, mon_item.S2_AWID, mon_item.S2_AWADDR, 
                            mon_item.S2_AWLEN, mon_item.S2_AWSIZE, mon_item.S2_AWBURST, mon_item.S2_AWLOCK, 
                            mon_item.S2_AWCACHE, mon_item.S2_AWPROT, mon_item.S2_AWQOS, mon_item.S2_AWREGION, mon_item.S2_AWUSER), UVM_LOW)
            end
            
            // Check for write data handshake
            if (s2_vif.s2_monitor_cb.S2_WVALID && s2_vif.s2_monitor_cb.S2_WREADY) begin
                // Capture write data signals
                mon_item.S2_WREADY = s2_vif.s2_monitor_cb.S2_WREADY;
                mon_item.S2_WDATA = s2_vif.s2_monitor_cb.S2_WDATA;
                mon_item.S2_WSTRB = s2_vif.s2_monitor_cb.S2_WSTRB;
                mon_item.S2_WLAST = s2_vif.s2_monitor_cb.S2_WLAST;
                mon_item.S2_WUSER = s2_vif.s2_monitor_cb.S2_WUSER;
                
                // Log write data transaction
                `uvm_info("S2_MONITOR", $sformatf("Time: %0t, S2_WVALID: %0b, S2_WREADY: %0b, S2_WDATA: 0x%0h, S2_WSTRB: 0x%0h, S2_WLAST: %0b, S2_WUSER: 0x%0h", 
                            $realtime, mon_item.S2_WVALID, mon_item.S2_WREADY, mon_item.S2_WDATA, 
                            mon_item.S2_WSTRB, mon_item.S2_WLAST, mon_item.S2_WUSER), UVM_LOW)
            end
            
            // Check for write response handshake
            if (s2_vif.s2_monitor_cb.S2_BVALID && s2_vif.s2_monitor_cb.S2_BREADY) begin
                // Capture write response signals
                mon_item.S2_BID = s2_vif.s2_monitor_cb.S2_BID;
                mon_item.S2_BVALID = s2_vif.s2_monitor_cb.S2_BVALID;
                mon_item.S2_BREADY = s2_vif.s2_monitor_cb.S2_BREADY;
                mon_item.S2_BRESP = s2_vif.s2_monitor_cb.S2_BRESP;
                mon_item.S2_BUSER = s2_vif.s2_monitor_cb.S2_BUSER;
                
                // Log write response transaction
                `uvm_info("S2_MONITOR", $sformatf("Time: %0t, S2_BVALID: %0b, S2_BREADY: %0b, S2_BID: 0x%0h, S2_BRESP: %0d, S2_BUSER: 0x%0h", 
                            $realtime, mon_item.S2_BVALID, mon_item.S2_BREADY, mon_item.S2_BID, 
                            mon_item.S2_BRESP, mon_item.S2_BUSER), UVM_LOW)
            end
            
            // Check for read address handshake
            if (s2_vif.s2_monitor_cb.S2_ARVALID && s2_vif.s2_monitor_cb.S2_ARREADY) begin
                // Capture read address signals
                mon_item.S2_ARID = s2_vif.s2_monitor_cb.S2_ARID;
                mon_item.S2_ARVALID = s2_vif.s2_monitor_cb.S2_ARVALID;
                mon_item.S2_ARREADY = s2_vif.s2_monitor_cb.S2_ARREADY;
                mon_item.S2_ARADDR = s2_vif.s2_monitor_cb.S2_ARADDR;
                mon_item.S2_ARLEN = s2_vif.s2_monitor_cb.S2_ARLEN;
                mon_item.S2_ARLOCK = s2_vif.s2_monitor_cb.S2_ARLOCK;
                mon_item.S2_ARSIZE = s2_vif.s2_monitor_cb.S2_ARSIZE;
                mon_item.S2_ARBURST = s2_vif.s2_monitor_cb.S2_ARBURST;
                mon_item.S2_ARCACHE = s2_vif.s2_monitor_cb.S2_ARCACHE;
                mon_item.S2_ARPROT = s2_vif.s2_monitor_cb.S2_ARPROT;
                mon_item.S2_ARQOS = s2_vif.s2_monitor_cb.S2_ARQOS;
                mon_item.S2_ARREGION = s2_vif.s2_monitor_cb.S2_ARREGION;
                mon_item.S2_ARUSER = s2_vif.s2_monitor_cb.S2_ARUSER;
                
                // Log read address transaction
                `uvm_info("S2_MONITOR", $sformatf("Time: %0t, S2_ARVALID: %0b, S2_ARREADY: %0b, S2_ARID: 0x%0h, S2_ARADDR: 0x%0h, S2_ARLEN: %0d, S2_ARSIZE: %0d, S2_ARBURST: %0d, S2_ARLOCK: %0b, S2_ARCACHE: 0x%0h, S2_ARPROT: 0x%0h, S2_ARQOS: 0x%0h, S2_ARREGION: 0x%0h, S2_ARUSER: 0x%0h", 
                            $realtime, mon_item.S2_ARVALID, mon_item.S2_ARREADY, mon_item.S2_ARID, mon_item.S2_ARADDR, 
                            mon_item.S2_ARLEN, mon_item.S2_ARSIZE, mon_item.S2_ARBURST, mon_item.S2_ARLOCK, 
                            mon_item.S2_ARCACHE, mon_item.S2_ARPROT, mon_item.S2_ARQOS, mon_item.S2_ARREGION, mon_item.S2_ARUSER), UVM_LOW)
            end
            
            // Check for read data handshake
            if (s2_vif.s2_monitor_cb.S2_RVALID && s2_vif.s2_monitor_cb.S2_RREADY) begin
                // Capture read data signals
                mon_item.S2_RID = s2_vif.s2_monitor_cb.S2_RID;
                mon_item.S2_RVALID = s2_vif.s2_monitor_cb.S2_RVALID;
                mon_item.S2_RREADY = s2_vif.s2_monitor_cb.S2_RREADY;
                mon_item.S2_RDATA = s2_vif.s2_monitor_cb.S2_RDATA;
                mon_item.S2_RRESP = s2_vif.s2_monitor_cb.S2_RRESP;
                mon_item.S2_RLAST = s2_vif.s2_monitor_cb.S2_RLAST;
                mon_item.S2_RUSER = s2_vif.s2_monitor_cb.S2_RUSER;
                
                // Log read data transaction
                `uvm_info("S2_MONITOR", $sformatf("Time: %0t, S2_RVALID: %0b, S2_RREADY: %0b, S2_RID: 0x%0h, S2_RDATA: 0x%0h, S2_RRESP: %0d, S2_RLAST: %0b, S2_RUSER: 0x%0h", 
                            $realtime, mon_item.S2_RVALID, mon_item.S2_RREADY, mon_item.S2_RID, mon_item.S2_RDATA, 
                            mon_item.S2_RRESP, mon_item.S2_RLAST, mon_item.S2_RUSER), UVM_LOW)
            end
            
            // End of monitor
            `uvm_info("S2_MONITOR", "End of Monitor", UVM_MEDIUM)
            
            // Broadcast the collected transaction
            item_collect_port.write(mon_item);
        end
    endtask
    
endclass : S2_monitor

`endif // S2_MONITOR_SV

//=============================================================================
// S6 Agent Monitor Class
//=============================================================================
// Simple passive monitor for Slave 6 that observes AXI transactions
// Uses S6_interface.monitor modport for synchronized signal sampling
// Only handles transaction observation and broadcasting - no coverage or protocol checking

`ifndef S6_MONITOR_SV
`define S6_MONITOR_SV

// Note: All imports and includes will be handled by define_files_package

class S6_monitor extends uvm_monitor;
    
    // Virtual interface for S6 AXI signals using monitor modport
    virtual S6_interface.monitor s6_vif;
    
    // Analysis port for transaction broadcasting
    uvm_analysis_port #(S6_seq_item) item_collect_port;
    
    // Single transaction item for reuse
    S6_seq_item mon_item;
    
    // UVM Factory registration
    `uvm_component_utils(S6_monitor)
    
    // Constructor
    function new(string name = "S6_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collect_port = new("item_collect_port", this);
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S6_interface.monitor)::get(this, "", "s6_vif", s6_vif)) begin
            `uvm_fatal("S6_MONITOR", "Virtual interface not found for S6 monitor")
        end
        
        // Create transaction item
        mon_item = S6_seq_item::type_id::create("mon_item");
    endfunction
    
    // Run phase - main monitoring loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S6_MONITOR", "S6 Monitor starting run phase", UVM_LOW)
        
        // Main monitoring loop
        collect_data();
    endtask
    
    // Simple data collection task - monitors all AXI channels
    virtual task collect_data();
        forever begin
            // Wait for clock edge
            @(posedge s6_vif.ACLK);
            
            // Collecting the address channel data
            mon_item.S6_AWVALID = s6_vif.s6_monitor_cb.S6_AWVALID;
            mon_item.S6_WVALID = s6_vif.s6_monitor_cb.S6_WVALID;
            
            // Check for write address handshake
            if (s6_vif.s6_monitor_cb.S6_AWVALID && s6_vif.s6_monitor_cb.S6_AWREADY) begin
                // Capture write address signals
                mon_item.S6_AWID = s6_vif.s6_monitor_cb.S6_AWID;
                mon_item.S6_AWREADY = s6_vif.s6_monitor_cb.S6_AWREADY;
                mon_item.S6_AWADDR = s6_vif.s6_monitor_cb.S6_AWADDR;
                mon_item.S6_AWLEN = s6_vif.s6_monitor_cb.S6_AWLEN;
                mon_item.S6_AWLOCK = s6_vif.s6_monitor_cb.S6_AWLOCK;
                mon_item.S6_AWSIZE = s6_vif.s6_monitor_cb.S6_AWSIZE;
                mon_item.S6_AWBURST = s6_vif.s6_monitor_cb.S6_AWBURST;
                mon_item.S6_AWCACHE = s6_vif.s6_monitor_cb.S6_AWCACHE;
                mon_item.S6_AWPROT = s6_vif.s6_monitor_cb.S6_AWPROT;
                mon_item.S6_AWQOS = s6_vif.s6_monitor_cb.S6_AWQOS;
                mon_item.S6_AWREGION = s6_vif.s6_monitor_cb.S6_AWREGION;
                
                // Log write address transaction
                `uvm_info("S6_MONITOR", $sformatf("Time: %0t, S6_AWVALID: %0b, S6_AWREADY: %0b, S6_AWID: 0x%0h, S6_AWADDR: 0x%0h, S6_AWLEN: %0d, S6_AWSIZE: %0d, S6_AWBURST: %0d, S6_AWLOCK: %0b, S6_AWCACHE: 0x%0h, S6_AWPROT: 0x%0h, S6_AWQOS: 0x%0h, S6_AWREGION: 0x%0h", 
                            $realtime, mon_item.S6_AWVALID, mon_item.S6_AWREADY, mon_item.S6_AWID, mon_item.S6_AWADDR, 
                            mon_item.S6_AWLEN, mon_item.S6_AWSIZE, mon_item.S6_AWBURST, mon_item.S6_AWLOCK, 
                            mon_item.S6_AWCACHE, mon_item.S6_AWPROT, mon_item.S6_AWQOS, mon_item.S6_AWREGION), UVM_LOW)
            end
            
            // Check for write data handshake
            if (s6_vif.s6_monitor_cb.S6_WVALID && s6_vif.s6_monitor_cb.S6_WREADY) begin
                // Capture write data signals
                mon_item.S6_WREADY = s6_vif.s6_monitor_cb.S6_WREADY;
                mon_item.S6_WDATA = s6_vif.s6_monitor_cb.S6_WDATA;
                mon_item.S6_WSTRB = s6_vif.s6_monitor_cb.S6_WSTRB;
                mon_item.S6_WLAST = s6_vif.s6_monitor_cb.S6_WLAST;
                
                // Log write data transaction
                `uvm_info("S6_MONITOR", $sformatf("Time: %0t, S6_WVALID: %0b, S6_WREADY: %0b, S6_WDATA: 0x%0h, S6_WSTRB: 0x%0h, S6_WLAST: %0b", 
                            $realtime, mon_item.S6_WVALID, mon_item.S6_WREADY, mon_item.S6_WDATA, 
                            mon_item.S6_WSTRB, mon_item.S6_WLAST), UVM_LOW)
            end
            
            // Check for write response handshake
            if (s6_vif.s6_monitor_cb.S6_BVALID && s6_vif.s6_monitor_cb.S6_BREADY) begin
                // Capture write response signals
                mon_item.S6_BID = s6_vif.s6_monitor_cb.S6_BID;
                mon_item.S6_BVALID = s6_vif.s6_monitor_cb.S6_BVALID;
                mon_item.S6_BREADY = s6_vif.s6_monitor_cb.S6_BREADY;
                mon_item.S6_BRESP = s6_vif.s6_monitor_cb.S6_BRESP;
                
                // Log write response transaction
                `uvm_info("S6_MONITOR", $sformatf("Time: %0t, S6_BVALID: %0b, S6_BREADY: %0b, S6_BID: 0x%0h, S6_BRESP: %0d", 
                            $realtime, mon_item.S6_BVALID, mon_item.S6_BREADY, mon_item.S6_BID, 
                            mon_item.S6_BRESP), UVM_LOW)
            end
            
            // Check for read address handshake
            if (s6_vif.s6_monitor_cb.S6_ARVALID && s6_vif.s6_monitor_cb.S6_ARREADY) begin
                // Capture read address signals
                mon_item.S6_ARID = s6_vif.s6_monitor_cb.S6_ARID;
                mon_item.S6_ARVALID = s6_vif.s6_monitor_cb.S6_ARVALID;
                mon_item.S6_ARREADY = s6_vif.s6_monitor_cb.S6_ARREADY;
                mon_item.S6_ARADDR = s6_vif.s6_monitor_cb.S6_ARADDR;
                mon_item.S6_ARLEN = s6_vif.s6_monitor_cb.S6_ARLEN;
                mon_item.S6_ARLOCK = s6_vif.s6_monitor_cb.S6_ARLOCK;
                mon_item.S6_ARSIZE = s6_vif.s6_monitor_cb.S6_ARSIZE;
                mon_item.S6_ARBURST = s6_vif.s6_monitor_cb.S6_ARBURST;
                mon_item.S6_ARCACHE = s6_vif.s6_monitor_cb.S6_ARCACHE;
                mon_item.S6_ARPROT = s6_vif.s6_monitor_cb.S6_ARPROT;
                mon_item.S6_ARQOS = s6_vif.s6_monitor_cb.S6_ARQOS;
                mon_item.S6_ARREGION = s6_vif.s6_monitor_cb.S6_ARREGION;
                
                // Log read address transaction
                `uvm_info("S6_MONITOR", $sformatf("Time: %0t, S6_ARVALID: %0b, S6_ARREADY: %0b, S6_ARID: 0x%0h, S6_ARADDR: 0x%0h, S6_ARLEN: %0d, S6_ARSIZE: %0d, S6_ARBURST: %0d, S6_ARLOCK: %0b, S6_ARCACHE: 0x%0h, S6_ARPROT: 0x%0h, S6_ARQOS: 0x%0h, S6_ARREGION: 0x%0h", 
                            $realtime, mon_item.S6_ARVALID, mon_item.S6_ARREADY, mon_item.S6_ARID, mon_item.S6_ARADDR, 
                            mon_item.S6_ARLEN, mon_item.S6_ARSIZE, mon_item.S6_ARBURST, mon_item.S6_ARLOCK, 
                            mon_item.S6_ARCACHE, mon_item.S6_ARPROT, mon_item.S6_ARQOS, mon_item.S6_ARREGION), UVM_LOW)
            end
            
            // Check for read data handshake
            if (s6_vif.s6_monitor_cb.S6_RVALID && s6_vif.s6_monitor_cb.S6_RREADY) begin
                // Capture read data signals
                mon_item.S6_RID = s6_vif.s6_monitor_cb.S6_RID;
                mon_item.S6_RVALID = s6_vif.s6_monitor_cb.S6_RVALID;
                mon_item.S6_RREADY = s6_vif.s6_monitor_cb.S6_RREADY;
                mon_item.S6_RDATA = s6_vif.s6_monitor_cb.S6_RDATA;
                mon_item.S6_RRESP = s6_vif.s6_monitor_cb.S6_RRESP;
                mon_item.S6_RLAST = s6_vif.s6_monitor_cb.S6_RLAST;
                
                // Log read data transaction
                `uvm_info("S6_MONITOR", $sformatf("Time: %0t, S6_RVALID: %0b, S6_RREADY: %0b, S6_RID: 0x%0h, S6_RDATA: 0x%0h, S6_RRESP: %0d, S6_RLAST: %0b", 
                            $realtime, mon_item.S6_RVALID, mon_item.S6_RREADY, mon_item.S6_RID, mon_item.S6_RDATA, 
                            mon_item.S6_RRESP, mon_item.S6_RLAST), UVM_LOW)
            end
            
            // End of monitor
            `uvm_info("S6_MONITOR", "End of Monitor", UVM_MEDIUM)
            
            // Broadcast the collected transaction
            item_collect_port.write(mon_item);
        end
    endtask
    
endclass : S6_monitor

`endif // S6_MONITOR_SV

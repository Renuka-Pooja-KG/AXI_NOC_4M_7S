//=============================================================================
// S1 Agent Monitor Class
//=============================================================================
// Simple passive monitor for Slave 1 that observes AXI transactions
// Uses S1_interface.monitor modport for synchronized signal sampling
// Only handles transaction observation and broadcasting - no coverage or protocol checking

`ifndef S1_MONITOR_SV
`define S1_MONITOR_SV

// Note: All imports and includes will be handled by define_files_package

class S1_monitor extends uvm_monitor;
    
    // Virtual interface for S1 AXI signals using monitor modport
    virtual S1_interface s1_vif;
    
    // Analysis port for transaction broadcasting
    uvm_analysis_port #(S1_seq_item) item_collect_port;
    
    // Single transaction item for reuse
    S1_seq_item mon_item;
    
    // UVM Factory registration
    `uvm_component_utils(S1_monitor)
    
    // Constructor
    function new(string name = "S1_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collect_port = new("item_collect_port", this);
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S1_interface)::get(this, "", "s1_vif", s1_vif)) begin
            `uvm_fatal("S1_MONITOR", "Virtual interface not found for S1 monitor")
        end
        
        // Create transaction item
        mon_item = S1_seq_item::type_id::create("mon_item");
    endfunction
    
    // Run phase - main monitoring loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S1_MONITOR", "S1 Monitor starting run phase", UVM_LOW)
        
        // Main monitoring loop
        collect_data();
    endtask
    
    // Simple data collection task - monitors all AXI channels
    virtual task collect_data();
        forever begin
            // Wait for clock edge
            @(posedge s1_vif.ACLK);
            
            // Collecting the address channel data
            mon_item.S1_AWVALID = s1_vif.s1_monitor_cb.S1_AWVALID;
            mon_item.S1_WVALID = s1_vif.s1_monitor_cb.S1_WVALID;
            
            // Check for write address handshake
            if (s1_vif.s1_monitor_cb.S1_AWVALID && s1_vif.s1_monitor_cb.S1_AWREADY) begin
                // Capture write address signals
                mon_item.S1_AWID = s1_vif.s1_monitor_cb.S1_AWID;
                mon_item.S1_AWREADY = s1_vif.s1_monitor_cb.S1_AWREADY;
                mon_item.S1_AWADDR = s1_vif.s1_monitor_cb.S1_AWADDR;
                mon_item.S1_AWLEN = s1_vif.s1_monitor_cb.S1_AWLEN;
                mon_item.S1_AWLOCK = s1_vif.s1_monitor_cb.S1_AWLOCK;
                mon_item.S1_AWSIZE = s1_vif.s1_monitor_cb.S1_AWSIZE;
                mon_item.S1_AWBURST = s1_vif.s1_monitor_cb.S1_AWBURST;
                mon_item.S1_AWCACHE = s1_vif.s1_monitor_cb.S1_AWCACHE;
                mon_item.S1_AWPROT = s1_vif.s1_monitor_cb.S1_AWPROT;
                mon_item.S1_AWQOS = s1_vif.s1_monitor_cb.S1_AWQOS;
                mon_item.S1_AWREGION = s1_vif.s1_monitor_cb.S1_AWREGION;
                
                // Log write address transaction
                `uvm_info("S1_MONITOR", $sformatf("Time: %0t, S1_AWVALID: %0b, S1_AWREADY: %0b, S1_AWID: 0x%0h, S1_AWADDR: 0x%0h, S1_AWLEN: %0d, S1_AWSIZE: %0d, S1_AWBURST: %0d, S1_AWLOCK: %0b, S1_AWCACHE: 0x%0h, S1_AWPROT: 0x%0h, S1_AWQOS: 0x%0h, S1_AWREGION: 0x%0h", 
                            $realtime, mon_item.S1_AWVALID, mon_item.S1_AWREADY, mon_item.S1_AWID, mon_item.S1_AWADDR, 
                            mon_item.S1_AWLEN, mon_item.S1_AWSIZE, mon_item.S1_AWBURST, mon_item.S1_AWLOCK, 
                            mon_item.S1_AWCACHE, mon_item.S1_AWPROT, mon_item.S1_AWQOS, mon_item.S1_AWREGION), UVM_LOW)
            end
            
            // Check for write data handshake
            if (s1_vif.s1_monitor_cb.S1_WVALID && s1_vif.s1_monitor_cb.S1_WREADY) begin
                // Capture write data signals
                mon_item.S1_WREADY = s1_vif.s1_monitor_cb.S1_WREADY;
                mon_item.S1_WDATA = s1_vif.s1_monitor_cb.S1_WDATA;
                mon_item.S1_WSTRB = s1_vif.s1_monitor_cb.S1_WSTRB;
                mon_item.S1_WLAST = s1_vif.s1_monitor_cb.S1_WLAST;
                
                // Log write data transaction
                `uvm_info("S1_MONITOR", $sformatf("Time: %0t, S1_WVALID: %0b, S1_WREADY: %0b, S1_WDATA: 0x%0h, S1_WSTRB: 0x%0h, S1_WLAST: %0b", 
                            $realtime, mon_item.S1_WVALID, mon_item.S1_WREADY, mon_item.S1_WDATA, 
                            mon_item.S1_WSTRB, mon_item.S1_WLAST), UVM_LOW)
            end
            
            // Check for write response handshake
            if (s1_vif.s1_monitor_cb.S1_BVALID && s1_vif.s1_monitor_cb.S1_BREADY) begin
                // Capture write response signals
                mon_item.S1_BID = s1_vif.s1_monitor_cb.S1_BID;
                mon_item.S1_BVALID = s1_vif.s1_monitor_cb.S1_BVALID;
                mon_item.S1_BREADY = s1_vif.s1_monitor_cb.S1_BREADY;
                mon_item.S1_BRESP = s1_vif.s1_monitor_cb.S1_BRESP;
                
                // Log write response transaction
                `uvm_info("S1_MONITOR", $sformatf("Time: %0t, S1_BVALID: %0b, S1_BREADY: %0b, S1_BID: 0x%0h, S1_BRESP: %0d", 
                            $realtime, mon_item.S1_BVALID, mon_item.S1_BREADY, mon_item.S1_BID, 
                            mon_item.S1_BRESP), UVM_LOW)
            end
            
            // Check for read address handshake
            if (s1_vif.s1_monitor_cb.S1_ARVALID && s1_vif.s1_monitor_cb.S1_ARREADY) begin
                // Capture read address signals
                mon_item.S1_ARID = s1_vif.s1_monitor_cb.S1_ARID;
                mon_item.S1_ARVALID = s1_vif.s1_monitor_cb.S1_ARVALID;
                mon_item.S1_ARREADY = s1_vif.s1_monitor_cb.S1_ARREADY;
                mon_item.S1_ARADDR = s1_vif.s1_monitor_cb.S1_ARADDR;
                mon_item.S1_ARLEN = s1_vif.s1_monitor_cb.S1_ARLEN;
                mon_item.S1_ARLOCK = s1_vif.s1_monitor_cb.S1_ARLOCK;
                mon_item.S1_ARSIZE = s1_vif.s1_monitor_cb.S1_ARSIZE;
                mon_item.S1_ARBURST = s1_vif.s1_monitor_cb.S1_ARBURST;
                mon_item.S1_ARCACHE = s1_vif.s1_monitor_cb.S1_ARCACHE;
                mon_item.S1_ARPROT = s1_vif.s1_monitor_cb.S1_ARPROT;
                mon_item.S1_ARQOS = s1_vif.s1_monitor_cb.S1_ARQOS;
                mon_item.S1_ARREGION = s1_vif.s1_monitor_cb.S1_ARREGION;
                
                // Log read address transaction
                `uvm_info("S1_MONITOR", $sformatf("Time: %0t, S1_ARVALID: %0b, S1_ARREADY: %0b, S1_ARID: 0x%0h, S1_ARADDR: 0x%0h, S1_ARLEN: %0d, S1_ARSIZE: %0d, S1_ARBURST: %0d, S1_ARLOCK: %0b, S1_ARCACHE: 0x%0h, S1_ARPROT: 0x%0h, S1_ARQOS: 0x%0h, S1_ARREGION: 0x%0h", 
                            $realtime, mon_item.S1_ARVALID, mon_item.S1_ARREADY, mon_item.S1_ARID, mon_item.S1_ARADDR, 
                            mon_item.S1_ARLEN, mon_item.S1_ARSIZE, mon_item.S1_ARBURST, mon_item.S1_ARLOCK, 
                            mon_item.S1_ARCACHE, mon_item.S1_ARPROT, mon_item.S1_ARQOS, mon_item.S1_ARREGION), UVM_LOW)
            end
            
            // Check for read data handshake
            if (s1_vif.s1_monitor_cb.S1_RVALID && s1_vif.s1_monitor_cb.S1_RREADY) begin
                // Capture read data signals
                mon_item.S1_RID = s1_vif.s1_monitor_cb.S1_RID;
                mon_item.S1_RVALID = s1_vif.s1_monitor_cb.S1_RVALID;
                mon_item.S1_RREADY = s1_vif.s1_monitor_cb.S1_RREADY;
                mon_item.S1_RDATA = s1_vif.s1_monitor_cb.S1_RDATA;
                mon_item.S1_RRESP = s1_vif.s1_monitor_cb.S1_RRESP;
                mon_item.S1_RLAST = s1_vif.s1_monitor_cb.S1_RLAST;
                
                // Log read data transaction
                `uvm_info("S1_MONITOR", $sformatf("Time: %0t, S1_RVALID: %0b, S1_RREADY: %0b, S1_RID: 0x%0h, S1_RDATA: 0x%0h, S1_RRESP: %0d, S1_RLAST: %0b", 
                            $realtime, mon_item.S1_RVALID, mon_item.S1_RREADY, mon_item.S1_RID, mon_item.S1_RDATA, 
                            mon_item.S1_RRESP, mon_item.S1_RLAST), UVM_LOW)
            end
            
            // End of monitor
            `uvm_info("S1_MONITOR", "End of Monitor", UVM_MEDIUM)
            
            // Broadcast the collected transaction
            item_collect_port.write(mon_item);
        end
    endtask
    
endclass : S1_monitor

`endif // S1_MONITOR_SV

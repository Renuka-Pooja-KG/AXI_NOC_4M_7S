//=============================================================================
// S4 Agent Monitor Class
//=============================================================================
// Simple passive monitor for Slave 4 that observes AXI transactions
// Uses S4_interface.monitor modport for synchronized signal sampling
// Only handles transaction observation and broadcasting - no coverage or protocol checking

`ifndef S4_MONITOR_SV
`define S4_MONITOR_SV

// Note: All imports and includes will be handled by define_files_package

class S4_monitor extends uvm_monitor;
    
    // Virtual interface for S4 AXI signals using monitor modport
    virtual S4_interface s4_vif;
    
    // Analysis port for transaction broadcasting
    uvm_analysis_port #(S4_seq_item) item_collect_port;
    
    // Single transaction item for reuse
    S4_seq_item mon_item;
    
    // UVM Factory registration
    `uvm_component_utils(S4_monitor)
    
    // Constructor
    function new(string name = "S4_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collect_port = new("item_collect_port", this);
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S4_interface)::get(this, "", "s4_vif", s4_vif)) begin
            `uvm_fatal("S4_MONITOR", "Virtual interface not found for S4 monitor")
        end
        
        // Create transaction item
        mon_item = S4_seq_item::type_id::create("mon_item");
    endfunction
    
    // Run phase - main monitoring loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S4_MONITOR", "S4 Monitor starting run phase", UVM_LOW)
        
        // Main monitoring loop
        collect_data();
    endtask
    
    // Simple data collection task - monitors all AXI channels
    virtual task collect_data();
        forever begin
            // Wait for clock edge
            @(posedge s4_vif.ACLK);
            
            // Collecting the address channel data
            mon_item.S4_AWVALID = s4_vif.s4_monitor_cb.S4_AWVALID;
            mon_item.S4_WVALID = s4_vif.s4_monitor_cb.S4_WVALID;
            
            // Check for write address handshake
            if (s4_vif.s4_monitor_cb.S4_AWVALID && s4_vif.s4_monitor_cb.S4_AWREADY) begin
                // Capture write address signals
                mon_item.S4_AWID = s4_vif.s4_monitor_cb.S4_AWID;
                mon_item.S4_AWREADY = s4_vif.s4_monitor_cb.S4_AWREADY;
                mon_item.S4_AWADDR = s4_vif.s4_monitor_cb.S4_AWADDR;
                mon_item.S4_AWLEN = s4_vif.s4_monitor_cb.S4_AWLEN;
                mon_item.S4_AWLOCK = s4_vif.s4_monitor_cb.S4_AWLOCK;
                mon_item.S4_AWSIZE = s4_vif.s4_monitor_cb.S4_AWSIZE;
                mon_item.S4_AWBURST = s4_vif.s4_monitor_cb.S4_AWBURST;
                mon_item.S4_AWCACHE = s4_vif.s4_monitor_cb.S4_AWCACHE;
                mon_item.S4_AWPROT = s4_vif.s4_monitor_cb.S4_AWPROT;
                mon_item.S4_AWQOS = s4_vif.s4_monitor_cb.S4_AWQOS;
                mon_item.S4_AWREGION = s4_vif.s4_monitor_cb.S4_AWREGION;
                
                // Log write address transaction
                `uvm_info("S4_MONITOR", $sformatf("Time: %0t, S4_AWVALID: %0b, S4_AWREADY: %0b, S4_AWID: 0x%0h, S4_AWADDR: 0x%0h, S4_AWLEN: %0d, S4_AWSIZE: %0d, S4_AWBURST: %0d, S4_AWLOCK: %0b, S4_AWCACHE: 0x%0h, S4_AWPROT: 0x%0h, S4_AWQOS: 0x%0h, S4_AWREGION: 0x%0h", 
                            $realtime, mon_item.S4_AWVALID, mon_item.S4_AWREADY, mon_item.S4_AWID, mon_item.S4_AWADDR, 
                            mon_item.S4_AWLEN, mon_item.S4_AWSIZE, mon_item.S4_AWBURST, mon_item.S4_AWLOCK, 
                            mon_item.S4_AWCACHE, mon_item.S4_AWPROT, mon_item.S4_AWQOS, mon_item.S4_AWREGION), UVM_LOW)
            end
            
            // Check for write data handshake
            if (s4_vif.s4_monitor_cb.S4_WVALID && s4_vif.s4_monitor_cb.S4_WREADY) begin
                // Capture write data signals
                mon_item.S4_WREADY = s4_vif.s4_monitor_cb.S4_WREADY;
                mon_item.S4_WDATA = s4_vif.s4_monitor_cb.S4_WDATA;
                mon_item.S4_WSTRB = s4_vif.s4_monitor_cb.S4_WSTRB;
                mon_item.S4_WLAST = s4_vif.s4_monitor_cb.S4_WLAST;
                
                // Log write data transaction
                `uvm_info("S4_MONITOR", $sformatf("Time: %0t, S4_WVALID: %0b, S4_WREADY: %0b, S4_WDATA: 0x%0h, S4_WSTRB: 0x%0h, S4_WLAST: %0b", 
                            $realtime, mon_item.S4_WVALID, mon_item.S4_WREADY, mon_item.S4_WDATA, 
                            mon_item.S4_WSTRB, mon_item.S4_WLAST), UVM_LOW)
            end
            
            // Check for write response handshake
            if (s4_vif.s4_monitor_cb.S4_BVALID && s4_vif.s4_monitor_cb.S4_BREADY) begin
                // Capture write response signals
                mon_item.S4_BID = s4_vif.s4_monitor_cb.S4_BID;
                mon_item.S4_BVALID = s4_vif.s4_monitor_cb.S4_BVALID;
                mon_item.S4_BREADY = s4_vif.s4_monitor_cb.S4_BREADY;
                mon_item.S4_BRESP = s4_vif.s4_monitor_cb.S4_BRESP;
                
                // Log write response transaction
                `uvm_info("S4_MONITOR", $sformatf("Time: %0t, S4_BVALID: %0b, S4_BREADY: %0b, S4_BID: 0x%0h, S4_BRESP: %0d", 
                            $realtime, mon_item.S4_BVALID, mon_item.S4_BREADY, mon_item.S4_BID, 
                            mon_item.S4_BRESP), UVM_LOW)
            end
            
            // Check for read address handshake
            if (s4_vif.s4_monitor_cb.S4_ARVALID && s4_vif.s4_monitor_cb.S4_ARREADY) begin
                // Capture read address signals
                mon_item.S4_ARID = s4_vif.s4_monitor_cb.S4_ARID;
                mon_item.S4_ARVALID = s4_vif.s4_monitor_cb.S4_ARVALID;
                mon_item.S4_ARREADY = s4_vif.s4_monitor_cb.S4_ARREADY;
                mon_item.S4_ARADDR = s4_vif.s4_monitor_cb.S4_ARADDR;
                mon_item.S4_ARLEN = s4_vif.s4_monitor_cb.S4_ARLEN;
                mon_item.S4_ARLOCK = s4_vif.s4_monitor_cb.S4_ARLOCK;
                mon_item.S4_ARSIZE = s4_vif.s4_monitor_cb.S4_ARSIZE;
                mon_item.S4_ARBURST = s4_vif.s4_monitor_cb.S4_ARBURST;
                mon_item.S4_ARCACHE = s4_vif.s4_monitor_cb.S4_ARCACHE;
                mon_item.S4_ARPROT = s4_vif.s4_monitor_cb.S4_ARPROT;
                mon_item.S4_ARQOS = s4_vif.s4_monitor_cb.S4_ARQOS;
                mon_item.S4_ARREGION = s4_vif.s4_monitor_cb.S4_ARREGION;
                
                // Log read address transaction
                `uvm_info("S4_MONITOR", $sformatf("Time: %0t, S4_ARVALID: %0b, S4_ARREADY: %0b, S4_ARID: 0x%0h, S4_ARADDR: 0x%0h, S4_ARLEN: %0d, S4_ARSIZE: %0d, S4_ARBURST: %0d, S4_ARLOCK: %0b, S4_ARCACHE: 0x%0h, S4_ARPROT: 0x%0h, S4_ARQOS: 0x%0h, S4_ARREGION: 0x%0h", 
                            $realtime, mon_item.S4_ARVALID, mon_item.S4_ARREADY, mon_item.S4_ARID, mon_item.S4_ARADDR, 
                            mon_item.S4_ARLEN, mon_item.S4_ARSIZE, mon_item.S4_ARBURST, mon_item.S4_ARLOCK, 
                            mon_item.S4_ARCACHE, mon_item.S4_ARPROT, mon_item.S4_ARQOS, mon_item.S4_ARREGION), UVM_LOW)
            end
            
            // Check for read data handshake
            if (s4_vif.s4_monitor_cb.S4_RVALID && s4_vif.s4_monitor_cb.S4_RREADY) begin
                // Capture read data signals
                mon_item.S4_RID = s4_vif.s4_monitor_cb.S4_RID;
                mon_item.S4_RVALID = s4_vif.s4_monitor_cb.S4_RVALID;
                mon_item.S4_RREADY = s4_vif.s4_monitor_cb.S4_RREADY;
                mon_item.S4_RDATA = s4_vif.s4_monitor_cb.S4_RDATA;
                mon_item.S4_RRESP = s4_vif.s4_monitor_cb.S4_RRESP;
                mon_item.S4_RLAST = s4_vif.s4_monitor_cb.S4_RLAST;
                
                // Log read data transaction
                `uvm_info("S4_MONITOR", $sformatf("Time: %0t, S4_RVALID: %0b, S4_RREADY: %0b, S4_RID: 0x%0h, S4_RDATA: 0x%0h, S4_RRESP: %0d, S4_RLAST: %0b", 
                            $realtime, mon_item.S4_RVALID, mon_item.S4_RREADY, mon_item.S4_RID, mon_item.S4_RDATA, 
                            mon_item.S4_RRESP, mon_item.S4_RLAST), UVM_LOW)
            end
            
            // End of monitor
            `uvm_info("S4_MONITOR", "End of Monitor", UVM_MEDIUM)
            
            // Broadcast the collected transaction
            item_collect_port.write(mon_item);
        end
    endtask
    
endclass : S4_monitor

`endif // S4_MONITOR_SV

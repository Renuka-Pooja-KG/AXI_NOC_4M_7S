//=============================================================================
// S0 Agent Monitor Class
//=============================================================================
// Simple passive monitor for Slave 0 that observes AXI transactions
// Uses S0_interface.monitor modport for synchronized signal sampling
// Only handles transaction observation and broadcasting - no coverage or protocol checking

`ifndef S0_MONITOR_SV
`define S0_MONITOR_SV

// Note: All imports and includes will be handled by define_files_package

class S0_monitor extends uvm_monitor;
    
    // Virtual interface for S0 AXI signals using monitor modport
    virtual S0_interface.monitor s0_vif;
    
    // Analysis port for transaction broadcasting
    uvm_analysis_port #(S0_seq_item) item_collect_port;
    
    // Single transaction item for reuse
    S0_seq_item mon_item;
    
    // UVM Factory registration
    `uvm_component_utils(S0_monitor)
    
    // Constructor
    function new(string name = "S0_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collect_port = new("item_collect_port", this);
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S0_interface.monitor)::get(this, "", "s0_vif", s0_vif)) begin
            `uvm_fatal("S0_MONITOR", "Virtual interface not found for S0 monitor")
        end
        
        // Create transaction item
        mon_item = S0_seq_item::type_id::create("mon_item");
    endfunction
    
    // Run phase - main monitoring loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S0_MONITOR", "S0 Monitor starting run phase", UVM_LOW)
        
        // Main monitoring loop
        collect_data();
    endtask
    
    // Simple data collection task - monitors all AXI channels
    virtual task collect_data();
        forever begin
            // Wait for clock edge
            @(posedge s0_vif.ACLK);
            
            // Collecting the address channel data
            mon_item.S0_AWVALID = s0_vif.s0_monitor_cb.S0_AWVALID;
            mon_item.S0_WVALID = s0_vif.s0_monitor_cb.S0_WVALID;
            
            // Check for write address handshake
            if (s0_vif.s0_monitor_cb.S0_AWVALID && s0_vif.s0_monitor_cb.S0_AWREADY) begin
                // Capture write address signals
                mon_item.S0_AWID = s0_vif.s0_monitor_cb.S0_AWID;
                mon_item.S0_AWREADY = s0_vif.s0_monitor_cb.S0_AWREADY;
                mon_item.S0_AWADDR = s0_vif.s0_monitor_cb.S0_AWADDR;
                mon_item.S0_AWLEN = s0_vif.s0_monitor_cb.S0_AWLEN;
                mon_item.S0_AWLOCK = s0_vif.s0_monitor_cb.S0_AWLOCK;
                mon_item.S0_AWSIZE = s0_vif.s0_monitor_cb.S0_AWSIZE;
                mon_item.S0_AWBURST = s0_vif.s0_monitor_cb.S0_AWBURST;
                mon_item.S0_AWCACHE = s0_vif.s0_monitor_cb.S0_AWCACHE;
                mon_item.S0_AWPROT = s0_vif.s0_monitor_cb.S0_AWPROT;
                mon_item.S0_AWQOS = s0_vif.s0_monitor_cb.S0_AWQOS;
                mon_item.S0_AWREGION = s0_vif.s0_monitor_cb.S0_AWREGION;
                mon_item.S0_AWUSER = s0_vif.s0_monitor_cb.S0_AWUSER;
                
                // Log write address transaction
                `uvm_info("S0_MONITOR", $sformatf("Time: %0t, S0_AWVALID: %0b, S0_AWREADY: %0b, S0_AWID: 0x%0h, S0_AWADDR: 0x%0h, S0_AWLEN: %0d, S0_AWSIZE: %0d, S0_AWBURST: %0d, S0_AWLOCK: %0b, S0_AWCACHE: 0x%0h, S0_AWPROT: 0x%0h, S0_AWQOS: 0x%0h, S0_AWREGION: 0x%0h, S0_AWUSER: 0x%0h", 
                            $realtime, mon_item.S0_AWVALID, mon_item.S0_AWREADY, mon_item.S0_AWID, mon_item.S0_AWADDR, 
                            mon_item.S0_AWLEN, mon_item.S0_AWSIZE, mon_item.S0_AWBURST, mon_item.S0_AWLOCK, 
                            mon_item.S0_AWCACHE, mon_item.S0_AWPROT, mon_item.S0_AWQOS, mon_item.S0_AWREGION, mon_item.S0_AWUSER), UVM_LOW)
            end
            
            // Check for write data handshake
            if (s0_vif.s0_monitor_cb.S0_WVALID && s0_vif.s0_monitor_cb.S0_WREADY) begin
                // Capture write data signals
                mon_item.S0_WREADY = s0_vif.s0_monitor_cb.S0_WREADY;
                mon_item.S0_WDATA = s0_vif.s0_monitor_cb.S0_WDATA;
                mon_item.S0_WSTRB = s0_vif.s0_monitor_cb.S0_WSTRB;
                mon_item.S0_WLAST = s0_vif.s0_monitor_cb.S0_WLAST;
                mon_item.S0_WUSER = s0_vif.s0_monitor_cb.S0_WUSER;
                
                // Log write data transaction
                `uvm_info("S0_MONITOR", $sformatf("Time: %0t, S0_WVALID: %0b, S0_WREADY: %0b, S0_WDATA: 0x%0h, S0_WSTRB: 0x%0h, S0_WLAST: %0b, S0_WUSER: 0x%0h", 
                            $realtime, mon_item.S0_WVALID, mon_item.S0_WREADY, mon_item.S0_WDATA, 
                            mon_item.S0_WSTRB, mon_item.S0_WLAST, mon_item.S0_WUSER), UVM_LOW)
            end
            
            // Check for write response handshake
            if (s0_vif.s0_monitor_cb.S0_BVALID && s0_vif.s0_monitor_cb.S0_BREADY) begin
                // Capture write response signals
                mon_item.S0_BID = s0_vif.s0_monitor_cb.S0_BID;
                mon_item.S0_BVALID = s0_vif.s0_monitor_cb.S0_BVALID;
                mon_item.S0_BREADY = s0_vif.s0_monitor_cb.S0_BREADY;
                mon_item.S0_BRESP = s0_vif.s0_monitor_cb.S0_BRESP;
                mon_item.S0_BUSER = s0_vif.s0_monitor_cb.S0_BUSER;
                
                // Log write response transaction
                `uvm_info("S0_MONITOR", $sformatf("Time: %0t, S0_BVALID: %0b, S0_BREADY: %0b, S0_BID: 0x%0h, S0_BRESP: %0d, S0_BUSER: 0x%0h", 
                            $realtime, mon_item.S0_BVALID, mon_item.S0_BREADY, mon_item.S0_BID, 
                            mon_item.S0_BRESP, mon_item.S0_BUSER), UVM_LOW)
            end
            
            // Check for read address handshake
            if (s0_vif.s0_monitor_cb.S0_ARVALID && s0_vif.s0_monitor_cb.S0_ARREADY) begin
                // Capture read address signals
                mon_item.S0_ARID = s0_vif.s0_monitor_cb.S0_ARID;
                mon_item.S0_ARVALID = s0_vif.s0_monitor_cb.S0_ARVALID;
                mon_item.S0_ARREADY = s0_vif.s0_monitor_cb.S0_ARREADY;
                mon_item.S0_ARADDR = s0_vif.s0_monitor_cb.S0_ARADDR;
                mon_item.S0_ARLEN = s0_vif.s0_monitor_cb.S0_ARLEN;
                mon_item.S0_ARLOCK = s0_vif.s0_monitor_cb.S0_ARLOCK;
                mon_item.S0_ARSIZE = s0_vif.s0_monitor_cb.S0_ARSIZE;
                mon_item.S0_ARBURST = s0_vif.s0_monitor_cb.S0_ARBURST;
                mon_item.S0_ARCACHE = s0_vif.s0_monitor_cb.S0_ARCACHE;
                mon_item.S0_ARPROT = s0_vif.s0_monitor_cb.S0_ARPROT;
                mon_item.S0_ARQOS = s0_vif.s0_monitor_cb.S0_ARQOS;
                mon_item.S0_ARREGION = s0_vif.s0_monitor_cb.S0_ARREGION;
                mon_item.S0_ARUSER = s0_vif.s0_monitor_cb.S0_ARUSER;
                
                // Log read address transaction
                `uvm_info("S0_MONITOR", $sformatf("Time: %0t, S0_ARVALID: %0b, S0_ARREADY: %0b, S0_ARID: 0x%0h, S0_ARADDR: 0x%0h, S0_ARLEN: %0d, S0_ARSIZE: %0d, S0_ARBURST: %0d, S0_ARLOCK: %0b, S0_ARCACHE: 0x%0h, S0_ARPROT: 0x%0h, S0_ARQOS: 0x%0h, S0_ARREGION: 0x%0h, S0_ARUSER: 0x%0h", 
                            $realtime, mon_item.S0_ARVALID, mon_item.S0_ARREADY, mon_item.S0_ARID, mon_item.S0_ARADDR, 
                            mon_item.S0_ARLEN, mon_item.S0_ARSIZE, mon_item.S0_ARBURST, mon_item.S0_ARLOCK, 
                            mon_item.S0_ARCACHE, mon_item.S0_ARPROT, mon_item.S0_ARQOS, mon_item.S0_ARREGION, mon_item.S0_ARUSER), UVM_LOW)
            end
            
            // Check for read data handshake
            if (s0_vif.s0_monitor_cb.S0_RVALID && s0_vif.s0_monitor_cb.S0_RREADY) begin
                // Capture read data signals
                mon_item.S0_RID = s0_vif.s0_monitor_cb.S0_RID;
                mon_item.S0_RVALID = s0_vif.s0_monitor_cb.S0_RVALID;
                mon_item.S0_RREADY = s0_vif.s0_monitor_cb.S0_RREADY;
                mon_item.S0_RDATA = s0_vif.s0_monitor_cb.S0_RDATA;
                mon_item.S0_RRESP = s0_vif.s0_monitor_cb.S0_RRESP;
                mon_item.S0_RLAST = s0_vif.s0_monitor_cb.S0_RLAST;
                mon_item.S0_RUSER = s0_vif.s0_monitor_cb.S0_RUSER;
                
                // Log read data transaction
                `uvm_info("S0_MONITOR", $sformatf("Time: %0t, S0_RVALID: %0b, S0_RREADY: %0b, S0_RID: 0x%0h, S0_RDATA: 0x%0h, S0_RRESP: %0d, S0_RLAST: %0b, S0_RUSER: 0x%0h", 
                            $realtime, mon_item.S0_RVALID, mon_item.S0_RREADY, mon_item.S0_RID, mon_item.S0_RDATA, 
                            mon_item.S0_RRESP, mon_item.S0_RLAST, mon_item.S0_RUSER), UVM_LOW)
            end
            
            // End of monitor
            `uvm_info("S0_MONITOR", "End of Monitor", UVM_MEDIUM)
            
            // Broadcast the collected transaction
            item_collect_port.write(mon_item);
        end
    endtask
    
endclass : S0_monitor

`endif // S0_MONITOR_SV

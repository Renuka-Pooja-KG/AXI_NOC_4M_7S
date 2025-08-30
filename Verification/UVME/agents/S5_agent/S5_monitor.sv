//=============================================================================
// S5 Agent Monitor Class
//=============================================================================
// Simple passive monitor for Slave 5 that observes AXI transactions
// Uses S5_interface.monitor modport for synchronized signal sampling
// Only handles transaction observation and broadcasting - no coverage or protocol checking

`ifndef S5_MONITOR_SV
`define S5_MONITOR_SV

// Note: All imports and includes will be handled by define_files_package

class S5_monitor extends uvm_monitor;
    
    // Virtual interface for S5 AXI signals using monitor modport
    virtual S5_interface.monitor s5_vif;
    
    // Analysis port for transaction broadcasting
    uvm_analysis_port #(S5_seq_item) item_collect_port;
    
    // Single transaction item for reuse
    S5_seq_item mon_item;
    
    // UVM Factory registration
    `uvm_component_utils(S5_monitor)
    
    // Constructor
    function new(string name = "S5_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collect_port = new("item_collect_port", this);
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual S5_interface.monitor)::get(this, "", "s5_vif", s5_vif)) begin
            `uvm_fatal("S5_MONITOR", "Virtual interface not found for S5 monitor")
        end
        
        // Create transaction item
        mon_item = S5_seq_item::type_id::create("mon_item");
    endfunction
    
    // Run phase - main monitoring loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("S5_MONITOR", "S5 Monitor starting run phase", UVM_LOW)
        
        // Main monitoring loop
        collect_data();
    endtask
    
    // Simple data collection task - monitors all AXI channels
    virtual task collect_data();
        forever begin
            // Wait for clock edge
            @(posedge s5_vif.ACLK);
            
            // Collecting the address channel data
            mon_item.S5_AWVALID = s5_vif.s5_monitor_cb.S5_AWVALID;
            mon_item.S5_WVALID = s5_vif.s5_monitor_cb.S5_WVALID;
            
            // Check for write address handshake
            if (s5_vif.s5_monitor_cb.S5_AWVALID && s5_vif.s5_monitor_cb.S5_AWREADY) begin
                // Capture write address signals
                mon_item.S5_AWID = s5_vif.s5_monitor_cb.S5_AWID;
                mon_item.S5_AWREADY = s5_vif.s5_monitor_cb.S5_AWREADY;
                mon_item.S5_AWADDR = s5_vif.s5_monitor_cb.S5_AWADDR;
                mon_item.S5_AWLEN = s5_vif.s5_monitor_cb.S5_AWLEN;
                mon_item.S5_AWLOCK = s5_vif.s5_monitor_cb.S5_AWLOCK;
                mon_item.S5_AWSIZE = s5_vif.s5_monitor_cb.S5_AWSIZE;
                mon_item.S5_AWBURST = s5_vif.s5_monitor_cb.S5_AWBURST;
                mon_item.S5_AWCACHE = s5_vif.s5_monitor_cb.S5_AWCACHE;
                mon_item.S5_AWPROT = s5_vif.s5_monitor_cb.S5_AWPROT;
                mon_item.S5_AWQOS = s5_vif.s5_monitor_cb.S5_AWQOS;
                mon_item.S5_AWREGION = s5_vif.s5_monitor_cb.S5_AWREGION;
                mon_item.S5_AWUSER = s5_vif.s5_monitor_cb.S5_AWUSER;
                
                // Log write address transaction
                `uvm_info("S5_MONITOR", $sformatf("Time: %0t, S5_AWVALID: %0b, S5_AWREADY: %0b, S5_AWID: 0x%0h, S5_AWADDR: 0x%0h, S5_AWLEN: %0d, S5_AWSIZE: %0d, S5_AWBURST: %0d, S5_AWLOCK: %0b, S5_AWCACHE: 0x%0h, S5_AWPROT: 0x%0h, S5_AWQOS: 0x%0h, S5_AWREGION: 0x%0h, S5_AWUSER: 0x%0h", 
                            $realtime, mon_item.S5_AWVALID, mon_item.S5_AWREADY, mon_item.S5_AWID, mon_item.S5_AWADDR, 
                            mon_item.S5_AWLEN, mon_item.S5_AWSIZE, mon_item.S5_AWBURST, mon_item.S5_AWLOCK, 
                            mon_item.S5_AWCACHE, mon_item.S5_AWPROT, mon_item.S5_AWQOS, mon_item.S5_AWREGION, mon_item.S5_AWUSER), UVM_LOW)
            end
            
            // Check for write data handshake
            if (s5_vif.s5_monitor_cb.S5_WVALID && s5_vif.s5_monitor_cb.S5_WREADY) begin
                // Capture write data signals
                mon_item.S5_WREADY = s5_vif.s5_monitor_cb.S5_WREADY;
                mon_item.S5_WDATA = s5_vif.s5_monitor_cb.S5_WDATA;
                mon_item.S5_WSTRB = s5_vif.s5_monitor_cb.S5_WSTRB;
                mon_item.S5_WLAST = s5_vif.s5_monitor_cb.S5_WLAST;
                mon_item.S5_WUSER = s5_vif.s5_monitor_cb.S5_WUSER;
                
                // Log write data transaction
                `uvm_info("S5_MONITOR", $sformatf("Time: %0t, S5_WVALID: %0b, S5_WREADY: %0b, S5_WDATA: 0x%0h, S5_WSTRB: 0x%0h, S5_WLAST: %0b, S5_WUSER: 0x%0h", 
                            $realtime, mon_item.S5_WVALID, mon_item.S5_WREADY, mon_item.S5_WDATA, 
                            mon_item.S5_WSTRB, mon_item.S5_WLAST, mon_item.S5_WUSER), UVM_LOW)
            end
            
            // Check for write response handshake
            if (s5_vif.s5_monitor_cb.S5_BVALID && s5_vif.s5_monitor_cb.S5_BREADY) begin
                // Capture write response signals
                mon_item.S5_BID = s5_vif.s5_monitor_cb.S5_BID;
                mon_item.S5_BVALID = s5_vif.s5_monitor_cb.S5_BVALID;
                mon_item.S5_BREADY = s5_vif.s5_monitor_cb.S5_BREADY;
                mon_item.S5_BRESP = s5_vif.s5_monitor_cb.S5_BRESP;
                mon_item.S5_BUSER = s5_vif.s5_monitor_cb.S5_BUSER;
                
                // Log write response transaction
                `uvm_info("S5_MONITOR", $sformatf("Time: %0t, S5_BVALID: %0b, S5_BREADY: %0b, S5_BID: 0x%0h, S5_BRESP: %0d, S5_BUSER: 0x%0h", 
                            $realtime, mon_item.S5_BVALID, mon_item.S5_BREADY, mon_item.S5_BID, 
                            mon_item.S5_BRESP, mon_item.S5_BUSER), UVM_LOW)
            end
            
            // Check for read address handshake
            if (s5_vif.s5_monitor_cb.S5_ARVALID && s5_vif.s5_monitor_cb.S5_ARREADY) begin
                // Capture read address signals
                mon_item.S5_ARID = s5_vif.s5_monitor_cb.S5_ARID;
                mon_item.S5_ARVALID = s5_vif.s5_monitor_cb.S5_ARVALID;
                mon_item.S5_ARREADY = s5_vif.s5_monitor_cb.S5_ARREADY;
                mon_item.S5_ARADDR = s5_vif.s5_monitor_cb.S5_ARADDR;
                mon_item.S5_ARLEN = s5_vif.s5_monitor_cb.S5_ARLEN;
                mon_item.S5_ARLOCK = s5_vif.s5_monitor_cb.S5_ARLOCK;
                mon_item.S5_ARSIZE = s5_vif.s5_monitor_cb.S5_ARSIZE;
                mon_item.S5_ARBURST = s5_vif.s5_monitor_cb.S5_ARBURST;
                mon_item.S5_ARCACHE = s5_vif.s5_monitor_cb.S5_ARCACHE;
                mon_item.S5_ARPROT = s5_vif.s5_monitor_cb.S5_ARPROT;
                mon_item.S5_ARQOS = s5_vif.s5_monitor_cb.S5_ARQOS;
                mon_item.S5_ARREGION = s5_vif.s5_monitor_cb.S5_ARREGION;
                mon_item.S5_ARUSER = s5_vif.s5_monitor_cb.S5_ARUSER;
                
                // Log read address transaction
                `uvm_info("S5_MONITOR", $sformatf("Time: %0t, S5_ARVALID: %0b, S5_ARREADY: %0b, S5_ARID: 0x%0h, S5_ARADDR: 0x%0h, S5_ARLEN: %0d, S5_ARSIZE: %0d, S5_ARBURST: %0d, S5_ARLOCK: %0b, S5_ARCACHE: 0x%0h, S5_ARPROT: 0x%0h, S5_ARQOS: 0x%0h, S5_ARREGION: 0x%0h, S5_ARUSER: 0x%0h", 
                            $realtime, mon_item.S5_ARVALID, mon_item.S5_ARREADY, mon_item.S5_ARID, mon_item.S5_ARADDR, 
                            mon_item.S5_ARLEN, mon_item.S5_ARSIZE, mon_item.S5_ARBURST, mon_item.S5_ARLOCK, 
                            mon_item.S5_ARCACHE, mon_item.S5_ARPROT, mon_item.S5_ARQOS, mon_item.S5_ARREGION, mon_item.S5_ARUSER), UVM_LOW)
            end
            
            // Check for read data handshake
            if (s5_vif.s5_monitor_cb.S5_RVALID && s5_vif.s5_monitor_cb.S5_RREADY) begin
                // Capture read data signals
                mon_item.S5_RID = s5_vif.s5_monitor_cb.S5_RID;
                mon_item.S5_RVALID = s5_vif.s5_monitor_cb.S5_RVALID;
                mon_item.S5_RREADY = s5_vif.s5_monitor_cb.S5_RREADY;
                mon_item.S5_RDATA = s5_vif.s5_monitor_cb.S5_RDATA;
                mon_item.S5_RRESP = s5_vif.s5_monitor_cb.S5_RRESP;
                mon_item.S5_RLAST = s5_vif.s5_monitor_cb.S5_RLAST;
                mon_item.S5_RUSER = s5_vif.s5_monitor_cb.S5_RUSER;
                
                // Log read data transaction
                `uvm_info("S5_MONITOR", $sformatf("Time: %0t, S5_RVALID: %0b, S5_RREADY: %0b, S5_RID: 0x%0h, S5_RDATA: 0x%0h, S5_RRESP: %0d, S5_RLAST: %0b, S5_RUSER: 0x%0h", 
                            $realtime, mon_item.S5_RVALID, mon_item.S5_RREADY, mon_item.S5_RID, mon_item.S5_RDATA, 
                            mon_item.S5_RRESP, mon_item.S5_RLAST, mon_item.S5_RUSER), UVM_LOW)
            end
            
            // End of monitor
            `uvm_info("S5_MONITOR", "End of Monitor", UVM_MEDIUM)
            
            // Broadcast the collected transaction
            item_collect_port.write(mon_item);
        end
    endtask
    
endclass : S5_monitor

`endif // S5_MONITOR_SV

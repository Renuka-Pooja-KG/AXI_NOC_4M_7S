//=============================================================================
// M3 Agent Monitor Class
//=============================================================================
// Simple passive monitor for Master 3 that observes AXI transactions
// Uses M3_interface.monitor modport for synchronized signal sampling
// Only handles transaction observation and broadcasting - no coverage or protocol checking

`ifndef M3_MONITOR_SV
`define M3_MONITOR_SV

// Note: All imports and includes will be handled by define_files_package

class M3_monitor extends uvm_monitor;
    
    // Virtual interface for M3 AXI signals using monitor modport
    virtual M3_interface.monitor m3_vif;
    
    // Analysis port for transaction broadcasting
    uvm_analysis_port #(M3_seq_item) item_collect_port;
    
    // Single transaction item for reuse
    M3_seq_item mon_item;
    
    // UVM Factory registration
    `uvm_component_utils(M3_monitor)
    
    // Constructor
    function new(string name = "M3_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collect_port = new("item_collect_port", this);
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual M3_interface.monitor)::get(this, "", "m3_vif", m3_vif)) begin
            `uvm_fatal("M3_MONITOR", "Virtual interface not found for M3 monitor")
        end
        
        // Create transaction item
        mon_item = M3_seq_item::type_id::create("mon_item");
    endfunction
    
    // Run phase - main monitoring loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("M3_MONITOR", "M3 Monitor starting run phase", UVM_LOW)
        
        // Main monitoring loop
        collect_data();
    endtask
    
    // Simple data collection task - monitors all AXI channels
    virtual task collect_data();
        forever begin
            // Wait for clock edge
            @(posedge m3_vif.ACLK);
            
            // Collecting the address channel data
            mon_item.M3_AWVALID = m3_vif.m3_monitor_cb.M3_AWVALID;
            mon_item.M3_WVALID = m3_vif.m3_monitor_cb.M3_WVALID;
            
            // Check for write address handshake
            if (m3_vif.m3_monitor_cb.M3_AWVALID && m3_vif.m3_monitor_cb.M3_AWREADY) begin
                    // Capture write address signals
                    mon_item.M3_AWID = m3_vif.m3_monitor_cb.M3_AWID;
                    mon_item.M3_AWREADY = m3_vif.m3_monitor_cb.M3_AWREADY;
                    mon_item.M3_AWADDR = m3_vif.m3_monitor_cb.M3_AWADDR;
                    mon_item.M3_AWLEN = m3_vif.m3_monitor_cb.M3_AWLEN;
                    mon_item.M3_AWLOCK = m3_vif.m3_monitor_cb.M3_AWLOCK;
                    mon_item.M3_AWSIZE = m3_vif.m3_monitor_cb.M3_AWSIZE;
                    mon_item.M3_AWBURST = m3_vif.m3_monitor_cb.M3_AWBURST;
                    mon_item.M3_AWCACHE = m3_vif.m3_monitor_cb.M3_AWCACHE;
                    mon_item.M3_AWPROT = m3_vif.m3_monitor_cb.M3_AWPROT;
                    mon_item.M3_AWQOS = m3_vif.m3_monitor_cb.M3_AWQOS;
                    mon_item.M3_AWREGION = m3_vif.m3_monitor_cb.M3_AWREGION;
                    mon_item.M3_AWUSER = m3_vif.m3_monitor_cb.M3_AWUSER;
                    
                    // Log write address transaction
                    `uvm_info("M3_MONITOR", $sformatf("Time: %0t, M3_AWVALID: %0b, M3_AWREADY: %0b, M3_AWID: 0x%0h, M3_AWADDR: 0x%0h, M3_AWLEN: %0d, M3_AWSIZE: %0d, M3_AWBURST: %0d, M3_AWLOCK: %0b, M3_AWCACHE: 0x%0h, M3_AWPROT: 0x%0h, M3_AWQOS: 0x%0h, M3_AWREGION: 0x%0h, M3_AWUSER: 0x%0h", 
                                $realtime, mon_item.M3_AWVALID, mon_item.M3_AWREADY, mon_item.M3_AWID, mon_item.M3_AWADDR, 
                                mon_item.M3_AWLEN, mon_item.M3_AWSIZE, mon_item.M3_AWBURST, mon_item.M3_AWLOCK, 
                                mon_item.M3_AWCACHE, mon_item.M3_AWPROT, mon_item.M3_AWQOS, mon_item.M3_AWREGION, mon_item.M3_AWUSER), UVM_LOW)
            end
            
            // Check for write data handshake
            if (m3_vif.m3_monitor_cb.M3_WVALID && m3_vif.m3_monitor_cb.M3_WREADY) begin
                    // Capture write data signals
                    mon_item.M3_WREADY = m3_vif.m3_monitor_cb.M3_WREADY;
                    mon_item.M3_WDATA = m3_vif.m3_monitor_cb.M3_WDATA;
                    mon_item.M3_WSTRB = m3_vif.m3_monitor_cb.M3_WSTRB;
                    mon_item.M3_WLAST = m3_vif.m3_monitor_cb.M3_WLAST;
                    mon_item.M3_WUSER = m3_vif.m3_monitor_cb.M3_WUSER;
                    
                    // Log write data transaction
                    `uvm_info("M3_MONITOR", $sformatf("Time: %0t, M3_WVALID: %0b, M3_WREADY: %0b, M3_WDATA: 0x%0h, M3_WSTRB: 0x%0h, M3_WLAST: %0b, M3_WUSER: 0x%0h", 
                                $realtime, mon_item.M3_WVALID, mon_item.M3_WREADY, mon_item.M3_WDATA, 
                                mon_item.M3_WSTRB, mon_item.M3_WLAST, mon_item.M3_WUSER), UVM_LOW)
            end
            
            // Check for write response handshake
            if (m3_vif.m3_monitor_cb.M3_BVALID && m3_vif.m3_monitor_cb.M3_BREADY) begin
                // Capture write response signals
                mon_item.M3_BID = m3_vif.m3_monitor_cb.M3_BID;
                mon_item.M3_BVALID = m3_vif.m3_monitor_cb.M3_BVALID;
                mon_item.M3_BREADY = m3_vif.m3_monitor_cb.M3_BREADY;
                mon_item.M3_BRESP = m3_vif.m3_monitor_cb.M3_BRESP;
                mon_item.M3_BUSER = m3_vif.m3_monitor_cb.M3_BUSER;
                
                // Log write response transaction
                `uvm_info("M3_MONITOR", $sformatf("Time: %0t, M3_BVALID: %0b, M3_BREADY: %0b, M3_BID: 0x%0h, M3_BRESP: %0d, M3_BUSER: 0x%0h", 
                            $realtime, mon_item.M3_BVALID, mon_item.M3_BREADY, mon_item.M3_BID, 
                            mon_item.M3_BRESP, mon_item.M3_BUSER), UVM_LOW)
            end
            
            // Check for read address handshake
            if (m3_vif.m3_monitor_cb.M3_ARVALID && m3_vif.m3_monitor_cb.M3_ARREADY) begin
                // Capture read address signals
                mon_item.M3_ARID = m3_vif.m3_monitor_cb.M3_ARID;
                mon_item.M3_ARVALID = m3_vif.m3_monitor_cb.M3_ARVALID;
                mon_item.M3_ARREADY = m3_vif.m3_monitor_cb.M3_ARREADY;
                mon_item.M3_ARADDR = m3_vif.m3_monitor_cb.M3_ARADDR;
                mon_item.M3_ARLEN = m3_vif.m3_monitor_cb.M3_ARLEN;
                mon_item.M3_ARLOCK = m3_vif.m3_monitor_cb.M3_ARLOCK;
                mon_item.M3_ARSIZE = m3_vif.m3_monitor_cb.M3_ARSIZE;
                mon_item.M3_ARBURST = m3_vif.m3_monitor_cb.M3_ARBURST;
                mon_item.M3_ARCACHE = m3_vif.m3_monitor_cb.M3_ARCACHE;
                mon_item.M3_ARPROT = m3_vif.m3_monitor_cb.M3_ARPROT;
                mon_item.M3_ARQOS = m3_vif.m3_monitor_cb.M3_ARQOS;
                mon_item.M3_ARREGION = m3_vif.m3_monitor_cb.M3_ARREGION;
                mon_item.M3_ARUSER = m3_vif.m3_monitor_cb.M3_ARUSER;
                
                // Log read address transaction
                `uvm_info("M3_MONITOR", $sformatf("Time: %0t, M3_ARVALID: %0b, M3_ARREADY: %0b, M3_ARID: 0x%0h, M3_ARADDR: 0x%0h, M3_ARLEN: %0d, M3_ARSIZE: %0d, M3_ARBURST: %0d, M3_ARLOCK: %0b, M3_ARCACHE: 0x%0h, M3_ARPROT: 0x%0h, M3_ARQOS: 0x%0h, M3_ARREGION: 0x%0h, M3_ARUSER: 0x%0h", 
                            $realtime, mon_item.M3_ARVALID, mon_item.M3_ARREADY, mon_item.M3_ARID, mon_item.M3_ARADDR, 
                            mon_item.M3_ARLEN, mon_item.M3_ARSIZE, mon_item.M3_ARBURST, mon_item.M3_ARLOCK, 
                            mon_item.M3_ARCACHE, mon_item.M3_ARPROT, mon_item.M3_ARQOS, mon_item.M3_ARREGION, mon_item.M3_ARUSER), UVM_LOW)
            end
            
            // Check for read data handshake
            if (m3_vif.m3_monitor_cb.M3_RVALID && m3_vif.m3_monitor_cb.M3_RREADY) begin
                // Capture read data signals
                mon_item.M3_RID = m3_vif.m3_monitor_cb.M3_RID;
                mon_item.M3_RVALID = m3_vif.m3_monitor_cb.M3_RVALID;
                mon_item.M3_RREADY = m3_vif.m3_monitor_cb.M3_RREADY;
                mon_item.M3_RDATA = m3_vif.m3_monitor_cb.M3_RDATA;
                mon_item.M3_RRESP = m3_vif.m3_monitor_cb.M3_RRESP;
                mon_item.M3_RLAST = m3_vif.m3_monitor_cb.M3_RLAST;
                mon_item.M3_RUSER = m3_vif.m3_monitor_cb.M3_RUSER;
                
                // Log read data transaction
                `uvm_info("M3_MONITOR", $sformatf("Time: %0t, M3_RVALID: %0b, M3_RREADY: %0b, M3_RID: 0x%0h, M3_RDATA: 0x%0h, M3_RRESP: %0d, M3_RLAST: %0b, M3_RUSER: 0x%0h", 
                            $realtime, mon_item.M3_RVALID, mon_item.M3_RREADY, mon_item.M3_RID, mon_item.M3_RDATA, 
                            mon_item.M3_RRESP, mon_item.M3_RLAST, mon_item.M3_RUSER), UVM_LOW)
            end
            
            // End of monitor
            `uvm_info("M3_MONITOR", "End of Monitor", UVM_MEDIUM)
            
            // Broadcast the collected transaction
            item_collect_port.write(mon_item);
        end
    endtask
    
endclass : M3_monitor

`endif // M3_MONITOR_SV
//=============================================================================
// M2 Agent Monitor Class
//=============================================================================
// Simple passive monitor for Master 2 that observes AXI transactions
// Uses M2_interface.monitor modport for synchronized signal sampling
// Only handles transaction observation and broadcasting - no coverage or protocol checking

`ifndef M2_MONITOR_SV
`define M2_MONITOR_SV

// Note: All imports and includes will be handled by define_files_package

class M2_monitor extends uvm_monitor;
    
    // Virtual interface for M2 AXI signals using monitor modport
    virtual M2_interface.monitor m2_vif;
    
    // Analysis port for transaction broadcasting
    uvm_analysis_port #(M2_seq_item) item_collect_port;
    
    // Single transaction item for reuse
    M2_seq_item mon_item;
    
    // UVM Factory registration
    `uvm_component_utils(M2_monitor)
    
    // Constructor
    function new(string name = "M2_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collect_port = new("item_collect_port", this);
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual M2_interface.monitor)::get(this, "", "m2_vif", m2_vif)) begin
            `uvm_fatal("M2_MONITOR", "Virtual interface not found for M2 monitor")
        end
        
        // Create transaction item
        mon_item = M2_seq_item::type_id::create("mon_item");
    endfunction
    
    // Run phase - main monitoring loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("M2_MONITOR", "M2 Monitor starting run phase", UVM_LOW)
        
        // Main monitoring loop
        collect_data();
    endtask
    
    // Simple data collection task - monitors all AXI channels
    virtual task collect_data();
        forever begin
            // Wait for clock edge
            @(posedge m2_vif.ACLK);
            
            // Collecting the address channel data
            mon_item.M2_AWVALID = m2_vif.m2_monitor_cb.M2_AWVALID;
            mon_item.M2_WVALID = m2_vif.m2_monitor_cb.M2_WVALID;
            
            // Check for write address handshake
            if (m2_vif.m2_monitor_cb.M2_AWVALID && m2_vif.m2_monitor_cb.M2_AWREADY) begin
                    // Capture write address signals
                    mon_item.M2_AWID = m2_vif.m2_monitor_cb.M2_AWID;
                    mon_item.M2_AWREADY = m2_vif.m2_monitor_cb.M2_AWREADY;
                    mon_item.M2_AWADDR = m2_vif.m2_monitor_cb.M2_AWADDR;
                    mon_item.M2_AWLEN = m2_vif.m2_monitor_cb.M2_AWLEN;
                    mon_item.M2_AWLOCK = m2_vif.m2_monitor_cb.M2_AWLOCK;
                    mon_item.M2_AWSIZE = m2_vif.m2_monitor_cb.M2_AWSIZE;
                    mon_item.M2_AWBURST = m2_vif.m2_monitor_cb.M2_AWBURST;
                    mon_item.M2_AWCACHE = m2_vif.m2_monitor_cb.M2_AWCACHE;
                    mon_item.M2_AWPROT = m2_vif.m2_monitor_cb.M2_AWPROT;
                    mon_item.M2_AWQOS = m2_vif.m2_monitor_cb.M2_AWQOS;
                    mon_item.M2_AWREGION = m2_vif.m2_monitor_cb.M2_AWREGION;
                    mon_item.M2_AWUSER = m2_vif.m2_monitor_cb.M2_AWUSER;
                    
                    // Log write address transaction
                    `uvm_info("M2_MONITOR", $sformatf("Time: %0t, M2_AWVALID: %0b, M2_AWREADY: %0b, M2_AWID: 0x%0h, M2_AWADDR: 0x%0h, M2_AWLEN: %0d, M2_AWSIZE: %0d, M2_AWBURST: %0d, M2_AWLOCK: %0b, M2_AWCACHE: 0x%0h, M2_AWPROT: 0x%0h, M2_AWQOS: 0x%0h, M2_AWREGION: 0x%0h, M2_AWUSER: 0x%0h", 
                                $realtime, mon_item.M2_AWVALID, mon_item.M2_AWREADY, mon_item.M2_AWID, mon_item.M2_AWADDR, 
                                mon_item.M2_AWLEN, mon_item.M2_AWSIZE, mon_item.M2_AWBURST, mon_item.M2_AWLOCK, 
                                mon_item.M2_AWCACHE, mon_item.M2_AWPROT, mon_item.M2_AWQOS, mon_item.M2_AWREGION, mon_item.M2_AWUSER), UVM_LOW)
            end
            
            // Check for write data handshake
            if (m2_vif.m2_monitor_cb.M2_WVALID && m2_vif.m2_monitor_cb.M2_WREADY) begin
                    // Capture write data signals
                    mon_item.M2_WREADY = m2_vif.m2_monitor_cb.M2_WREADY;
                    mon_item.M2_WDATA = m2_vif.m2_monitor_cb.M2_WDATA;
                    mon_item.M2_WSTRB = m2_vif.m2_monitor_cb.M2_WSTRB;
                    mon_item.M2_WLAST = m2_vif.m2_monitor_cb.M2_WLAST;
                    mon_item.M2_WUSER = m2_vif.m2_monitor_cb.M2_WUSER;
                    
                    // Log write data transaction
                    `uvm_info("M2_MONITOR", $sformatf("Time: %0t, M2_WVALID: %0b, M2_WREADY: %0b, M2_WDATA: 0x%0h, M2_WSTRB: 0x%0h, M2_WLAST: %0b, M2_WUSER: 0x%0h", 
                                $realtime, mon_item.M2_WVALID, mon_item.M2_WREADY, mon_item.M2_WDATA, 
                                mon_item.M2_WSTRB, mon_item.M2_WLAST, mon_item.M2_WUSER), UVM_LOW)
            end
            
            // Check for write response handshake
            if (m2_vif.m2_monitor_cb.M2_BVALID && m2_vif.m2_monitor_cb.M2_BREADY) begin
                // Capture write response signals
                mon_item.M2_BID = m2_vif.m2_monitor_cb.M2_BID;
                mon_item.M2_BVALID = m2_vif.m2_monitor_cb.M2_BVALID;
                mon_item.M2_BREADY = m2_vif.m2_monitor_cb.M2_BREADY;
                mon_item.M2_BRESP = m2_vif.m2_monitor_cb.M2_BRESP;
                mon_item.M2_BUSER = m2_vif.m2_monitor_cb.M2_BUSER;
                
                // Log write response transaction
                `uvm_info("M2_MONITOR", $sformatf("Time: %0t, M2_BVALID: %0b, M2_BREADY: %0b, M2_BID: 0x%0h, M2_BRESP: %0d, M2_BUSER: 0x%0h", 
                            $realtime, mon_item.M2_BVALID, mon_item.M2_BREADY, mon_item.M2_BID, 
                            mon_item.M2_BRESP, mon_item.M2_BUSER), UVM_LOW)
            end
            
            // Check for read address handshake
            if (m2_vif.m2_monitor_cb.M2_ARVALID && m2_vif.m2_monitor_cb.M2_ARREADY) begin
                // Capture read address signals
                mon_item.M2_ARID = m2_vif.m2_monitor_cb.M2_ARID;
                mon_item.M2_ARVALID = m2_vif.m2_monitor_cb.M2_ARVALID;
                mon_item.M2_ARREADY = m2_vif.m2_monitor_cb.M2_ARREADY;
                mon_item.M2_ARADDR = m2_vif.m2_monitor_cb.M2_ARADDR;
                mon_item.M2_ARLEN = m2_vif.m2_monitor_cb.M2_ARLEN;
                mon_item.M2_ARLOCK = m2_vif.m2_monitor_cb.M2_ARLOCK;
                mon_item.M2_ARSIZE = m2_vif.m2_monitor_cb.M2_ARSIZE;
                mon_item.M2_ARBURST = m2_vif.m2_monitor_cb.M2_ARBURST;
                mon_item.M2_ARCACHE = m2_vif.m2_monitor_cb.M2_ARCACHE;
                mon_item.M2_ARPROT = m2_vif.m2_monitor_cb.M2_ARPROT;
                mon_item.M2_ARQOS = m2_vif.m2_monitor_cb.M2_ARQOS;
                mon_item.M2_ARREGION = m2_vif.m2_monitor_cb.M2_ARREGION;
                mon_item.M2_ARUSER = m2_vif.m2_monitor_cb.M2_ARUSER;
                
                // Log read address transaction
                `uvm_info("M2_MONITOR", $sformatf("Time: %0t, M2_ARVALID: %0b, M2_ARREADY: %0b, M2_ARID: 0x%0h, M2_ARADDR: 0x%0h, M2_ARLEN: %0d, M2_ARSIZE: %0d, M2_ARBURST: %0d, M2_ARLOCK: %0b, M2_ARCACHE: 0x%0h, M2_ARPROT: 0x%0h, M2_ARQOS: 0x%0h, M2_ARREGION: 0x%0h, M2_ARUSER: 0x%0h", 
                            $realtime, mon_item.M2_ARVALID, mon_item.M2_ARREADY, mon_item.M2_ARID, mon_item.M2_ARADDR, 
                            mon_item.M2_ARLEN, mon_item.M2_ARSIZE, mon_item.M2_ARBURST, mon_item.M2_ARLOCK, 
                            mon_item.M2_ARCACHE, mon_item.M2_ARPROT, mon_item.M2_ARQOS, mon_item.M2_ARREGION, mon_item.M2_ARUSER), UVM_LOW)
            end
            
            // Check for read data handshake
            if (m2_vif.m2_monitor_cb.M2_RVALID && m2_vif.m2_monitor_cb.M2_RREADY) begin
                // Capture read data signals
                mon_item.M2_RID = m2_vif.m2_monitor_cb.M2_RID;
                mon_item.M2_RVALID = m2_vif.m2_monitor_cb.M2_RVALID;
                mon_item.M2_RREADY = m2_vif.m2_monitor_cb.M2_RREADY;
                mon_item.M2_RDATA = m2_vif.m2_monitor_cb.M2_RDATA;
                mon_item.M2_RRESP = m2_vif.m2_monitor_cb.M2_RRESP;
                mon_item.M2_RLAST = m2_vif.m2_monitor_cb.M2_RLAST;
                mon_item.M2_RUSER = m2_vif.m2_monitor_cb.M2_RUSER;
                
                // Log read data transaction
                `uvm_info("M2_MONITOR", $sformatf("Time: %0t, M2_RVALID: %0b, M2_RREADY: %0b, M2_RID: 0x%0h, M2_RDATA: 0x%0h, M2_RRESP: %0d, M2_RLAST: %0b, M2_RUSER: 0x%0h", 
                            $realtime, mon_item.M2_RVALID, mon_item.M2_RREADY, mon_item.M2_RID, mon_item.M2_RDATA, 
                            mon_item.M2_RRESP, mon_item.M2_RLAST, mon_item.M2_RUSER), UVM_LOW)
            end
            
            // End of monitor
            `uvm_info("M2_MONITOR", "End of Monitor", UVM_MEDIUM)
            
            // Broadcast the collected transaction
            item_collect_port.write(mon_item);
        end
    endtask
    
endclass : M2_monitor

`endif // M2_MONITOR_SV
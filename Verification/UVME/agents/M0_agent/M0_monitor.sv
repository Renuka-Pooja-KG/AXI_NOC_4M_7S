//=============================================================================
// M0 Agent Monitor Class
//=============================================================================
// Simple passive monitor for Master 0 that observes AXI transactions
// Uses M0_interface.monitor modport for synchronized signal sampling
// Only handles transaction observation and broadcasting - no coverage or protocol checking

`ifndef M0_MONITOR_SV
`define M0_MONITOR_SV

// Note: All imports and includes will be handled by define_files_package

class M0_monitor extends uvm_monitor;
    
    // Virtual interface for M0 AXI signals using monitor modport
    virtual M0_interface.monitor m0_vif;
    
    // Analysis port for transaction broadcasting
    uvm_analysis_port #(M0_seq_item) item_collect_port;
    
    // Single transaction item for reuse
    M0_seq_item mon_item;
    
    // UVM Factory registration
    `uvm_component_utils(M0_monitor)
    
    // Constructor
    function new(string name = "M0_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collect_port = new("item_collect_port", this);
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual M0_interface)::get(this, "", "m0_vif", m0_vif)) begin
            `uvm_fatal("M0_MONITOR", "Virtual interface not found for M0 monitor")
        end
        
        // Create transaction item
        mon_item = M0_seq_item::type_id::create("mon_item");
    endfunction
    
    // Run phase - main monitoring loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("M0_MONITOR", "M0 Monitor starting run phase", UVM_LOW)
        
        // Main monitoring loop
        collect_data();
    endtask
    
    // Simple data collection task - monitors all AXI channels
    virtual task collect_data();
        forever begin
            // Wait for clock edge
            @(posedge m0_vif.ACLK);
            
            // Collecting the address channel data
            mon_item.M0_AWVALID = m0_vif.m0_monitor_cb.M0_AWVALID;
            mon_item.M0_WVALID = m0_vif.m0_monitor_cb.M0_WVALID;
            
            // Check for write address handshake
            if (m0_vif.m0_monitor_cb.M0_AWVALID && m0_vif.m0_monitor_cb.M0_AWREADY) begin
                    // Capture write address signals
                    mon_item.M0_AWID = m0_vif.m0_monitor_cb.M0_AWID;
                    mon_item.M0_AWREADY = m0_vif.m0_monitor_cb.M0_AWREADY;
                    mon_item.M0_AWADDR = m0_vif.m0_monitor_cb.M0_AWADDR;
                    mon_item.M0_AWLEN = m0_vif.m0_monitor_cb.M0_AWLEN;
                    mon_item.M0_AWLOCK = m0_vif.m0_monitor_cb.M0_AWLOCK;
                    mon_item.M0_AWSIZE = m0_vif.m0_monitor_cb.M0_AWSIZE;
                    mon_item.M0_AWBURST = m0_vif.m0_monitor_cb.M0_AWBURST;
                    mon_item.M0_AWCACHE = m0_vif.m0_monitor_cb.M0_AWCACHE;
                    mon_item.M0_AWPROT = m0_vif.m0_monitor_cb.M0_AWPROT;
                    mon_item.M0_AWQOS = m0_vif.m0_monitor_cb.M0_AWQOS;
                    mon_item.M0_AWREGION = m0_vif.m0_monitor_cb.M0_AWREGION;
                    
                    // Log write address transaction
                    `uvm_info("M0_MONITOR", $sformatf("Time: %0t, M0_AWVALID: %0b, M0_AWREADY: %0b, M0_AWID: 0x%0h, M0_AWADDR: 0x%0h, M0_AWLEN: %0d, M0_AWSIZE: %0d, M0_AWBURST: %0d, M0_AWLOCK: %0b, M0_AWCACHE: 0x%0h, M0_AWPROT: 0x%0h, M0_AWQOS: 0x%0h, M0_AWREGION: 0x%0h", 
                                $realtime, mon_item.M0_AWVALID, mon_item.M0_AWREADY, mon_item.M0_AWID, mon_item.M0_AWADDR, 
                                mon_item.M0_AWLEN, mon_item.M0_AWSIZE, mon_item.M0_AWBURST, mon_item.M0_AWLOCK, 
                                mon_item.M0_AWCACHE, mon_item.M0_AWPROT, mon_item.M0_AWQOS, mon_item.M0_AWREGION), UVM_LOW)
            end
            
            // Check for write data handshake
            if (m0_vif.m0_monitor_cb.M0_WVALID && m0_vif.m0_monitor_cb.M0_WREADY) begin
                    // Capture write data signals
                    mon_item.M0_WREADY = m0_vif.m0_monitor_cb.M0_WREADY;
                    mon_item.M0_WDATA = m0_vif.m0_monitor_cb.M0_WDATA;
                    mon_item.M0_WSTRB = m0_vif.m0_monitor_cb.M0_WSTRB;
                    mon_item.M0_WLAST = m0_vif.m0_monitor_cb.M0_WLAST;
                    
                    // Log write data transaction
                    `uvm_info("M0_MONITOR", $sformatf("Time: %0t, M0_WVALID: %0b, M0_WREADY: %0b, M0_WDATA: 0x%0h, M0_WSTRB: 0x%0h, M0_WLAST: %0b", 
                                $realtime, mon_item.M0_WVALID, mon_item.M0_WREADY, mon_item.M0_WDATA, 
                                mon_item.M0_WSTRB, mon_item.M0_WLAST), UVM_LOW)
            end
            
            // Check for write response handshake
            if (m0_vif.m0_monitor_cb.M0_BVALID && m0_vif.m0_monitor_cb.M0_BREADY) begin
                // Capture write response signals
                mon_item.M0_BID = m0_vif.m0_monitor_cb.M0_BID;
                mon_item.M0_BVALID = m0_vif.m0_monitor_cb.M0_BVALID;
                mon_item.M0_BREADY = m0_vif.m0_monitor_cb.M0_BREADY;
                mon_item.M0_BRESP = m0_vif.m0_monitor_cb.M0_BRESP;
                
                // Log write response transaction
                `uvm_info("M0_MONITOR", $sformatf("Time: %0t, M0_BVALID: %0b, M0_BREADY: %0b, M0_BID: 0x%0h, M0_BRESP: %0d", 
                            $realtime, mon_item.M0_BVALID, mon_item.M0_BREADY, mon_item.M0_BID, 
                            mon_item.M0_BRESP), UVM_LOW)
            end
            
            // Check for read address handshake
            if (m0_vif.m0_monitor_cb.M0_ARVALID && m0_vif.m0_monitor_cb.M0_ARREADY) begin
                // Capture read address signals
                mon_item.M0_ARID = m0_vif.m0_monitor_cb.M0_ARID;
                mon_item.M0_ARVALID = m0_vif.m0_monitor_cb.M0_ARVALID;
                mon_item.M0_ARREADY = m0_vif.m0_monitor_cb.M0_ARREADY;
                mon_item.M0_ARADDR = m0_vif.m0_monitor_cb.M0_ARADDR;
                mon_item.M0_ARLEN = m0_vif.m0_monitor_cb.M0_ARLEN;
                mon_item.M0_ARLOCK = m0_vif.m0_monitor_cb.M0_ARLOCK;
                mon_item.M0_ARSIZE = m0_vif.m0_monitor_cb.M0_ARSIZE;
                mon_item.M0_ARBURST = m0_vif.m0_monitor_cb.M0_ARBURST;
                mon_item.M0_ARCACHE = m0_vif.m0_monitor_cb.M0_ARCACHE;
                mon_item.M0_ARPROT = m0_vif.m0_monitor_cb.M0_ARPROT;
                mon_item.M0_ARQOS = m0_vif.m0_monitor_cb.M0_ARQOS;
                mon_item.M0_ARREGION = m0_vif.m0_monitor_cb.M0_ARREGION;
                
                // Log read address transaction
                `uvm_info("M0_MONITOR", $sformatf("Time: %0t, M0_ARVALID: %0b, M0_ARREADY: %0b, M0_ARID: 0x%0h, M0_ARADDR: 0x%0h, M0_ARLEN: %0d, M0_ARSIZE: %0d, M0_ARBURST: %0d, M0_ARLOCK: %0b, M0_ARCACHE: 0x%0h, M0_ARPROT: 0x%0h, M0_ARQOS: 0x%0h, M0_ARREGION: 0x%0h", 
                            $realtime, mon_item.M0_ARVALID, mon_item.M0_ARREADY, mon_item.M0_ARID, mon_item.M0_ARADDR, 
                            mon_item.M0_ARLEN, mon_item.M0_ARSIZE, mon_item.M0_ARBURST, mon_item.M0_ARLOCK, 
                            mon_item.M0_ARCACHE, mon_item.M0_ARPROT, mon_item.M0_ARQOS, mon_item.M0_ARREGION), UVM_LOW)
            end
            
            // Check for read data handshake
            if (m0_vif.m0_monitor_cb.M0_RVALID && m0_vif.m0_monitor_cb.M0_RREADY) begin
                // Capture read data signals
                mon_item.M0_RID = m0_vif.m0_monitor_cb.M0_RID;
                mon_item.M0_RVALID = m0_vif.m0_monitor_cb.M0_RVALID;
                mon_item.M0_RREADY = m0_vif.m0_monitor_cb.M0_RREADY;
                mon_item.M0_RDATA = m0_vif.m0_monitor_cb.M0_RDATA;
                mon_item.M0_RRESP = m0_vif.m0_monitor_cb.M0_RRESP;
                mon_item.M0_RLAST = m0_vif.m0_monitor_cb.M0_RLAST;
                
                // Log read data transaction
                `uvm_info("M0_MONITOR", $sformatf("Time: %0t, M0_RVALID: %0b, M0_RREADY: %0b, M0_RID: 0x%0h, M0_RDATA: 0x%0h, M0_RRESP: %0d, M0_RLAST: %0b", 
                            $realtime, mon_item.M0_RVALID, mon_item.M0_RREADY, mon_item.M0_RID, mon_item.M0_RDATA, 
                            mon_item.M0_RRESP, mon_item.M0_RLAST), UVM_LOW)
            end
            
            // End of monitor
            `uvm_info("M0_MONITOR", "End of Monitor", UVM_MEDIUM)
            
            // Broadcast the collected transaction
            item_collect_port.write(mon_item);
        end
    endtask
    
endclass : M0_monitor

`endif // M0_MONITOR_SV
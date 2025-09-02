//=============================================================================
// M1 Agent Monitor Class
//=============================================================================
// Simple passive monitor for Master 1 that observes AXI transactions
// Uses M1_interface.monitor modport for synchronized signal sampling
// Only handles transaction observation and broadcasting - no coverage or protocol checking

`ifndef M1_MONITOR_SV
`define M1_MONITOR_SV

// Note: All imports and includes will be handled by define_files_package

class M1_monitor extends uvm_monitor;
    
    // Virtual interface for M1 AXI signals using monitor modport
    virtual M1_interface.monitor m1_vif;
    
    // Analysis port for transaction broadcasting
    uvm_analysis_port #(M1_seq_item) item_collect_port;
    
    // Single transaction item for reuse
    M1_seq_item mon_item;
    
    // UVM Factory registration
    `uvm_component_utils(M1_monitor)
    
    // Constructor
    function new(string name = "M1_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collect_port = new("item_collect_port", this);
    endfunction
    
    // Build phase - get virtual interface
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface from config database
        if (!uvm_config_db#(virtual M1_interface)::get(this, "", "m1_vif", m1_vif)) begin
            `uvm_fatal("M1_MONITOR", "Virtual interface not found for M1 monitor")
        end
        
        // Create transaction item
        mon_item = M1_seq_item::type_id::create("mon_item");
    endfunction
    
    // Run phase - main monitoring loop
    virtual task run_phase(uvm_phase phase);
        `uvm_info("M1_MONITOR", "M1 Monitor starting run phase", UVM_LOW)
        
        // Main monitoring loop
        collect_data();
    endtask
    
    // Simple data collection task - monitors all AXI channels
    virtual task collect_data();
        forever begin
            // Wait for clock edge
            @(posedge m1_vif.ACLK);
            
            // Collecting the address channel data
            mon_item.M1_AWVALID = m1_vif.m1_monitor_cb.M1_AWVALID;
            mon_item.M1_WVALID = m1_vif.m1_monitor_cb.M1_WVALID;
            
            // Check for write address handshake
            if (m1_vif.m1_monitor_cb.M1_AWVALID && m1_vif.m1_monitor_cb.M1_AWREADY) begin
                    // Capture write address signals
                    mon_item.M1_AWID = m1_vif.m1_monitor_cb.M1_AWID;
                    mon_item.M1_AWREADY = m1_vif.m1_monitor_cb.M1_AWREADY;
                    mon_item.M1_AWADDR = m1_vif.m1_monitor_cb.M1_AWADDR;
                    mon_item.M1_AWLEN = m1_vif.m1_monitor_cb.M1_AWLEN;
                    mon_item.M1_AWLOCK = m1_vif.m1_monitor_cb.M1_AWLOCK;
                    mon_item.M1_AWSIZE = m1_vif.m1_monitor_cb.M1_AWSIZE;
                    mon_item.M1_AWBURST = m1_vif.m1_monitor_cb.M1_AWBURST;
                    mon_item.M1_AWCACHE = m1_vif.m1_monitor_cb.M1_AWCACHE;
                    mon_item.M1_AWPROT = m1_vif.m1_monitor_cb.M1_AWPROT;
                    mon_item.M1_AWQOS = m1_vif.m1_monitor_cb.M1_AWQOS;
                    mon_item.M1_AWREGION = m1_vif.m1_monitor_cb.M1_AWREGION;
                    
                    // Log write address transaction
                    `uvm_info("M1_MONITOR", $sformatf("Time: %0t, M1_AWVALID: %0b, M1_AWREADY: %0b, M1_AWID: 0x%0h, M1_AWADDR: 0x%0h, M1_AWLEN: %0d, M1_AWSIZE: %0d, M1_AWBURST: %0d, M1_AWLOCK: %0b, M1_AWCACHE: 0x%0h, M1_AWPROT: 0x%0h, M1_AWQOS: 0x%0h, M1_AWREGION: 0x%0h", 
                                $realtime, mon_item.M1_AWVALID, mon_item.M1_AWREADY, mon_item.M1_AWID, mon_item.M1_AWADDR, 
                                mon_item.M1_AWLEN, mon_item.M1_AWSIZE, mon_item.M1_AWBURST, mon_item.M1_AWLOCK, 
                                mon_item.M1_AWCACHE, mon_item.M1_AWPROT, mon_item.M1_AWQOS, mon_item.M1_AWREGION), UVM_LOW)
            end
            
            // Check for write data handshake
            if (m1_vif.m1_monitor_cb.M1_WVALID && m1_vif.m1_monitor_cb.M1_WREADY) begin
                    // Capture write data signals
                    mon_item.M1_WREADY = m1_vif.m1_monitor_cb.M1_WREADY;
                    mon_item.M1_WDATA = m1_vif.m1_monitor_cb.M1_WDATA;
                    mon_item.M1_WSTRB = m1_vif.m1_monitor_cb.M1_WSTRB;
                    mon_item.M1_WLAST = m1_vif.m1_monitor_cb.M1_WLAST;
                    
                    // Log write data transaction
                    `uvm_info("M1_MONITOR", $sformatf("Time: %0t, M1_WVALID: %0b, M1_WREADY: %0b, M1_WDATA: 0x%0h, M1_WSTRB: 0x%0h, M1_WLAST: %0b", 
                                $realtime, mon_item.M1_WVALID, mon_item.M1_WREADY, mon_item.M1_WDATA, 
                                mon_item.M1_WSTRB, mon_item.M1_WLAST), UVM_LOW)
            end
            
            // Check for write response handshake
            if (m1_vif.m1_monitor_cb.M1_BVALID && m1_vif.m1_monitor_cb.M1_BREADY) begin
                // Capture write response signals
                mon_item.M1_BID = m1_vif.m1_monitor_cb.M1_BID;
                mon_item.M1_BVALID = m1_vif.m1_monitor_cb.M1_BVALID;
                mon_item.M1_BREADY = m1_vif.m1_monitor_cb.M1_BREADY;
                mon_item.M1_BRESP = m1_vif.m1_monitor_cb.M1_BRESP;
                
                // Log write response transaction
                `uvm_info("M1_MONITOR", $sformatf("Time: %0t, M1_BVALID: %0b, M1_BREADY: %0b, M1_BID: 0x%0h, M1_BRESP: %0d", 
                            $realtime, mon_item.M1_BVALID, mon_item.M1_BREADY, mon_item.M1_BID, 
                            mon_item.M1_BRESP), UVM_LOW)
            end
            
            // Check for read address handshake
            if (m1_vif.m1_monitor_cb.M1_ARVALID && m1_vif.m1_monitor_cb.M1_ARREADY) begin
                // Capture read address signals
                mon_item.M1_ARID = m1_vif.m1_monitor_cb.M1_ARID;
                mon_item.M1_ARVALID = m1_vif.m1_monitor_cb.M1_ARVALID;
                mon_item.M1_ARREADY = m1_vif.m1_monitor_cb.M1_ARREADY;
                mon_item.M1_ARADDR = m1_vif.m1_monitor_cb.M1_ARADDR;
                mon_item.M1_ARLEN = m1_vif.m1_monitor_cb.M1_ARLEN;
                mon_item.M1_ARLOCK = m1_vif.m1_monitor_cb.M1_ARLOCK;
                mon_item.M1_ARSIZE = m1_vif.m1_monitor_cb.M1_ARSIZE;
                mon_item.M1_ARBURST = m1_vif.m1_monitor_cb.M1_ARBURST;
                mon_item.M1_ARCACHE = m1_vif.m1_monitor_cb.M1_ARCACHE;
                mon_item.M1_ARPROT = m1_vif.m1_monitor_cb.M1_ARPROT;
                mon_item.M1_ARQOS = m1_vif.m1_monitor_cb.M1_ARQOS;
                mon_item.M1_ARREGION = m1_vif.m1_monitor_cb.M1_ARREGION;
                
                // Log read address transaction
                `uvm_info("M1_MONITOR", $sformatf("Time: %0t, M1_ARVALID: %0b, M1_ARREADY: %0b, M1_ARID: 0x%0h, M1_ARADDR: 0x%0h, M1_ARLEN: %0d, M1_ARSIZE: %0d, M1_ARBURST: %0d, M1_ARLOCK: %0b, M1_ARCACHE: 0x%0h, M1_ARPROT: 0x%0h, M1_ARQOS: 0x%0h, M1_ARREGION: 0x%0h", 
                            $realtime, mon_item.M1_ARVALID, mon_item.M1_ARREADY, mon_item.M1_ARID, mon_item.M1_ARADDR, 
                            mon_item.M1_ARLEN, mon_item.M1_ARSIZE, mon_item.M1_ARBURST, mon_item.M1_ARLOCK, 
                            mon_item.M1_ARCACHE, mon_item.M1_ARPROT, mon_item.M1_ARQOS, mon_item.M1_ARREGION), UVM_LOW)
            end
            
            // Check for read data handshake
            if (m1_vif.m1_monitor_cb.M1_RVALID && m1_vif.m1_monitor_cb.M1_RREADY) begin
                // Capture read data signals
                mon_item.M1_RID = m1_vif.m1_monitor_cb.M1_RID;
                mon_item.M1_RVALID = m1_vif.m1_monitor_cb.M1_RVALID;
                mon_item.M1_RREADY = m1_vif.m1_monitor_cb.M1_RREADY;
                mon_item.M1_RDATA = m1_vif.m1_monitor_cb.M1_RDATA;
                mon_item.M1_RRESP = m1_vif.m1_monitor_cb.M1_RRESP;
                mon_item.M1_RLAST = m1_vif.m1_monitor_cb.M1_RLAST;
                
                // Log read data transaction
                `uvm_info("M1_MONITOR", $sformatf("Time: %0t, M1_RVALID: %0b, M1_RREADY: %0b, M1_RID: 0x%0h, M1_RDATA: 0x%0h, M1_RRESP: %0d, M1_RLAST: %0b", 
                            $realtime, mon_item.M1_RVALID, mon_item.M1_RREADY, mon_item.M1_RID, mon_item.M1_RDATA, 
                            mon_item.M1_RRESP, mon_item.M1_RLAST), UVM_LOW)
            end
            
            // End of monitor
            `uvm_info("M1_MONITOR", "End of Monitor", UVM_MEDIUM)
            
            // Broadcast the collected transaction
            item_collect_port.write(mon_item);
        end
    endtask
    
endclass : M1_monitor

`endif // M1_MONITOR_SV
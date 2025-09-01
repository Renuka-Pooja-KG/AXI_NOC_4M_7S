//=============================================================================
// M3 AXI Interface
//=============================================================================
// Interface for Master 3 (M3) AXI signals
// Based on RTL: amba_axi_m4s7.v
// Compatible with M3_seq_item.sv and axi_common_types_pkg.sv
// Note: This interface is specifically for M3; slave interfaces will be created separately
// Features: Clocking block for synchronized signal access at posedge ACLK

interface M3_interface(
    input logic ACLK,
    input logic ARESETn
);
    import axi_common_types_pkg::*;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    logic [AXI_ID_WIDTH-1:0]     M3_AWID;           // Write address ID
    logic [AXI_ADDR_WIDTH-1:0]   M3_AWADDR;         // Write address
    logic [AXI_LEN_WIDTH-1:0]    M3_AWLEN;          // Burst length (0-15)
    logic                        M3_AWLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   M3_AWSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  M3_AWBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  M3_AWCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   M3_AWPROT;         // Protection attributes
    logic                        M3_AWVALID;        // Write address valid
    logic                        M3_AWREADY;        // Write address ready (from slave)
    logic [AXI_QOS_WIDTH-1:0]    M3_AWQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] M3_AWREGION;       // Region identifier
    logic [0:0]                  M3_AWUSER;         // Write-address user path (if enabled)
    
    // ===== WRITE DATA CHANNEL (W) =====
    logic [AXI_DATA_WIDTH-1:0]   M3_WDATA;          // Write data
    logic [AXI_STRB_WIDTH-1:0]   M3_WSTRB;          // Write strobes
    logic                        M3_WLAST;          // Write last
    logic                        M3_WVALID;         // Write valid
    logic                        M3_WREADY;         // Write ready (from slave)
    logic [0:0]                  M3_WUSER;          // Write-data user path (if enabled)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    logic [AXI_ID_WIDTH-1:0]     M3_BID;            // Write response ID (from slave)
    logic [AXI_RESP_WIDTH-1:0]   M3_BRESP;          // Write response (from slave)
    logic                        M3_BVALID;         // Write response valid (from slave)
    logic                        M3_BREADY;         // Write response ready
    logic [0:0]                  M3_BUSER;          // Write-response user path (if enabled)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    logic [AXI_ID_WIDTH-1:0]     M3_ARID;           // Read address ID
    logic [AXI_ADDR_WIDTH-1:0]   M3_ARADDR;         // Read address
    logic [AXI_LEN_WIDTH-1:0]    M3_ARLEN;          // Burst length (0-15)
    logic                        M3_ARLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   M3_ARSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  M3_ARBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  M3_ARCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   M3_ARPROT;         // Protection attributes
    logic                        M3_ARVALID;        // Read address valid
    logic                        M3_ARREADY;        // Read address ready (from slave)
    logic [AXI_QOS_WIDTH-1:0]    M3_ARQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] M3_ARREGION;       // Region identifier
    logic [0:0]                  M3_ARUSER;         // Read-address user path (if enabled)
    
    // ===== READ DATA CHANNEL (R) =====
    logic [AXI_ID_WIDTH-1:0]     M3_RID;            // Read ID (from slave)
    logic [AXI_DATA_WIDTH-1:0]   M3_RDATA;          // Read data (from slave)
    logic [AXI_RESP_WIDTH-1:0]   M3_RRESP;          // Read response (from slave)
    logic                        M3_RLAST;          // Read last (from slave)
    logic                        M3_RVALID;         // Read valid (from slave)
    logic                        M3_RREADY;         // Read ready
    logic [0:0]                  M3_RUSER;          // Read-data user path (if enabled)
    
    // ===== CLOCKING BLOCK =====
    // Clocking block for synchronizing signals to posedge of ACLK
    clocking m3_cb @(posedge ACLK);
        // Write Address Channel (M3 drives, slave receives)
        output M3_AWID, M3_AWADDR, M3_AWLEN, M3_AWLOCK, M3_AWSIZE, M3_AWBURST,
               M3_AWCACHE, M3_AWPROT, M3_AWVALID, M3_AWQOS, M3_AWREGION, M3_AWUSER;
        input  M3_AWREADY;
        
        // Write Data Channel (M3 drives, slave receives)
        output M3_WDATA, M3_WSTRB, M3_WLAST, M3_WVALID, M3_WUSER;
        input  M3_WREADY;
        
        // Write Response Channel (M3 receives, slave drives)
        input  M3_BID, M3_BRESP, M3_BVALID, M3_BUSER;
        output M3_BREADY;
        
        // Read Address Channel (M3 drives, slave receives)
        output M3_ARID, M3_ARADDR, M3_ARLEN, M3_ARLOCK, M3_ARSIZE, M3_ARBURST,
               M3_ARCACHE, M3_ARPROT, M3_ARVALID, M3_ARQOS, M3_ARREGION, M3_ARUSER;
        input  M3_ARREADY;
        
        // Read Data Channel (M3 receives, slave drives)
        input  M3_RID, M3_RDATA, M3_RRESP, M3_RLAST, M3_RVALID, M3_RUSER;
        output M3_RREADY;
    endclocking
    
    // ===== INTERFACE MODPORTS =====
    
    // Driver modport - Uses clocking block for synchronized signal access
    modport driver (
        // Clock and reset (inputs)
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized access (primary interface)
        clocking m3_cb
    );
    
    // Monitor clocking block - For synchronized monitoring at posedge ACLK
    clocking m3_monitor_cb @(posedge ACLK);
        // All signals as inputs for monitoring
        input  M3_AWID, M3_AWADDR, M3_AWLEN, M3_AWLOCK, M3_AWSIZE, M3_AWBURST,
               M3_AWCACHE, M3_AWPROT, M3_AWVALID, M3_AWREADY, M3_AWQOS, M3_AWREGION, M3_AWUSER,
               M3_WDATA, M3_WSTRB, M3_WLAST, M3_WVALID, M3_WREADY, M3_WUSER,
               M3_BID, M3_BRESP, M3_BVALID, M3_BREADY, M3_BUSER,
               M3_ARID, M3_ARADDR, M3_ARLEN, M3_ARLOCK, M3_ARSIZE, M3_ARBURST,
               M3_ARCACHE, M3_ARPROT, M3_ARVALID, M3_ARREADY, M3_ARQOS, M3_ARREGION, M3_ARUSER,
               M3_RID, M3_RDATA, M3_RRESP, M3_RLAST, M3_RVALID, M3_RREADY, M3_RUSER;
    endclocking
    
    // Monitor modport - For passive monitoring with synchronized access
    modport monitor (
        // Clock and reset (inputs)
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized monitoring
        clocking m3_monitor_cb
    );
    
    // ===== INTERFACE TASKS =====
    
    // Task to initialize all signals to default values
    task automatic init_signals();
        // Write Address Channel
        M3_AWID = '0;
        M3_AWADDR = '0;
        M3_AWLEN = '0;
        M3_AWLOCK = '0;
        M3_AWSIZE = '0;
        M3_AWBURST = '0;
        M3_AWCACHE = '0;
        M3_AWPROT = '0;
        M3_AWVALID = '0;
        M3_AWQOS = '0;
        M3_AWREGION = '0;
        M3_AWUSER = '0;
        
        // Write Data Channel
        M3_WDATA = '0;
        M3_WSTRB = '0;
        M3_WLAST = '0;
        M3_WVALID = '0;
        M3_WUSER = '0;
        
        // Write Response Channel
        M3_BREADY = '0;
        
        // Read Address Channel
        M3_ARID = '0;
        M3_ARADDR = '0;
        M3_ARLEN = '0;
        M3_ARLOCK = '0;
        M3_ARSIZE = '0;
        M3_ARBURST = '0;
        M3_ARCACHE = '0;
        M3_ARPROT = '0;
        M3_ARVALID = '0;
        M3_ARQOS = '0;
        M3_ARREGION = '0;
        M3_ARUSER = '0;
        
        // Read Data Channel
        M3_RREADY = '0;
    endtask
    
    // Task to wait for clock edge
    task automatic wait_for_clk();
        @(posedge ACLK);
    endtask
    
    // Task to wait for reset deassertion
    task automatic wait_for_reset();
        wait(ARESETn == 1'b1);
    endtask
    
    // Task to wait for reset assertion
    task automatic wait_for_reset_assert();
        wait(ARESETn == 1'b0);
    endtask
    
    // ===== SIGNAL MONITORING TASKS =====
    
    // Task to monitor write address channel
    task automatic monitor_aw_channel();
        forever begin
            @(posedge ACLK);
            if (M3_AWVALID && M3_AWREADY) begin
                $display("M3 AW: ID=0x%0h, ADDR=0x%0h, LEN=%0d, SIZE=%0d, BURST=%0d, LOCK=%0d, CACHE=0x%0h, PROT=0x%0h, QOS=0x%0h, REGION=0x%0h, USER=0x%0h",
                         M3_AWID, M3_AWADDR, M3_AWLEN, M3_AWSIZE, M3_AWBURST, M3_AWLOCK, 
                         M3_AWCACHE, M3_AWPROT, M3_AWQOS, M3_AWREGION, M3_AWUSER);
            end
        end
    endtask
    
    // Task to monitor write data channel
    task automatic monitor_w_channel();
        forever begin
            @(posedge ACLK);
            if (M3_WVALID && M3_WREADY) begin
                $display("M3 W: DATA=0x%0h, STRB=0x%0h, LAST=%0d, USER=0x%0h",
                         M3_WDATA, M3_WSTRB, M3_WLAST, M3_WUSER);
            end
        end
    endtask
    
    // Task to monitor write response channel
    task automatic monitor_b_channel();
        forever begin
            @(posedge ACLK);
            if (M3_BVALID && M3_BREADY) begin
                $display("M3 B: ID=0x%0h, RESP=0x%0h, USER=0x%0h",
                         M3_BID, M3_BRESP, M3_BUSER);
            end
        end
    endtask
    
    // Task to monitor read address channel
    task automatic monitor_ar_channel();
        forever begin
            @(posedge ACLK);
            if (M3_ARVALID && M3_ARREADY) begin
                $display("M3 AR: ID=0x%0h, ADDR=0x%0h, LEN=%0d, SIZE=%0d, BURST=%0d, LOCK=%0d, CACHE=0x%0h, PROT=0x%0h, QOS=0x%0h, REGION=0x%0h, USER=0x%0h",
                         M3_ARID, M3_ARADDR, M3_ARLEN, M3_ARSIZE, M3_ARBURST, M3_ARLOCK, 
                         M3_ARCACHE, M3_ARPROT, M3_ARQOS, M3_ARREGION, M3_ARUSER);
            end
        end
    endtask
    
    // Task to monitor read data channel
    task automatic monitor_r_channel();
        forever begin
            @(posedge ACLK);
            if (M3_RVALID && M3_RREADY) begin
                $display("M3 R: ID=0x%0h, DATA=0x%0h, RESP=0x%0h, LAST=%0d, USER=0x%0h",
                         M3_RID, M3_RDATA, M3_RRESP, M3_RLAST, M3_RUSER);
            end
        end
    endtask
    
    // ===== INTERFACE ASSERTIONS =====
    
    // Property: AWVALID should not be asserted when AWREADY is low (unless handshake occurs)
    property awvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M3_AWVALID && !M3_AWREADY |-> ##1 M3_AWVALID;
    endproperty
    
    // Property: WVALID should not be asserted when WREADY is low (unless handshake occurs)
    property wvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M3_WVALID && !M3_WREADY |-> ##1 M3_WVALID;
    endproperty
    
    // Property: ARVALID should not be asserted when ARREADY is low (unless handshake occurs)
    property arvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M3_ARVALID && !M3_ARREADY |-> ##1 M3_ARVALID;
    endproperty
    
    // Property: BREADY should not be asserted when BVALID is low (unless handshake occurs)
    property breaddy_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M3_BREADY && !M3_BVALID |-> ##1 M3_BREADY;
    endproperty
    
    // Property: RREADY should not be asserted when RVALID is low (unless handshake occurs)
    property rready_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M3_RREADY && !M3_RVALID |-> ##1 M3_RREADY;
    endproperty
    
    // Assertions
    assert property (awvalid_stable) else
        $error("M3_AWVALID must remain stable until AWREADY is asserted");
    
    assert property (wvalid_stable) else
        $error("M3_WVALID must remain stable until WREADY is asserted");
    
    assert property (arvalid_stable) else
        $error("M3_ARVALID must remain stable until ARREADY is asserted");
    
    assert property (breaddy_stable) else
        $error("M3_BREADY must remain stable until BVALID is asserted");
    
    assert property (rready_stable) else
        $error("M3_RREADY must remain stable until RVALID is asserted");
    
    // ===== INTERFACE INITIALIZATION =====
    initial begin
        init_signals();
    end
    
endinterface : M3_interface

`endif // M3_INTERFACE_SV

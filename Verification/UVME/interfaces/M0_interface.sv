//=============================================================================
// M0 AXI Interface
//=============================================================================
// Interface for Master 0 (M0) AXI signals
// Based on RTL: amba_axi_m4s7.v
// Compatible with M0_seq_item.sv and axi_common_types_pkg.sv
// Note: This interface is specifically for M0; slave interfaces will be created separately
// Features: Clocking block for synchronized signal access at posedge ACLK

interface M0_interface(
    input logic ACLK,
    input logic ARESETn
);
    
        // ===== CLOCK AND RESET =====
    
        
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    logic [AXI_ID_WIDTH-1:0]     M0_AWID;           // Write address ID
    logic [AXI_ADDR_WIDTH-1:0]   M0_AWADDR;         // Write address
    logic [AXI_LEN_WIDTH-1:0]    M0_AWLEN;          // Burst length (0-15)
    logic                        M0_AWLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   M0_AWSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  M0_AWBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  M0_AWCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   M0_AWPROT;         // Protection attributes
    logic                        M0_AWVALID;        // Write address valid
    logic                        M0_AWREADY;        // Write address ready (from slave)
    logic [AXI_QOS_WIDTH-1:0]    M0_AWQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] M0_AWREGION;       // Region identifier
    logic [0:0]                  M0_AWUSER;         // Write-address user path (if enabled)
    
    // ===== WRITE DATA CHANNEL (W) =====
    logic [AXI_DATA_WIDTH-1:0]   M0_WDATA;          // Write data
    logic [AXI_STRB_WIDTH-1:0]   M0_WSTRB;          // Write strobes
    logic                        M0_WLAST;          // Write last
    logic                        M0_WVALID;         // Write valid
    logic                        M0_WREADY;         // Write ready (from slave)
    logic [0:0]                  M0_WUSER;          // Write-data user path (if enabled)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    logic [AXI_ID_WIDTH-1:0]     M0_BID;            // Write response ID (from slave)
    logic [AXI_RESP_WIDTH-1:0]   M0_BRESP;          // Write response (from slave)
    logic                        M0_BVALID;         // Write response valid (from slave)
    logic                        M0_BREADY;         // Write response ready
    logic [0:0]                  M0_BUSER;          // Write-response user path (if enabled)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    logic [AXI_ID_WIDTH-1:0]     M0_ARID;           // Read address ID
    logic [AXI_ADDR_WIDTH-1:0]   M0_ARADDR;         // Read address
    logic [AXI_LEN_WIDTH-1:0]    M0_ARLEN;          // Burst length (0-15)
    logic                        M0_ARLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   M0_ARSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  M0_ARBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  M0_ARCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   M0_ARPROT;         // Protection attributes
    logic                        M0_ARVALID;        // Read address valid
    logic                        M0_ARREADY;        // Read address ready (from slave)
    logic [AXI_QOS_WIDTH-1:0]    M0_ARQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] M0_ARREGION;       // Region identifier
    logic [0:0]                  M0_ARUSER;         // Read-address user path (if enabled)
    
    // ===== READ DATA CHANNEL (R) =====
    logic [AXI_ID_WIDTH-1:0]     M0_RID;            // Read ID (from slave)
    logic [AXI_DATA_WIDTH-1:0]   M0_RDATA;          // Read data (from slave)
    logic [AXI_RESP_WIDTH-1:0]   M0_RRESP;          // Read response (from slave)
    logic                        M0_RLAST;          // Read last (from slave)
    logic                        M0_RVALID;         // Read valid (from slave)
    logic                        M0_RREADY;         // Read ready
    logic [0:0]                  M0_RUSER;          // Read-data user path (if enabled)
    
    // ===== CLOCKING BLOCK =====
    // Clocking block for synchronizing signals to posedge of ACLK
    clocking m0_cb @(posedge ACLK);
        // Write Address Channel (M0 drives, slave receives)
        output M0_AWID, M0_AWADDR, M0_AWLEN, M0_AWLOCK, M0_AWSIZE, M0_AWBURST,
               M0_AWCACHE, M0_AWPROT, M0_AWVALID, M0_AWQOS, M0_AWREGION, M0_AWUSER;
        input  M0_AWREADY;
        
        // Write Data Channel (M0 drives, slave receives)
        output M0_WDATA, M0_WSTRB, M0_WLAST, M0_WVALID, M0_WUSER;
        input  M0_WREADY;
        
        // Write Response Channel (M0 receives, slave drives)
        input  M0_BID, M0_BRESP, M0_BVALID, M0_BUSER;
        output M0_BREADY;
        
        // Read Address Channel (M0 drives, slave receives)
        output M0_ARID, M0_ARADDR, M0_ARLEN, M0_ARLOCK, M0_ARSIZE, M0_ARBURST,
               M0_ARCACHE, M0_ARPROT, M0_ARVALID, M0_ARQOS, M0_ARREGION, M0_ARUSER;
        input  M0_ARREADY;
        
        // Read Data Channel (M0 receives, slave drives)
        input  M0_RID, M0_RDATA, M0_RRESP, M0_RLAST, M0_RVALID, M0_RUSER;
        output M0_RREADY;
    endclocking
    
    // ===== INTERFACE MODPORTS =====
    
    // Driver modport - Uses clocking block for synchronized signal access
    modport driver (
        // Clock and reset (inputs)
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized access (primary interface)
        clocking m0_cb
    );
    
    // Monitor clocking block - For synchronized monitoring at posedge ACLK
    clocking m0_monitor_cb @(posedge ACLK);
        // All signals as inputs for monitoring
        input  M0_AWID, M0_AWADDR, M0_AWLEN, M0_AWLOCK, M0_AWSIZE, M0_AWBURST,
               M0_AWCACHE, M0_AWPROT, M0_AWVALID, M0_AWREADY, M0_AWQOS, M0_AWREGION, M0_AWUSER,
               M0_WDATA, M0_WSTRB, M0_WLAST, M0_WVALID, M0_WREADY, M0_WUSER,
               M0_BID, M0_BRESP, M0_BVALID, M0_BREADY, M0_BUSER,
               M0_ARID, M0_ARADDR, M0_ARLEN, M0_ARLOCK, M0_ARSIZE, M0_ARBURST,
               M0_ARCACHE, M0_ARPROT, M0_ARVALID, M0_ARREADY, M0_ARQOS, M0_ARREGION, M0_ARUSER,
               M0_RID, M0_RDATA, M0_RRESP, M0_RLAST, M0_RVALID, M0_RREADY, M0_RUSER;
    endclocking
    
    // Monitor modport - For passive monitoring with synchronized access
    modport monitor (
        // Clock and reset (inputs)
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized monitoring
        clocking m0_monitor_cb
    );
    
    // ===== INTERFACE TASKS =====
    
    // Task to initialize all signals to default values
    task automatic init_signals();
        // Write Address Channel
        M0_AWID = '0;
        M0_AWADDR = '0;
        M0_AWLEN = '0;
        M0_AWLOCK = '0;
        M0_AWSIZE = '0;
        M0_AWBURST = '0;
        M0_AWCACHE = '0;
        M0_AWPROT = '0;
        M0_AWVALID = '0;
        M0_AWQOS = '0;
        M0_AWREGION = '0;
        M0_AWUSER = '0;
        
        // Write Data Channel
        M0_WDATA = '0;
        M0_WSTRB = '0;
        M0_WLAST = '0;
        M0_WVALID = '0;
        M0_WUSER = '0;
        
        // Write Response Channel
        M0_BREADY = '0;
        
        // Read Address Channel
        M0_ARID = '0;
        M0_ARADDR = '0;
        M0_ARLEN = '0;
        M0_ARLOCK = '0;
        M0_ARSIZE = '0;
        M0_ARBURST = '0;
        M0_ARCACHE = '0;
        M0_ARPROT = '0;
        M0_ARVALID = '0;
        M0_ARQOS = '0;
        M0_ARREGION = '0;
        M0_ARUSER = '0;
        
        // Read Data Channel
        M0_RREADY = '0;
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
            if (M0_AWVALID && M0_AWREADY) begin
                $display("M0 AW: ID=0x%0h, ADDR=0x%0h, LEN=%0d, SIZE=%0d, BURST=%0d, LOCK=%0d, CACHE=0x%0h, PROT=0x%0h, QOS=0x%0h, REGION=0x%0h, USER=0x%0h",
                         M0_AWID, M0_AWADDR, M0_AWLEN, M0_AWSIZE, M0_AWBURST, M0_AWLOCK, 
                         M0_AWCACHE, M0_AWPROT, M0_AWQOS, M0_AWREGION, M0_AWUSER);
            end
        end
    endtask
    
    // Task to monitor write data channel
    task automatic monitor_w_channel();
        forever begin
            @(posedge ACLK);
            if (M0_WVALID && M0_WREADY) begin
                $display("M0 W: DATA=0x%0h, STRB=0x%0h, LAST=%0d, USER=0x%0h",
                         M0_WDATA, M0_WSTRB, M0_WLAST, M0_WUSER);
            end
        end
    endtask
    
    // Task to monitor write response channel
    task automatic monitor_b_channel();
        forever begin
            @(posedge ACLK);
            if (M0_BVALID && M0_BREADY) begin
                $display("M0 B: ID=0x%0h, RESP=0x%0h, USER=0x%0h",
                         M0_BID, M0_BRESP, M0_BUSER);
            end
        end
    endtask
    
    // Task to monitor read address channel
    task automatic monitor_ar_channel();
        forever begin
            @(posedge ACLK);
            if (M0_ARVALID && M0_ARREADY) begin
                $display("M0 AR: ID=0x%0h, ADDR=0x%0h, LEN=%0d, SIZE=%0d, BURST=%0d, LOCK=%0d, CACHE=0x%0h, PROT=0x%0h, QOS=0x%0h, REGION=0x%0h, USER=0x%0h",
                         M0_ARID, M0_ARADDR, M0_ARLEN, M0_ARSIZE, M0_ARBURST, M0_ARLOCK, 
                         M0_ARCACHE, M0_ARPROT, M0_ARQOS, M0_ARREGION, M0_ARUSER);
            end
        end
    endtask
    
    // Task to monitor read data channel
    task automatic monitor_r_channel();
        forever begin
            @(posedge ACLK);
            if (M0_RVALID && M0_RREADY) begin
                $display("M0 R: ID=0x%0h, DATA=0x%0h, RESP=0x%0h, LAST=%0d, USER=0x%0h",
                         M0_RID, M0_RDATA, M0_RRESP, M0_RLAST, M0_RUSER);
            end
        end
    endtask
    
    // ===== INTERFACE ASSERTIONS =====
    
    // Property: AWVALID should not be asserted when AWREADY is low (unless handshake occurs)
    property awvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M0_AWVALID && !M0_AWREADY |-> ##1 M0_AWVALID;
    endproperty
    
    // Property: WVALID should not be asserted when WREADY is low (unless handshake occurs)
    property wvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M0_WVALID && !M0_WREADY |-> ##1 M0_WVALID;
    endproperty
    
    // Property: ARVALID should not be asserted when ARREADY is low (unless handshake occurs)
    property arvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M0_ARVALID && !M0_ARREADY |-> ##1 M0_ARVALID;
    endproperty
    
    // Property: BREADY should not be asserted when BVALID is low (unless handshake occurs)
    property breaddy_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M0_BREADY && !M0_BVALID |-> ##1 M0_BREADY;
    endproperty
    
    // Property: RREADY should not be asserted when RVALID is low (unless handshake occurs)
    property rready_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M0_RREADY && !M0_RVALID |-> ##1 M0_RREADY;
    endproperty
    
    // Assertions
    assert property (awvalid_stable) else
        $error("M0_AWVALID must remain stable until AWREADY is asserted");
    
    assert property (wvalid_stable) else
        $error("M0_WVALID must remain stable until WREADY is asserted");
    
    assert property (arvalid_stable) else
        $error("M0_ARVALID must remain stable until ARREADY is asserted");
    
    assert property (breaddy_stable) else
        $error("M0_BREADY must remain stable until BVALID is asserted");
    
    assert property (rready_stable) else
        $error("M0_RREADY must remain stable until RVALID is asserted");
    
    // ===== INTERFACE INITIALIZATION =====
    initial begin
        init_signals();
    end
    
endinterface : M0_interface

`endif // M0_INTERFACE_SV

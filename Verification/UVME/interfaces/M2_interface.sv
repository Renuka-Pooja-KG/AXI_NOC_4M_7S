//=============================================================================
// M2 AXI Interface
//=============================================================================
// Interface for Master 2 (M2) AXI signals
// Based on RTL: amba_axi_m4s7.v
// Compatible with M2_seq_item.sv and axi_common_types_pkg.sv
// Note: This interface is specifically for M2; slave interfaces will be created separately
// Features: Clocking block for synchronized signal access at posedge ACLK


`ifndef M2_INTERFACE_SV
`define M2_INTERFACE_SV

interface M2_interface(
    input logic ACLK,
    input logic ARESETn
);
    import axi_common_types_pkg::*;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    logic [AXI_ID_WIDTH-1:0]     M2_AWID;           // Write address ID
    logic [AXI_ADDR_WIDTH-1:0]   M2_AWADDR;         // Write address
    logic [AXI_LEN_WIDTH-1:0]    M2_AWLEN;          // Burst length (0-15)
    logic                        M2_AWLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   M2_AWSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  M2_AWBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  M2_AWCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   M2_AWPROT;         // Protection attributes
    logic                        M2_AWVALID;        // Write address valid
    logic                        M2_AWREADY;        // Write address ready (from slave)
    logic [AXI_QOS_WIDTH-1:0]    M2_AWQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] M2_AWREGION;       // Region identifier
    logic [0:0]                  M2_AWUSER;         // Write-address user path (if enabled)
    
    // ===== WRITE DATA CHANNEL (W) =====
    logic [AXI_DATA_WIDTH-1:0]   M2_WDATA;          // Write data
    logic [AXI_STRB_WIDTH-1:0]   M2_WSTRB;          // Write strobes
    logic                        M2_WLAST;          // Write last
    logic                        M2_WVALID;         // Write valid
    logic                        M2_WREADY;         // Write ready (from slave)
    logic [0:0]                  M2_WUSER;          // Write-data user path (if enabled)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    logic [AXI_ID_WIDTH-1:0]     M2_BID;            // Write response ID (from slave)
    logic [AXI_RESP_WIDTH-1:0]   M2_BRESP;          // Write response (from slave)
    logic                        M2_BVALID;         // Write response valid (from slave)
    logic                        M2_BREADY;         // Write response ready
    logic [0:0]                  M2_BUSER;          // Write-response user path (if enabled)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    logic [AXI_ID_WIDTH-1:0]     M2_ARID;           // Read address ID
    logic [AXI_ADDR_WIDTH-1:0]   M2_ARADDR;         // Read address
    logic [AXI_LEN_WIDTH-1:0]    M2_ARLEN;          // Burst length (0-15)
    logic                        M2_ARLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   M2_ARSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  M2_ARBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  M2_ARCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   M2_ARPROT;         // Protection attributes
    logic                        M2_ARVALID;        // Read address valid
    logic                        M2_ARREADY;        // Read address ready (from slave)
    logic [AXI_QOS_WIDTH-1:0]    M2_ARQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] M2_ARREGION;       // Region identifier
    logic [0:0]                  M2_ARUSER;         // Read-address user path (if enabled)
    
    // ===== READ DATA CHANNEL (R) =====
    logic [AXI_ID_WIDTH-1:0]     M2_RID;            // Read ID (from slave)
    logic [AXI_DATA_WIDTH-1:0]   M2_RDATA;          // Read data (from slave)
    logic [AXI_RESP_WIDTH-1:0]   M2_RRESP;          // Read response (from slave)
    logic                        M2_RLAST;          // Read last (from slave)
    logic                        M2_RVALID;         // Read valid (from slave)
    logic                        M2_RREADY;         // Read ready
    logic [0:0]                  M2_RUSER;          // Read-data user path (if enabled)
    
    // ===== CLOCKING BLOCK =====
    // Clocking block for synchronizing signals to posedge of ACLK
    clocking m2_cb @(posedge ACLK);
        // Write Address Channel (M2 drives, slave receives)
        output M2_AWID, M2_AWADDR, M2_AWLEN, M2_AWLOCK, M2_AWSIZE, M2_AWBURST,
               M2_AWCACHE, M2_AWPROT, M2_AWVALID, M2_AWQOS, M2_AWREGION, M2_AWUSER;
        input  M2_AWREADY;
        
        // Write Data Channel (M2 drives, slave receives)
        output M2_WDATA, M2_WSTRB, M2_WLAST, M2_WVALID, M2_WUSER;
        input  M2_WREADY;
        
        // Write Response Channel (M2 receives, slave drives)
        input  M2_BID, M2_BRESP, M2_BVALID, M2_BUSER;
        output M2_BREADY;
        
        // Read Address Channel (M2 drives, slave receives)
        output M2_ARID, M2_ARADDR, M2_ARLEN, M2_ARLOCK, M2_ARSIZE, M2_ARBURST,
               M2_ARCACHE, M2_ARPROT, M2_ARVALID, M2_ARQOS, M2_ARREGION, M2_ARUSER;
        input  M2_ARREADY;
        
        // Read Data Channel (M2 receives, slave drives)
        input  M2_RID, M2_RDATA, M2_RRESP, M2_RLAST, M2_RVALID, M2_RUSER;
        output M2_RREADY;
    endclocking
    
    // ===== INTERFACE MODPORTS =====
    
    // Driver modport - Uses clocking block for synchronized signal access
    modport driver (
        // Clock and reset (inputs)
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized access (primary interface)
        clocking m2_cb
    );
    
    // Monitor clocking block - For synchronized monitoring at posedge ACLK
    clocking m2_monitor_cb @(posedge ACLK);
        // All signals as inputs for monitoring
        input  M2_AWID, M2_AWADDR, M2_AWLEN, M2_AWLOCK, M2_AWSIZE, M2_AWBURST,
               M2_AWCACHE, M2_AWPROT, M2_AWVALID, M2_AWREADY, M2_AWQOS, M2_AWREGION, M2_AWUSER,
               M2_WDATA, M2_WSTRB, M2_WLAST, M2_WVALID, M2_WREADY, M2_WUSER,
               M2_BID, M2_BRESP, M2_BVALID, M2_BREADY, M2_BUSER,
               M2_ARID, M2_ARADDR, M2_ARLEN, M2_ARLOCK, M2_ARSIZE, M2_ARBURST,
               M2_ARCACHE, M2_ARPROT, M2_ARVALID, M2_ARREADY, M2_ARQOS, M2_ARREGION, M2_ARUSER,
               M2_RID, M2_RDATA, M2_RRESP, M2_RLAST, M2_RVALID, M2_RREADY, M2_RUSER;
    endclocking
    
    // Monitor modport - For passive monitoring with synchronized access
    modport monitor (
        // Clock and reset (inputs)
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized monitoring
        clocking m2_monitor_cb
    );
    
    // ===== INTERFACE TASKS =====
    
    // Task to initialize all signals to default values
    task automatic init_signals();
        // Write Address Channel
        M2_AWID = '0;
        M2_AWADDR = '0;
        M2_AWLEN = '0;
        M2_AWLOCK = '0;
        M2_AWSIZE = '0;
        M2_AWBURST = '0;
        //M2_AWCACHE = '0;
        M2_AWPROT = '0;
        M2_AWVALID = '0;
        M2_AWQOS = '0;
        M2_AWREGION = '0;
        //M2_AWUSER = '0;
        
        // Write Data Channel
        M2_WDATA = '0;
        M2_WSTRB = '0;
        M2_WLAST = '0;
        M2_WVALID = '0;
        //M2_WUSER = '0;
        
        // Write Response Channel
        M2_BREADY = '0;
        
        // Read Address Channel
        M2_ARID = '0;
        M2_ARADDR = '0;
        M2_ARLEN = '0;
        M2_ARLOCK = '0;
        M2_ARSIZE = '0;
        M2_ARBURST = '0;
        //M2_ARCACHE = '0;
        M2_ARPROT = '0;
        M2_ARVALID = '0;
        M2_ARQOS = '0;
        M2_ARREGION = '0;
        //M2_ARUSER = '0;
        
        // Read Data Channel
        M2_RREADY = '0;
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
            if (M2_AWVALID && M2_AWREADY) begin
                $display("M2 AW: ID=0x%0h, ADDR=0x%0h, LEN=%0d, SIZE=%0d, BURST=%0d, LOCK=%0d, CACHE=0x%0h, PROT=0x%0h, QOS=0x%0h, REGION=0x%0h, USER=0x%0h",
                         M2_AWID, M2_AWADDR, M2_AWLEN, M2_AWSIZE, M2_AWBURST, M2_AWLOCK, 
                         M2_AWCACHE, M2_AWPROT, M2_AWQOS, M2_AWREGION, M2_AWUSER);
            end
        end
    endtask
    
    // Task to monitor write data channel
    task automatic monitor_w_channel();
        forever begin
            @(posedge ACLK);
            if (M2_WVALID && M2_WREADY) begin
                $display("M2 W: DATA=0x%0h, STRB=0x%0h, LAST=%0d, USER=0x%0h",
                         M2_WDATA, M2_WSTRB, M2_WLAST, M2_WUSER);
            end
        end
    endtask
    
    // Task to monitor write response channel
    task automatic monitor_b_channel();
        forever begin
            @(posedge ACLK);
            if (M2_BVALID && M2_BREADY) begin
                $display("M2 B: ID=0x%0h, RESP=0x%0h, USER=0x%0h",
                         M2_BID, M2_BRESP, M2_BUSER);
            end
        end
    endtask
    
    // Task to monitor read address channel
    task automatic monitor_ar_channel();
        forever begin
            @(posedge ACLK);
            if (M2_ARVALID && M2_ARREADY) begin
                $display("M2 AR: ID=0x%0h, ADDR=0x%0h, LEN=%0d, SIZE=%0d, BURST=%0d, LOCK=%0d, CACHE=0x%0h, PROT=0x%0h, QOS=0x%0h, REGION=0x%0h, USER=0x%0h",
                         M2_ARID, M2_ARADDR, M2_ARLEN, M2_ARSIZE, M2_ARBURST, M2_ARLOCK, 
                         M2_ARCACHE, M2_ARPROT, M2_ARQOS, M2_ARREGION, M2_ARUSER);
            end
        end
    endtask
    
    // Task to monitor read data channel
    task automatic monitor_r_channel();
        forever begin
            @(posedge ACLK);
            if (M2_RVALID && M2_RREADY) begin
                $display("M2 R: ID=0x%0h, DATA=0x%0h, RESP=0x%0h, LAST=%0d, USER=0x%0h",
                         M2_RID, M2_RDATA, M2_RRESP, M2_RLAST, M2_RUSER);
            end
        end
    endtask
    
    // ===== INTERFACE ASSERTIONS =====
    
    // Property: AWVALID should not be asserted when AWREADY is low (unless handshake occurs)
    property awvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M2_AWVALID && !M2_AWREADY |-> ##1 M2_AWVALID;
    endproperty
    
    // Property: WVALID should not be asserted when WREADY is low (unless handshake occurs)
    property wvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M2_WVALID && !M2_WREADY |-> ##1 M2_WVALID;
    endproperty
    
    // Property: ARVALID should not be asserted when ARREADY is low (unless handshake occurs)
    property arvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M2_ARVALID && !M2_ARREADY |-> ##1 M2_ARVALID;
    endproperty
    
    // Property: BREADY should not be asserted when BVALID is low (unless handshake occurs)
    property breaddy_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M2_BREADY && !M2_BVALID |-> ##1 M2_BREADY;
    endproperty
    
    // Property: RREADY should not be asserted when RVALID is low (unless handshake occurs)
    property rready_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        M2_RREADY && !M2_RVALID |-> ##1 M2_RREADY;
    endproperty
    
    // Assertions
    assert property (awvalid_stable) else
        $error("M2_AWVALID must remain stable until AWREADY is asserted");
    
    assert property (wvalid_stable) else
        $error("M2_WVALID must remain stable until WREADY is asserted");
    
    assert property (arvalid_stable) else
        $error("M2_ARVALID must remain stable until ARREADY is asserted");
    
    assert property (breaddy_stable) else
        $error("M2_BREADY must remain stable until BVALID is asserted");
    
    assert property (rready_stable) else
        $error("M2_RREADY must remain stable until RVALID is asserted");
    
    // ===== INTERFACE INITIALIZATION =====
    initial begin
        init_signals();
    end
    
endinterface : M2_interface

`endif // M2_INTERFACE_SV

//=============================================================================
// M1 AXI Interface
//=============================================================================
// Interface for Master 1 (M1) AXI signals
// Based on RTL: amba_axi_m4s7.v
// Compatible with M1_seq_item.sv and axi_common_types_pkg.sv
// Note: This interface is specifically for M1; slave interfaces will be created separately
// Features: Clocking block for synchronized signal access at posedge ACLK

`ifndef M1_INTERFACE_SV
`define M1_INTERFACE_SV

interface M1_interface(
    input logic ACLK,
    input logic ARESETn
);
    
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    logic [AXI_ID_WIDTH-1:0]     M1_AWID;           // Write address ID
    logic [AXI_ADDR_WIDTH-1:0]   M1_AWADDR;         // Write address
    logic [AXI_LEN_WIDTH-1:0]    M1_AWLEN;          // Burst length (0-15)
    logic                        M1_AWLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   M1_AWSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  M1_AWBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  M1_AWCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   M1_AWPROT;         // Protection attributes
    logic                        M1_AWVALID;        // Write address valid
    logic                        M1_AWREADY;        // Write address ready (from slave)
    logic [AXI_QOS_WIDTH-1:0]    M1_AWQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] M1_AWREGION;       // Region identifier
    logic [0:0]                  M1_AWUSER;         // Write-address user path (if enabled)
    
    // ===== WRITE DATA CHANNEL (W) =====
    logic [AXI_DATA_WIDTH-1:0]   M1_WDATA;          // Write data
    logic [AXI_STRB_WIDTH-1:0]   M1_WSTRB;          // Write strobes
    logic                        M1_WLAST;          // Write last
    logic                        M1_WVALID;         // Write valid
    logic                        M1_WREADY;         // Write ready (from slave)
    logic [0:0]                  M1_WUSER;          // Write-data user path (if enabled)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    logic [AXI_ID_WIDTH-1:0]     M1_BID;            // Write response ID (from slave)
    logic [AXI_RESP_WIDTH-1:0]   M1_BRESP;          // Write response (from slave)
    logic                        M1_BVALID;         // Write response valid (from slave)
    logic                        M1_BREADY;         // Write response ready
    logic [0:0]                  M1_BUSER;          // Write-response user path (if enabled)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    logic [AXI_ID_WIDTH-1:0]     M1_ARID;           // Read address ID
    logic [AXI_ADDR_WIDTH-1:0]   M1_ARADDR;         // Read address
    logic [AXI_LEN_WIDTH-1:0]    M1_ARLEN;          // Burst length (0-15)
    logic                        M1_ARLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   M1_ARSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  M1_ARBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  M1_ARCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   M1_ARPROT;         // Protection attributes
    logic                        M1_ARVALID;        // Read address valid
    logic                        M1_ARREADY;        // Read address ready (from slave)
    logic [AXI_QOS_WIDTH-1:0]    M1_ARQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] M1_ARREGION;       // Region identifier
    logic [0:0]                  M1_ARUSER;         // Read-address user path (if enabled)
    
    // ===== READ DATA CHANNEL (R) =====
    logic [AXI_ID_WIDTH-1:0]     M1_RID;            // Read ID (from slave)
    logic [AXI_DATA_WIDTH-1:0]   M1_RDATA;          // Read data (from slave)
    logic [AXI_RESP_WIDTH-1:0]   M1_RRESP;          // Read response (from slave)
    logic                        M1_RLAST;          // Read last (from slave)
    logic                        M1_RVALID;         // Read valid (from slave)
    logic                        M1_RREADY;         // Read ready
    logic [0:0]                  M1_RUSER;          // Read-data user path (if enabled)
    
    // ===== CLOCKING BLOCK =====
    // Clocking block for synchronizing signals to posedge of ACLK
    // Note: ACLK and ARESETn are NOT in clocking blocks - they are interface-level signals
    clocking m1_cb @(posedge ACLK);
        // Write Address Channel (M1 drives, slave receives)
        output M1_AWID, M1_AWADDR, M1_AWLEN, M1_AWLOCK, M1_AWSIZE, M1_AWBURST,
               M1_AWCACHE, M1_AWPROT, M1_AWVALID, M1_AWQOS, M1_AWREGION, M1_AWUSER;
        input  M1_AWREADY;
        
        // Write Data Channel (M1 drives, slave receives)
        output M1_WDATA, M1_WSTRB, M1_WLAST, M1_WVALID, M1_WUSER;
        input  M1_WREADY;
        
        // Write Response Channel (M1 receives, slave drives)
        input  M1_BID, M1_BRESP, M1_BVALID, M1_BUSER;
        output M1_BREADY;
        
        // Read Address Channel (M1 drives, slave receives)
        output M1_ARID, M1_ARADDR, M1_ARLEN, M1_ARLOCK, M1_ARSIZE, M1_ARBURST,
               M1_ARCACHE, M1_ARPROT, M1_ARVALID, M1_ARQOS, M1_ARREGION, M1_ARUSER;
        input  M1_ARREADY;
        
        // Read Data Channel (M1 receives, slave drives)
        input  M1_RID, M1_RDATA, M1_RRESP, M1_RLAST, M1_RVALID, M1_RUSER;
        output M1_RREADY;
    endclocking
    
    // ===== INTERFACE MODPORTS =====
    
    // Driver modport - Uses clocking block for synchronized signal access
    modport driver (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized access (primary interface)
        clocking m1_cb
    );
    
    // Monitor clocking block - For synchronized monitoring at posedge ACLK
    clocking m1_monitor_cb @(posedge ACLK);
        // All signals as inputs for monitoring
        input  M1_AWID, M1_AWADDR, M1_AWLEN, M1_AWLOCK, M1_AWSIZE, M1_AWBURST,
               M1_AWCACHE, M1_AWPROT, M1_AWVALID, M1_AWREADY, M1_AWQOS, M1_AWREGION, M1_AWUSER,
               M1_WDATA, M1_WSTRB, M1_WLAST, M1_WVALID, M1_WREADY, M1_WUSER,
               M1_BID, M1_BRESP, M1_BVALID, M1_BREADY, M1_BUSER,
               M1_ARID, M1_ARADDR, M1_ARLEN, M1_ARLOCK, M1_ARSIZE, M1_ARBURST,
               M1_ARCACHE, M1_ARPROT, M1_ARVALID, M1_ARREADY, M1_ARQOS, M1_ARREGION, M1_ARUSER,
               M1_RID, M1_RDATA, M1_RRESP, M1_RLAST, M1_RVALID, M1_RREADY, M1_RUSER;
    endclocking
    
    // Monitor modport - For passive monitoring with synchronized access
    modport monitor (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized monitoring
        clocking m1_monitor_cb
    );
    
    // ===== INTERFACE TASKS =====
    
    // Task to initialize all signals to default values
    task automatic init_signals();
        // Write Address Channel - M1 drives these
        M1_AWID = '0;
        M1_AWADDR = '0;
        M1_AWLEN = '0;
        M1_AWLOCK = '0;
        M1_AWSIZE = '0;
        M1_AWBURST = '0;
        M1_AWCACHE = '0;
        M1_AWPROT = '0;
        M1_AWVALID = '0;
        M1_AWQOS = '0;
        M1_AWREGION = '0;
        M1_AWUSER = '0;
        M1_AWREADY = '0;  // M1 receives this
        
        // Write Data Channel - M1 drives these
        M1_WDATA = '0;
        M1_WSTRB = '0;
        M1_WLAST = '0;
        M1_WVALID = '0;
        M1_WUSER = '0;
        M1_WREADY = '0;  // M1 receives this
        
        // Write Response Channel - M1 receives these
        M1_BID = '0;
        M1_BRESP = '0;
        M1_BVALID = '0;
        M1_BREADY = '0;  // M1 drives this
        M1_BUSER = '0;
        
        // Read Address Channel - M1 drives these
        M1_ARID = '0;
        M1_ARADDR = '0;
        M1_ARLEN = '0;
        M1_ARLOCK = '0;
        M1_ARSIZE = '0;
        M1_ARBURST = '0;
        M1_ARCACHE = '0;
        M1_ARPROT = '0;
        M1_ARVALID = '0;
        M1_ARQOS = '0;
        M1_ARREGION = '0;
        M1_ARUSER = '0;
        M1_ARREADY = '0;  // M1 receives this
        
        // Read Data Channel - M1 receives these
        M1_RID = '0;
        M1_RDATA = '0;
        M1_RRESP = '0;
        M1_RLAST = '0;
        M1_RVALID = '0;
        M1_RREADY = '0;  // M1 drives this
        M1_RUSER = '0;
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
    
    // ===== INTERFACE INITIALIZATION =====
    initial begin
        init_signals();
    end
    
endinterface : M1_interface

`endif // M1_INTERFACE_SV
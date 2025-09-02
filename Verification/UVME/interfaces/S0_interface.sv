//=============================================================================
// S0 AXI Interface
//=============================================================================
// Interface for Slave 0 (S0) AXI signals
// Based on RTL: amba_axi_m4s7.v
// Compatible with S0_seq_item.sv and axi_common_types_pkg.sv
// Note: This interface is specifically for S0; master interfaces are created separately
// Features: Clocking block for synchronized signal access at posedge ACLK

`ifndef S0_INTERFACE_SV
`define S0_INTERFACE_SV

interface S0_interface(
    input logic ACLK,
    input logic ARESETn
);
    import axi_common_types_pkg::*;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S0 receives these signals from masters
    logic [AXI_SID_WIDTH-1:0]     S0_AWID;           // Write address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S0_AWADDR;         // Write address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S0_AWLEN;          // Burst length (0-15)
    logic                        S0_AWLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S0_AWSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S0_AWBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S0_AWCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S0_AWPROT;         // Protection attributes
    logic                        S0_AWVALID;        // Write address valid (from master)
    logic                        S0_AWREADY;        // Write address ready (S0 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S0_AWQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S0_AWREGION;       // Region identifier
    logic [0:0]                  S0_AWUSER;         // Write-address user path (if enabled)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S0 receives these signals from masters
    logic [AXI_DATA_WIDTH-1:0]   S0_WDATA;          // Write data (from master)
    logic [AXI_STRB_WIDTH-1:0]   S0_WSTRB;          // Write strobes (from master)
    logic                        S0_WLAST;          // Write last (from master)
    logic                        S0_WVALID;         // Write valid (from master)
    logic                        S0_WREADY;         // Write ready (S0 drives this)
    logic [0:0]                  S0_WUSER;          // Write-data user path (if enabled)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S0 drives these signals to masters
    logic [AXI_SID_WIDTH-1:0]     S0_BID;            // Write response ID (S0 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S0_BRESP;          // Write response (S0 drives this)
    logic                        S0_BVALID;         // Write response valid (S0 drives this)
    logic                        S0_BREADY;         // Write response ready (from master)
    logic [0:0]                  S0_BUSER;          // Write-response user path (if enabled)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S0 receives these signals from masters
    logic [AXI_SID_WIDTH-1:0]     S0_ARID;           // Read address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S0_ARADDR;         // Read address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S0_ARLEN;          // Burst length (0-15)
    logic                        S0_ARLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S0_ARSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S0_ARBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S0_ARCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S0_ARPROT;         // Protection attributes
    logic                        S0_ARVALID;        // Read address valid (from master)
    logic                        S0_ARREADY;        // Read address ready (S0 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S0_ARQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S0_ARREGION;       // Region identifier
    logic [0:0]                  S0_ARUSER;         // Read-address user path (if enabled)
    
    // ===== READ DATA CHANNEL (R) =====
    // S0 drives these signals to masters
    logic [AXI_SID_WIDTH-1:0]     S0_RID;            // Read ID (S0 drives this)
    logic [AXI_DATA_WIDTH-1:0]   S0_RDATA;          // Read data (S0 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S0_RRESP;          // Read response (S0 drives this)
    logic                        S0_RLAST;          // Read last (S0 drives this)
    logic                        S0_RVALID;         // Read valid (S0 drives this)
    logic                        S0_RREADY;         // Read ready (from master)
    logic [0:0]                  S0_RUSER;          // Read-data user path (if enabled)
    
    // ===== CLOCKING BLOCK =====
    // Clocking block for synchronizing signals to posedge of ACLK
    // Note: ACLK and ARESETn are NOT in clocking blocks - they are interface-level signals
    clocking s0_cb @(posedge ACLK);
        // Write Address Channel (S0 receives from master, drives AWREADY)
        input  S0_AWID, S0_AWADDR, S0_AWLEN, S0_AWLOCK, S0_AWSIZE, S0_AWBURST,
               S0_AWCACHE, S0_AWPROT, S0_AWVALID, S0_AWQOS, S0_AWREGION, S0_AWUSER;
        output S0_AWREADY;
        
        // Write Data Channel (S0 receives from master, drives WREADY)
        input  S0_WDATA, S0_WSTRB, S0_WLAST, S0_WVALID, S0_WUSER;
        output S0_WREADY;
        
        // Write Response Channel (S0 drives to master, receives BREADY)
        output S0_BID, S0_BRESP, S0_BVALID, S0_BUSER;
        input  S0_BREADY;
        
        // Read Address Channel (S0 receives from master, drives ARREADY)
        input  S0_ARID, S0_ARADDR, S0_ARLEN, S0_ARLOCK, S0_ARSIZE, S0_ARBURST,
               S0_ARCACHE, S0_ARPROT, S0_ARVALID, S0_ARQOS, S0_ARREGION, S0_ARUSER;
        output S0_ARREADY;
        
        // Read Data Channel (S0 drives to master, receives RREADY)
        output S0_RID, S0_RDATA, S0_RRESP, S0_RLAST, S0_RVALID, S0_RUSER;
        input  S0_RREADY;
    endclocking
    
    // ===== INTERFACE MODPORTS =====
    
    // Driver modport - For S0 driver (S0 responds to master requests)
    modport driver (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized access (primary interface)
        clocking s0_cb
    );
    
    // Monitor clocking block - For synchronized monitoring at posedge ACLK
    clocking s0_monitor_cb @(posedge ACLK);
        // All signals as inputs for monitoring
        input  S0_AWID, S0_AWADDR, S0_AWLEN, S0_AWLOCK, S0_AWSIZE, S0_AWBURST,
               S0_AWCACHE, S0_AWPROT, S0_AWVALID, S0_AWREADY, S0_AWQOS, S0_AWREGION, S0_AWUSER,
               S0_WDATA, S0_WSTRB, S0_WLAST, S0_WVALID, S0_WREADY, S0_WUSER,
               S0_BID, S0_BRESP, S0_BVALID, S0_BREADY, S0_BUSER,
               S0_ARID, S0_ARADDR, S0_ARLEN, S0_ARLOCK, S0_ARSIZE, S0_ARBURST,
               S0_ARCACHE, S0_ARPROT, S0_ARVALID, S0_ARREADY, S0_ARQOS, S0_ARREGION, S0_ARUSER,
               S0_RID, S0_RDATA, S0_RRESP, S0_RLAST, S0_RVALID, S0_RREADY, S0_RUSER;
    endclocking
    
    // Monitor modport - For passive monitoring with synchronized access
    modport monitor (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized monitoring
        clocking s0_monitor_cb
    );
    
    // ===== INTERFACE TASKS =====
    
    // Task to initialize all signals to default values
    task automatic init_signals();
        // Write Address Channel - S0 receives these (INPUT signals), DO NOT initialize
        // S0_AWID = '0;      // REMOVED: S0 receives this (INPUT signal)
        // S0_AWADDR = '0;    // REMOVED: S0 receives this (INPUT signal)
        // S0_AWLEN = '0;     // REMOVED: S0 receives this (INPUT signal)
        // S0_AWLOCK = '0;    // REMOVED: S0 receives this (INPUT signal)
        // S0_AWSIZE = '0;    // REMOVED: S0 receives this (INPUT signal)
        // S0_AWBURST = '0;   // REMOVED: S0 receives this (INPUT signal)
        // S0_AWCACHE = '0;   // REMOVED: S0 receives this (INPUT signal)
        // S0_AWPROT = '0;    // REMOVED: S0 receives this (INPUT signal)
        // S0_AWVALID = '0;   // REMOVED: S0 receives this (INPUT signal)
        // S0_AWQOS = '0;     // REMOVED: S0 receives this (INPUT signal)
        // S0_AWREGION = '0;  // REMOVED: S0 receives this (INPUT signal)
        // S0_AWUSER = '0;    // REMOVED: S0 receives this (INPUT signal)
        S0_AWREADY = '0;  // S0 drives this (OUTPUT signal)
        
        // Write Data Channel - S0 receives these (INPUT signals), DO NOT initialize
        // S0_WDATA = '0;     // REMOVED: S0 receives this (INPUT signal)
        // S0_WSTRB = '0;     // REMOVED: S0 receives this (INPUT signal)
        // S0_WLAST = '0;     // REMOVED: S0 receives this (INPUT signal)
        // S0_WVALID = '0;    // REMOVED: S0 receives this (INPUT signal)
        // S0_WUSER = '0;     // REMOVED: S0 receives this (INPUT signal)
        S0_WREADY = '0;   // S0 drives this (OUTPUT signal)
        
        // Write Response Channel - S0 drives these signals (OUTPUT signals)
        S0_BID = '0;      // S0 drives this (OUTPUT signal)
        S0_BRESP = '0;    // S0 drives this (OUTPUT signal)
        S0_BVALID = '0;   // S0 drives this (OUTPUT signal)
        // S0_BREADY = '0;   // REMOVED: S0 receives this (INPUT signal)
        S0_BUSER = '0;    // S0 drives this (OUTPUT signal)
        
        // Read Address Channel - S0 receives these (INPUT signals), DO NOT initialize
        // S0_ARID = '0;     // REMOVED: S0 receives this (INPUT signal)
        // S0_ARADDR = '0;   // REMOVED: S0 receives this (INPUT signal)
        // S0_ARLEN = '0;    // REMOVED: S0 receives this (INPUT signal)
        // S0_ARLOCK = '0;   // REMOVED: S0 receives this (INPUT signal)
        // S0_ARSIZE = '0;   // REMOVED: S0 receives this (INPUT signal)
        // S0_ARBURST = '0;  // REMOVED: S0 receives this (INPUT signal)
        // S0_ARCACHE = '0;  // REMOVED: S0 receives this (INPUT signal)
        // S0_ARPROT = '0;   // REMOVED: S0 receives this (INPUT signal)
        // S0_ARVALID = '0;  // REMOVED: S0 receives this (INPUT signal)
        // S0_ARQOS = '0;    // REMOVED: S0 receives this (INPUT signal)
        // S0_ARREGION = '0; // REMOVED: S0 receives this (INPUT signal)
        // S0_ARUSER = '0;   // REMOVED: S0 receives this (INPUT signal)
        S0_ARREADY = '0;  // S0 drives this (OUTPUT signal)
        
        // Read Data Channel - S0 drives these signals (OUTPUT signals)
        S0_RID = '0;      // S0 drives this (OUTPUT signal)
        S0_RDATA = '0;    // S0 drives this (OUTPUT signal)
        S0_RRESP = '0;    // S0 drives this (OUTPUT signal)
        S0_RLAST = '0;    // S0 drives this (OUTPUT signal)
        S0_RVALID = '0;   // S0 drives this (OUTPUT signal)
        // S0_RREADY = '0;   // REMOVED: S0 receives this (INPUT signal)
       // S0_RUSER = '0;    // S0 drives this (OUTPUT signal)
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
    
endinterface : S0_interface

`endif // S0_INTERFACE_SV


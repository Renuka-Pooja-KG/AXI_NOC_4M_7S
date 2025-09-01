//=============================================================================
// S2 AXI Interface
//=============================================================================
// Interface for Slave 2 (S2) AXI signals
// Based on RTL: amba_axi_m4s7.v
// Compatible with S2_seq_item.sv and axi_common_types_pkg.sv
// Note: This interface is specifically for S2; master interfaces are created separately
// Features: Clocking block for synchronized signal access at posedge ACLK

`ifndef S2_INTERFACE_SV
`define S2_INTERFACE_SV

interface S2_interface(
    input logic ACLK,
    input logic ARESETn
);
    import axi_common_types_pkg::*;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S2 receives these signals from masters
    logic [AXI_ID_WIDTH-1:0]     S2_AWID;           // Write address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S2_AWADDR;         // Write address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S2_AWLEN;          // Burst length (0-15)
    logic                        S2_AWLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S2_AWSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S2_AWBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S2_AWCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S2_AWPROT;         // Protection attributes
    logic                        S2_AWVALID;        // Write address valid (from master)
    logic                        S2_AWREADY;        // Write address ready (S2 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S2_AWQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S2_AWREGION;       // Region identifier
    logic [0:0]                  S2_AWUSER;         // Write-address user path (if enabled)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S2 receives these signals from masters
    logic [AXI_DATA_WIDTH-1:0]   S2_WDATA;          // Write data (from master)
    logic [AXI_STRB_WIDTH-1:0]   S2_WSTRB;          // Write strobes (from master)
    logic                        S2_WLAST;          // Write last (from master)
    logic                        S2_WVALID;         // Write valid (from master)
    logic                        S2_WREADY;         // Write ready (S2 drives this)
    logic [0:0]                  S2_WUSER;          // Write-data user path (if enabled)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S2 drives these signals to masters
    logic [AXI_ID_WIDTH-1:0]     S2_BID;            // Write response ID (S2 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S2_BRESP;          // Write response (S2 drives this)
    logic                        S2_BVALID;         // Write response valid (S2 drives this)
    logic                        S2_BREADY;         // Write response ready (from master)
    logic [0:0]                  S2_BUSER;          // Write-response user path (if enabled)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S2 receives these signals from masters
    logic [AXI_ID_WIDTH-1:0]     S2_ARID;           // Read address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S2_ARADDR;         // Read address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S2_ARLEN;          // Burst length (0-15)
    logic                        S2_ARLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S2_ARSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S2_ARBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S2_ARCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S2_ARPROT;         // Protection attributes
    logic                        S2_ARVALID;        // Read address valid (from master)
    logic                        S2_ARREADY;        // Read address ready (S2 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S2_ARQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S2_ARREGION;       // Region identifier
    logic [0:0]                  S2_ARUSER;         // Read-address user path (if enabled)
    
    // ===== READ DATA CHANNEL (R) =====
    // S2 drives these signals to masters
    logic [AXI_ID_WIDTH-1:0]     S2_RID;            // Read ID (S2 drives this)
    logic [AXI_DATA_WIDTH-1:0]   S2_RDATA;          // Read data (S2 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S2_RRESP;          // Read response (S2 drives this)
    logic                        S2_RLAST;          // Read last (S2 drives this)
    logic                        S2_RVALID;         // Read valid (S2 drives this)
    logic                        S2_RREADY;         // Read ready (from master)
    logic [0:0]                  S2_RUSER;          // Read-data user path (if enabled)
    
    // ===== CLOCKING BLOCK =====
    // Clocking block for synchronizing signals to posedge of ACLK
    // Note: ACLK and ARESETn are NOT in clocking blocks - they are interface-level signals
    clocking s2_cb @(posedge ACLK);
        // Write Address Channel (S2 receives from master, drives AWREADY)
        input  S2_AWID, S2_AWADDR, S2_AWLEN, S2_AWLOCK, S2_AWSIZE, S2_AWBURST,
               S2_AWCACHE, S2_AWPROT, S2_AWVALID, S2_AWQOS, S2_AWREGION, S2_AWUSER;
        output S2_AWREADY;
        
        // Write Data Channel (S2 receives from master, drives WREADY)
        input  S2_WDATA, S2_WSTRB, S2_WLAST, S2_WVALID, S2_WUSER;
        output S2_WREADY;
        
        // Write Response Channel (S2 drives to master, receives BREADY)
        output S2_BID, S2_BRESP, S2_BVALID, S2_BUSER;
        input  S2_BREADY;
        
        // Read Address Channel (S2 receives from master, drives ARREADY)
        input  S2_ARID, S2_ARADDR, S2_ARLEN, S2_ARLOCK, S2_ARSIZE, S2_ARBURST,
               S2_ARCACHE, S2_ARPROT, S2_ARVALID, S2_ARQOS, S2_ARREGION, S2_ARUSER;
        output S2_ARREADY;
        
        // Read Data Channel (S2 drives to master, receives RREADY)
        output S2_RID, S2_RDATA, S2_RRESP, S2_RLAST, S2_RVALID, S2_RUSER;
        input  S2_RREADY;
    endclocking
    
    // ===== INTERFACE MODPORTS =====
    
    // Driver modport - For S2 driver (S2 responds to master requests)
    modport driver (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized access (primary interface)
        clocking s2_cb
    );
    
    // Monitor clocking block - For synchronized monitoring at posedge ACLK
    clocking s2_monitor_cb @(posedge ACLK);
        // All signals as inputs for monitoring
        input  S2_AWID, S2_AWADDR, S2_AWLEN, S2_AWLOCK, S2_AWSIZE, S2_AWBURST,
               S2_AWCACHE, S2_AWPROT, S2_AWVALID, S2_AWREADY, S2_AWQOS, S2_AWREGION, S2_AWUSER,
               S2_WDATA, S2_WSTRB, S2_WLAST, S2_WVALID, S2_WREADY, S2_WUSER,
               S2_BID, S2_BRESP, S2_BVALID, S2_BREADY, S2_BUSER,
               S2_ARID, S2_ARADDR, S2_ARLEN, S2_ARLOCK, S2_ARSIZE, S2_ARBURST,
               S2_ARCACHE, S2_ARPROT, S2_ARVALID, S2_ARREADY, S2_ARQOS, S2_ARREGION, S2_ARUSER,
               S2_RID, S2_RDATA, S2_RRESP, S2_RLAST, S2_RVALID, S2_RREADY, S2_RUSER;
    endclocking
    
    // Monitor modport - For passive monitoring with synchronized access
    modport monitor (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized monitoring
        clocking s2_monitor_cb
    );
    
    // ===== INTERFACE TASKS =====
    
    // Task to initialize all signals to default values
    task automatic init_signals();
        // Write Address Channel - S2 receives these, initialize to safe defaults
        S2_AWID = '0;
        S2_AWADDR = '0;
        S2_AWLEN = '0;
        S2_AWLOCK = '0;
        S2_AWSIZE = '0;
        S2_AWBURST = '0;
        S2_AWCACHE = '0;
        S2_AWPROT = '0;
        S2_AWVALID = '0;
        S2_AWQOS = '0;
        S2_AWREGION = '0;
        S2_AWUSER = '0;
        S2_AWREADY = '0;  // S2 drives this
        
        // Write Data Channel - S2 receives these, initialize to safe defaults
        S2_WDATA = '0;
        S2_WSTRB = '0;
        S2_WLAST = '0;
        S2_WVALID = '0;
        S2_WUSER = '0;
        S2_WREADY = '0;  // S2 drives this
        
        // Write Response Channel - S2 drives these signals
        S2_BID = '0;
        S2_BRESP = '0;
        S2_BVALID = '0;
        S2_BREADY = '0;  // S2 receives this
        S2_BUSER = '0;
        
        // Read Address Channel - S2 receives these, initialize to safe defaults
        S2_ARID = '0;
        S2_ARADDR = '0;
        S2_ARLEN = '0;
        S2_ARLOCK = '0;
        S2_ARSIZE = '0;
        S2_ARBURST = '0;
        S2_ARCACHE = '0;
        S2_ARPROT = '0;
        S2_ARVALID = '0;
        S2_ARQOS = '0;
        S2_ARREGION = '0;
        S2_ARUSER = '0;
        S2_ARREADY = '0;  // S2 drives this
        
        // Read Data Channel - S2 drives these signals
        S2_RID = '0;
        S2_RDATA = '0;
        S2_RRESP = '0;
        S2_RLAST = '0;
        S2_RVALID = '0;
        S2_RREADY = '0;  // S2 receives this
        S2_RUSER = '0;
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
    
endinterface : S2_interface

`endif // S2_INTERFACE_SV


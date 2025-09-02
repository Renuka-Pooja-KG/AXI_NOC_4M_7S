//=============================================================================
// S6 AXI Interface
//=============================================================================
// Interface for Slave 6 (S6) AXI signals
// Based on RTL: amba_axi_m4s7.v
// Compatible with S6_seq_item.sv and axi_common_types_pkg.sv
// Note: This interface is specifically for S6; master interfaces are created separately
// Features: Clocking block for synchronized signal access at posedge ACLK

`ifndef S6_INTERFACE_SV
`define S6_INTERFACE_SV

interface S6_interface(
    input logic ACLK,
    input logic ARESETn
);
    import axi_common_types_pkg::*;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S6 receives these signals from masters
    logic [AXI_SID_WIDTH-1:0]     S6_AWID;           // Write address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S6_AWADDR;         // Write address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S6_AWLEN;          // Burst length (0-15)
    logic                        S6_AWLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S6_AWSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S6_AWBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S6_AWCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S6_AWPROT;         // Protection attributes
    logic                        S6_AWVALID;        // Write address valid (from master)
    logic                        S6_AWREADY;        // Write address ready (S6 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S6_AWQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S6_AWREGION;       // Region identifier
    logic [0:0]                  S6_AWUSER;         // Write-address user path (if enabled)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S6 receives these signals from masters
    logic [AXI_DATA_WIDTH-1:0]   S6_WDATA;          // Write data (from master)
    logic [AXI_STRB_WIDTH-1:0]   S6_WSTRB;          // Write strobes (from master)
    logic                        S6_WLAST;          // Write last (from master)
    logic                        S6_WVALID;         // Write valid (from master)
    logic                        S6_WREADY;         // Write ready (S6 drives this)
    logic [0:0]                  S6_WUSER;          // Write-data user path (if enabled)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S6 drives these signals to masters
    logic [AXI_SID_WIDTH-1:0]     S6_BID;            // Write response ID (S6 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S6_BRESP;          // Write response (S6 drives this)
    logic                        S6_BVALID;         // Write response valid (S6 drives this)
    logic                        S6_BREADY;         // Write response ready (from master)
    logic [0:0]                  S6_BUSER;          // Write-response user path (if enabled)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S6 receives these signals from masters
    logic [AXI_SID_WIDTH-1:0]     S6_ARID;           // Read address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S6_ARADDR;         // Read address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S6_ARLEN;          // Burst length (0-15)
    logic                        S6_ARLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S6_ARSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S6_ARBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S6_ARCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S6_ARPROT;         // Protection attributes
    logic                        S6_ARVALID;        // Read address valid (from master)
    logic                        S6_ARREADY;        // Read address ready (S6 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S6_ARQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S6_ARREGION;       // Region identifier
    logic [0:0]                  S6_ARUSER;         // Read-address user path (if enabled)
    
    // ===== READ DATA CHANNEL (R) =====
    // S6 drives these signals to masters
    logic [AXI_SID_WIDTH-1:0]     S6_RID;            // Read ID (S6 drives this)
    logic [AXI_DATA_WIDTH-1:0]   S6_RDATA;          // Read data (S6 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S6_RRESP;          // Read response (S6 drives this)
    logic                        S6_RLAST;          // Read last (S6 drives this)
    logic                        S6_RVALID;         // Read valid (S6 drives this)
    logic                        S6_RREADY;         // Read ready (from master)
    logic [0:0]                  S6_RUSER;          // Read-data user path (if enabled)
    
    // ===== CLOCKING BLOCK =====
    // Clocking block for synchronizing signals to posedge of ACLK
    // Note: ACLK and ARESETn are NOT in clocking blocks - they are interface-level signals
    clocking s6_cb @(posedge ACLK);
        // Write Address Channel (S6 receives from master, drives AWREADY)
        input  S6_AWID, S6_AWADDR, S6_AWLEN, S6_AWLOCK, S6_AWSIZE, S6_AWBURST,
               S6_AWCACHE, S6_AWPROT, S6_AWVALID, S6_AWQOS, S6_AWREGION, S6_AWUSER;
        output S6_AWREADY;
        
        // Write Data Channel (S6 receives from master, drives WREADY)
        input  S6_WDATA, S6_WSTRB, S6_WLAST, S6_WVALID, S6_WUSER;
        output S6_WREADY;
        
        // Write Response Channel (S6 drives to master, receives BREADY)
        output S6_BID, S6_BRESP, S6_BVALID, S6_BUSER;
        input  S6_BREADY;
        
        // Read Address Channel (S6 receives from master, drives ARREADY)
        input  S6_ARID, S6_ARADDR, S6_ARLEN, S6_ARLOCK, S6_ARSIZE, S6_ARBURST,
               S6_ARCACHE, S6_ARPROT, S6_ARVALID, S6_ARQOS, S6_ARREGION, S6_ARUSER;
        output S6_ARREADY;
        
        // Read Data Channel (S6 drives to master, receives RREADY)
        output S6_RID, S6_RDATA, S6_RRESP, S6_RLAST, S6_RVALID, S6_RUSER;
        input  S6_RREADY;
    endclocking
    
    // ===== INTERFACE MODPORTS =====
    
    // Driver modport - For S6 driver (S6 responds to master requests)
    modport driver (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized access (primary interface)
        clocking s6_cb
    );
    
    // Monitor clocking block - For synchronized monitoring at posedge ACLK
    clocking s6_monitor_cb @(posedge ACLK);
        // All signals as inputs for monitoring
        input  S6_AWID, S6_AWADDR, S6_AWLEN, S6_AWLOCK, S6_AWSIZE, S6_AWBURST,
               S6_AWCACHE, S6_AWPROT, S6_AWVALID, S6_AWREADY, S6_AWQOS, S6_AWREGION, S6_AWUSER,
               S6_WDATA, S6_WSTRB, S6_WLAST, S6_WVALID, S6_WREADY, S6_WUSER,
               S6_BID, S6_BRESP, S6_BVALID, S6_BREADY, S6_BUSER,
               S6_ARID, S6_ARADDR, S6_ARLEN, S6_ARLOCK, S6_ARSIZE, S6_ARBURST,
               S6_ARCACHE, S6_ARPROT, S6_ARVALID, S6_ARREADY, S6_ARQOS, S6_ARREGION, S6_ARUSER,
               S6_RID, S6_RDATA, S6_RRESP, S6_RLAST, S6_RVALID, S6_RREADY, S6_RUSER;
    endclocking
    
    // Monitor modport - For passive monitoring with synchronized access
    modport monitor (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized monitoring
        clocking s6_monitor_cb
    );
    
    // ===== INTERFACE TASKS =====
    
    // Task to initialize all signals to default values
    task automatic init_signals();
        // Write Address Channel - S6 receives these, initialize to safe defaults
        // S6_AWID = '0;
        // S6_AWADDR = '0;
        // S6_AWLEN = '0;
        // S6_AWLOCK = '0;
        // S6_AWSIZE = '0;
        // S6_AWBURST = '0;
        // S6_AWCACHE = '0;
        // S6_AWPROT = '0;
        // S6_AWVALID = '0;
        // S6_AWQOS = '0;
        // S6_AWREGION = '0;
        // S6_AWUSER = '0;
        S6_AWREADY = '0;  // S6 drives this
        
        // Write Data Channel - S6 receives these, initialize to safe defaults
        // S6_WDATA = '0;
        // S6_WSTRB = '0;
        // S6_WLAST = '0;
        // S6_WVALID = '0;
        // S6_WUSER = '0;
        S6_WREADY = '0;  // S6 drives this
        
        // Write Response Channel - S6 drives these signals
        S6_BID = '0;
        S6_BRESP = '0;
        S6_BVALID = '0;
        // S6_BREADY = '0;  // S6 receives this
        // S6_BUSER = '0;
        
        // Read Address Channel - S6 receives these, initialize to safe defaults
        // S6_ARID = '0;
        // S6_ARADDR = '0;
        // S6_ARLEN = '0;
        // S6_ARLOCK = '0;
        // S6_ARSIZE = '0;
        // S6_ARBURST = '0;
        // S6_ARCACHE = '0;
        // S6_ARPROT = '0;
        // S6_ARVALID = '0;
        // S6_ARQOS = '0;
        // S6_ARREGION = '0;
        // S6_ARUSER = '0;
        S6_ARREADY = '0;  // S6 drives this
        
        // Read Data Channel - S6 drives these signals
        S6_RID = '0;
        S6_RDATA = '0;
        S6_RRESP = '0;
        S6_RLAST = '0;
        S6_RVALID = '0;
        // S6_RREADY = '0;  // S6 receives this
        // S6_RUSER = '0;
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
    
endinterface : S6_interface

`endif // S6_INTERFACE_SV


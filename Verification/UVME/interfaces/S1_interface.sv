//=============================================================================
// S1 AXI Interface
//=============================================================================
// Interface for Slave 1 (S1) AXI signals
// Based on RTL: amba_axi_m4s7.v
// Compatible with S1_seq_item.sv and axi_common_types_pkg.sv
// Note: This interface is specifically for S1; master interfaces are created separately
// Features: Clocking block for synchronized signal access at posedge ACLK

`ifndef S1_INTERFACE_SV
`define S1_INTERFACE_SV

interface S1_interface(
    input logic ACLK,
    input logic ARESETn
);
    import axi_common_types_pkg::*;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S1 receives these signals from masters
    logic [AXI_ID_WIDTH-1:0]     S1_AWID;           // Write address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S1_AWADDR;         // Write address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S1_AWLEN;          // Burst length (0-15)
    logic                        S1_AWLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S1_AWSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S1_AWBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S1_AWCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S1_AWPROT;         // Protection attributes
    logic                        S1_AWVALID;        // Write address valid (from master)
    logic                        S1_AWREADY;        // Write address ready (S1 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S1_AWQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S1_AWREGION;       // Region identifier
    logic [0:0]                  S1_AWUSER;         // Write-address user path (if enabled)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S1 receives these signals from masters
    logic [AXI_DATA_WIDTH-1:0]   S1_WDATA;          // Write data (from master)
    logic [AXI_STRB_WIDTH-1:0]   S1_WSTRB;          // Write strobes (from master)
    logic                        S1_WLAST;          // Write last (from master)
    logic                        S1_WVALID;         // Write valid (from master)
    logic                        S1_WREADY;         // Write ready (S1 drives this)
    logic [0:0]                  S1_WUSER;          // Write-data user path (if enabled)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S1 drives these signals to masters
    logic [AXI_ID_WIDTH-1:0]     S1_BID;            // Write response ID (S1 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S1_BRESP;          // Write response (S1 drives this)
    logic                        S1_BVALID;         // Write response valid (S1 drives this)
    logic                        S1_BREADY;         // Write response ready (from master)
    logic [0:0]                  S1_BUSER;          // Write-response user path (if enabled)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S1 receives these signals from masters
    logic [AXI_ID_WIDTH-1:0]     S1_ARID;           // Read address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S1_ARADDR;         // Read address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S1_ARLEN;          // Burst length (0-15)
    logic                        S1_ARLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S1_ARSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S1_ARBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S1_ARCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S1_ARPROT;         // Protection attributes
    logic                        S1_ARVALID;        // Read address valid (from master)
    logic                        S1_ARREADY;        // Read address ready (S1 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S1_ARQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S1_ARREGION;       // Region identifier
    logic [0:0]                  S1_ARUSER;         // Read-address user path (if enabled)
    
    // ===== READ DATA CHANNEL (R) =====
    // S1 drives these signals to masters
    logic [AXI_ID_WIDTH-1:0]     S1_RID;            // Read ID (S1 drives this)
    logic [AXI_DATA_WIDTH-1:0]   S1_RDATA;          // Read data (S1 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S1_RRESP;          // Read response (S1 drives this)
    logic                        S1_RLAST;          // Read last (S1 drives this)
    logic                        S1_RVALID;         // Read valid (S1 drives this)
    logic                        S1_RREADY;         // Read ready (from master)
    logic [0:0]                  S1_RUSER;          // Read-data user path (if enabled)
    
    // ===== CLOCKING BLOCK =====
    // Clocking block for synchronizing signals to posedge of ACLK
    // Note: ACLK and ARESETn are NOT in clocking blocks - they are interface-level signals
    clocking s1_cb @(posedge ACLK);
        // Write Address Channel (S1 receives from master, drives AWREADY)
        input  S1_AWID, S1_AWADDR, S1_AWLEN, S1_AWLOCK, S1_AWSIZE, S1_AWBURST,
               S1_AWCACHE, S1_AWPROT, S1_AWVALID, S1_AWQOS, S1_AWREGION, S1_AWUSER;
        output S1_AWREADY;
        
        // Write Data Channel (S1 receives from master, drives WREADY)
        input  S1_WDATA, S1_WSTRB, S1_WLAST, S1_WVALID, S1_WUSER;
        output S1_WREADY;
        
        // Write Response Channel (S1 drives to master, receives BREADY)
        output S1_BID, S1_BRESP, S1_BVALID, S1_BUSER;
        input  S1_BREADY;
        
        // Read Address Channel (S1 receives from master, drives ARREADY)
        input  S1_ARID, S1_ARADDR, S1_ARLEN, S1_ARLOCK, S1_ARSIZE, S1_ARBURST,
               S1_ARCACHE, S1_ARPROT, S1_ARVALID, S1_ARQOS, S1_ARREGION, S1_ARUSER;
        output S1_ARREADY;
        
        // Read Data Channel (S1 drives to master, receives RREADY)
        output S1_RID, S1_RDATA, S1_RRESP, S1_RLAST, S1_RVALID, S1_RUSER;
        input  S1_RREADY;
    endclocking
    
    // ===== INTERFACE MODPORTS =====
    
    // Driver modport - For S1 driver (S1 responds to master requests)
    modport driver (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized access (primary interface)
        clocking s1_cb
    );
    
    // Monitor clocking block - For synchronized monitoring at posedge ACLK
    clocking s1_monitor_cb @(posedge ACLK);
        // All signals as inputs for monitoring
        input  S1_AWID, S1_AWADDR, S1_AWLEN, S1_AWLOCK, S1_AWSIZE, S1_AWBURST,
               S1_AWCACHE, S1_AWPROT, S1_AWVALID, S1_AWREADY, S1_AWQOS, S1_AWREGION, S1_AWUSER,
               S1_WDATA, S1_WSTRB, S1_WLAST, S1_WVALID, S1_WREADY, S1_WUSER,
               S1_BID, S1_BRESP, S1_BVALID, S1_BREADY, S1_BUSER,
               S1_ARID, S1_ARADDR, S1_ARLEN, S1_ARLOCK, S1_ARSIZE, S1_ARBURST,
               S1_ARCACHE, S1_ARPROT, S1_ARVALID, S1_ARREADY, S1_ARQOS, S1_ARREGION, S1_ARUSER,
               S1_RID, S1_RDATA, S1_RRESP, S1_RLAST, S1_RVALID, S1_RREADY, S1_RUSER;
    endclocking
    
    // Monitor modport - For passive monitoring with synchronized access
    modport monitor (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized monitoring
        clocking s1_monitor_cb
    );
    
    // ===== INTERFACE TASKS =====
    
    // Task to initialize all signals to default values
    task automatic init_signals();
        // Write Address Channel - S1 receives these, initialize to safe defaults
        S1_AWID = '0;
        S1_AWADDR = '0;
        S1_AWLEN = '0;
        S1_AWLOCK = '0;
        S1_AWSIZE = '0;
        S1_AWBURST = '0;
        S1_AWCACHE = '0;
        S1_AWPROT = '0;
        S1_AWVALID = '0;
        S1_AWQOS = '0;
        S1_AWREGION = '0;
        S1_AWUSER = '0;
        S1_AWREADY = '0;  // S1 drives this
        
        // Write Data Channel - S1 receives these, initialize to safe defaults
        S1_WDATA = '0;
        S1_WSTRB = '0;
        S1_WLAST = '0;
        S1_WVALID = '0;
        S1_WUSER = '0;
        S1_WREADY = '0;  // S1 drives this
        
        // Write Response Channel - S1 drives these signals
        S1_BID = '0;
        S1_BRESP = '0;
        S1_BVALID = '0;
        S1_BREADY = '0;  // S1 receives this
        S1_BUSER = '0;
        
        // Read Address Channel - S1 receives these, initialize to safe defaults
        S1_ARID = '0;
        S1_ARADDR = '0;
        S1_ARLEN = '0;
        S1_ARLOCK = '0;
        S1_ARSIZE = '0;
        S1_ARBURST = '0;
        S1_ARCACHE = '0;
        S1_ARPROT = '0;
        S1_ARVALID = '0;
        S1_ARQOS = '0;
        S1_ARREGION = '0;
        S1_ARUSER = '0;
        S1_ARREADY = '0;  // S1 drives this
        
        // Read Data Channel - S1 drives these signals
        S1_RID = '0;
        S1_RDATA = '0;
        S1_RRESP = '0;
        S1_RLAST = '0;
        S1_RVALID = '0;
        S1_RREADY = '0;  // S1 receives this
        S1_RUSER = '0;
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
    
endinterface : S1_interface

`endif // S1_INTERFACE_SV


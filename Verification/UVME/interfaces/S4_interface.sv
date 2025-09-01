//=============================================================================
// S4 AXI Interface
//=============================================================================
// Interface for Slave 4 (S4) AXI signals
// Based on RTL: amba_axi_m4s7.v
// Compatible with S4_seq_item.sv and axi_common_types_pkg.sv
// Note: This interface is specifically for S4; master interfaces are created separately
// Features: Clocking block for synchronized signal access at posedge ACLK

`ifndef S4_INTERFACE_SV
`define S4_INTERFACE_SV

interface S4_interface(
    input logic ACLK,
    input logic ARESETn
);
    import axi_common_types_pkg::*;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S4 receives these signals from masters
    logic [AXI_ID_WIDTH-1:0]     S4_AWID;           // Write address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S4_AWADDR;         // Write address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S4_AWLEN;          // Burst length (0-15)
    logic                        S4_AWLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S4_AWSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S4_AWBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S4_AWCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S4_AWPROT;         // Protection attributes
    logic                        S4_AWVALID;        // Write address valid (from master)
    logic                        S4_AWREADY;        // Write address ready (S4 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S4_AWQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S4_AWREGION;       // Region identifier
    logic [0:0]                  S4_AWUSER;         // Write-address user path (if enabled)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S4 receives these signals from masters
    logic [AXI_DATA_WIDTH-1:0]   S4_WDATA;          // Write data (from master)
    logic [AXI_STRB_WIDTH-1:0]   S4_WSTRB;          // Write strobes (from master)
    logic                        S4_WLAST;          // Write last (from master)
    logic                        S4_WVALID;         // Write valid (from master)
    logic                        S4_WREADY;         // Write ready (S4 drives this)
    logic [0:0]                  S4_WUSER;          // Write-data user path (if enabled)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S4 drives these signals to masters
    logic [AXI_ID_WIDTH-1:0]     S4_BID;            // Write response ID (S4 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S4_BRESP;          // Write response (S4 drives this)
    logic                        S4_BVALID;         // Write response valid (S4 drives this)
    logic                        S4_BREADY;         // Write response ready (from master)
    logic [0:0]                  S4_BUSER;          // Write-response user path (if enabled)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S4 receives these signals from masters
    logic [AXI_ID_WIDTH-1:0]     S4_ARID;           // Read address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S4_ARADDR;         // Read address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S4_ARLEN;          // Burst length (0-15)
    logic                        S4_ARLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S4_ARSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S4_ARBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S4_ARCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S4_ARPROT;         // Protection attributes
    logic                        S4_ARVALID;        // Read address valid (from master)
    logic                        S4_ARREADY;        // Read address ready (S4 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S4_ARQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S4_ARREGION;       // Region identifier
    logic [0:0]                  S4_ARUSER;         // Read-address user path (if enabled)
    
    // ===== READ DATA CHANNEL (R) =====
    // S4 drives these signals to masters
    logic [AXI_ID_WIDTH-1:0]     S4_RID;            // Read ID (S4 drives this)
    logic [AXI_DATA_WIDTH-1:0]   S4_RDATA;          // Read data (S4 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S4_RRESP;          // Read response (S4 drives this)
    logic                        S4_RLAST;          // Read last (S4 drives this)
    logic                        S4_RVALID;         // Read valid (S4 drives this)
    logic                        S4_RREADY;         // Read ready (from master)
    logic [0:0]                  S4_RUSER;          // Read-data user path (if enabled)
    
    // ===== CLOCKING BLOCK =====
    // Clocking block for synchronizing signals to posedge of ACLK
    // Note: ACLK and ARESETn are NOT in clocking blocks - they are interface-level signals
    clocking s4_cb @(posedge ACLK);
        // Write Address Channel (S4 receives from master, drives AWREADY)
        input  S4_AWID, S4_AWADDR, S4_AWLEN, S4_AWLOCK, S4_AWSIZE, S4_AWBURST,
               S4_AWCACHE, S4_AWPROT, S4_AWVALID, S4_AWQOS, S4_AWREGION, S4_AWUSER;
        output S4_AWREADY;
        
        // Write Data Channel (S4 receives from master, drives WREADY)
        input  S4_WDATA, S4_WSTRB, S4_WLAST, S4_WVALID, S4_WUSER;
        output S4_WREADY;
        
        // Write Response Channel (S4 drives to master, receives BREADY)
        output S4_BID, S4_BRESP, S4_BVALID, S4_BUSER;
        input  S4_BREADY;
        
        // Read Address Channel (S4 receives from master, drives ARREADY)
        input  S4_ARID, S4_ARADDR, S4_ARLEN, S4_ARLOCK, S4_ARSIZE, S4_ARBURST,
               S4_ARCACHE, S4_ARPROT, S4_ARVALID, S4_ARQOS, S4_ARREGION, S4_ARUSER;
        output S4_ARREADY;
        
        // Read Data Channel (S4 drives to master, receives RREADY)
        output S4_RID, S4_RDATA, S4_RRESP, S4_RLAST, S4_RVALID, S4_RUSER;
        input  S4_RREADY;
    endclocking
    
    // ===== INTERFACE MODPORTS =====
    
    // Driver modport - For S4 driver (S4 responds to master requests)
    modport driver (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized access (primary interface)
        clocking s4_cb
    );
    
    // Monitor clocking block - For synchronized monitoring at posedge ACLK
    clocking s4_monitor_cb @(posedge ACLK);
        // All signals as inputs for monitoring
        input  S4_AWID, S4_AWADDR, S4_AWLEN, S4_AWLOCK, S4_AWSIZE, S4_AWBURST,
               S4_AWCACHE, S4_AWPROT, S4_AWVALID, S4_AWREADY, S4_AWQOS, S4_AWREGION, S4_AWUSER,
               S4_WDATA, S4_WSTRB, S4_WLAST, S4_WVALID, S4_WREADY, S4_WUSER,
               S4_BID, S4_BRESP, S4_BVALID, S4_BREADY, S4_BUSER,
               S4_ARID, S4_ARADDR, S4_ARLEN, S4_ARLOCK, S4_ARSIZE, S4_ARBURST,
               S4_ARCACHE, S4_ARPROT, S4_ARVALID, S4_ARREADY, S4_ARQOS, S4_ARREGION, S4_ARUSER,
               S4_RID, S4_RDATA, S4_RRESP, S4_RLAST, S4_RVALID, S4_RREADY, S4_RUSER;
    endclocking
    
    // Monitor modport - For passive monitoring with synchronized access
    modport monitor (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized monitoring
        clocking s4_monitor_cb
    );
    
    // ===== INTERFACE TASKS =====
    
    // Task to initialize all signals to default values
    task automatic init_signals();
        // Write Address Channel - S4 receives these, initialize to safe defaults
        S4_AWID = '0;
        S4_AWADDR = '0;
        S4_AWLEN = '0;
        S4_AWLOCK = '0;
        S4_AWSIZE = '0;
        S4_AWBURST = '0;
        S4_AWCACHE = '0;
        S4_AWPROT = '0;
        S4_AWVALID = '0;
        S4_AWQOS = '0;
        S4_AWREGION = '0;
        S4_AWUSER = '0;
        S4_AWREADY = '0;  // S4 drives this
        
        // Write Data Channel - S4 receives these, initialize to safe defaults
        S4_WDATA = '0;
        S4_WSTRB = '0;
        S4_WLAST = '0;
        S4_WVALID = '0;
        S4_WUSER = '0;
        S4_WREADY = '0;  // S4 drives this
        
        // Write Response Channel - S4 drives these signals
        S4_BID = '0;
        S4_BRESP = '0;
        S4_BVALID = '0;
        S4_BREADY = '0;  // S4 receives this
        S4_BUSER = '0;
        
        // Read Address Channel - S4 receives these, initialize to safe defaults
        S4_ARID = '0;
        S4_ARADDR = '0;
        S4_ARLEN = '0;
        S4_ARLOCK = '0;
        S4_ARSIZE = '0;
        S4_ARBURST = '0;
        S4_ARCACHE = '0;
        S4_ARPROT = '0;
        S4_ARVALID = '0;
        S4_ARQOS = '0;
        S4_ARREGION = '0;
        S4_ARUSER = '0;
        S4_ARREADY = '0;  // S4 drives this
        
        // Read Data Channel - S4 drives these signals
        S4_RID = '0;
        S4_RDATA = '0;
        S4_RRESP = '0;
        S4_RLAST = '0;
        S4_RVALID = '0;
        S4_RREADY = '0;  // S4 receives this
        S4_RUSER = '0;
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
    
endinterface : S4_interface

`endif // S4_INTERFACE_SV


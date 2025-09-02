//=============================================================================
// S3 AXI Interface
//=============================================================================
// Interface for Slave 3 (S3) AXI signals
// Based on RTL: amba_axi_m4s7.v
// Compatible with S3_seq_item.sv and axi_common_types_pkg.sv
// Note: This interface is specifically for S3; master interfaces are created separately
// Features: Clocking block for synchronized signal access at posedge ACLK

`ifndef S3_INTERFACE_SV
`define S3_INTERFACE_SV

interface S3_interface(
    input logic ACLK,
    input logic ARESETn
);
    import axi_common_types_pkg::*;
    
    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S3 receives these signals from masters
    logic [AXI_SID_WIDTH-1:0]     S3_AWID;           // Write address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S3_AWADDR;         // Write address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S3_AWLEN;          // Burst length (0-15)
    logic                        S3_AWLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S3_AWSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S3_AWBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S3_AWCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S3_AWPROT;         // Protection attributes
    logic                        S3_AWVALID;        // Write address valid (from master)
    logic                        S3_AWREADY;        // Write address ready (S3 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S3_AWQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S3_AWREGION;       // Region identifier
    logic [0:0]                  S3_AWUSER;         // Write-address user path (if enabled)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S3 receives these signals from masters
    logic [AXI_DATA_WIDTH-1:0]   S3_WDATA;          // Write data (from master)
    logic [AXI_STRB_WIDTH-1:0]   S3_WSTRB;          // Write strobes (from master)
    logic                        S3_WLAST;          // Write last (from master)
    logic                        S3_WVALID;         // Write valid (from master)
    logic                        S3_WREADY;         // Write ready (S3 drives this)
    logic [0:0]                  S3_WUSER;          // Write-data user path (if enabled)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S3 drives these signals to masters
    logic [AXI_SID_WIDTH-1:0]     S3_BID;            // Write response ID (S3 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S3_BRESP;          // Write response (S3 drives this)
    logic                        S3_BVALID;         // Write response valid (S3 drives this)
    logic                        S3_BREADY;         // Write response ready (from master)
    logic [0:0]                  S3_BUSER;          // Write-response user path (if enabled)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S3 receives these signals from masters
    logic [AXI_SID_WIDTH-1:0]     S3_ARID;           // Read address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S3_ARADDR;         // Read address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S3_ARLEN;          // Burst length (0-15)
    logic                        S3_ARLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S3_ARSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S3_ARBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S3_ARCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S3_ARPROT;         // Protection attributes
    logic                        S3_ARVALID;        // Read address valid (from master)
    logic                        S3_ARREADY;        // Read address ready (S3 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S3_ARQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S3_ARREGION;       // Region identifier
    logic [0:0]                  S3_ARUSER;         // Read-address user path (if enabled)
    
    // ===== READ DATA CHANNEL (R) =====
    // S3 drives these signals to masters
    logic [AXI_SID_WIDTH-1:0]     S3_RID;            // Read ID (S3 drives this)
    logic [AXI_DATA_WIDTH-1:0]   S3_RDATA;          // Read data (S3 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S3_RRESP;          // Read response (S3 drives this)
    logic                        S3_RLAST;          // Read last (S3 drives this)
    logic                        S3_RVALID;         // Read valid (S3 drives this)
    logic                        S3_RREADY;         // Read ready (from master)
    logic [0:0]                  S3_RUSER;          // Read-data user path (if enabled)
    
    // ===== CLOCKING BLOCK =====
    // Clocking block for synchronizing signals to posedge of ACLK
    // Note: ACLK and ARESETn are NOT in clocking blocks - they are interface-level signals
    clocking s3_cb @(posedge ACLK);
        // Write Address Channel (S3 receives from master, drives AWREADY)
        input  S3_AWID, S3_AWADDR, S3_AWLEN, S3_AWLOCK, S3_AWSIZE, S3_AWBURST,
               S3_AWCACHE, S3_AWPROT, S3_AWVALID, S3_AWQOS, S3_AWREGION, S3_AWUSER;
        output S3_AWREADY;
        
        // Write Data Channel (S3 receives from master, drives WREADY)
        input  S3_WDATA, S3_WSTRB, S3_WLAST, S3_WVALID, S3_WUSER;
        output S3_WREADY;
        
        // Write Response Channel (S3 drives to master, receives BREADY)
        output S3_BID, S3_BRESP, S3_BVALID, S3_BUSER;
        input  S3_BREADY;
        
        // Read Address Channel (S3 receives from master, drives ARREADY)
        input  S3_ARID, S3_ARADDR, S3_ARLEN, S3_ARLOCK, S3_ARSIZE, S3_ARBURST,
               S3_ARCACHE, S3_ARPROT, S3_ARVALID, S3_ARQOS, S3_ARREGION, S3_ARUSER;
        output S3_ARREADY;
        
        // Read Data Channel (S3 drives to master, receives RREADY)
        output S3_RID, S3_RDATA, S3_RRESP, S3_RLAST, S3_RVALID, S3_RUSER;
        input  S3_RREADY;
    endclocking
    
    // ===== INTERFACE MODPORTS =====
    
    // Driver modport - For S3 driver (S3 responds to master requests)
    modport driver (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized access (primary interface)
        clocking s3_cb
    );
    
    // Monitor clocking block - For synchronized monitoring at posedge ACLK
    clocking s3_monitor_cb @(posedge ACLK);
        // All signals as inputs for monitoring
        input  S3_AWID, S3_AWADDR, S3_AWLEN, S3_AWLOCK, S3_AWSIZE, S3_AWBURST,
               S3_AWCACHE, S3_AWPROT, S3_AWVALID, S3_AWREADY, S3_AWQOS, S3_AWREGION, S3_AWUSER,
               S3_WDATA, S3_WSTRB, S3_WLAST, S3_WVALID, S3_WREADY, S3_WUSER,
               S3_BID, S3_BRESP, S3_BVALID, S3_BREADY, S3_BUSER,
               S3_ARID, S3_ARADDR, S3_ARLEN, S3_ARLOCK, S3_ARSIZE, S3_ARBURST,
               S3_ARCACHE, S3_ARPROT, S3_ARVALID, S3_ARREADY, S3_ARQOS, S3_ARREGION, S3_ARUSER,
               S3_RID, S3_RDATA, S3_RRESP, S3_RLAST, S3_RVALID, S3_RREADY, S3_RUSER;
    endclocking
    
    // Monitor modport - For passive monitoring with synchronized access
    modport monitor (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized monitoring
        clocking s3_monitor_cb
    );
    
    // ===== INTERFACE TASKS =====
    
    // Task to initialize all signals to default values
    task automatic init_signals();
        // Write Address Channel - S3 receives these, initialize to safe defaults
        // S3_AWID = '0;
        // S3_AWADDR = '0;
        // S3_AWLEN = '0;
        // S3_AWLOCK = '0;
        // S3_AWSIZE = '0;
        // S3_AWBURST = '0;
        // S3_AWCACHE = '0;
        // S3_AWPROT = '0;
        // S3_AWVALID = '0;
        // S3_AWQOS = '0;
        // S3_AWREGION = '0;
        // S3_AWUSER = '0;
        S3_AWREADY = '0;  // S3 drives this
        
        // Write Data Channel - S3 receives these, initialize to safe defaults
        // S3_WDATA = '0;
        // S3_WSTRB = '0;
        // S3_WLAST = '0;
        // S3_WVALID = '0;
        // S3_WUSER = '0;
        S3_WREADY = '0;  // S3 drives this
        
        // Write Response Channel - S3 drives these signals
        S3_BID = '0;
        S3_BRESP = '0;
        S3_BVALID = '0;
        //S3_BREADY = '0;  // S3 receives this
        //S3_BUSER = '0;
        
        // Read Address Channel - S3 receives these, initialize to safe defaults
        // S3_ARID = '0;
        // S3_ARADDR = '0;
        // S3_ARLEN = '0;
        // S3_ARLOCK = '0;
        // S3_ARSIZE = '0;
        // S3_ARBURST = '0;
        // S3_ARCACHE = '0;
        // S3_ARPROT = '0;
        // S3_ARVALID = '0;
        // S3_ARQOS = '0;
        // S3_ARREGION = '0;
        // S3_ARUSER = '0;
        S3_ARREADY = '0;  // S3 drives this
        
        // Read Data Channel - S3 drives these signals
        S3_RID = '0;
        S3_RDATA = '0;
        S3_RRESP = '0;
        S3_RLAST = '0;
        S3_RVALID = '0;
        // S3_RREADY = '0;  // S3 receives this
        // S3_RUSER = '0;
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
    
endinterface : S3_interface

`endif // S3_INTERFACE_SV


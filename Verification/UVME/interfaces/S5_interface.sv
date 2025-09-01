//=============================================================================
// S5 AXI Interface
//=============================================================================
// Interface for Slave 5 (S5) AXI signals
// Based on RTL: amba_axi_m4s7.v
// Compatible with S5_seq_item.sv and axi_common_types_pkg.sv
// Note: This interface is specifically for S5; master interfaces are created separately
// Features: Clocking block for synchronized signal access at posedge ACLK

`ifndef S5_INTERFACE_SV
`define S5_INTERFACE_SV

interface S5_interface(
    input logic ACLK,
    input logic ARESETn
);
    import axi_common_types_pkg::*;
    

    // ===== WRITE ADDRESS CHANNEL (AW) =====
    // S5 receives these signals from masters
    logic [AXI_ID_WIDTH-1:0]     S5_AWID;           // Write address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S5_AWADDR;         // Write address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S5_AWLEN;          // Burst length (0-15)
    logic                        S5_AWLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S5_AWSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S5_AWBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S5_AWCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S5_AWPROT;         // Protection attributes
    logic                        S5_AWVALID;        // Write address valid (from master)
    logic                        S5_AWREADY;        // Write address ready (S5 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S5_AWQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S5_AWREGION;       // Region identifier
    logic [0:0]                  S5_AWUSER;         // Write-address user path (if enabled)
    
    // ===== WRITE DATA CHANNEL (W) =====
    // S5 receives these signals from masters
    logic [AXI_DATA_WIDTH-1:0]   S5_WDATA;          // Write data (from master)
    logic [AXI_STRB_WIDTH-1:0]   S5_WSTRB;          // Write strobes (from master)
    logic                        S5_WLAST;          // Write last (from master)
    logic                        S5_WVALID;         // Write valid (from master)
    logic                        S5_WREADY;         // Write ready (S5 drives this)
    logic [0:0]                  S5_WUSER;          // Write-data user path (if enabled)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    // S5 drives these signals to masters
    logic [AXI_ID_WIDTH-1:0]     S5_BID;            // Write response ID (S5 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S5_BRESP;          // Write response (S5 drives this)
    logic                        S5_BVALID;         // Write response valid (S5 drives this)
    logic                        S5_BREADY;         // Write response ready (from master)
    logic [0:0]                  S5_BUSER;          // Write-response user path (if enabled)
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    // S5 receives these signals from masters
    logic [AXI_ID_WIDTH-1:0]     S5_ARID;           // Read address ID (from master)
    logic [AXI_ADDR_WIDTH-1:0]   S5_ARADDR;         // Read address (from master)
    logic [AXI_LEN_WIDTH-1:0]    S5_ARLEN;          // Burst length (0-15)
    logic                        S5_ARLOCK;         // Lock type
    logic [AXI_SIZE_WIDTH-1:0]   S5_ARSIZE;         // Burst size
    logic [AXI_BURST_WIDTH-1:0]  S5_ARBURST;        // Burst type
    logic [AXI_CACHE_WIDTH-1:0]  S5_ARCACHE;        // Cache attributes
    logic [AXI_PROT_WIDTH-1:0]   S5_ARPROT;         // Protection attributes
    logic                        S5_ARVALID;        // Read address valid (from master)
    logic                        S5_ARREADY;        // Read address ready (S5 drives this)
    logic [AXI_QOS_WIDTH-1:0]    S5_ARQOS;          // Quality of service
    logic [AXI_REGION_WIDTH-1:0] S5_ARREGION;       // Region identifier
    logic [0:0]                  S5_ARUSER;         // Read-address user path (if enabled)
    
    // ===== READ DATA CHANNEL (R) =====
    // S5 drives these signals to masters
    logic [AXI_ID_WIDTH-1:0]     S5_RID;            // Read ID (S5 drives this)
    logic [AXI_DATA_WIDTH-1:0]   S5_RDATA;          // Read data (S5 drives this)
    logic [AXI_RESP_WIDTH-1:0]   S5_RRESP;          // Read response (S5 drives this)
    logic                        S5_RLAST;          // Read last (S5 drives this)
    logic                        S5_RVALID;         // Read valid (S5 drives this)
    logic                        S5_RREADY;         // Read ready (from master)
    logic [0:0]                  S5_RUSER;          // Read-data user path (if enabled)
    
    // ===== CLOCKING BLOCK =====
    // Clocking block for synchronizing signals to posedge of ACLK
    // Note: ACLK and ARESETn are NOT in clocking blocks - they are interface-level signals
    clocking s5_cb @(posedge ACLK);
        // Write Address Channel (S5 receives from master, drives AWREADY)
        input  S5_AWID, S5_AWADDR, S5_AWLEN, S5_AWLOCK, S5_AWSIZE, S5_AWBURST,
               S5_AWCACHE, S5_AWPROT, S5_AWVALID, S5_AWQOS, S5_AWREGION, S5_AWUSER;
        output S5_AWREADY;
        
        // Write Data Channel (S5 receives from master, drives WREADY)
        input  S5_WDATA, S5_WSTRB, S5_WLAST, S5_WVALID, S5_WUSER;
        output S5_WREADY;
        
        // Write Response Channel (S5 drives to master, receives BREADY)
        output S5_BID, S5_BRESP, S5_BVALID, S5_BUSER;
        input  S5_BREADY;
        
        // Read Address Channel (S5 receives from master, drives ARREADY)
        input  S5_ARID, S5_ARADDR, S5_ARLEN, S5_ARLOCK, S5_ARSIZE, S5_ARBURST,
               S5_ARCACHE, S5_ARPROT, S5_ARVALID, S5_ARQOS, S5_ARREGION, S5_ARUSER;
        output S5_ARREADY;
        
        // Read Data Channel (S5 drives to master, receives RREADY)
        output S5_RID, S5_RDATA, S5_RRESP, S5_RLAST, S5_RVALID, S5_RUSER;
        input  S5_RREADY;
    endclocking
    
    // ===== INTERFACE MODPORTS =====
    
    // Driver modport - For S5 driver (S5 responds to master requests)
    modport driver (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized access (primary interface)
        clocking s5_cb
    );
    
    // Monitor clocking block - For synchronized monitoring at posedge ACLK
    clocking s5_monitor_cb @(posedge ACLK);
        // All signals as inputs for monitoring
        input  S5_AWID, S5_AWADDR, S5_AWLEN, S5_AWLOCK, S5_AWSIZE, S5_AWBURST,
               S5_AWCACHE, S5_AWPROT, S5_AWVALID, S5_AWREADY, S5_AWQOS, S5_AWREGION, S5_AWUSER,
               S5_WDATA, S5_WSTRB, S5_WLAST, S5_WVALID, S5_WREADY, S5_WUSER,
               S5_BID, S5_BRESP, S5_BVALID, S5_BREADY, S5_BUSER,
               S5_ARID, S5_ARADDR, S5_ARLEN, S5_ARLOCK, S5_ARSIZE, S5_ARBURST,
               S5_ARCACHE, S5_ARPROT, S5_ARVALID, S5_ARREADY, S5_ARQOS, S5_ARREGION, S5_ARUSER,
               S5_RID, S5_RDATA, S5_RRESP, S5_RLAST, S5_RVALID, S5_RREADY, S5_RUSER;
    endclocking
    
    // Monitor modport - For passive monitoring with synchronized access
    modport monitor (
        // Clock and reset (inputs) - interface-level signals
        input  ACLK, ARESETn,
        
        // Clocking block for synchronized monitoring
        clocking s5_monitor_cb
    );
    
    // ===== INTERFACE TASKS =====
    
    // Task to initialize all signals to default values
    task automatic init_signals();
        // Write Address Channel - S5 receives these, initialize to safe defaults
        S5_AWID = '0;
        S5_AWADDR = '0;
        S5_AWLEN = '0;
        S5_AWLOCK = '0;
        S5_AWSIZE = '0;
        S5_AWBURST = '0;
        S5_AWCACHE = '0;
        S5_AWPROT = '0;
        S5_AWVALID = '0;
        S5_AWQOS = '0;
        S5_AWREGION = '0;
        S5_AWUSER = '0;
        S5_AWREADY = '0;  // S5 drives this
        
        // Write Data Channel - S5 receives these, initialize to safe defaults
        S5_WDATA = '0;
        S5_WSTRB = '0;
        S5_WLAST = '0;
        S5_WVALID = '0;
        S5_WUSER = '0;
        S5_WREADY = '0;  // S5 drives this
        
        // Write Response Channel - S5 drives these signals
        S5_BID = '0;
        S5_BRESP = '0;
        S5_BVALID = '0;
        S5_BREADY = '0;  // S5 receives this
        S5_BUSER = '0;
        
        // Read Address Channel - S5 receives these, initialize to safe defaults
        S5_ARID = '0;
        S5_ARADDR = '0;
        S5_ARLEN = '0;
        S5_ARLOCK = '0;
        S5_ARSIZE = '0;
        S5_ARBURST = '0;
        S5_ARCACHE = '0;
        S5_ARPROT = '0;
        S5_ARVALID = '0;
        S5_ARQOS = '0;
        S5_ARREGION = '0;
        S5_ARUSER = '0;
        S5_ARREADY = '0;  // S5 drives this
        
        // Read Data Channel - S5 drives these signals
        S5_RID = '0;
        S5_RDATA = '0;
        S5_RRESP = '0;
        S5_RLAST = '0;
        S5_RVALID = '0;
        S5_RREADY = '0;  // S5 receives this
        S5_RUSER = '0;
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
    
endinterface : S5_interface

`endif // S5_INTERFACE_SV


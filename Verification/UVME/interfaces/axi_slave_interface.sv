//=============================================================================
// AXI Slave Interface
//=============================================================================
// Generic interface for any AXI slave (S0, S1, S2, S3, S4, S5, S6)
// Fixed widths matching the RTL design

`ifndef AXI_SLAVE_INTERFACE_SV
`define AXI_SLAVE_INTERFACE_SV

// AXI Slave Interface
interface axi_slave_interface(
    input logic clk,      // Clock input
    input logic resetn    // Active low reset input
);

    // ===== WRITE ADDRESS CHANNEL (AW) =====
    logic [3:0]  awid;      // Write address ID (4 bits)
    logic [31:0] awaddr;    // Write address (32 bits)
    logic [7:0]  awlen;     // Burst length (8 bits)
    logic [2:0]  awsize;    // Burst size (3 bits)
    logic [1:0]  awburst;   // Burst type (2 bits)
    logic        awlock;     // Lock type (1 bit)
    logic [3:0]  awcache;   // Memory type (4 bits)
    logic [2:0]  awprot;    // Protection type (3 bits)
    logic [3:0]  awqos;     // Quality of service (4 bits)
    logic [3:0]  awregion;  // Region identifier (4 bits)
    logic        awuser;     // User signal (1 bit)
    logic        awvalid;    // Write address valid (1 bit)
    logic        awready;    // Write address ready (1 bit)

    // ===== WRITE DATA CHANNEL (W) =====
    logic [31:0] wdata;     // Write data (32 bits)
    logic [3:0]  wstrb;     // Write strobes (4 bits)
    logic        wlast;      // Write last (1 bit)
    logic        wuser;      // User signal (1 bit)
    logic        wvalid;     // Write valid (1 bit)
    logic        wready;     // Write ready (1 bit)

    // ===== WRITE RESPONSE CHANNEL (B) =====
    logic [3:0]  bid;       // Response ID (4 bits)
    logic [1:0]  bresp;     // Write response (2 bits)
    logic        buser;     // User signal (1 bit)
    logic        bvalid;    // Write response valid (1 bit)
    logic        bready;    // Response ready (1 bit)

    // ===== READ ADDRESS CHANNEL (AR) =====
    logic [3:0]  arid;      // Read address ID (4 bits)
    logic [31:0] araddr;    // Read address (32 bits)
    logic [7:0]  arlen;     // Burst length (8 bits)
    logic [2:0]  arsize;    // Burst size (3 bits)
    logic [1:0]  arburst;   // Burst type (2 bits)
    logic        arlock;     // Lock type (1 bit)
    logic [3:0]  arcache;   // Memory type (4 bits)
    logic [2:0]  arprot;    // Protection type (3 bits)
    logic [3:0]  arqos;     // Quality of service (4 bits)
    logic [3:0]  arregion;  // Region identifier (4 bits)
    logic        aruser;     // User signal (1 bit)
    logic        arvalid;    // Read address valid (1 bit)
    logic        arready;    // Read address ready (1 bit)

    // ===== READ DATA CHANNEL (R) =====
    logic [3:0]  rid;       // Read ID (4 bits)
    logic [31:0] rdata;     // Read data (32 bits)
    logic [1:0]  rresp;     // Read response (2 bits)
    logic        rlast;      // Read last (1 bit)
    logic        ruser;      // User signal (1 bit)
    logic        rvalid;     // Read valid (1 bit)
    logic        rready;     // Read ready (1 bit)

    // ===== CLOCKING BLOCKS =====
    // Slave perspective - receives requests, sends responses
    clocking slave_cb @(posedge clk);
        // Inputs (from master)
        input  awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid;
        input  wdata, wstrb, wlast, wuser, wvalid;
        input  bready;
        input  arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser, arvalid;
        input  rready;
        
        // Outputs (to master)
        output awready;
        output wready;
        output bid, bresp, buser, bvalid;
        output arready;
        output rid, rdata, rresp, rlast, ruser, rvalid;
    endclocking

    // ===== MODPORTS =====
    // Slave modport - for slave VIP
    modport slave_modport(
        clocking slave_cb,
        input  clk, resetn
    );

    // Monitor modport - for monitoring
    modport monitor_modport(
        input  clk, resetn,
        input  awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid, awready,
        input  wdata, wstrb, wlast, wuser, wvalid, wready,
        input  bid, bresp, buser, bvalid, bready,
        input  arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser, arvalid, arready,
        input  rid, rdata, rresp, rlast, ruser, rvalid, rready
    );

endinterface

`endif // AXI_SLAVE_INTERFACE_SV
//=============================================================================
// AXI Master Interface
//=============================================================================
// Generic interface for any AXI master (M0, M1, M2, M3)
// Contains only master-related functionality

`ifndef AXI_MASTER_INTERFACE_SV
`define AXI_MASTER_INTERFACE_SV

// AXI Master Interface
interface axi_master_interface(
    input logic clk,      // Clock input
    input logic resetn    // Active low reset input
);

    // ===== WRITE ADDRESS CHANNEL (AW) =====
    logic [3:0]  awid;      // Write address ID (4 bits)
    logic [31:0] awaddr;    // Write address (32 bits)
    logic [7:0]  awlen;     // Burst length (0-15)
    logic        awlock;    // Lock type
    logic [2:0]  awsize;    // Burst size
    logic [1:0]  awburst;   // Burst type
    logic [3:0]  awcache;   // Cache attributes
    logic [2:0]  awprot;    // Protection attributes
    logic [3:0]  awqos;     // Quality of service
    logic [3:0]  awregion;  // Region identifier
    logic        awvalid;   // Write address valid
    logic        awready;   // Write address ready (from slave)
    
    // ===== WRITE DATA CHANNEL (W) =====
    logic [31:0] wdata;     // Write data (32 bits)
    logic [3:0]  wstrb;     // Write strobes (4 bits for 32-bit data)
    logic        wlast;     // Write last
    logic        wvalid;    // Write valid
    logic        wready;    // Write ready (from slave)
    
    // ===== WRITE RESPONSE CHANNEL (B) =====
    logic [3:0]  bid;       // Write response ID (from slave)
    logic [1:0]  bresp;     // Write response (from slave)
    logic        bvalid;    // Write response valid (from slave)
    logic        bready;    // Write response ready
    
    // ===== READ ADDRESS CHANNEL (AR) =====
    logic [3:0]  arid;      // Read address ID
    logic [31:0] araddr;    // Read address
    logic [7:0]  arlen;     // Burst length (0-15)
    logic        arlock;    // Lock type
    logic [2:0]  arsize;    // Burst size
    logic [1:0]  arburst;   // Burst type
    logic [3:0]  arcache;   // Cache attributes
    logic [2:0]  arprot;    // Protection attributes
    logic [3:0]  arqos;     // Quality of service
    logic [3:0]  arregion;  // Region identifier
    logic        arvalid;   // Read address valid
    logic        arready;   // Read address ready (from slave)
    
    // ===== READ DATA CHANNEL (R) =====
    logic [3:0]  rid;       // Read ID (from slave)
    logic [31:0] rdata;     // Read data (from slave)
    logic [1:0]  rresp;     // Read response (from slave)
    logic        rlast;     // Read last (from slave)
    logic        rvalid;    // Read valid (from slave)
    logic        rready;    // Read ready
    
    // ===== MODPORTS =====
    
    // Master modport - for UVM driver/sequencer
    modport master (
        // Clock and reset
        input  clk, resetn,
        
        // Write Address Channel - Master drives, Slave receives
        output awid, awaddr, awlen, awlock, awsize, awburst, awcache, awprot, awqos, awregion, awvalid,
        input  awready,
        
        // Write Data Channel - Master drives, Slave receives
        output wdata, wstrb, wlast, wvalid,
        input  wready,
        
        // Write Response Channel - Slave drives, Master receives
        input  bid, bresp, bvalid,
        output bready,
        
        // Read Address Channel - Master drives, Slave receives
        output arid, araddr, arlen, arlock, arsize, arburst, arcache, arprot, arqos, arregion, arvalid,
        input  arready,
        
        // Read Data Channel - Slave drives, Master receives
        input  rid, rdata, rresp, rlast, rvalid,
        output rready
    );
    
    // Monitor modport - for UVM monitor (read-only)
    modport monitor (
        // Clock and reset
        input  clk, resetn,
        
        // All signals are inputs for monitoring
        input  awid, awaddr, awlen, awlock, awsize, awburst, awcache, awprot, awqos, awregion, awvalid, awready,
        input  wdata, wstrb, wlast, wvalid, wready,
        input  bid, bresp, bvalid, bready,
        input  arid, araddr, arlen, arlock, arsize, arburst, arcache, arprot, arqos, arregion, arvalid, arready,
        input  rid, rdata, rresp, rlast, rvalid, rready
    );
    
    // ===== CLOCKING BLOCKS =====
    
    // Clocking block for master driving (master perspective only)
    clocking master_cb @(posedge clk);
        // Write Address Channel - Master drives these
        output awid, awaddr, awlen, awlock, awsize, awburst, awcache, awprot, awqos, awregion, awvalid;
        input  awready;
        
        // Write Data Channel - Master drives these
        output wdata, wstrb, wlast, wvalid;
        input  wready;
        
        // Write Response Channel - Master receives these
        input  bid, bresp, bvalid;
        output bready;
        
        // Read Address Channel - Master drives these
        output arid, araddr, arlen, arlock, arsize, arburst, arcache, arprot, arqos, arregion, arvalid;
        input  arready;
        
        // Read Data Channel - Master receives these
        input  rid, rdata, rresp, rlast, rvalid;
        output rready;
    endclocking
    
    // ===== DEFAULT VALUES =====
    
    // Initialize interface signals
    initial begin
        // Write Address Channel
        awid = 0;
        awaddr = 0;
        awlen = 0;
        awlock = 0;
        awsize = 0;
        awburst = 0;
        awcache = 0;
        awprot = 0;
        awqos = 0;
        awregion = 0;
        awvalid = 0;
        
        // Write Data Channel
        wdata = 0;
        wstrb = 0;
        wlast = 0;
        wvalid = 0;
        
        // Write Response Channel
        bready = 0;
        
        // Read Address Channel
        arid = 0;
        araddr = 0;
        arlen = 0;
        arlock = 0;
        arsize = 0;
        arburst = 0;
        arcache = 0;
        arprot = 0;
        arqos = 0;
        arregion = 0;
        arvalid = 0;
        
        // Read Data Channel
        rready = 0;
    end
    
    // ===== ASSERTIONS =====
    
    // Write address handshake assertion
    property aw_handshake;
        @(posedge clk) disable iff (!resetn)
        awvalid && !awready |-> awvalid until awready;
    endproperty
    
    // Write data handshake assertion
    property w_handshake;
        @(posedge clk) disable iff (!resetn)
        wvalid && !wready |-> wvalid until wready;
    endproperty
    
    // Write response handshake assertion
    property b_handshake;
        @(posedge clk) disable iff (!resetn)
        bvalid && !bready |-> bvalid until bready;
    endproperty
    
    // Read address handshake assertion
    property ar_handshake;
        @(posedge clk) disable iff (!resetn)
        arvalid && !arready |-> arvalid until arready;
    endproperty
    
    // Read data handshake assertion
    property r_handshake;
        @(posedge clk) disable iff (!resetn)
        rvalid && !rready |-> rvalid until rready;
    endproperty
    
    // Assert handshake properties
    assert property (aw_handshake) else
        $error("AW handshake violation: awvalid not stable until awready");
    
    assert property (w_handshake) else
        $error("W handshake violation: wvalid not stable until wready");
    
    assert property (b_handshake) else
        $error("B handshake violation: bvalid not stable until bready");
    
    assert property (ar_handshake) else
        $error("AR handshake violation: arvalid not stable until arready");
    
    assert property (r_handshake) else
        $error("R handshake violation: rvalid not stable until rready");
    
endinterface : axi_master_interface

`endif // AXI_MASTER_INTERFACE_SV
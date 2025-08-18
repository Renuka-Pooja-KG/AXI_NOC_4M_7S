//=============================================================================
// AXI Interface Definition
//=============================================================================
// This file contains the base AXI interface definition with all AXI signals
// for both master and slave interfaces in the NOC verification environment.

`ifndef AXI_IF_SV
`define AXI_IF_SV

// AXI Interface
interface axi_if (input bit clk, input bit rstn);
    
    // Write Address Channel (AW)
    logic [3:0]  awid;      // Write address ID
    logic [31:0] awaddr;    // Write address
    logic [3:0]  awlen;     // Burst length
    logic [2:0]  awsize;    // Burst size
    logic [1:0]  awburst;   // Burst type
    logic        awlock;    // Lock type
    logic [3:0]  awcache;   // Memory type
    logic [2:0]  awprot;    // Protection type
    logic [3:0]  awqos;     // Quality of service
    logic [3:0]  awregion;  // Region identifier
    logic        awvalid;   // Write address valid
    logic        awready;   // Write address ready
    
    // Write Data Channel (W)
    logic [31:0] wdata;     // Write data
    logic [3:0]  wstrb;     // Write strobes
    logic        wlast;     // Write last
    logic        wvalid;    // Write valid
    logic        wready;    // Write ready
    
    // Write Response Channel (B)
    logic [5:0]  bid;       // Write response ID
    logic [1:0]  bresp;     // Write response
    logic        bvalid;    // Write response valid
    logic        bready;    // Response ready
    
    // Read Address Channel (AR)
    logic [3:0]  arid;      // Read address ID
    logic [31:0] araddr;    // Read address
    logic [3:0]  arlen;     // Burst length
    logic [2:0]  arsize;    // Burst size
    logic [1:0]  arburst;   // Burst type
    logic        arlock;    // Lock type
    logic [3:0]  arcache;   // Memory type
    logic [2:0]  arprot;    // Protection type
    logic [3:0]  arqos;     // Quality of service
    logic [3:0]  arregion;  // Region identifier
    logic        arvalid;   // Read address valid
    logic        arready;   // Read address ready
    
    // Read Data Channel (R)
    logic [5:0]  rid;       // Read ID
    logic [31:0] rdata;     // Read data
    logic [1:0]  rresp;     // Read response
    logic        rlast;     // Read last
    logic        rvalid;    // Read valid
    logic        rready;    // Read ready
    
    // Clock and Reset
    logic        axi_clk;   // AXI clock
    logic        axi_rstn;  // AXI reset (active low)
    
    // Clock and reset assignment
    assign axi_clk = clk;
    assign axi_rstn = rstn;
    
    // Modport for Master (drives address, data, control; receives ready, response)
    modport master (
        // Clock and Reset
        input  axi_clk, axi_rstn,
        
        // Write Address Channel
        output awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awvalid,
        input  awready,
        
        // Write Data Channel
        output wdata, wstrb, wlast, wvalid,
        input  wready,
        
        // Write Response Channel
        input  bid, bresp, bvalid,
        output bready,
        
        // Read Address Channel
        output arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, arvalid,
        input  arready,
        
        // Read Data Channel
        input  rid, rdata, rresp, rlast, rvalid,
        output rready
    );
    
    // Modport for Slave (receives address, data, control; drives ready, response)
    modport slave (
        // Clock and Reset
        input  axi_clk, axi_rstn,
        
        // Write Address Channel
        input  awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awvalid,
        output awready,
        
        // Write Data Channel
        input  wdata, wstrb, wlast, wvalid,
        output wready,
        
        // Write Response Channel
        output bid, bresp, bvalid,
        input  bready,
        
        // Read Address Channel
        input  arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, arvalid,
        output arready,
        
        // Read Data Channel
        output rid, rdata, rresp, rlast, rvalid,
        input  rready
    );
    
    // Modport for Monitor (observes all signals)
    modport monitor (
        // Clock and Reset
        input  axi_clk, axi_rstn,
        
        // Write Address Channel
        input  awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awvalid, awready,
        
        // Write Data Channel
        input  wdata, wstrb, wlast, wvalid, wready,
        
        // Write Response Channel
        input  bid, bresp, bvalid, bready,
        
        // Read Address Channel
        input  arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, arvalid, arready,
        
        // Read Data Channel
        input  rid, rdata, rresp, rlast, rvalid, rready
    );
    
    // Clocking block for synchronous operations
    clocking cb @(posedge axi_clk);
        // Write Address Channel
        input  awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awvalid, awready;
        
        // Write Data Channel
        input  wdata, wstrb, wlast, wvalid, wready;
        
        // Write Response Channel
        input  bid, bresp, bvalid, bready;
        
        // Read Address Channel
        input  arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, arvalid, arready;
        
        // Read Data Channel
        input  rid, rdata, rresp, rlast, rvalid, rready;
    endclocking
    
    // Default clocking for the interface
    default clocking cb;
    
    // Reset assertion task
    task automatic assert_reset();
        axi_rstn = 0;
        @(posedge axi_clk);
        @(posedge axi_clk);
        axi_rstn = 1;
        @(posedge axi_clk);
    endtask
    
    // Reset deassertion task
    task automatic deassert_reset();
        axi_rstn = 1;
        @(posedge axi_clk);
    endtask
    
    // Wait for reset task
    task automatic wait_for_reset();
        wait(axi_rstn == 0);
        wait(axi_rstn == 1);
        @(posedge axi_clk);
    endtask
    
    // Wait for clock edge task
    task automatic wait_for_clk(int num_clks = 1);
        repeat(num_clks) @(posedge axi_clk);
    endtask
    
endinterface : axi_if

`endif // AXI_IF_SV

//=============================================================================
// AXI Master 0 Interface
//=============================================================================
// This file contains the Master 0 specific AXI interface that has full access
// to all slaves (S0-S6) in the NOC verification environment.

`ifndef AXI_MASTER0_IF_SV
`define AXI_MASTER0_IF_SV

`include "axi_if.sv"

// AXI Master 0 Interface
interface axi_master0_if (input bit clk, input bit rstn);
    
    // Include base AXI interface
    axi_if axi_intf(clk, rstn);
    
    // Master 0 specific signals
    logic [3:0]  m0_awid;      // Master 0 write address ID
    logic [31:0] m0_awaddr;    // Master 0 write address
    logic [3:0]  m0_awlen;     // Master 0 burst length
    logic [2:0]  m0_awsize;    // Master 0 burst size
    logic [1:0]  m0_awburst;   // Master 0 burst type
    logic        m0_awlock;    // Master 0 lock type
    logic [3:0]  m0_awcache;   // Master 0 memory type
    logic [2:0]  m0_awprot;    // Master 0 protection type
    logic [3:0]  m0_awqos;     // Master 0 quality of service
    logic [3:0]  m0_awregion;  // Master 0 region identifier
    logic        m0_awvalid;   // Master 0 write address valid
    logic        m0_awready;   // Master 0 write address ready
    
    // Write Data Channel
    logic [31:0] m0_wdata;     // Master 0 write data
    logic [3:0]  m0_wstrb;     // Master 0 write strobes
    logic        m0_wlast;     // Master 0 write last
    logic        m0_wvalid;    // Master 0 write valid
    logic        m0_wready;    // Master 0 write ready
    
    // Write Response Channel
    logic [5:0]  m0_bid;       // Master 0 write response ID
    logic [1:0]  m0_bresp;     // Master 0 write response
    logic        m0_bvalid;    // Master 0 write response valid
    logic        m0_bready;    // Master 0 response ready
    
    // Read Address Channel
    logic [3:0]  m0_arid;      // Master 0 read address ID
    logic [31:0] m0_araddr;    // Master 0 read address
    logic [3:0]  m0_arlen;     // Master 0 burst length
    logic [2:0]  m0_arsize;    // Master 0 burst size
    logic [1:0]  m0_arburst;   // Master 0 burst type
    logic        m0_arlock;    // Master 0 lock type
    logic [3:0]  m0_arcache;   // Master 0 memory type
    logic [2:0]  m0_arprot;    // Master 0 protection type
    logic [3:0]  m0_arqos;     // Master 0 quality of service
    logic [3:0]  m0_arregion;  // Master 0 region identifier
    logic        m0_arvalid;   // Master 0 read address valid
    logic        m0_arready;   // Master 0 read address ready
    
    // Read Data Channel
    logic [5:0]  m0_rid;       // Master 0 read ID
    logic [31:0] m0_rdata;     // Master 0 read data
    logic [1:0]  m0_rresp;     // Master 0 read response
    logic        m0_rlast;     // Master 0 read last
    logic        m0_rvalid;    // Master 0 read valid
    logic        m0_rready;    // Master 0 read ready
    
    // Connect to base interface
    assign axi_intf.awid = m0_awid;
    assign axi_intf.awaddr = m0_awaddr;
    assign axi_intf.awlen = m0_awlen;
    assign axi_intf.awsize = m0_awsize;
    assign axi_intf.awburst = m0_awburst;
    assign axi_intf.awlock = m0_awlock;
    assign axi_intf.awcache = m0_awcache;
    assign axi_intf.awprot = m0_awprot;
    assign axi_intf.awqos = m0_awqos;
    assign axi_intf.awregion = m0_awregion;
    assign axi_intf.awvalid = m0_awvalid;
    assign m0_awready = axi_intf.awready;
    
    assign axi_intf.wdata = m0_wdata;
    assign axi_intf.wstrb = m0_wstrb;
    assign axi_intf.wlast = m0_wlast;
    assign axi_intf.wvalid = m0_wvalid;
    assign m0_wready = axi_intf.wready;
    
    assign m0_bid = axi_intf.bid;
    assign m0_bresp = axi_intf.bresp;
    assign m0_bvalid = axi_intf.bvalid;
    assign axi_intf.bready = m0_bready;
    
    assign axi_intf.arid = m0_arid;
    assign axi_intf.araddr = m0_araddr;
    assign axi_intf.arlen = m0_arlen;
    assign axi_intf.arsize = m0_arsize;
    assign axi_intf.arburst = m0_arburst;
    assign axi_intf.arlock = m0_arlock;
    assign axi_intf.arcache = m0_arcache;
    assign axi_intf.arprot = m0_arprot;
    assign axi_intf.arqos = m0_arqos;
    assign axi_intf.arregion = m0_arregion;
    assign axi_intf.arvalid = m0_arvalid;
    assign m0_arready = axi_intf.arready;
    
    assign m0_rid = axi_intf.rid;
    assign m0_rdata = axi_intf.rdata;
    assign m0_rresp = axi_intf.rresp;
    assign m0_rlast = axi_intf.rlast;
    assign m0_rvalid = axi_intf.rvalid;
    assign axi_intf.rready = m0_rready;
    
    // Master 0 specific modport
    modport master0 (
        // Clock and Reset
        input  clk, rstn,
        
        // Write Address Channel
        output m0_awid, m0_awaddr, m0_awlen, m0_awsize, m0_awburst, m0_awlock, m0_awcache, m0_awprot, m0_awqos, m0_awregion, m0_awvalid,
        input  m0_awready,
        
        // Write Data Channel
        output m0_wdata, m0_wstrb, m0_wlast, m0_wvalid,
        input  m0_wready,
        
        // Write Response Channel
        input  m0_bid, m0_bresp, m0_bvalid,
        output m0_bready,
        
        // Read Address Channel
        output m0_arid, m0_araddr, m0_arlen, m0_arsize, m0_arburst, m0_arlock, m0_arcache, m0_arprot, m0_arqos, m0_arregion, m0_arvalid,
        input  m0_arready,
        
        // Read Data Channel
        input  m0_rid, m0_rdata, m0_rresp, m0_rlast, m0_rvalid,
        output m0_rready
    );
    
    // Master 0 specific tasks
    task automatic m0_write_transaction(
        input  [31:0] addr,
        input  [31:0] data,
        input  [3:0]  len = 0,
        input  [2:0]  size = 2,
        input  [1:0]  burst = 1
    );
        // Write Address Phase
        m0_awaddr = addr;
        m0_awlen = len;
        m0_awsize = size;
        m0_awburst = burst;
        m0_awvalid = 1;
        
        wait(m0_awready);
        @(posedge clk);
        m0_awvalid = 0;
        
        // Write Data Phase
        m0_wdata = data;
        m0_wstrb = 4'hF;
        m0_wlast = (len == 0) ? 1 : 0;
        m0_wvalid = 1;
        
        wait(m0_wready);
        @(posedge clk);
        m0_wvalid = 0;
        
        // Write Response Phase
        m0_bready = 1;
        wait(m0_bvalid);
        @(posedge clk);
        m0_bready = 0;
    endtask
    
    task automatic m0_read_transaction(
        input  [31:0] addr,
        output [31:0] data,
        input  [3:0]  len = 0,
        input  [2:0]  size = 2,
        input  [1:0]  burst = 1
    );
        // Read Address Phase
        m0_araddr = addr;
        m0_arlen = len;
        m0_arsize = size;
        m0_arburst = burst;
        m0_arvalid = 1;
        
        wait(m0_arready);
        @(posedge clk);
        m0_arvalid = 0;
        
        // Read Data Phase
        m0_rready = 1;
        wait(m0_rvalid);
        data = m0_rdata;
        @(posedge clk);
        m0_rready = 0;
    endtask
    
    // Master 0 specific assertions
    property m0_awvalid_stable;
        @(posedge clk) disable iff (!rstn)
        m0_awvalid |-> ##[1:5] m0_awready;
    endproperty
    
    property m0_wvalid_stable;
        @(posedge clk) disable iff (!rstn)
        m0_wvalid |-> ##[1:5] m0_wready;
    endproperty
    
    property m0_arvalid_stable;
        @(posedge clk) disable iff (!rstn)
        m0_arvalid |-> ##[1:5] m0_arready;
    endproperty
    
    // Assertion instances
    assert property (m0_awvalid_stable) else
        $error("Master 0 AWVALID not stable until AWREADY");
    
    assert property (m0_wvalid_stable) else
        $error("Master 0 WVALID not stable until WREADY");
    
    assert property (m0_arvalid_stable) else
        $error("Master 0 ARVALID not stable until ARREADY");
    
endinterface : axi_master0_if

`endif // AXI_MASTER0_IF_SV

//=============================================================================
// AXI Master 2 Interface
//=============================================================================
// This file contains the Master 2 specific AXI interface that has restricted
// access to only slaves S1, S2, and S4 in the NOC verification environment.

`ifndef AXI_MASTER2_IF_SV
`define AXI_MASTER2_IF_SV

`include "axi_if.sv"

// AXI Master 2 Interface
interface axi_master2_if (input bit clk, input bit rstn);
    
    // Include base AXI interface
    axi_if axi_intf(clk, rstn);
    
    // Master 2 specific signals
    logic [3:0]  m2_awid;      // Master 2 write address ID
    logic [31:0] m2_awaddr;    // Master 2 write address
    logic [3:0]  m2_awlen;     // Master 2 burst length
    logic [2:0]  m2_awsize;    // Master 2 burst size
    logic [1:0]  m2_awburst;   // Master 2 burst type
    logic        m2_awlock;    // Master 2 lock type
    logic [3:0]  m2_awcache;   // Master 2 memory type
    logic [2:0]  m2_awprot;    // Master 2 protection type
    logic [3:0]  m2_awqos;     // Master 2 quality of service
    logic [3:0]  m2_awregion;  // Master 2 region identifier
    logic        m2_awvalid;   // Master 2 write address valid
    logic        m2_awready;   // Master 2 write address ready
    
    // Write Data Channel
    logic [31:0] m2_wdata;     // Master 2 write data
    logic [3:0]  m2_wstrb;     // Master 2 write strobes
    logic        m2_wlast;     // Master 2 write last
    logic        m2_wvalid;    // Master 2 write valid
    logic        m2_wready;    // Master 2 write ready
    
    // Write Response Channel
    logic [5:0]  m2_bid;       // Master 2 write response ID
    logic [1:0]  m2_bresp;     // Master 2 write response
    logic        m2_bvalid;    // Master 2 write response valid
    logic        m2_bready;    // Master 2 response ready
    
    // Read Address Channel
    logic [3:0]  m2_arid;      // Master 2 read address ID
    logic [31:0] m2_araddr;    // Master 2 read address
    logic [3:0]  m2_arlen;     // Master 2 burst length
    logic [2:0]  m2_arsize;    // Master 2 burst size
    logic [1:0]  m2_arburst;   // Master 2 burst type
    logic        m2_arlock;    // Master 2 lock type
    logic [3:0]  m2_arcache;   // Master 2 memory type
    logic [2:0]  m2_arprot;    // Master 2 protection type
    logic [3:0]  m2_arqos;     // Master 2 quality of service
    logic [3:0]  m2_arregion;  // Master 2 region identifier
    logic        m2_arvalid;   // Master 2 read address valid
    logic        m2_arready;   // Master 2 read address ready
    
    // Read Data Channel
    logic [5:0]  m2_rid;       // Master 2 read ID
    logic [31:0] m2_rdata;     // Master 2 read data
    logic [1:0]  m2_rresp;     // Master 2 read response
    logic        m2_rlast;     // Master 2 read last
    logic        m2_rvalid;    // Master 2 read valid
    logic        m2_rready;    // Master 2 read ready
    
    // Connect to base interface
    assign axi_intf.awid = m2_awid;
    assign axi_intf.awaddr = m2_awaddr;
    assign axi_intf.awlen = m2_awlen;
    assign axi_intf.awsize = m2_awsize;
    assign axi_intf.awburst = m2_awburst;
    assign axi_intf.awlock = m2_awlock;
    assign axi_intf.awcache = m2_awcache;
    assign axi_intf.awprot = m2_awprot;
    assign axi_intf.awqos = m2_awqos;
    assign axi_intf.awregion = m2_awregion;
    assign axi_intf.awvalid = m2_awvalid;
    assign m2_awready = axi_intf.awready;
    
    assign axi_intf.wdata = m2_wdata;
    assign axi_intf.wstrb = m2_wstrb;
    assign axi_intf.wlast = m2_wlast;
    assign axi_intf.wvalid = m2_wvalid;
    assign m2_wready = axi_intf.wready;
    
    assign m2_bid = axi_intf.bid;
    assign m2_bresp = axi_intf.bresp;
    assign m2_bvalid = axi_intf.bvalid;
    assign axi_intf.bready = m2_bready;
    
    assign axi_intf.arid = m2_arid;
    assign axi_intf.araddr = m2_araddr;
    assign axi_intf.arlen = m2_arlen;
    assign axi_intf.arsize = m2_arsize;
    assign axi_intf.arburst = m2_arburst;
    assign axi_intf.arlock = m2_arlock;
    assign axi_intf.arcache = m2_arcache;
    assign axi_intf.arprot = m2_arprot;
    assign axi_intf.arqos = m2_arqos;
    assign axi_intf.arregion = m2_arregion;
    assign axi_intf.arvalid = m2_arvalid;
    assign m2_arready = axi_intf.arready;
    
    assign m2_rid = axi_intf.rid;
    assign m2_rdata = axi_intf.rdata;
    assign m2_rresp = axi_intf.rresp;
    assign m2_rlast = axi_intf.rlast;
    assign m2_rvalid = axi_intf.rvalid;
    assign axi_intf.rready = m2_rready;
    
    // Master 2 specific modport
    modport master2 (
        // Clock and Reset
        input  clk, rstn,
        
        // Write Address Channel
        output m2_awid, m2_awaddr, m2_awlen, m2_awsize, m2_awburst, m2_awlock, m2_awcache, m2_awprot, m2_awqos, m2_awregion, m2_awvalid,
        input  m2_awready,
        
        // Write Data Channel
        output m2_wdata, m2_wstrb, m2_wlast, m2_wvalid,
        input  m2_wready,
        
        // Write Response Channel
        input  m2_bid, m2_bresp, m2_bvalid,
        output m2_bready,
        
        // Read Address Channel
        output m2_arid, m2_araddr, m2_arlen, m2_arsize, m2_arburst, m2_arlock, m2_arcache, m2_arprot, m2_arqos, m2_arregion, m2_arvalid,
        input  m2_arready,
        
        // Read Data Channel
        input  m2_rid, m2_rdata, m2_rresp, m2_rlast, m2_rvalid,
        output m2_rready
    );
    
    // Master 2 access control function
    function automatic bit m2_can_access_address(input [31:0] addr);
        // Master 2 can only access S1, S2, S4
        return ((addr >= 32'h0000_2000 && addr <= 32'h0000_2FFF) ||  // S1
                (addr >= 32'h0000_4000 && addr <= 32'h0000_4FFF) ||  // S2
                (addr >= 32'h0000_8000 && addr <= 32'h0000_8FFF));   // S4
    endfunction
    
    // Master 2 specific assertions
    property m2_awvalid_stable;
        @(posedge clk) disable iff (!rstn)
        m2_awvalid |-> ##[1:5] m2_awready;
    endproperty
    
    property m2_wvalid_stable;
        @(posedge clk) disable iff (!rstn)
        m2_wvalid |-> ##[1:5] m2_wready;
    endproperty
    
    property m2_arvalid_stable;
        @(posedge clk) disable iff (!rstn)
        m2_arvalid |-> ##[1:5] m2_arready;
    endproperty
    
    // Access control assertion
    property m2_access_control;
        @(posedge clk) disable iff (!rstn)
        (m2_awvalid || m2_arvalid) |-> m2_can_access_address(m2_awvalid ? m2_awaddr : m2_araddr);
    endproperty
    
    // Assertion instances
    assert property (m2_awvalid_stable) else
        $error("Master 2 AWVALID not stable until AWREADY");
    
    assert property (m2_wvalid_stable) else
        $error("Master 2 WVALID not stable until WREADY");
    
    assert property (m2_arvalid_stable) else
        $error("Master 2 ARVALID not stable until ARREADY");
    
    assert property (m2_access_control) else
        $error("Master 2 attempting to access unauthorized address");
    
endinterface : axi_master2_if

`endif // AXI_MASTER2_IF_SV

//=============================================================================
// AXI Master 3 Interface
//=============================================================================
// This file contains the Master 3 specific AXI interface that has restricted
// access to only slaves S1, S5, and S6 in the NOC verification environment.

`ifndef AXI_MASTER3_IF_SV
`define AXI_MASTER3_IF_SV

`include "axi_if.sv"

// AXI Master 3 Interface
interface axi_master3_if (input bit clk, input bit rstn);
    
    // Include base AXI interface
    axi_if axi_intf(clk, rstn);
    
    // Master 3 specific signals
    logic [3:0]  m3_awid;      // Master 3 write address ID
    logic [31:0] m3_awaddr;    // Master 3 write address
    logic [3:0]  m3_awlen;     // Master 3 burst length
    logic [2:0]  m3_awsize;    // Master 3 burst size
    logic [1:0]  m3_awburst;   // Master 3 burst type
    logic        m3_awlock;    // Master 3 lock type
    logic [3:0]  m3_awcache;   // Master 3 memory type
    logic [2:0]  m3_awprot;    // Master 3 protection type
    logic [3:0]  m3_awqos;     // Master 3 quality of service
    logic [3:0]  m3_awregion;  // Master 3 region identifier
    logic        m3_awvalid;   // Master 3 write address valid
    logic        m3_awready;   // Master 3 write address ready
    
    // Write Data Channel
    logic [31:0] m3_wdata;     // Master 3 write data
    logic [3:0]  m3_wstrb;     // Master 3 write strobes
    logic        m3_wlast;     // Master 3 write last
    logic        m3_wvalid;    // Master 3 write valid
    logic        m3_wready;    // Master 3 write ready
    
    // Write Response Channel
    logic [5:0]  m3_bid;       // Master 3 write response ID
    logic [1:0]  m3_bresp;     // Master 3 write response
    logic        m3_bvalid;    // Master 3 write response valid
    logic        m3_bready;    // Master 3 response ready
    
    // Read Address Channel
    logic [3:0]  m3_arid;      // Master 3 read address ID
    logic [31:0] m3_araddr;    // Master 3 read address
    logic [3:0]  m3_arlen;     // Master 3 burst length
    logic [2:0]  m3_arsize;    // Master 3 burst size
    logic [1:0]  m3_arburst;   // Master 3 burst type
    logic        m3_arlock;    // Master 3 lock type
    logic [3:0]  m3_arcache;   // Master 3 memory type
    logic [2:0]  m3_arprot;    // Master 3 protection type
    logic [3:0]  m3_arqos;     // Master 3 quality of service
    logic [3:0]  m3_arregion;  // Master 3 region identifier
    logic        m3_arvalid;   // Master 3 read address valid
    logic        m3_arready;   // Master 3 read address ready
    
    // Read Data Channel
    logic [5:0]  m3_rid;       // Master 3 read ID
    logic [31:0] m3_rdata;     // Master 3 read data
    logic [1:0]  m3_rresp;     // Master 3 read response
    logic        m3_rlast;     // Master 3 read last
    logic        m3_rvalid;    // Master 3 read valid
    logic        m3_rready;    // Master 3 read ready
    
    // Connect to base interface
    assign axi_intf.awid = m3_awid;
    assign axi_intf.awaddr = m3_awaddr;
    assign axi_intf.awlen = m3_awlen;
    assign axi_intf.awsize = m3_awsize;
    assign axi_intf.awburst = m3_awburst;
    assign axi_intf.awlock = m3_awlock;
    assign axi_intf.awcache = m3_awcache;
    assign axi_intf.awprot = m3_awprot;
    assign axi_intf.awqos = m3_awqos;
    assign axi_intf.awregion = m3_awregion;
    assign axi_intf.awvalid = m3_awvalid;
    assign m3_awready = axi_intf.awready;
    
    assign axi_intf.wdata = m3_wdata;
    assign axi_intf.wstrb = m3_wstrb;
    assign axi_intf.wlast = m3_wlast;
    assign axi_intf.wvalid = m3_wvalid;
    assign m3_wready = axi_intf.wready;
    
    assign m3_bid = axi_intf.bid;
    assign m3_bresp = axi_intf.bresp;
    assign m3_bvalid = axi_intf.bvalid;
    assign axi_intf.bready = m3_bready;
    
    assign axi_intf.arid = m3_arid;
    assign axi_intf.araddr = m3_araddr;
    assign axi_intf.arlen = m3_arlen;
    assign axi_intf.arsize = m3_arsize;
    assign axi_intf.arburst = m3_arburst;
    assign axi_intf.arlock = m3_arlock;
    assign axi_intf.arcache = m3_arcache;
    assign axi_intf.arprot = m3_arprot;
    assign axi_intf.arqos = m3_arqos;
    assign axi_intf.arregion = m3_arregion;
    assign axi_intf.arvalid = m3_arvalid;
    assign m3_arready = axi_intf.arready;
    
    assign m3_rid = axi_intf.rid;
    assign m3_rdata = axi_intf.rdata;
    assign m3_rresp = axi_intf.rresp;
    assign m3_rlast = axi_intf.rlast;
    assign m3_rvalid = axi_intf.rvalid;
    assign axi_intf.rready = m3_rready;
    
    // Master 3 specific modport
    modport master3 (
        // Clock and Reset
        input  clk, rstn,
        
        // Write Address Channel
        output m3_awid, m3_awaddr, m3_awlen, m3_awsize, m3_awburst, m3_awlock, m3_awcache, m3_awprot, m3_awqos, m3_awregion, m3_awvalid,
        input  m3_awready,
        
        // Write Data Channel
        output m3_wdata, m3_wstrb, m3_wlast, m3_wvalid,
        input  m3_wready,
        
        // Write Response Channel
        input  m3_bid, m3_bresp, m3_bvalid,
        output m3_bready,
        
        // Read Address Channel
        output m3_arid, m3_araddr, m3_arlen, m3_arsize, m3_arburst, m3_arlock, m3_arcache, m3_arprot, m3_arqos, m3_arregion, m3_arvalid,
        input  m3_arready,
        
        // Read Data Channel
        input  m3_rid, m3_rdata, m3_rresp, m3_rlast, m3_rvalid,
        output m3_rready
    );
    
    // Master 3 access control function
    function automatic bit m3_can_access_address(input [31:0] addr);
        // Master 3 can only access S1, S5, S6
        return ((addr >= 32'h0000_2000 && addr <= 32'h0000_2FFF) ||  // S1
                (addr >= 32'h0000_A000 && addr <= 32'h0000_AFFF) ||  // S5
                (addr >= 32'h0000_C000 && addr <= 32'h0000_CFFF));   // S6
    endfunction
    
    // Master 3 specific assertions
    property m3_awvalid_stable;
        @(posedge clk) disable iff (!rstn)
        m3_awvalid |-> ##[1:5] m3_awready;
    endproperty
    
    property m3_wvalid_stable;
        @(posedge clk) disable iff (!rstn)
        m3_wvalid |-> ##[1:5] m3_wready;
    endproperty
    
    property m3_arvalid_stable;
        @(posedge clk) disable iff (!rstn)
        m3_arvalid |-> ##[1:5] m3_arready;
    endproperty
    
    // Access control assertion
    property m3_access_control;
        @(posedge clk) disable iff (!rstn)
        (m3_awvalid || m3_arvalid) |-> m3_can_access_address(m3_awvalid ? m3_awaddr : m3_araddr);
    endproperty
    
    // Assertion instances
    assert property (m3_awvalid_stable) else
        $error("Master 3 AWVALID not stable until AWREADY");
    
    assert property (m3_wvalid_stable) else
        $error("Master 3 WVALID not stable until WREADY");
    
    assert property (m3_arvalid_stable) else
        $error("Master 3 ARVALID not stable until ARREADY");
    
    assert property (m3_access_control) else
        $error("Master 3 attempting to access unauthorized address");
    
endinterface : axi_master3_if

`endif // AXI_MASTER3_IF_SV

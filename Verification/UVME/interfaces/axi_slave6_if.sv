//=============================================================================
// AXI Slave 6 Interface
//=============================================================================
// This file contains the Slave 6 specific AXI interface with address range
// 0x0000_C000-0x0000_CFFF in the NOC verification environment.

`ifndef AXI_SLAVE6_IF_SV
`define AXI_SLAVE6_IF_SV

`include "axi_if.sv"

// AXI Slave 6 Interface
interface axi_slave6_if (input bit clk, input bit rstn);
    
    // Include base AXI interface
    axi_if axi_intf(clk, rstn);
    
    // Slave 6 specific signals
    logic        s6_awready;   // Slave 6 write address ready
    logic        s6_wready;    // Slave 6 write data ready
    logic [5:0]  s6_bid;       // Slave 6 write response ID
    logic [1:0]  s6_bresp;     // Slave 6 write response
    logic        s6_bvalid;    // Slave 6 write response valid
    logic        s6_arready;   // Slave 6 read address ready
    logic [5:0]  s6_rid;       // Slave 6 read ID
    logic [31:0] s6_rdata;     // Slave 6 read data
    logic [1:0]  s6_rresp;     // Slave 6 read response
    logic        s6_rlast;     // Slave 6 read last
    logic        s6_rvalid;    // Slave 6 read valid
    
    // Connect to base interface
    assign s6_awready = axi_intf.awready;
    assign s6_wready = axi_intf.wready;
    assign axi_intf.bid = s6_bid;
    assign axi_intf.bresp = s6_bresp;
    assign axi_intf.bvalid = s6_bvalid;
    assign s6_arready = axi_intf.arready;
    assign axi_intf.rid = s6_rid;
    assign axi_intf.rdata = s6_rdata;
    assign axi_intf.rresp = s6_rresp;
    assign axi_intf.rlast = s6_rlast;
    assign axi_intf.rvalid = s6_rvalid;
    
    // Slave 6 specific modport
    modport slave6 (
        // Clock and Reset
        input  clk, rstn,
        
        // Write Address Channel
        input  axi_intf.awid, axi_intf.awaddr, axi_intf.awlen, axi_intf.awsize, axi_intf.awburst, axi_intf.awlock, axi_intf.awcache, axi_intf.awprot, axi_intf.awqos, axi_intf.awregion, axi_intf.awvalid,
        output s6_awready,
        
        // Write Data Channel
        input  axi_intf.wdata, axi_intf.wstrb, axi_intf.wlast, axi_intf.wvalid,
        output s6_wready,
        
        // Write Response Channel
        output s6_bid, s6_bresp, s6_bvalid,
        input  axi_intf.bready,
        
        // Read Address Channel
        input  axi_intf.arid, axi_intf.araddr, axi_intf.arlen, axi_intf.arsize, axi_intf.arburst, axi_intf.arlock, axi_intf.arcache, axi_intf.arprot, axi_intf.arqos, axi_intf.arregion, axi_intf.arvalid,
        output s6_arready,
        
        // Read Data Channel
        output s6_rid, s6_rdata, s6_rresp, s6_rlast, s6_rvalid,
        input  axi_intf.rready
    );
    
    // Slave 6 address range constants
    localparam [31:0] S6_BASE_ADDR = 32'h0000_C000;
    localparam [31:0] S6_END_ADDR  = 32'h0000_CFFF;
    
    // Slave 6 address validation function
    function automatic bit s6_is_address_valid(input [31:0] addr);
        return (addr >= S6_BASE_ADDR && addr <= S6_END_ADDR);
    endfunction
    
    // Address range assertion
    property s6_address_range;
        @(posedge clk) disable iff (!rstn)
        (axi_intf.awvalid || axi_intf.arvalid) |-> s6_is_address_valid(axi_intf.awvalid ? axi_intf.awaddr : axi_intf.araddr);
    endproperty
    
    // Assertion instance
    assert property (s6_address_range) else
        $error("Slave 6 received transaction outside its address range");
    
endinterface : axi_slave6_if

`endif // AXI_SLAVE6_IF_SV

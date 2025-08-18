//=============================================================================
// AXI Slave 2 Interface
//=============================================================================
// This file contains the Slave 2 specific AXI interface with address range
// 0x0000_4000-0x0000_4FFF in the NOC verification environment.

`ifndef AXI_SLAVE2_IF_SV
`define AXI_SLAVE2_IF_SV

`include "axi_if.sv"

// AXI Slave 2 Interface
interface axi_slave2_if (input bit clk, input bit rstn);
    
    // Include base AXI interface
    axi_if axi_intf(clk, rstn);
    
    // Slave 2 specific signals
    logic        s2_awready;   // Slave 2 write address ready
    logic        s2_wready;    // Slave 2 write data ready
    logic [5:0]  s2_bid;       // Slave 2 write response ID
    logic [1:0]  s2_bresp;     // Slave 2 write response
    logic        s2_bvalid;    // Slave 2 write response valid
    logic        s2_arready;   // Slave 2 read address ready
    logic [5:0]  s2_rid;       // Slave 2 read ID
    logic [31:0] s2_rdata;     // Slave 2 read data
    logic [1:0]  s2_rresp;     // Slave 2 read response
    logic        s2_rlast;     // Slave 2 read last
    logic        s2_rvalid;    // Slave 2 read valid
    
    // Connect to base interface
    assign s2_awready = axi_intf.awready;
    assign s2_wready = axi_intf.wready;
    assign axi_intf.bid = s2_bid;
    assign axi_intf.bresp = s2_bresp;
    assign axi_intf.bvalid = s2_bvalid;
    assign s2_arready = axi_intf.arready;
    assign axi_intf.rid = s2_rid;
    assign axi_intf.rdata = s2_rdata;
    assign axi_intf.rresp = s2_rresp;
    assign axi_intf.rlast = s2_rlast;
    assign axi_intf.rvalid = s2_rvalid;
    
    // Slave 2 specific modport
    modport slave2 (
        // Clock and Reset
        input  clk, rstn,
        
        // Write Address Channel
        input  axi_intf.awid, axi_intf.awaddr, axi_intf.awlen, axi_intf.awsize, axi_intf.awburst, axi_intf.awlock, axi_intf.awcache, axi_intf.awprot, axi_intf.awqos, axi_intf.awregion, axi_intf.awvalid,
        output s2_awready,
        
        // Write Data Channel
        input  axi_intf.wdata, axi_intf.wstrb, axi_intf.wlast, axi_intf.wvalid,
        output s2_wready,
        
        // Write Response Channel
        output s2_bid, s2_bresp, s2_bvalid,
        input  axi_intf.bready,
        
        // Read Address Channel
        input  axi_intf.arid, axi_intf.araddr, axi_intf.arlen, axi_intf.arsize, axi_intf.arburst, axi_intf.arlock, axi_intf.arcache, axi_intf.arprot, axi_intf.arqos, axi_intf.arregion, axi_intf.arvalid,
        output s2_arready,
        
        // Read Data Channel
        output s2_rid, s2_rdata, s2_rresp, s2_rlast, s2_rvalid,
        input  axi_intf.rready
    );
    
    // Slave 2 address range constants
    localparam [31:0] S2_BASE_ADDR = 32'h0000_4000;
    localparam [31:0] S2_END_ADDR  = 32'h0000_4FFF;
    
    // Slave 2 address validation function
    function automatic bit s2_is_address_valid(input [31:0] addr);
        return (addr >= S2_BASE_ADDR && addr <= S2_END_ADDR);
    endfunction
    
    // Address range assertion
    property s2_address_range;
        @(posedge clk) disable iff (!rstn)
        (axi_intf.awvalid || axi_intf.arvalid) |-> s2_is_address_valid(axi_intf.awvalid ? axi_intf.awaddr : axi_intf.araddr);
    endproperty
    
    // Assertion instance
    assert property (s2_address_range) else
        $error("Slave 2 received transaction outside its address range");
    
endinterface : axi_slave2_if

`endif // AXI_SLAVE2_IF_SV

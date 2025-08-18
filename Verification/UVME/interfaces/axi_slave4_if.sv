//=============================================================================
// AXI Slave 4 Interface
//=============================================================================
// This file contains the Slave 4 specific AXI interface with address range
// 0x0000_8000-0x0000_8FFF in the NOC verification environment.

`ifndef AXI_SLAVE4_IF_SV
`define AXI_SLAVE4_IF_SV

`include "axi_if.sv"

// AXI Slave 4 Interface
interface axi_slave4_if (input bit clk, input bit rstn);
    
    // Include base AXI interface
    axi_if axi_intf(clk, rstn);
    
    // Slave 4 specific signals
    logic        s4_awready;   // Slave 4 write address ready
    logic        s4_wready;    // Slave 4 write data ready
    logic [5:0]  s4_bid;       // Slave 4 write response ID
    logic [1:0]  s4_bresp;     // Slave 4 write response
    logic        s4_bvalid;    // Slave 4 write response valid
    logic        s4_arready;   // Slave 4 read address ready
    logic [5:0]  s4_rid;       // Slave 4 read ID
    logic [31:0] s4_rdata;     // Slave 4 read data
    logic [1:0]  s4_rresp;     // Slave 4 read response
    logic        s4_rlast;     // Slave 4 read last
    logic        s4_rvalid;    // Slave 4 read valid
    
    // Connect to base interface
    assign s4_awready = axi_intf.awready;
    assign s4_wready = axi_intf.wready;
    assign axi_intf.bid = s4_bid;
    assign axi_intf.bresp = s4_bresp;
    assign axi_intf.bvalid = s4_bvalid;
    assign s4_arready = axi_intf.arready;
    assign axi_intf.rid = s4_rid;
    assign axi_intf.rdata = s4_rdata;
    assign axi_intf.rresp = s4_rresp;
    assign axi_intf.rlast = s4_rlast;
    assign axi_intf.rvalid = s4_rvalid;
    
    // Slave 4 specific modport
    modport slave4 (
        // Clock and Reset
        input  clk, rstn,
        
        // Write Address Channel
        input  axi_intf.awid, axi_intf.awaddr, axi_intf.awlen, axi_intf.awsize, axi_intf.awburst, axi_intf.awlock, axi_intf.awcache, axi_intf.awprot, axi_intf.awqos, axi_intf.awregion, axi_intf.awvalid,
        output s4_awready,
        
        // Write Data Channel
        input  axi_intf.wdata, axi_intf.wstrb, axi_intf.wlast, axi_intf.wvalid,
        output s4_wready,
        
        // Write Response Channel
        output s4_bid, s4_bresp, s4_bvalid,
        input  axi_intf.bready,
        
        // Read Address Channel
        input  axi_intf.arid, axi_intf.araddr, axi_intf.arlen, axi_intf.arsize, axi_intf.arburst, axi_intf.arlock, axi_intf.arcache, axi_intf.arprot, axi_intf.arqos, axi_intf.arregion, axi_intf.arvalid,
        output s4_arready,
        
        // Read Data Channel
        output s4_rid, s4_rdata, s4_rresp, s4_rlast, s4_rvalid,
        input  axi_intf.rready
    );
    
    // Slave 4 address range constants
    localparam [31:0] S4_BASE_ADDR = 32'h0000_8000;
    localparam [31:0] S4_END_ADDR  = 32'h0000_8FFF;
    
    // Slave 4 address validation function
    function automatic bit s4_is_address_valid(input [31:0] addr);
        return (addr >= S4_BASE_ADDR && addr <= S4_END_ADDR);
    endfunction
    
    // Address range assertion
    property s4_address_range;
        @(posedge clk) disable iff (!rstn)
        (axi_intf.awvalid || axi_intf.arvalid) |-> s4_is_address_valid(axi_intf.awvalid ? axi_intf.awaddr : axi_intf.araddr);
    endproperty
    
    // Assertion instance
    assert property (s4_address_range) else
        $error("Slave 4 received transaction outside its address range");
    
endinterface : axi_slave4_if

`endif // AXI_SLAVE4_IF_SV

//=============================================================================
// AXI Slave 5 Interface
//=============================================================================
// This file contains the Slave 5 specific AXI interface with address range
// 0x0000_A000-0x0000_AFFF in the NOC verification environment.

`ifndef AXI_SLAVE5_IF_SV
`define AXI_SLAVE5_IF_SV

`include "axi_if.sv"

// AXI Slave 5 Interface
interface axi_slave5_if (input bit clk, input bit rstn);
    
    // Include base AXI interface
    axi_if axi_intf(clk, rstn);
    
    // Slave 5 specific signals
    logic        s5_awready;   // Slave 5 write address ready
    logic        s5_wready;    // Slave 5 write data ready
    logic [5:0]  s5_bid;       // Slave 5 write response ID
    logic [1:0]  s5_bresp;     // Slave 5 write response
    logic        s5_bvalid;    // Slave 5 write response valid
    logic        s5_arready;   // Slave 5 read address ready
    logic [5:0]  s5_rid;       // Slave 5 read ID
    logic [31:0] s5_rdata;     // Slave 5 read data
    logic [1:0]  s5_rresp;     // Slave 5 read response
    logic        s5_rlast;     // Slave 5 read last
    logic        s5_rvalid;    // Slave 5 read valid
    
    // Connect to base interface
    assign s5_awready = axi_intf.awready;
    assign s5_wready = axi_intf.wready;
    assign axi_intf.bid = s5_bid;
    assign axi_intf.bresp = s5_bresp;
    assign axi_intf.bvalid = s5_bvalid;
    assign s5_arready = axi_intf.arready;
    assign axi_intf.rid = s5_rid;
    assign axi_intf.rdata = s5_rdata;
    assign axi_intf.rresp = s5_rresp;
    assign axi_intf.rlast = s5_rlast;
    assign axi_intf.rvalid = s5_rvalid;
    
    // Slave 5 specific modport
    modport slave5 (
        // Clock and Reset
        input  clk, rstn,
        
        // Write Address Channel
        input  axi_intf.awid, axi_intf.awaddr, axi_intf.awlen, axi_intf.awsize, axi_intf.awburst, axi_intf.awlock, axi_intf.awcache, axi_intf.awprot, axi_intf.awqos, axi_intf.awregion, axi_intf.awvalid,
        output s5_awready,
        
        // Write Data Channel
        input  axi_intf.wdata, axi_intf.wstrb, axi_intf.wlast, axi_intf.wvalid,
        output s5_wready,
        
        // Write Response Channel
        output s5_bid, s5_bresp, s5_bvalid,
        input  axi_intf.bready,
        
        // Read Address Channel
        input  axi_intf.arid, axi_intf.araddr, axi_intf.arlen, axi_intf.arsize, axi_intf.arburst, axi_intf.arlock, axi_intf.arcache, axi_intf.arprot, axi_intf.arqos, axi_intf.arregion, axi_intf.arvalid,
        output s5_arready,
        
        // Read Data Channel
        output s5_rid, s5_rdata, s5_rresp, s5_rlast, s5_rvalid,
        input  axi_intf.rready
    );
    
    // Slave 5 address range constants
    localparam [31:0] S5_BASE_ADDR = 32'h0000_A000;
    localparam [31:0] S5_END_ADDR  = 32'h0000_AFFF;
    
    // Slave 5 address validation function
    function automatic bit s5_is_address_valid(input [31:0] addr);
        return (addr >= S5_BASE_ADDR && addr <= S5_END_ADDR);
    endfunction
    
    // Address range assertion
    property s5_address_range;
        @(posedge clk) disable iff (!rstn)
        (axi_intf.awvalid || axi_intf.arvalid) |-> s5_is_address_valid(axi_intf.awvalid ? axi_intf.awaddr : axi_intf.araddr);
    endproperty
    
    // Assertion instance
    assert property (s5_address_range) else
        $error("Slave 5 received transaction outside its address range");
    
endinterface : axi_slave5_if

`endif // AXI_SLAVE5_IF_SV

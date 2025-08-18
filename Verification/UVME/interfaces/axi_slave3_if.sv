//=============================================================================
// AXI Slave 3 Interface
//=============================================================================
// This file contains the Slave 3 specific AXI interface with address range
// 0x0000_6000-0x0000_6FFF in the NOC verification environment.

`ifndef AXI_SLAVE3_IF_SV
`define AXI_SLAVE3_IF_SV

`include "axi_if.sv"

// AXI Slave 3 Interface
interface axi_slave3_if (input bit clk, input bit rstn);
    
    // Include base AXI interface
    axi_if axi_intf(clk, rstn);
    
    // Slave 3 specific signals
    logic        s3_awready;   // Slave 3 write address ready
    logic        s3_wready;    // Slave 3 write data ready
    logic [5:0]  s3_bid;       // Slave 3 write response ID
    logic [1:0]  s3_bresp;     // Slave 3 write response
    logic        s3_bvalid;    // Slave 3 write response valid
    logic        s3_arready;   // Slave 3 read address ready
    logic [5:0]  s3_rid;       // Slave 3 read ID
    logic [31:0] s3_rdata;     // Slave 3 read data
    logic [1:0]  s3_rresp;     // Slave 3 read response
    logic        s3_rlast;     // Slave 3 read last
    logic        s3_rvalid;    // Slave 3 read valid
    
    // Connect to base interface
    assign s3_awready = axi_intf.awready;
    assign s3_wready = axi_intf.wready;
    assign axi_intf.bid = s3_bid;
    assign axi_intf.bresp = s3_bresp;
    assign axi_intf.bvalid = s3_bvalid;
    assign s3_arready = axi_intf.arready;
    assign axi_intf.rid = s3_rid;
    assign axi_intf.rdata = s3_rdata;
    assign axi_intf.rresp = s3_rresp;
    assign axi_intf.rlast = s3_rlast;
    assign axi_intf.rvalid = s3_rvalid;
    
    // Slave 3 specific modport
    modport slave3 (
        // Clock and Reset
        input  clk, rstn,
        
        // Write Address Channel
        input  axi_intf.awid, axi_intf.awaddr, axi_intf.awlen, axi_intf.awsize, axi_intf.awburst, axi_intf.awlock, axi_intf.awcache, axi_intf.awprot, axi_intf.awqos, axi_intf.awregion, axi_intf.awvalid,
        output s3_awready,
        
        // Write Data Channel
        input  axi_intf.wdata, axi_intf.wstrb, axi_intf.wlast, axi_intf.wvalid,
        output s3_wready,
        
        // Write Response Channel
        output s3_bid, s3_bresp, s3_bvalid,
        input  axi_intf.bready,
        
        // Read Address Channel
        input  axi_intf.arid, axi_intf.araddr, axi_intf.arlen, axi_intf.arsize, axi_intf.arburst, axi_intf.arlock, axi_intf.arcache, axi_intf.arprot, axi_intf.arqos, axi_intf.arregion, axi_intf.arvalid,
        output s3_arready,
        
        // Read Data Channel
        output s3_rid, s3_rdata, s3_rresp, s3_rlast, s3_rvalid,
        input  axi_intf.rready
    );
    
    // Slave 3 address range constants
    localparam [31:0] S3_BASE_ADDR = 32'h0000_6000;
    localparam [31:0] S3_END_ADDR  = 32'h0000_6FFF;
    
    // Slave 3 address validation function
    function automatic bit s3_is_address_valid(input [31:0] addr);
        return (addr >= S3_BASE_ADDR && addr <= S3_END_ADDR);
    endfunction
    
    // Address range assertion
    property s3_address_range;
        @(posedge clk) disable iff (!rstn)
        (axi_intf.awvalid || axi_intf.arvalid) |-> s3_is_address_valid(axi_intf.awvalid ? axi_intf.awaddr : axi_intf.araddr);
    endproperty
    
    // Assertion instance
    assert property (s3_address_range) else
        $error("Slave 3 received transaction outside its address range");
    
endinterface : axi_slave3_if

`endif // AXI_SLAVE3_IF_SV

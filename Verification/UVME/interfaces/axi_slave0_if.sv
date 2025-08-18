//=============================================================================
// AXI Slave 0 Interface
//=============================================================================
// This file contains the Slave 0 specific AXI interface with address range
// 0x0000_0000-0x0000_0FFF in the NOC verification environment.

`ifndef AXI_SLAVE0_IF_SV
`define AXI_SLAVE0_IF_SV

`include "axi_if.sv"

// AXI Slave 0 Interface
interface axi_slave0_if (input bit clk, input bit rstn);
    
    // Include base AXI interface
    axi_if axi_intf(clk, rstn);
    
    // Slave 0 specific signals
    logic        s0_awready;   // Slave 0 write address ready
    logic        s0_wready;    // Slave 0 write data ready
    logic [5:0]  s0_bid;       // Slave 0 write response ID
    logic [1:0]  s0_bresp;     // Slave 0 write response
    logic        s0_bvalid;    // Slave 0 write response valid
    logic        s0_arready;   // Slave 0 read address ready
    logic [5:0]  s0_rid;       // Slave 0 read ID
    logic [31:0] s0_rdata;     // Slave 0 read data
    logic [1:0]  s0_rresp;     // Slave 0 read response
    logic        s0_rlast;     // Slave 0 read last
    logic        s0_rvalid;    // Slave 0 read valid
    
    // Connect to base interface
    assign s0_awready = axi_intf.awready;
    assign s0_wready = axi_intf.wready;
    assign axi_intf.bid = s0_bid;
    assign axi_intf.bresp = s0_bresp;
    assign axi_intf.bvalid = s0_bvalid;
    assign s0_arready = axi_intf.arready;
    assign axi_intf.rid = s0_rid;
    assign axi_intf.rdata = s0_rdata;
    assign axi_intf.rresp = s0_rresp;
    assign axi_intf.rlast = s0_rlast;
    assign axi_intf.rvalid = s0_rvalid;
    
    // Slave 0 specific modport
    modport slave0 (
        // Clock and Reset
        input  clk, rstn,
        
        // Write Address Channel
        input  axi_intf.awid, axi_intf.awaddr, axi_intf.awlen, axi_intf.awsize, axi_intf.awburst, axi_intf.awlock, axi_intf.awcache, axi_intf.awprot, axi_intf.awqos, axi_intf.awregion, axi_intf.awvalid,
        output s0_awready,
        
        // Write Data Channel
        input  axi_intf.wdata, axi_intf.wstrb, axi_intf.wlast, axi_intf.wvalid,
        output s0_wready,
        
        // Write Response Channel
        output s0_bid, s0_bresp, s0_bvalid,
        input  axi_intf.bready,
        
        // Read Address Channel
        input  axi_intf.arid, axi_intf.araddr, axi_intf.arlen, axi_intf.arsize, axi_intf.arburst, axi_intf.arlock, axi_intf.arcache, axi_intf.arprot, axi_intf.arqos, axi_intf.arregion, axi_intf.arvalid,
        output s0_arready,
        
        // Read Data Channel
        output s0_rid, s0_rdata, s0_rresp, s0_rlast, s0_rvalid,
        input  axi_intf.rready
    );
    
    // Slave 0 address range constants
    localparam [31:0] S0_BASE_ADDR = 32'h0000_0000;
    localparam [31:0] S0_END_ADDR  = 32'h0000_0FFF;
    
    // Slave 0 specific tasks
    task automatic s0_respond_to_write(
        input [5:0]  bid,
        input [1:0]  bresp = 2'b00,  // OKAY
        input int    delay = 0
    );
        // Wait for delay if specified
        repeat(delay) @(posedge clk);
        
        // Send write response
        s0_bid = bid;
        s0_bresp = bresp;
        s0_bvalid = 1;
        
        wait(axi_intf.bready);
        @(posedge clk);
        s0_bvalid = 0;
    endtask
    
    task automatic s0_respond_to_read(
        input [5:0]  rid,
        input [31:0] rdata,
        input [1:0]  rresp = 2'b00,  // OKAY
        input int    delay = 0
    );
        // Wait for delay if specified
        repeat(delay) @(posedge clk);
        
        // Send read response
        s0_rid = rid;
        s0_rdata = rdata;
        s0_rresp = rresp;
        s0_rlast = 1;
        s0_rvalid = 1;
        
        wait(axi_intf.rready);
        @(posedge clk);
        s0_rvalid = 0;
    endtask
    
    // Slave 0 address validation function
    function automatic bit s0_is_address_valid(input [31:0] addr);
        return (addr >= S0_BASE_ADDR && addr <= S0_END_ADDR);
    endfunction
    
    // Slave 0 specific assertions
    property s0_awready_stable;
        @(posedge clk) disable iff (!rstn)
        s0_awready |-> ##[1:5] axi_intf.awvalid;
    endproperty
    
    property s0_wready_stable;
        @(posedge clk) disable iff (!rstn)
        s0_wready |-> ##[1:5] axi_intf.wvalid;
    endproperty
    
    property s0_arready_stable;
        @(posedge clk) disable iff (!rstn)
        s0_arready |-> ##[1:5] axi_intf.arvalid;
    endproperty
    
    property s0_bvalid_stable;
        @(posedge clk) disable iff (!rstn)
        s0_bvalid |-> ##[1:5] axi_intf.bready;
    endproperty
    
    property s0_rvalid_stable;
        @(posedge clk) disable iff (!rstn)
        s0_rvalid |-> ##[1:5] axi_intf.rready;
    endproperty
    
    // Address range assertion
    property s0_address_range;
        @(posedge clk) disable iff (!rstn)
        (axi_intf.awvalid || axi_intf.arvalid) |-> s0_is_address_valid(axi_intf.awvalid ? axi_intf.awaddr : axi_intf.araddr);
    endproperty
    
    // Assertion instances
    assert property (s0_awready_stable) else
        $error("Slave 0 AWREADY not stable until AWVALID");
    
    assert property (s0_wready_stable) else
        $error("Slave 0 WREADY not stable until WVALID");
    
    assert property (s0_arready_stable) else
        $error("Slave 0 ARREADY not stable until ARVALID");
    
    assert property (s0_bvalid_stable) else
        $error("Slave 0 BVALID not stable until BREADY");
    
    assert property (s0_rvalid_stable) else
        $error("Slave 0 RVALID not stable until RREADY");
    
    assert property (s0_address_range) else
        $error("Slave 0 received transaction outside its address range");
    
endinterface : axi_slave0_if

`endif // AXI_SLAVE0_IF_SV

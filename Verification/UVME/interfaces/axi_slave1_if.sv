//=============================================================================
// AXI Slave 1 Interface
//=============================================================================
// This file contains the Slave 1 specific AXI interface with address range
// 0x0000_2000-0x0000_2FFF in the NOC verification environment.

`ifndef AXI_SLAVE1_IF_SV
`define AXI_SLAVE1_IF_SV

`include "axi_if.sv"

// AXI Slave 1 Interface
interface axi_slave1_if (input bit clk, input bit rstn);
    
    // Include base AXI interface
    axi_if axi_intf(clk, rstn);
    
    // Slave 1 specific signals
    logic        s1_awready;   // Slave 1 write address ready
    logic        s1_wready;    // Slave 1 write data ready
    logic [5:0]  s1_bid;       // Slave 1 write response ID
    logic [1:0]  s1_bresp;     // Slave 1 write response
    logic        s1_bvalid;    // Slave 1 write response valid
    logic        s1_arready;   // Slave 1 read address ready
    logic [5:0]  s1_rid;       // Slave 1 read ID
    logic [31:0] s1_rdata;     // Slave 1 read data
    logic [1:0]  s1_rresp;     // Slave 1 read response
    logic        s1_rlast;     // Slave 1 read last
    logic        s1_rvalid;    // Slave 1 read valid
    
    // Connect to base interface
    assign s1_awready = axi_intf.awready;
    assign s1_wready = axi_intf.wready;
    assign axi_intf.bid = s1_bid;
    assign axi_intf.bresp = s1_bresp;
    assign axi_intf.bvalid = s1_bvalid;
    assign s1_arready = axi_intf.arready;
    assign axi_intf.rid = s1_rid;
    assign axi_intf.rdata = s1_rdata;
    assign axi_intf.rresp = s1_rresp;
    assign axi_intf.rlast = s1_rlast;
    assign axi_intf.rvalid = s1_rvalid;
    
    // Slave 1 specific modport
    modport slave1 (
        // Clock and Reset
        input  clk, rstn,
        
        // Write Address Channel
        input  axi_intf.awid, axi_intf.awaddr, axi_intf.awlen, axi_intf.awsize, axi_intf.awburst, axi_intf.awlock, axi_intf.awcache, axi_intf.awprot, axi_intf.awqos, axi_intf.awregion, axi_intf.awvalid,
        output s1_awready,
        
        // Write Data Channel
        input  axi_intf.wdata, axi_intf.wstrb, axi_intf.wlast, axi_intf.wvalid,
        output s1_wready,
        
        // Write Response Channel
        output s1_bid, s1_bresp, s1_bvalid,
        input  axi_intf.bready,
        
        // Read Address Channel
        input  axi_intf.arid, axi_intf.araddr, axi_intf.arlen, axi_intf.arsize, axi_intf.arburst, axi_intf.arlock, axi_intf.arcache, axi_intf.arprot, axi_intf.arqos, axi_intf.arregion, axi_intf.arvalid,
        output s1_arready,
        
        // Read Data Channel
        output s1_rid, s1_rdata, s1_rresp, s1_rlast, s1_rvalid,
        input  axi_intf.rready
    );
    
    // Slave 1 address range constants
    localparam [31:0] S1_BASE_ADDR = 32'h0000_2000;
    localparam [31:0] S1_END_ADDR  = 32'h0000_2FFF;
    
    // Slave 1 specific tasks
    task automatic s1_respond_to_write(
        input [5:0]  bid,
        input [1:0]  bresp = 2'b00,  // OKAY
        input int    delay = 0
    );
        // Wait for delay if specified
        repeat(delay) @(posedge clk);
        
        // Send write response
        s1_bid = bid;
        s1_bresp = bresp;
        s1_bvalid = 1;
        
        wait(axi_intf.bready);
        @(posedge clk);
        s1_bvalid = 0;
    endtask
    
    task automatic s1_respond_to_read(
        input [5:0]  rid,
        input [31:0] rdata,
        input [1:0]  rresp = 2'b00,  // OKAY
        input int    delay = 0
    );
        // Wait for delay if specified
        repeat(delay) @(posedge clk);
        
        // Send read response
        s1_rid = rid;
        s1_rdata = rdata;
        s1_rresp = rresp;
        s1_rlast = 1;
        s1_rvalid = 1;
        
        wait(axi_intf.rready);
        @(posedge clk);
        s1_rvalid = 0;
    endtask
    
    // Slave 1 address validation function
    function automatic bit s1_is_address_valid(input [31:0] addr);
        return (addr >= S1_BASE_ADDR && addr <= S1_END_ADDR);
    endfunction
    
    // Slave 1 specific assertions
    property s1_awready_stable;
        @(posedge clk) disable iff (!rstn)
        s1_awready |-> ##[1:5] axi_intf.awvalid;
    endproperty
    
    property s1_wready_stable;
        @(posedge clk) disable iff (!rstn)
        s1_wready |-> ##[1:5] axi_intf.wvalid;
    endproperty
    
    property s1_arready_stable;
        @(posedge clk) disable iff (!rstn)
        s1_arready |-> ##[1:5] axi_intf.arvalid;
    endproperty
    
    property s1_bvalid_stable;
        @(posedge clk) disable iff (!rstn)
        s1_bvalid |-> ##[1:5] axi_intf.bready;
    endproperty
    
    property s1_rvalid_stable;
        @(posedge clk) disable iff (!rstn)
        s1_rvalid |-> ##[1:5] axi_intf.rready;
    endproperty
    
    // Address range assertion
    property s1_address_range;
        @(posedge clk) disable iff (!rstn)
        (axi_intf.awvalid || axi_intf.arvalid) |-> s1_is_address_valid(axi_intf.awvalid ? axi_intf.awaddr : axi_intf.araddr);
    endproperty
    
    // Assertion instances
    assert property (s1_awready_stable) else
        $error("Slave 1 AWREADY not stable until AWVALID");
    
    assert property (s1_wready_stable) else
        $error("Slave 1 WREADY not stable until WVALID");
    
    assert property (s1_arready_stable) else
        $error("Slave 1 ARREADY not stable until ARVALID");
    
    assert property (s1_bvalid_stable) else
        $error("Slave 1 BVALID not stable until BREADY");
    
    assert property (s1_rvalid_stable) else
        $error("Slave 1 RVALID not stable until RREADY");
    
    assert property (s1_address_range) else
        $error("Slave 1 received transaction outside its address range");
    
endinterface : axi_slave1_if

`endif // AXI_SLAVE1_IF_SV

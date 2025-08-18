//=============================================================================
// AXI Master 1 Interface
//=============================================================================
// This file contains the Master 1 specific AXI interface that has restricted
// access to only slaves S1, S3, and S4 in the NOC verification environment.

`ifndef AXI_MASTER1_IF_SV
`define AXI_MASTER1_IF_SV

`include "axi_if.sv"

// AXI Master 1 Interface
interface axi_master1_if (input bit clk, input bit rstn);
    
    // Include base AXI interface
    axi_if axi_intf(clk, rstn);
    
    // Master 1 specific signals
    logic [3:0]  m1_awid;      // Master 1 write address ID
    logic [31:0] m1_awaddr;    // Master 1 write address
    logic [3:0]  m1_awlen;     // Master 1 burst length
    logic [2:0]  m1_awsize;    // Master 1 burst size
    logic [1:0]  m1_awburst;   // Master 1 burst type
    logic        m1_awlock;    // Master 1 lock type
    logic [3:0]  m1_awcache;   // Master 1 memory type
    logic [2:0]  m1_awprot;    // Master 1 protection type
    logic [3:0]  m1_awqos;     // Master 1 quality of service
    logic [3:0]  m1_awregion;  // Master 1 region identifier
    logic        m1_awvalid;   // Master 1 write address valid
    logic        m1_awready;   // Master 1 write address ready
    
    // Write Data Channel
    logic [31:0] m1_wdata;     // Master 1 write data
    logic [3:0]  m1_wstrb;     // Master 1 write strobes
    logic        m1_wlast;     // Master 1 write last
    logic        m1_wvalid;    // Master 1 write valid
    logic        m1_wready;    // Master 1 write ready
    
    // Write Response Channel
    logic [5:0]  m1_bid;       // Master 1 write response ID
    logic [1:0]  m1_bresp;     // Master 1 write response
    logic        m1_bvalid;    // Master 1 write response valid
    logic        m1_bready;    // Master 1 response ready
    
    // Read Address Channel
    logic [3:0]  m1_arid;      // Master 1 read address ID
    logic [31:0] m1_araddr;    // Master 1 read address
    logic [3:0]  m1_arlen;     // Master 1 burst length
    logic [2:0]  m1_arsize;    // Master 1 burst size
    logic [1:0]  m1_arburst;   // Master 1 burst type
    logic        m1_arlock;    // Master 1 lock type
    logic [3:0]  m1_arcache;   // Master 1 memory type
    logic [2:0]  m1_arprot;    // Master 1 protection type
    logic [3:0]  m1_arqos;     // Master 1 quality of service
    logic [3:0]  m1_arregion;  // Master 1 region identifier
    logic        m1_arvalid;   // Master 1 read address valid
    logic        m1_arready;   // Master 1 read address ready
    
    // Read Data Channel
    logic [5:0]  m1_rid;       // Master 1 read ID
    logic [31:0] m1_rdata;     // Master 1 read data
    logic [1:0]  m1_rresp;     // Master 1 read response
    logic        m1_rlast;     // Master 1 read last
    logic        m1_rvalid;    // Master 1 read valid
    logic        m1_rready;    // Master 1 read ready
    
    // Connect to base interface
    assign axi_intf.awid = m1_awid;
    assign axi_intf.awaddr = m1_awaddr;
    assign axi_intf.awlen = m1_awlen;
    assign axi_intf.awsize = m1_awsize;
    assign axi_intf.awburst = m1_awburst;
    assign axi_intf.awlock = m1_awlock;
    assign axi_intf.awcache = m1_awcache;
    assign axi_intf.awprot = m1_awprot;
    assign axi_intf.awqos = m1_awqos;
    assign axi_intf.awregion = m1_awregion;
    assign axi_intf.awvalid = m1_awvalid;
    assign m1_awready = axi_intf.awready;
    
    assign axi_intf.wdata = m1_wdata;
    assign axi_intf.wstrb = m1_wstrb;
    assign axi_intf.wlast = m1_wlast;
    assign axi_intf.wvalid = m1_wvalid;
    assign m1_wready = axi_intf.wready;
    
    assign m1_bid = axi_intf.bid;
    assign m1_bresp = axi_intf.bresp;
    assign m1_bvalid = axi_intf.bvalid;
    assign axi_intf.bready = m1_bready;
    
    assign axi_intf.arid = m1_arid;
    assign axi_intf.araddr = m1_araddr;
    assign axi_intf.arlen = m1_arlen;
    assign axi_intf.arsize = m1_arsize;
    assign axi_intf.arburst = m1_arburst;
    assign axi_intf.arlock = m1_arlock;
    assign axi_intf.arcache = m1_arcache;
    assign axi_intf.arprot = m1_arprot;
    assign axi_intf.arqos = m1_arqos;
    assign axi_intf.arregion = m1_arregion;
    assign axi_intf.arvalid = m1_arvalid;
    assign m1_arready = axi_intf.arready;
    
    assign m1_rid = axi_intf.rid;
    assign m1_rdata = axi_intf.rdata;
    assign m1_rresp = axi_intf.rresp;
    assign m1_rlast = axi_intf.rlast;
    assign m1_rvalid = axi_intf.rvalid;
    assign axi_intf.rready = m1_rready;
    
    // Master 1 specific modport
    modport master1 (
        // Clock and Reset
        input  clk, rstn,
        
        // Write Address Channel
        output m1_awid, m1_awaddr, m1_awlen, m1_awsize, m1_awburst, m1_awlock, m1_awcache, m1_awprot, m1_awqos, m1_awregion, m1_awvalid,
        input  m1_awready,
        
        // Write Data Channel
        output m1_wdata, m1_wstrb, m1_wlast, m1_wvalid,
        input  m1_wready,
        
        // Write Response Channel
        input  m1_bid, m1_bresp, m1_bvalid,
        output m1_bready,
        
        // Read Address Channel
        output m1_arid, m1_araddr, m1_arlen, m1_arsize, m1_arburst, m1_arlock, m1_arcache, m1_arprot, m1_arqos, m1_arregion, m1_arvalid,
        input  m1_arready,
        
        // Read Data Channel
        input  m1_rid, m1_rdata, m1_rresp, m1_rlast, m1_rvalid,
        output m1_rready
    );
    
    // Master 1 specific tasks with access control
    task automatic m1_write_transaction(
        input  [31:0] addr,
        input  [31:0] data,
        input  [3:0]  len = 0,
        input  [2:0]  size = 2,
        input  [1:0]  burst = 1
    );
        // Check access control for Master 1
        if (!m1_can_access_address(addr)) begin
            $error("Master 1 cannot access address 0x%08X - Access denied", addr);
            return;
        end
        
        // Write Address Phase
        m1_awaddr = addr;
        m1_awlen = len;
        m1_awsize = size;
        m1_awburst = burst;
        m1_awvalid = 1;
        
        wait(m1_awready);
        @(posedge clk);
        m1_awvalid = 0;
        
        // Write Data Phase
        m1_wdata = data;
        m1_wstrb = 4'hF;
        m1_wlast = (len == 0) ? 1 : 0;
        m1_wvalid = 1;
        
        wait(m1_wready);
        @(posedge clk);
        m1_wvalid = 0;
        
        // Write Response Phase
        m1_bready = 1;
        wait(m1_bvalid);
        @(posedge clk);
        m1_bready = 0;
    endtask
    
    task automatic m1_read_transaction(
        input  [31:0] addr,
        output [31:0] data,
        input  [3:0]  len = 0,
        input  [2:0]  size = 2,
        input  [1:0]  burst = 1
    );
        // Check access control for Master 1
        if (!m1_can_access_address(addr)) begin
            $error("Master 1 cannot access address 0x%08X - Access denied", addr);
            return;
        end
        
        // Read Address Phase
        m1_araddr = addr;
        m1_arlen = len;
        m1_arsize = size;
        m1_arburst = burst;
        m1_arvalid = 1;
        
        wait(m1_arready);
        @(posedge clk);
        m1_arvalid = 0;
        
        // Read Data Phase
        m1_rready = 1;
        wait(m1_rvalid);
        data = m1_rdata;
        @(posedge clk);
        m1_rready = 0;
    endtask
    
    // Master 1 access control function
    function automatic bit m1_can_access_address(input [31:0] addr);
        // Master 1 can only access S1, S3, S4
        return ((addr >= 32'h0000_2000 && addr <= 32'h0000_2FFF) ||  // S1
                (addr >= 32'h0000_6000 && addr <= 32'h0000_6FFF) ||  // S3
                (addr >= 32'h0000_8000 && addr <= 32'h0000_8FFF));   // S4
    endfunction
    
    // Master 1 specific assertions
    property m1_awvalid_stable;
        @(posedge clk) disable iff (!rstn)
        m1_awvalid |-> ##[1:5] m1_awready;
    endproperty
    
    property m1_wvalid_stable;
        @(posedge clk) disable iff (!rstn)
        m1_wvalid |-> ##[1:5] m1_wready;
    endproperty
    
    property m1_arvalid_stable;
        @(posedge clk) disable iff (!rstn)
        m1_arvalid |-> ##[1:5] m1_arready;
    endproperty
    
    // Access control assertion
    property m1_access_control;
        @(posedge clk) disable iff (!rstn)
        (m1_awvalid || m1_arvalid) |-> m1_can_access_address(m1_awvalid ? m1_awaddr : m1_araddr);
    endproperty
    
    // Assertion instances
    assert property (m1_awvalid_stable) else
        $error("Master 1 AWVALID not stable until AWREADY");
    
    assert property (m1_wvalid_stable) else
        $error("Master 1 WVALID not stable until WREADY");
    
    assert property (m1_arvalid_stable) else
        $error("Master 1 ARVALID not stable until ARREADY");
    
    assert property (m1_access_control) else
        $error("Master 1 attempting to access unauthorized address");
    
endinterface : axi_master1_if

`endif // AXI_MASTER1_IF_SV

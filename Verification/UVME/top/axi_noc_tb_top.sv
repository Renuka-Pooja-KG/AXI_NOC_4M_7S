//=============================================================================
// AXI NOC Testbench Top Module
//=============================================================================
// Top-level testbench with DUT instantiation and all interfaces

`ifndef AXI_NOC_TB_TOP_SV
`define AXI_NOC_TB_TOP_SV

// Include necessary files
`include "axi_master_interface.sv"
`include "axi_slave_interface.sv"

// Testbench top module
module axi_noc_tb_top;

    // ===== CLOCK AND RESET GENERATION =====
    logic clk;
    logic resetn;
    
    // Clock generation (100MHz = 10ns period)
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Reset generation
    initial begin
        resetn = 0;
        #100 resetn = 1;
    end

    // ===== MASTER INTERFACES =====
    // Master 0 - has access to all slaves (S0-S6)
    axi_master_interface master0_if(clk, resetn);
    
    // Master 1 - has access to slaves S0, S1, S2
    axi_master_interface master1_if(clk, resetn);
    
    // Master 2 - has access to slaves S0, S1, S2
    axi_master_interface master2_if(clk, resetn);
    
    // Master 3 - has access to slaves S0, S1, S2
    axi_master_interface master3_if(clk, resetn);

    // ===== SLAVE INTERFACES =====
    // Slave 0 - accessible by all masters
    axi_slave_interface slave0_if(clk, resetn);
    
    // Slave 1 - accessible by all masters
    axi_slave_interface slave1_if(clk, resetn);
    
    // Slave 2 - accessible by all masters
    axi_slave_interface slave2_if(clk, resetn);
    
    // Slave 3 - accessible only by Master 0
    axi_slave_interface slave3_if(clk, resetn);
    
    // Slave 4 - accessible only by Master 0
    axi_slave_interface slave4_if(clk, resetn);
    
    // Slave 5 - accessible only by Master 0
    axi_slave_interface slave5_if(clk, resetn);
    
    // Slave 6 - accessible only by Master 0
    axi_slave_interface slave6_if(clk, resetn);

    // ===== DUT INSTANTIATION =====
    // Main AXI NOC arbiter module
    AXI_TO_AXI_NOC_ARBITER_4_TO_7_CONFIG dut (
        // Clock and reset
        .clk(clk),
        .resetn(resetn),
        
        // ===== MASTER 0 INTERFACE (Full access to all slaves) =====
        // Write Address Channel
        .M0_AWID(master0_if.awid),
        .M0_AWADDR(master0_if.awaddr),
        .M0_AWLEN(master0_if.awlen),
        .M0_AWSIZE(master0_if.awsize),
        .M0_AWBURST(master0_if.awburst),
        .M0_AWLOCK(master0_if.awlock),
        .M0_AWCACHE(master0_if.awcache),
        .M0_AWPROT(master0_if.awprot),
        .M0_AWQOS(master0_if.awqos),
        .M0_AWREGION(master0_if.awregion),
        .M0_AWUSER(master0_if.awuser),
        .M0_AWVALID(master0_if.awvalid),
        .M0_AWREADY(master0_if.awready),
        
        // Write Data Channel
        .M0_WDATA(master0_if.wdata),
        .M0_WSTRB(master0_if.wstrb),
        .M0_WLAST(master0_if.wlast),
        .M0_WUSER(master0_if.wuser),
        .M0_WVALID(master0_if.wvalid),
        .M0_WREADY(master0_if.wready),
        
        // Write Response Channel
        .M0_BID(master0_if.bid),
        .M0_BRESP(master0_if.bresp),
        .M0_BUSER(master0_if.buser),
        .M0_BVALID(master0_if.bvalid),
        .M0_BREADY(master0_if.bready),
        
        // Read Address Channel
        .M0_ARID(master0_if.arid),
        .M0_ARADDR(master0_if.araddr),
        .M0_ARLEN(master0_if.arlen),
        .M0_ARSIZE(master0_if.arsize),
        .M0_ARBURST(master0_if.arburst),
        .M0_ARLOCK(master0_if.arlock),
        .M0_ARCACHE(master0_if.arcache),
        .M0_ARPROT(master0_if.arprot),
        .M0_ARQOS(master0_if.arqos),
        .M0_ARREGION(master0_if.arregion),
        .M0_ARUSER(master0_if.aruser),
        .M0_ARVALID(master0_if.arvalid),
        .M0_ARREADY(master0_if.arready),
        
        // Read Data Channel
        .M0_RID(master0_if.rid),
        .M0_RDATA(master0_if.rdata),
        .M0_RRESP(master0_if.rresp),
        .M0_RLAST(master0_if.rlast),
        .M0_RUSER(master0_if.ruser),
        .M0_RVALID(master0_if.rvalid),
        .M0_RREADY(master0_if.rready),
        
        // ===== MASTER 1 INTERFACE (Access to S0, S1, S2) =====
        // Write Address Channel
        .M1_AWID(master1_if.awid),
        .M1_AWADDR(master1_if.awaddr),
        .M1_AWLEN(master1_if.awlen),
        .M1_AWSIZE(master1_if.awsize),
        .M1_AWBURST(master1_if.awburst),
        .M1_AWLOCK(master1_if.awlock),
        .M1_AWCACHE(master1_if.awcache),
        .M1_AWPROT(master1_if.awprot),
        .M1_AWQOS(master1_if.awqos),
        .M1_AWREGION(master1_if.awregion),
        .M1_AWUSER(master1_if.awuser),
        .M1_AWVALID(master1_if.awvalid),
        .M1_AWREADY(master1_if.awready),
        
        // Write Data Channel
        .M1_WDATA(master1_if.wdata),
        .M1_WSTRB(master1_if.wstrb),
        .M1_WLAST(master1_if.wlast),
        .M1_WUSER(master1_if.wuser),
        .M1_WVALID(master1_if.wvalid),
        .M1_WREADY(master1_if.wready),
        
        // Write Response Channel
        .M1_BID(master1_if.bid),
        .M1_BRESP(master1_if.bresp),
        .M1_BUSER(master1_if.buser),
        .M1_BVALID(master1_if.bvalid),
        .M1_BREADY(master1_if.bready),
        
        // Read Address Channel
        .M1_ARID(master1_if.arid),
        .M1_ARADDR(master1_if.araddr),
        .M1_ARLEN(master1_if.arlen),
        .M1_ARSIZE(master1_if.arsize),
        .M1_ARBURST(master1_if.arburst),
        .M1_ARLOCK(master1_if.arlock),
        .M1_ARCACHE(master1_if.arcache),
        .M1_ARPROT(master1_if.arprot),
        .M1_ARQOS(master1_if.arqos),
        .M1_ARREGION(master1_if.arregion),
        .M1_ARUSER(master1_if.aruser),
        .M1_ARVALID(master1_if.arvalid),
        .M1_ARREADY(master1_if.arready),
        
        // Read Data Channel
        .M1_RID(master1_if.rid),
        .M1_RDATA(master1_if.rdata),
        .M1_RRESP(master1_if.rresp),
        .M1_RLAST(master1_if.rlast),
        .M1_RUSER(master1_if.ruser),
        .M1_RVALID(master1_if.rvalid),
        .M1_RREADY(master1_if.rready),
        
        // ===== MASTER 2 INTERFACE (Access to S0, S1, S2) =====
        // Write Address Channel
        .M2_AWID(master2_if.awid),
        .M2_AWADDR(master2_if.awaddr),
        .M2_AWLEN(master2_if.awlen),
        .M2_AWSIZE(master2_if.awsize),
        .M2_AWBURST(master2_if.awburst),
        .M2_AWLOCK(master2_if.awlock),
        .M2_AWCACHE(master2_if.awcache),
        .M2_AWPROT(master2_if.awprot),
        .M2_AWQOS(master2_if.awqos),
        .M2_AWREGION(master2_if.awregion),
        .M2_AWUSER(master2_if.awuser),
        .M2_AWVALID(master2_if.awvalid),
        .M2_AWREADY(master2_if.awready),
        
        // Write Data Channel
        .M2_WDATA(master2_if.wdata),
        .M2_WSTRB(master2_if.wstrb),
        .M2_WLAST(master2_if.wlast),
        .M2_WUSER(master2_if.wuser),
        .M2_WVALID(master2_if.wvalid),
        .M2_WREADY(master2_if.wready),
        
        // Write Response Channel
        .M2_BID(master2_if.bid),
        .M2_BRESP(master2_if.bresp),
        .M2_BUSER(master2_if.buser),
        .M2_BVALID(master2_if.bvalid),
        .M2_BREADY(master2_if.bready),
        
        // Read Address Channel
        .M2_ARID(master2_if.arid),
        .M2_ARADDR(master2_if.araddr),
        .M2_ARLEN(master2_if.arlen),
        .M2_ARSIZE(master2_if.arsize),
        .M2_ARBURST(master2_if.arburst),
        .M2_ARLOCK(master2_if.arlock),
        .M2_ARCACHE(master2_if.arcache),
        .M2_ARPROT(master2_if.arprot),
        .M2_ARQOS(master2_if.arqos),
        .M2_ARREGION(master2_if.arregion),
        .M2_ARUSER(master2_if.aruser),
        .M2_ARVALID(master2_if.arvalid),
        .M2_ARREADY(master2_if.arready),
        
        // Read Data Channel
        .M2_RID(master2_if.rid),
        .M2_RDATA(master2_if.rdata),
        .M2_RRESP(master2_if.rresp),
        .M2_RLAST(master2_if.rlast),
        .M2_RUSER(master2_if.ruser),
        .M2_RVALID(master2_if.rvalid),
        .M2_RREADY(master2_if.rready),
        
        // ===== MASTER 3 INTERFACE (Access to S0, S1, S2) =====
        // Write Address Channel
        .M3_AWID(master3_if.awid),
        .M3_AWADDR(master3_if.awaddr),
        .M3_AWLEN(master3_if.awlen),
        .M3_AWSIZE(master3_if.awsize),
        .M3_AWBURST(master3_if.awburst),
        .M3_AWLOCK(master3_if.awlock),
        .M3_AWCACHE(master3_if.awcache),
        .M3_AWPROT(master3_if.awprot),
        .M3_AWQOS(master3_if.awqos),
        .M3_AWREGION(master3_if.awregion),
        .M3_AWUSER(master3_if.awuser),
        .M3_AWVALID(master3_if.awvalid),
        .M3_AWREADY(master3_if.awready),
        
        // Write Data Channel
        .M3_WDATA(master3_if.wdata),
        .M3_WSTRB(master3_if.wstrb),
        .M3_WLAST(master3_if.wlast),
        .M3_WUSER(master3_if.wuser),
        .M3_WVALID(master3_if.wvalid),
        .M3_WREADY(master3_if.wready),
        
        // Write Response Channel
        .M3_BID(master3_if.bid),
        .M3_BRESP(master3_if.bresp),
        .M3_BUSER(master3_if.buser),
        .M3_BVALID(master3_if.bvalid),
        .M3_BREADY(master3_if.bready),
        
        // Read Address Channel
        .M3_ARID(master3_if.arid),
        .M3_ARADDR(master3_if.araddr),
        .M3_ARLEN(master3_if.arlen),
        .M3_ARSIZE(master3_if.arsize),
        .M3_ARBURST(master3_if.arburst),
        .M3_ARLOCK(master3_if.arlock),
        .M3_ARCACHE(master3_if.arcache),
        .M3_ARPROT(master3_if.arprot),
        .M3_ARQOS(master3_if.arqos),
        .M3_ARREGION(master3_if.arregion),
        .M3_ARUSER(master3_if.aruser),
        .M3_ARVALID(master3_if.arvalid),
        .M3_ARREADY(master3_if.arready),
        
        // Read Data Channel
        .M3_RID(master3_if.rid),
        .M3_RDATA(master3_if.rdata),
        .M3_RRESP(master3_if.rresp),
        .M3_RLAST(master3_if.rlast),
        .M3_RUSER(master3_if.ruser),
        .M3_RVALID(master3_if.rvalid),
        .M3_RREADY(master3_if.rready),
        
        // ===== SLAVE 0 INTERFACE (Accessible by all masters) =====
        // Write Address Channel
        .S0_AWID(slave0_if.awid),
        .S0_AWADDR(slave0_if.awaddr),
        .S0_AWLEN(slave0_if.awlen),
        .S0_AWSIZE(slave0_if.awsize),
        .S0_AWBURST(slave0_if.awburst),
        .S0_AWLOCK(slave0_if.awlock),
        .S0_AWCACHE(slave0_if.awcache),
        .S0_AWPROT(slave0_if.awprot),
        .S0_AWQOS(slave0_if.awqos),
        .S0_AWREGION(slave0_if.awregion),
        .S0_AWUSER(slave0_if.awuser),
        .S0_AWVALID(slave0_if.awvalid),
        .S0_AWREADY(slave0_if.awready),
        
        // Write Data Channel
        .S0_WDATA(slave0_if.wdata),
        .S0_WSTRB(slave0_if.wstrb),
        .S0_WLAST(slave0_if.wlast),
        .S0_WUSER(slave0_if.wuser),
        .S0_WVALID(slave0_if.wvalid),
        .S0_WREADY(slave0_if.wready),
        
        // Write Response Channel
        .S0_BID(slave0_if.bid),
        .S0_BRESP(slave0_if.bresp),
        .S0_BUSER(slave0_if.buser),
        .S0_BVALID(slave0_if.bvalid),
        .S0_BREADY(slave0_if.bready),
        
        // Read Address Channel
        .S0_ARID(slave0_if.arid),
        .S0_ARADDR(slave0_if.araddr),
        .S0_ARLEN(slave0_if.arlen),
        .S0_ARSIZE(slave0_if.arsize),
        .S0_ARBURST(slave0_if.arburst),
        .S0_ARLOCK(slave0_if.arlock),
        .S0_ARCACHE(slave0_if.arcache),
        .S0_ARPROT(slave0_if.arprot),
        .S0_ARQOS(slave0_if.arqos),
        .S0_ARREGION(slave0_if.arregion),
        .S0_ARUSER(slave0_if.aruser),
        .S0_ARVALID(slave0_if.arvalid),
        .S0_ARREADY(slave0_if.arready),
        
        // Read Data Channel
        .S0_RID(slave0_if.rid),
        .S0_RDATA(slave0_if.rdata),
        .S0_RRESP(slave0_if.rresp),
        .S0_RLAST(slave0_if.rlast),
        .S0_RUSER(slave0_if.ruser),
        .S0_RVALID(slave0_if.rvalid),
        .S0_RREADY(slave0_if.rready),
        
        // ===== SLAVE 1 INTERFACE (Accessible by all masters) =====
        // Write Address Channel
        .S1_AWID(slave1_if.awid),
        .S1_AWADDR(slave1_if.awaddr),
        .S1_AWLEN(slave1_if.awlen),
        .S1_AWSIZE(slave1_if.awsize),
        .S1_AWBURST(slave1_if.awburst),
        .S1_AWLOCK(slave1_if.awlock),
        .S1_AWCACHE(slave1_if.awcache),
        .S1_AWPROT(slave1_if.awprot),
        .S1_AWQOS(slave1_if.awqos),
        .S1_AWREGION(slave1_if.awregion),
        .S1_AWUSER(slave1_if.awuser),
        .S1_AWVALID(slave1_if.awvalid),
        .S1_AWREADY(slave1_if.awready),
        
        // Write Data Channel
        .S1_WDATA(slave1_if.wdata),
        .S1_WSTRB(slave1_if.wstrb),
        .S1_WLAST(slave1_if.wlast),
        .S1_WUSER(slave1_if.wuser),
        .S1_WVALID(slave1_if.wvalid),
        .S1_WREADY(slave1_if.wready),
        
        // Write Response Channel
        .S1_BID(slave1_if.bid),
        .S1_BRESP(slave1_if.bresp),
        .S1_BUSER(slave1_if.buser),
        .S1_BVALID(slave1_if.bvalid),
        .S1_BREADY(slave1_if.bready),
        
        // Read Address Channel
        .S1_ARID(slave1_if.arid),
        .S1_ARADDR(slave1_if.araddr),
        .S1_ARLEN(slave1_if.arlen),
        .S1_ARSIZE(slave1_if.arsize),
        .S1_ARBURST(slave1_if.arburst),
        .S1_ARLOCK(slave1_if.arlock),
        .S1_ARCACHE(slave1_if.arcache),
        .S1_ARPROT(slave1_if.arprot),
        .S1_ARQOS(slave1_if.arqos),
        .S1_ARREGION(slave1_if.arregion),
        .S1_ARUSER(slave1_if.aruser),
        .S1_ARVALID(slave1_if.arvalid),
        .S1_ARREADY(slave1_if.arready),
        
        // Read Data Channel
        .S1_RID(slave1_if.rid),
        .S1_RDATA(slave1_if.rdata),
        .S1_RRESP(slave1_if.rresp),
        .S1_RLAST(slave1_if.rlast),
        .S1_RUSER(slave1_if.ruser),
        .S1_RVALID(slave1_if.rvalid),
        .S1_RREADY(slave1_if.rready),
        
        // ===== SLAVE 2 INTERFACE (Accessible by all masters) =====
        // Write Address Channel
        .S2_AWID(slave2_if.awid),
        .S2_AWADDR(slave2_if.awaddr),
        .S2_AWLEN(slave2_if.awlen),
        .S2_AWSIZE(slave2_if.awsize),
        .S2_AWBURST(slave2_if.awburst),
        .S2_AWLOCK(slave2_if.awlock),
        .S2_AWCACHE(slave2_if.awcache),
        .S2_AWPROT(slave2_if.awprot),
        .S2_AWQOS(slave2_if.awqos),
        .S2_AWREGION(slave2_if.awregion),
        .S2_AWUSER(slave2_if.awuser),
        .S2_AWVALID(slave2_if.awvalid),
        .S2_AWREADY(slave2_if.awready),
        
        // Write Data Channel
        .S2_WDATA(slave2_if.wdata),
        .S2_WSTRB(slave2_if.wstrb),
        .S2_WLAST(slave2_if.wlast),
        .S2_WUSER(slave2_if.wuser),
        .S2_WVALID(slave2_if.wvalid),
        .S2_WREADY(slave2_if.wready),
        
        // Write Response Channel
        .S2_BID(slave2_if.bid),
        .S2_BRESP(slave2_if.bresp),
        .S2_BUSER(slave2_if.buser),
        .S2_BVALID(slave2_if.bvalid),
        .S2_BREADY(slave2_if.bready),
        
        // Read Address Channel
        .S2_ARID(slave2_if.arid),
        .S2_ARADDR(slave2_if.araddr),
        .S2_ARLEN(slave2_if.arlen),
        .S2_ARSIZE(slave2_if.arsize),
        .S2_ARBURST(slave2_if.arburst),
        .S2_ARLOCK(slave2_if.arlock),
        .S2_ARCACHE(slave2_if.arcache),
        .S2_ARPROT(slave2_if.arprot),
        .S2_ARQOS(slave2_if.arqos),
        .S2_ARREGION(slave2_if.arregion),
        .S2_ARUSER(slave2_if.aruser),
        .S2_ARVALID(slave2_if.arvalid),
        .S2_ARREADY(slave2_if.arready),
        
        // Read Data Channel
        .S2_RID(slave2_if.rid),
        .S2_RDATA(slave2_if.rdata),
        .S2_RRESP(slave2_if.rresp),
        .S2_RLAST(slave2_if.rlast),
        .S2_RUSER(slave2_if.ruser),
        .S2_RVALID(slave2_if.rvalid),
        .S2_RREADY(slave2_if.rready),
        
        // ===== SLAVE 3 INTERFACE (Accessible only by Master 0) =====
        // Write Address Channel
        .S3_AWID(slave3_if.awid),
        .S3_AWADDR(slave3_if.awaddr),
        .S3_AWLEN(slave3_if.awlen),
        .S3_AWSIZE(slave3_if.awsize),
        .S3_AWBURST(slave3_if.awburst),
        .S3_AWLOCK(slave3_if.awlock),
        .S3_AWCACHE(slave3_if.awcache),
        .S3_AWPROT(slave3_if.awprot),
        .S3_AWQOS(slave3_if.awqos),
        .S3_AWREGION(slave3_if.awregion),
        .S3_AWUSER(slave3_if.awuser),
        .S3_AWVALID(slave3_if.awvalid),
        .S3_AWREADY(slave3_if.awready),
        
        // Write Data Channel
        .S3_WDATA(slave3_if.wdata),
        .S3_WSTRB(slave3_if.wstrb),
        .S3_WLAST(slave3_if.wlast),
        .S3_WUSER(slave3_if.wuser),
        .S3_WVALID(slave3_if.wvalid),
        .S3_WREADY(slave3_if.wready),
        
        // Write Response Channel
        .S3_BID(slave3_if.bid),
        .S3_BRESP(slave3_if.bresp),
        .S3_BUSER(slave3_if.buser),
        .S3_BVALID(slave3_if.bvalid),
        .S3_BREADY(slave3_if.bready),
        
        // Read Address Channel
        .S3_ARID(slave3_if.arid),
        .S3_ARADDR(slave3_if.araddr),
        .S3_ARLEN(slave3_if.arlen),
        .S3_ARSIZE(slave3_if.arsize),
        .S3_ARBURST(slave3_if.arburst),
        .S3_ARLOCK(slave3_if.arlock),
        .S3_ARCACHE(slave3_if.arcache),
        .S3_ARPROT(slave3_if.arprot),
        .S3_ARQOS(slave3_if.arqos),
        .S3_ARREGION(slave3_if.arregion),
        .S3_ARUSER(slave3_if.aruser),
        .S3_ARVALID(slave3_if.arvalid),
        .S3_ARREADY(slave3_if.arready),
        
        // Read Data Channel
        .S3_RID(slave3_if.rid),
        .S3_RDATA(slave3_if.rdata),
        .S3_RRESP(slave3_if.rresp),
        .S3_RLAST(slave3_if.rlast),
        .S3_RUSER(slave3_if.ruser),
        .S3_RVALID(slave3_if.rvalid),
        .S3_RREADY(slave3_if.rready),
        
        // ===== SLAVE 4 INTERFACE (Accessible only by Master 0) =====
        // Write Address Channel
        .S4_AWID(slave4_if.awid),
        .S4_AWADDR(slave4_if.awaddr),
        .S4_AWLEN(slave4_if.awlen),
        .S4_AWSIZE(slave4_if.awsize),
        .S4_AWBURST(slave4_if.awburst),
        .S4_AWLOCK(slave4_if.awlock),
        .S4_AWCACHE(slave4_if.awcache),
        .S4_AWPROT(slave4_if.awprot),
        .S4_AWQOS(slave4_if.awqos),
        .S4_AWREGION(slave4_if.awregion),
        .S4_AWUSER(slave4_if.awuser),
        .S4_AWVALID(slave4_if.awvalid),
        .S4_AWREADY(slave4_if.awready),
        
        // Write Data Channel
        .S4_WDATA(slave4_if.wdata),
        .S4_WSTRB(slave4_if.wstrb),
        .S4_WLAST(slave4_if.wlast),
        .S4_WUSER(slave4_if.wuser),
        .S4_WVALID(slave4_if.wvalid),
        .S4_WREADY(slave4_if.wready),
        
        // Write Response Channel
        .S4_BID(slave4_if.bid),
        .S4_BRESP(slave4_if.bresp),
        .S4_BUSER(slave4_if.buser),
        .S4_BVALID(slave4_if.bvalid),
        .S4_BREADY(slave4_if.bready),
        
        // Read Address Channel
        .S4_ARID(slave4_if.arid),
        .S4_ARADDR(slave4_if.araddr),
        .S4_ARLEN(slave4_if.arlen),
        .S4_ARSIZE(slave4_if.arsize),
        .S4_ARBURST(slave4_if.arburst),
        .S4_ARLOCK(slave4_if.arlock),
        .S4_ARCACHE(slave4_if.arcache),
        .S4_ARPROT(slave4_if.arprot),
        .S4_ARQOS(slave4_if.arqos),
        .S4_ARREGION(slave4_if.arregion),
        .S4_ARUSER(slave4_if.aruser),
        .S4_ARVALID(slave4_if.arvalid),
        .S4_ARREADY(slave4_if.arready),
        
        // Read Data Channel
        .S4_RID(slave4_if.rid),
        .S4_RDATA(slave4_if.rdata),
        .S4_RRESP(slave4_if.rresp),
        .S4_RLAST(slave4_if.rlast),
        .S4_RUSER(slave4_if.ruser),
        .S4_RVALID(slave4_if.rvalid),
        .S4_RREADY(slave4_if.rready),
        
        // ===== SLAVE 5 INTERFACE (Accessible only by Master 0) =====
        // Write Address Channel
        .S5_AWID(slave5_if.awid),
        .S5_AWADDR(slave5_if.awaddr),
        .S5_AWLEN(slave5_if.awlen),
        .S5_AWSIZE(slave5_if.awsize),
        .S5_AWBURST(slave5_if.awburst),
        .S5_AWLOCK(slave5_if.awlock),
        .S5_AWCACHE(slave5_if.awcache),
        .S5_AWPROT(slave5_if.awprot),
        .S5_AWQOS(slave5_if.awqos),
        .S5_AWREGION(slave5_if.awregion),
        .S5_AWUSER(slave5_if.awuser),
        .S5_AWVALID(slave5_if.awvalid),
        .S5_AWREADY(slave5_if.awready),
        
        // Write Data Channel
        .S5_WDATA(slave5_if.wdata),
        .S5_WSTRB(slave5_if.wstrb),
        .S5_WLAST(slave5_if.wlast),
        .S5_WUSER(slave5_if.wuser),
        .S5_WVALID(slave5_if.wvalid),
        .S5_WREADY(slave5_if.wready),
        
        // Write Response Channel
        .S5_BID(slave5_if.bid),
        .S5_BRESP(slave5_if.bresp),
        .S5_BUSER(slave5_if.buser),
        .S5_BVALID(slave5_if.bvalid),
        .S5_BREADY(slave5_if.bready),
        
        // Read Address Channel
        .S5_ARID(slave5_if.arid),
        .S5_ARADDR(slave5_if.araddr),
        .S5_ARLEN(slave5_if.arlen),
        .S5_ARSIZE(slave5_if.arsize),
        .S5_ARBURST(slave5_if.arburst),
        .S5_ARLOCK(slave5_if.arlock),
        .S5_ARCACHE(slave5_if.arcache),
        .S5_ARPROT(slave5_if.arprot),
        .S5_ARQOS(slave5_if.arqos),
        .S5_ARREGION(slave5_if.arregion),
        .S5_ARUSER(slave5_if.aruser),
        .S5_ARVALID(slave5_if.arvalid),
        .S5_ARREADY(slave5_if.arready),
        
        // Read Data Channel
        .S5_RID(slave5_if.rid),
        .S5_RDATA(slave5_if.rdata),
        .S5_RRESP(slave5_if.rresp),
        .S5_RLAST(slave5_if.rlast),
        .S5_RUSER(slave5_if.ruser),
        .S5_RVALID(slave5_if.rvalid),
        .S5_RREADY(slave5_if.rready),
        
        // ===== SLAVE 6 INTERFACE (Accessible only by Master 0) =====
        // Write Address Channel
        .S6_AWID(slave6_if.awid),
        .S6_AWADDR(slave6_if.awaddr),
        .S6_AWLEN(slave6_if.awlen),
        .S6_AWSIZE(slave6_if.awsize),
        .S6_AWBURST(slave6_if.awburst),
        .S6_AWLOCK(slave6_if.awlock),
        .S6_AWCACHE(slave6_if.awcache),
        .S6_AWPROT(slave6_if.awprot),
        .S6_AWQOS(slave6_if.awqos),
        .S6_AWREGION(slave6_if.awregion),
        .S6_AWUSER(slave6_if.awuser),
        .S6_AWVALID(slave6_if.awvalid),
        .S6_AWREADY(slave6_if.awready),
        
        // Write Data Channel
        .S6_WDATA(slave6_if.wdata),
        .S6_WSTRB(slave6_if.wstrb),
        .S6_WLAST(slave6_if.wlast),
        .S6_WUSER(slave6_if.wuser),
        .S6_WVALID(slave6_if.wvalid),
        .S6_WREADY(slave6_if.wready),
        
        // Write Response Channel
        .S6_BID(slave6_if.bid),
        .S6_BRESP(slave6_if.bresp),
        .S6_BUSER(slave6_if.buser),
        .S6_BVALID(slave6_if.bvalid),
        .S6_BREADY(slave6_if.bready),
        
        // Read Address Channel
        .S6_ARID(slave6_if.arid),
        .S6_ARADDR(slave6_if.araddr),
        .S6_ARLEN(slave6_if.arlen),
        .S6_ARSIZE(slave6_if.arsize),
        .S6_ARBURST(slave6_if.arburst),
        .S6_ARLOCK(slave6_if.arlock),
        .S6_ARCACHE(slave6_if.arcache),
        .S6_ARPROT(slave6_if.arprot),
        .S6_ARQOS(slave6_if.arqos),
        .S6_ARREGION(slave6_if.arregion),
        .S6_ARUSER(slave6_if.aruser),
        .S6_ARVALID(slave6_if.arvalid),
        .S6_ARREADY(slave6_if.arready),
        
        // Read Data Channel
        .S6_RID(slave6_if.rid),
        .S6_RDATA(slave6_if.rdata),
        .S6_RRESP(slave6_if.rresp),
        .S6_RLAST(slave6_if.rlast),
        .S6_RUSER(slave6_if.ruser),
        .S6_RVALID(slave6_if.rvalid),
        .S6_RREADY(slave6_if.rready)
    );

    // ===== UVM TEST START =====
    initial begin
        // Set virtual interfaces in config database for UVM components
        uvm_config_db#(virtual axi_master_interface.master)::set(null, "uvm_test_top", "master0_vif", master0_if);
        uvm_config_db#(virtual axi_master_interface.master)::set(null, "uvm_test_top", "master1_vif", master1_if);
        uvm_config_db#(virtual axi_master_interface.master)::set(null, "uvm_test_top", "master2_vif", master2_if);
        uvm_config_db#(virtual axi_master_interface.master)::set(null, "uvm_test_top", "master3_vif", master3_if);
        
        uvm_config_db#(virtual axi_slave_interface.slave_modport)::set(null, "uvm_test_top", "slave0_vif", slave0_if);
        uvm_config_db#(virtual axi_slave_interface.slave_modport)::set(null, "uvm_test_top", "slave1_vif", slave1_if);
        uvm_config_db#(virtual axi_slave_interface.slave_modport)::set(null, "uvm_test_top", "slave2_vif", slave2_if);
        uvm_config_db#(virtual axi_slave_interface.slave_modport)::set(null, "uvm_test_top", "slave3_vif", slave3_if);
        uvm_config_db#(virtual axi_slave_interface.slave_modport)::set(null, "uvm_test_top", "slave4_vif", slave4_if);
        uvm_config_db#(virtual axi_slave_interface.slave_modport)::set(null, "uvm_test_top", "slave5_vif", slave5_if);
        uvm_config_db#(virtual axi_slave_interface.slave_modport)::set(null, "uvm_test_top", "slave6_vif", slave6_if);
        
        // Start UVM test
        run_test();
    end

    // ===== WAVEFORM DUMPING =====
    initial begin
        $dumpfile("axi_noc_tb.vcd");
        $dumpvars(0, axi_noc_tb_top);
    end

    // ===== MONITORING =====
    // Monitor for basic signal activity
    always @(posedge clk) begin
        if (resetn) begin
            // Monitor master activity
            if (master0_if.awvalid && master0_if.awready) begin
                $display("Time %0t: M0 Write Address - ID: %0d, Addr: 0x%h, Burst: %0d", 
                         $time, master0_if.awid, master0_if.awaddr, master0_if.awburst);
            end
            
            if (master1_if.awvalid && master1_if.awready) begin
                $display("Time %0t: M1 Write Address - ID: %0d, Addr: 0x%h, Burst: %0d", 
                         $time, master1_if.awid, master1_if.awaddr, master1_if.awburst);
            end
            
            // Monitor slave responses
            if (slave0_if.bvalid && slave0_if.bready) begin
                $display("Time %0t: S0 Write Response - ID: %0d, Resp: %0d", 
                         $time, slave0_if.bid, slave0_if.bresp);
            end
        end
    end

endmodule

`endif // AXI_NOC_TB_TOP_SV
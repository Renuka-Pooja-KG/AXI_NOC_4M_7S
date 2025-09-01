//=============================================================================
// AXI NOC Testbench Top Module
//=============================================================================
// Top-level testbench with DUT instantiation and all interfaces

`ifndef AXI_NOC_TB_TOP_SV
`define AXI_NOC_TB_TOP_SV


// Testbench top module
module axi_noc_tb_top;


    
    // ===== CLOCK AND RESET GENERATION =====
    logic ACLK;
    logic ARESETn;
    
    // Clock generation (100MHz = 10ns period)
    initial begin
        ACLK = 0;
        forever #5 ACLK = ~ACLK;
    end
    
    // Reset generation
    initial begin
        ARESETn = 0;
        #100 ARESETn = 1;
    end

    // ===== MASTER INTERFACES =====
    // Master 0 - has access to all slaves (S0-S6)
    M0_interface master0_if(ACLK, ARESETn);
    
    // Master 1 - has access to slaves S0, S1, S2
    M1_interface master1_if(ACLK, ARESETn);
    
    // Master 2 - has access to slaves S0, S1, S2
    M2_interface master2_if(ACLK, ARESETn);
    
    // Master 3 - has access to slaves S0, S1, S2
    M3_interface master3_if(ACLK, ARESETn);

    // ===== SLAVE INTERFACES =====
    // Slave 0 - accessible by all masters
    S0_interface slave0_if(ACLK, ARESETn);
    
    // Slave 1 - accessible by all masters
    S1_interface slave1_if(ACLK, ARESETn);
    
    // Slave 2 - accessible by all masters
    S2_interface slave2_if(ACLK, ARESETn);
    
    // Slave 3 - accessible only by Master 0
    S3_interface slave3_if(ACLK, ARESETn);
    
    // Slave 4 - accessible only by Master 0
    S4_interface slave4_if(ACLK, ARESETn);
    
    // Slave 5 - accessible only by Master 0
    S5_interface slave5_if(ACLK, ARESETn);
    
    // Slave 6 - accessible only by Master 0
    S6_interface slave6_if(ACLK, ARESETn);

    // ===== DUT INSTANTIATION =====
    // Main AXI NOC arbiter module

    AXI_TO_AXI_NOC_ARBITER_4_TO_7_CONFIG dut (
        // Clock and reset
        .ACLK(ACLK),
        .ARESETn(ARESETn),
        
        // ===== MASTER 0 INTERFACE (Full access to all slaves) =====
        // Write Address Channel
        .M0_AWID(master0_if.M0_AWID),
        .M0_AWADDR(master0_if.M0_AWADDR),
        .M0_AWLEN(master0_if.M0_AWLEN),
        .M0_AWSIZE(master0_if.M0_AWSIZE),
        .M0_AWBURST(master0_if.M0_AWBURST),
        .M0_AWLOCK(master0_if.M0_AWLOCK),
        .M0_AWCACHE(master0_if.M0_AWCACHE),
        .M0_AWPROT(master0_if.M0_AWPROT),
        .M0_AWQOS(master0_if.M0_AWQOS),
        .M0_AWREGION(master0_if.M0_AWREGION),
        .M0_AWUSER(master0_if.M0_AWUSER),
        .M0_AWVALID(master0_if.M0_AWVALID),
        .M0_AWREADY(master0_if.M0_AWREADY),
        
        // Write Data Channel
        .M0_WDATA(master0_if.M0_WDATA),
        .M0_WSTRB(master0_if.M0_WSTRB),
        .M0_WLAST(master0_if.M0_WLAST),
        .M0_WUSER(master0_if.M0_WUSER),
        .M0_WVALID(master0_if.M0_WVALID),
        .M0_WREADY(master0_if.M0_WREADY),
        
        // Write Response Channel
        .M0_BID(master0_if.M0_BID),
        .M0_BRESP(master0_if.M0_BRESP),
        .M0_BUSER(master0_if.M0_BUSER),
        .M0_BVALID(master0_if.M0_BVALID),
        .M0_BREADY(master0_if.M0_BREADY),
        
        // Read Address Channel
        .M0_ARID(master0_if.M0_ARID),
        .M0_ARADDR(master0_if.M0_ARADDR),
        .M0_ARLEN(master0_if.M0_ARLEN),
        .M0_ARSIZE(master0_if.M0_ARSIZE),
        .M0_ARBURST(master0_if.M0_ARBURST),
        .M0_ARLOCK(master0_if.M0_ARLOCK),
        .M0_ARCACHE(master0_if.M0_ARCACHE),
        .M0_ARPROT(master0_if.M0_ARPROT),
        .M0_ARQOS(master0_if.M0_ARQOS),
        .M0_ARREGION(master0_if.M0_ARREGION),
        .M0_ARUSER(master0_if.M0_ARUSER),
        .M0_ARVALID(master0_if.M0_ARVALID),
        .M0_ARREADY(master0_if.M0_ARREADY),
        
        // Read Data Channel
        .M0_RID(master0_if.M0_RID),
        .M0_RDATA(master0_if.M0_RDATA),
        .M0_RRESP(master0_if.M0_RRESP),
        .M0_RLAST(master0_if.M0_RLAST),
        .M0_RUSER(master0_if.M0_RUSER),
        .M0_RVALID(master0_if.M0_RVALID),
        .M0_RREADY(master0_if.M0_RREADY),
        
        // ===== MASTER 1 INTERFACE (Access to S0, S1, S2) =====
        // Write Address Channel
        .M1_AWID(master1_if.M1_AWID),
        .M1_AWADDR(master1_if.M1_AWADDR),
        .M1_AWLEN(master1_if.M1_AWLEN),
        .M1_AWSIZE(master1_if.M1_AWSIZE),
        .M1_AWBURST(master1_if.M1_AWBURST),
        .M1_AWLOCK(master1_if.M1_AWLOCK),
        .M1_AWCACHE(master1_if.M1_AWCACHE),
        .M1_AWPROT(master1_if.M1_AWPROT),
        .M1_AWQOS(master1_if.M1_AWQOS),
        .M1_AWREGION(master1_if.M1_AWREGION),
        .M1_AWUSER(master1_if.M1_AWUSER),
        .M1_AWVALID(master1_if.M1_AWVALID),
        .M1_AWREADY(master1_if.M1_AWREADY),
        
        // Write Data Channel
        .M1_WDATA(master1_if.M1_WDATA),
        .M1_WSTRB(master1_if.M1_WSTRB),
        .M1_WLAST(master1_if.M1_WLAST),
        .M1_WUSER(master1_if.M1_WUSER),
        .M1_WVALID(master1_if.M1_WVALID),
        .M1_WREADY(master1_if.M1_WREADY),
        
        // Write Response Channel
        .M1_BID(master1_if.M1_BID),
        .M1_BRESP(master1_if.M1_BRESP),
        .M1_BUSER(master1_if.M1_BUSER),
        .M1_BVALID(master1_if.M1_BVALID),
        .M1_BREADY(master1_if.M1_BREADY),
        
        // Read Address Channel
        .M1_ARID(master1_if.M1_ARID),
        .M1_ARADDR(master1_if.M1_ARADDR),
        .M1_ARLEN(master1_if.M1_ARLEN),
        .M1_ARSIZE(master1_if.M1_ARSIZE),
        .M1_ARBURST(master1_if.M1_ARBURST),
        .M1_ARLOCK(master1_if.M1_ARLOCK),
        .M1_ARCACHE(master1_if.M1_ARCACHE),
        .M1_ARPROT(master1_if.M1_ARPROT),
        .M1_ARQOS(master1_if.M1_ARQOS),
        .M1_ARREGION(master1_if.M1_ARREGION),
        .M1_ARUSER(master1_if.M1_ARUSER),
        .M1_ARVALID(master1_if.M1_ARVALID),
        .M1_ARREADY(master1_if.M1_ARREADY),
        
        // Read Data Channel
        .M1_RID(master1_if.M1_RID),
        .M1_RDATA(master1_if.M1_RDATA),
        .M1_RRESP(master1_if.M1_RRESP),
        .M1_RLAST(master1_if.M1_RLAST),
        .M1_RUSER(master1_if.M1_RUSER),
        .M1_RVALID(master1_if.M1_RVALID),
        .M1_RREADY(master1_if.M1_RREADY),
        
        // ===== MASTER 2 INTERFACE (Access to S0, S1, S2) =====
        // Write Address Channel
        .M2_AWID(master2_if.M2_AWID),
        .M2_AWADDR(master2_if.M2_AWADDR),
        .M2_AWLEN(master2_if.M2_AWLEN),
        .M2_AWSIZE(master2_if.M2_AWSIZE),
        .M2_AWBURST(master2_if.M2_AWBURST),
        .M2_AWLOCK(master2_if.M2_AWLOCK),
        .M2_AWCACHE(master2_if.M2_AWCACHE),
        .M2_AWPROT(master2_if.M2_AWPROT),
        .M2_AWQOS(master2_if.M2_AWQOS),
        .M2_AWREGION(master2_if.M2_AWREGION),
        .M2_AWUSER(master2_if.M2_AWUSER),
        .M2_AWVALID(master2_if.M2_AWVALID),
        .M2_AWREADY(master2_if.M2_AWREADY),
        
        // Write Data Channel
        .M2_WDATA(master2_if.M2_WDATA),
        .M2_WSTRB(master2_if.M2_WSTRB),
        .M2_WLAST(master2_if.M2_WLAST),
        .M2_WUSER(master2_if.M2_WUSER),
        .M2_WVALID(master2_if.M2_WVALID),
        .M2_WREADY(master2_if.M2_WREADY),
        
        // Write Response Channel
        .M2_BID(master2_if.M2_BID),
        .M2_BRESP(master2_if.M2_BRESP),
        .M2_BUSER(master2_if.M2_BUSER),
        .M2_BVALID(master2_if.M2_BVALID),
        .M2_BREADY(master2_if.M2_BREADY),
        
        // Read Address Channel
        .M2_ARID(master2_if.M2_ARID),
        .M2_ARADDR(master2_if.M2_ARADDR),
        .M2_ARLEN(master2_if.M2_ARLEN),
        .M2_ARSIZE(master2_if.M2_ARSIZE),
        .M2_ARBURST(master2_if.M2_ARBURST),
        .M2_ARLOCK(master2_if.M2_ARLOCK),
        .M2_ARCACHE(master2_if.M2_ARCACHE),
        .M2_ARPROT(master2_if.M2_ARPROT),
        .M2_ARQOS(master2_if.M2_ARQOS),
        .M2_ARREGION(master2_if.M2_ARREGION),
        .M2_ARUSER(master2_if.M2_ARUSER),
        .M2_ARVALID(master2_if.M2_ARVALID),
        .M2_ARREADY(master2_if.M2_ARREADY),
        
        // Read Data Channel
        .M2_RID(master2_if.M2_RID),
        .M2_RDATA(master2_if.M2_RDATA),
        .M2_RRESP(master2_if.M2_RRESP),
        .M2_RLAST(master2_if.M2_RLAST),
        .M2_RUSER(master2_if.M2_RUSER),
        .M2_RVALID(master2_if.M2_RVALID),
        .M2_RREADY(master2_if.M2_RREADY),
        
        // ===== MASTER 3 INTERFACE (Access to S0, S1, S2) =====
        // Write Address Channel
        .M3_AWID(master3_if.M3_AWID),
        .M3_AWADDR(master3_if.M3_AWADDR),
        .M3_AWLEN(master3_if.M3_AWLEN),
        .M3_AWSIZE(master3_if.M3_AWSIZE),
        .M3_AWBURST(master3_if.M3_AWBURST),
        .M3_AWLOCK(master3_if.M3_AWLOCK),
        .M3_AWCACHE(master3_if.M3_AWCACHE),
        .M3_AWPROT(master3_if.M3_AWPROT),
        .M3_AWQOS(master3_if.M3_AWQOS),
        .M3_AWREGION(master3_if.M3_AWREGION),
        .M3_AWUSER(master3_if.M3_AWUSER),
        .M3_AWVALID(master3_if.M3_AWVALID),
        .M3_AWREADY(master3_if.M3_AWREADY),
        
        // Write Data Channel
        .M3_WDATA(master3_if.M3_WDATA),
        .M3_WSTRB(master3_if.M3_WSTRB),
        .M3_WLAST(master3_if.M3_WLAST),
        .M3_WUSER(master3_if.M3_WUSER),
        .M3_WVALID(master3_if.M3_WVALID),
        .M3_WREADY(master3_if.M3_WREADY),
        
        // Write Response Channel
        .M3_BID(master3_if.M3_BID),
        .M3_BRESP(master3_if.M3_BRESP),
        .M3_BUSER(master3_if.M3_BUSER),
        .M3_BVALID(master3_if.M3_BVALID),
        .M3_BREADY(master3_if.M3_BREADY),
        
        // Read Address Channel
        .M3_ARID(master3_if.M3_ARID),
        .M3_ARADDR(master3_if.M3_ARADDR),
        .M3_ARLEN(master3_if.M3_ARLEN),
        .M3_ARSIZE(master3_if.M3_ARSIZE),
        .M3_ARBURST(master3_if.M3_ARBURST),
        .M3_ARLOCK(master3_if.M3_ARLOCK),
        .M3_ARCACHE(master3_if.M3_ARCACHE),
        .M3_ARPROT(master3_if.M3_ARPROT),
        .M3_ARQOS(master3_if.M3_ARQOS),
        .M3_ARREGION(master3_if.M3_ARREGION),
        .M3_ARUSER(master3_if.M3_ARUSER),
        .M3_ARVALID(master3_if.M3_ARVALID),
        .M3_ARREADY(master3_if.M3_ARREADY),
        
        // Read Data Channel
        .M3_RID(master3_if.M3_RID),
        .M3_RDATA(master3_if.M3_RDATA),
        .M3_RRESP(master3_if.M3_RRESP),
        .M3_RLAST(master3_if.M3_RLAST),
        .M3_RUSER(master3_if.M3_RUSER),
        .M3_RVALID(master3_if.M3_RVALID),
        .M3_RREADY(master3_if.M3_RREADY),
        
        // ===== SLAVE 0 INTERFACE (Accessible by all masters) =====
        // Write Address Channel
        .S0_AWID(slave0_if.S0_AWID),
        .S0_AWADDR(slave0_if.S0_AWADDR),
        .S0_AWLEN(slave0_if.S0_AWLEN),
        .S0_AWSIZE(slave0_if.S0_AWSIZE),
        .S0_AWBURST(slave0_if.S0_AWBURST),
        .S0_AWLOCK(slave0_if.S0_AWLOCK),
        .S0_AWCACHE(slave0_if.S0_AWCACHE),
        .S0_AWPROT(slave0_if.S0_AWPROT),
        .S0_AWQOS(slave0_if.S0_AWQOS),
        .S0_AWREGION(slave0_if.S0_AWREGION),
        .S0_AWUSER(slave0_if.S0_AWUSER),
        .S0_AWVALID(slave0_if.S0_AWVALID),
        .S0_AWREADY(slave0_if.S0_AWREADY),
        
        // Write Data Channel
        .S0_WDATA(slave0_if.S0_WDATA),
        .S0_WSTRB(slave0_if.S0_WSTRB),
        .S0_WLAST(slave0_if.S0_WLAST),
        .S0_WUSER(slave0_if.S0_WUSER),
        .S0_WVALID(slave0_if.S0_WVALID),
        .S0_WREADY(slave0_if.S0_WREADY),
        
        // Write Response Channel
        .S0_BID(slave0_if.S0_BID),
        .S0_BRESP(slave0_if.S0_BRESP),
        .S0_BUSER(slave0_if.S0_BUSER),
        .S0_BVALID(slave0_if.S0_BVALID),
        .S0_BREADY(slave0_if.S0_BREADY),
        
        // Read Address Channel
        .S0_ARID(slave0_if.S0_ARID),
        .S0_ARADDR(slave0_if.S0_ARADDR),
        .S0_ARLEN(slave0_if.S0_ARLEN),
        .S0_ARSIZE(slave0_if.S0_ARSIZE),
        .S0_ARBURST(slave0_if.S0_ARBURST),
        .S0_ARLOCK(slave0_if.S0_ARLOCK),
        .S0_ARCACHE(slave0_if.S0_ARCACHE),
        .S0_ARPROT(slave0_if.S0_ARPROT),
        .S0_ARQOS(slave0_if.S0_ARQOS),
        .S0_ARREGION(slave0_if.S0_ARREGION),
        .S0_ARUSER(slave0_if.S0_ARUSER),
        .S0_ARVALID(slave0_if.S0_ARVALID),
        .S0_ARREADY(slave0_if.S0_ARREADY),
        
        // Read Data Channel
        .S0_RID(slave0_if.S0_RID),
        .S0_RDATA(slave0_if.S0_RDATA),
        .S0_RRESP(slave0_if.S0_RRESP),
        .S0_RLAST(slave0_if.S0_RLAST),
        .S0_RUSER(slave0_if.S0_RUSER),
        .S0_RVALID(slave0_if.S0_RVALID),
        .S0_RREADY(slave0_if.S0_RREADY),
        
        // ===== SLAVE 1 INTERFACE (Accessible by all masters) =====
        // Write Address Channel
        .S1_AWID(slave1_if.S1_AWID),
        .S1_AWADDR(slave1_if.S1_AWADDR),
        .S1_AWLEN(slave1_if.S1_AWLEN),
        .S1_AWSIZE(slave1_if.S1_AWSIZE),
        .S1_AWBURST(slave1_if.S1_AWBURST),
        .S1_AWLOCK(slave1_if.S1_AWLOCK),
        .S1_AWCACHE(slave1_if.S1_AWCACHE),
        .S1_AWPROT(slave1_if.S1_AWPROT),
        .S1_AWQOS(slave1_if.S1_AWQOS),
        .S1_AWREGION(slave1_if.S1_AWREGION),
        .S1_AWUSER(slave1_if.S1_AWUSER),
        .S1_AWVALID(slave1_if.S1_AWVALID),
        .S1_AWREADY(slave1_if.S1_AWREADY),
        
        // Write Data Channel
        .S1_WDATA(slave1_if.S1_WDATA),
        .S1_WSTRB(slave1_if.S1_WSTRB),
        .S1_WLAST(slave1_if.S1_WLAST),
        .S1_WUSER(slave1_if.S1_WUSER),
        .S1_WVALID(slave1_if.S1_WVALID),
        .S1_WREADY(slave1_if.S1_WREADY),
        
        // Write Response Channel
        .S1_BID(slave1_if.S1_BID),
        .S1_BRESP(slave1_if.S1_BRESP),
        .S1_BUSER(slave1_if.S1_BUSER),
        .S1_BVALID(slave1_if.S1_BVALID),
        .S1_BREADY(slave1_if.S1_BREADY),
        
        // Read Address Channel
        .S1_ARID(slave1_if.S1_ARID),
        .S1_ARADDR(slave1_if.S1_ARADDR),
        .S1_ARLEN(slave1_if.S1_ARLEN),
        .S1_ARSIZE(slave1_if.S1_ARSIZE),
        .S1_ARBURST(slave1_if.S1_ARBURST),
        .S1_ARLOCK(slave1_if.S1_ARLOCK),
        .S1_ARCACHE(slave1_if.S1_ARCACHE),
        .S1_ARPROT(slave1_if.S1_ARPROT),
        .S1_ARQOS(slave1_if.S1_ARQOS),
        .S1_ARREGION(slave1_if.S1_ARREGION),
        .S1_ARUSER(slave1_if.S1_ARUSER),
        .S1_ARVALID(slave1_if.S1_ARVALID),
        .S1_ARREADY(slave1_if.S1_ARREADY),
        
        // Read Data Channel
        .S1_RID(slave1_if.S1_RID),
        .S1_RDATA(slave1_if.S1_RDATA),
        .S1_RRESP(slave1_if.S1_RRESP),
        .S1_RLAST(slave1_if.S1_RLAST),
        .S1_RUSER(slave1_if.S1_RUSER),
        .S1_RVALID(slave1_if.S1_RVALID),
        .S1_RREADY(slave1_if.S1_RREADY),
        
        // ===== SLAVE 2 INTERFACE (Accessible by all masters) =====
        // Write Address Channel
        .S2_AWID(slave2_if.S2_AWID),
        .S2_AWADDR(slave2_if.S2_AWADDR),
        .S2_AWLEN(slave2_if.S2_AWLEN),
        .S2_AWSIZE(slave2_if.S2_AWSIZE),
        .S2_AWBURST(slave2_if.S2_AWBURST),
        .S2_AWLOCK(slave2_if.S2_AWLOCK),
        .S2_AWCACHE(slave2_if.S2_AWCACHE),
        .S2_AWPROT(slave2_if.S2_AWPROT),
        .S2_AWQOS(slave2_if.S2_AWQOS),
        .S2_AWREGION(slave2_if.S2_AWREGION),
        .S2_AWUSER(slave2_if.S2_AWUSER),
        .S2_AWVALID(slave2_if.S2_AWVALID),
        .S2_AWREADY(slave2_if.S2_AWREADY),
        
        // Write Data Channel
        .S2_WDATA(slave2_if.S2_WDATA),
        .S2_WSTRB(slave2_if.S2_WSTRB),
        .S2_WLAST(slave2_if.S2_WLAST),
        .S2_WUSER(slave2_if.S2_WUSER),
        .S2_WVALID(slave2_if.S2_WVALID),
        .S2_WREADY(slave2_if.S2_WREADY),
        
        // Write Response Channel
        .S2_BID(slave2_if.S2_BID),
        .S2_BRESP(slave2_if.S2_BRESP),
        .S2_BUSER(slave2_if.S2_BUSER),
        .S2_BVALID(slave2_if.S2_BVALID),
        .S2_BREADY(slave2_if.S2_BREADY),
        
        // Read Address Channel
        .S2_ARID(slave2_if.S2_ARID),
        .S2_ARADDR(slave2_if.S2_ARADDR),
        .S2_ARLEN(slave2_if.S2_ARLEN),
        .S2_ARSIZE(slave2_if.S2_ARSIZE),
        .S2_ARBURST(slave2_if.S2_ARBURST),
        .S2_ARLOCK(slave2_if.S2_ARLOCK),
        .S2_ARCACHE(slave2_if.S2_ARCACHE),
        .S2_ARPROT(slave2_if.S2_ARPROT),
        .S2_ARQOS(slave2_if.S2_ARQOS),
        .S2_ARREGION(slave2_if.S2_ARREGION),
        .S2_ARUSER(slave2_if.S2_ARUSER),
        .S2_ARVALID(slave2_if.S2_ARVALID),
        .S2_ARREADY(slave2_if.S2_ARREADY),
        
        // Read Data Channel
        .S2_RID(slave2_if.S2_RID),
        .S2_RDATA(slave2_if.S2_RDATA),
        .S2_RRESP(slave2_if.S2_RRESP),
        .S2_RLAST(slave2_if.S2_RLAST),
        .S2_RUSER(slave2_if.S2_RUSER),
        .S2_RVALID(slave2_if.S2_RVALID),
        .S2_RREADY(slave2_if.S2_RREADY),
        
        // ===== SLAVE 3 INTERFACE (Accessible only by Master 0) =====
        // Write Address Channel
        .S3_AWID(slave3_if.S3_AWID),
        .S3_AWADDR(slave3_if.S3_AWADDR),
        .S3_AWLEN(slave3_if.S3_AWLEN),
        .S3_AWSIZE(slave3_if.S3_AWSIZE),
        .S3_AWBURST(slave3_if.S3_AWBURST),
        .S3_AWLOCK(slave3_if.S3_AWLOCK),
        .S3_AWCACHE(slave3_if.S3_AWCACHE),
        .S3_AWPROT(slave3_if.S3_AWPROT),
        .S3_AWQOS(slave3_if.S3_AWQOS),
        .S3_AWREGION(slave3_if.S3_AWREGION),
        .S3_AWUSER(slave3_if.S3_AWUSER),
        .S3_AWVALID(slave3_if.S3_AWVALID),
        .S3_AWREADY(slave3_if.S3_AWREADY),
        
        // Write Data Channel
        .S3_WDATA(slave3_if.S3_WDATA),
        .S3_WSTRB(slave3_if.S3_WSTRB),
        .S3_WLAST(slave3_if.S3_WLAST),
        .S3_WUSER(slave3_if.S3_WUSER),
        .S3_WVALID(slave3_if.S3_WVALID),
        .S3_WREADY(slave3_if.S3_WREADY),
        
        // Write Response Channel
        .S3_BID(slave3_if.S3_BID),
        .S3_BRESP(slave3_if.S3_BRESP),
        .S3_BUSER(slave3_if.S3_BUSER),
        .S3_BVALID(slave3_if.S3_BVALID),
        .S3_BREADY(slave3_if.S3_BREADY),
        
        // Read Address Channel
        .S3_ARID(slave3_if.S3_ARID),
        .S3_ARADDR(slave3_if.S3_ARADDR),
        .S3_ARLEN(slave3_if.S3_ARLEN),
        .S3_ARSIZE(slave3_if.S3_ARSIZE),
        .S3_ARBURST(slave3_if.S3_ARBURST),
        .S3_ARLOCK(slave3_if.S3_ARLOCK),
        .S3_ARCACHE(slave3_if.S3_ARCACHE),
        .S3_ARPROT(slave3_if.S3_ARPROT),
        .S3_ARQOS(slave3_if.S3_ARQOS),
        .S3_ARREGION(slave3_if.S3_ARREGION),
        .S3_ARUSER(slave3_if.S3_ARUSER),
        .S3_ARVALID(slave3_if.S3_ARVALID),
        .S3_ARREADY(slave3_if.S3_ARREADY),
        
        // Read Data Channel
        .S3_RID(slave3_if.S3_RID),
        .S3_RDATA(slave3_if.S3_RDATA),
        .S3_RRESP(slave3_if.S3_RRESP),
        .S3_RLAST(slave3_if.S3_RLAST),
        .S3_RUSER(slave3_if.S3_RUSER),
        .S3_RVALID(slave3_if.S3_RVALID),
        .S3_RREADY(slave3_if.S3_RREADY),
        
        // ===== SLAVE 4 INTERFACE (Accessible only by Master 0) =====
        // Write Address Channel
        .S4_AWID(slave4_if.S4_AWID),
        .S4_AWADDR(slave4_if.S4_AWADDR),
        .S4_AWLEN(slave4_if.S4_AWLEN),
        .S4_AWSIZE(slave4_if.S4_AWSIZE),
        .S4_AWBURST(slave4_if.S4_AWBURST),
        .S4_AWLOCK(slave4_if.S4_AWLOCK),
        .S4_AWCACHE(slave4_if.S4_AWCACHE),
        .S4_AWPROT(slave4_if.S4_AWPROT),
        .S4_AWQOS(slave4_if.S4_AWQOS),
        .S4_AWREGION(slave4_if.S4_AWREGION),
        .S4_AWUSER(slave4_if.S4_AWUSER),
        .S4_AWVALID(slave4_if.S4_AWVALID),
        .S4_AWREADY(slave4_if.S4_AWREADY),
        
        // Write Data Channel
        .S4_WDATA(slave4_if.S4_WDATA),
        .S4_WSTRB(slave4_if.S4_WSTRB),
        .S4_WLAST(slave4_if.S4_WLAST),
        .S4_WUSER(slave4_if.S4_WUSER),
        .S4_WVALID(slave4_if.S4_WVALID),
        .S4_WREADY(slave4_if.S4_WREADY),
        
        // Write Response Channel
        .S4_BID(slave4_if.S4_BID),
        .S4_BRESP(slave4_if.S4_BRESP),
        .S4_BUSER(slave4_if.S4_BUSER),
        .S4_BVALID(slave4_if.S4_BVALID),
        .S4_BREADY(slave4_if.S4_BREADY),
        
        // Read Address Channel
        .S4_ARID(slave4_if.S4_ARID),
        .S4_ARADDR(slave4_if.S4_ARADDR),
        .S4_ARLEN(slave4_if.S4_ARLEN),
        .S4_ARSIZE(slave4_if.S4_ARSIZE),
        .S4_ARBURST(slave4_if.S4_ARBURST),
        .S4_ARLOCK(slave4_if.S4_ARLOCK),
        .S4_ARCACHE(slave4_if.S4_ARCACHE),
        .S4_ARPROT(slave4_if.S4_ARPROT),
        .S4_ARQOS(slave4_if.S4_ARQOS),
        .S4_ARREGION(slave4_if.S4_ARREGION),
        .S4_ARUSER(slave4_if.S4_ARUSER),
        .S4_ARVALID(slave4_if.S4_ARVALID),
        .S4_ARREADY(slave4_if.S4_ARREADY),
        
        // Read Data Channel
        .S4_RID(slave4_if.S4_RID),
        .S4_RDATA(slave4_if.S4_RDATA),
        .S4_RRESP(slave4_if.S4_RRESP),
        .S4_RLAST(slave4_if.S4_RLAST),
        .S4_RUSER(slave4_if.S4_RUSER),
        .S4_RVALID(slave4_if.S4_RVALID),
        .S4_RREADY(slave4_if.S4_RREADY),
        
        // ===== SLAVE 5 INTERFACE (Accessible only by Master 0) =====
        // Write Address Channel
        .S5_AWID(slave5_if.S5_AWID),
        .S5_AWADDR(slave5_if.S5_AWADDR),
        .S5_AWLEN(slave5_if.S5_AWLEN),
        .S5_AWSIZE(slave5_if.S5_AWSIZE),
        .S5_AWBURST(slave5_if.S5_AWBURST),
        .S5_AWLOCK(slave5_if.S5_AWLOCK),
        .S5_AWCACHE(slave5_if.S5_AWCACHE),
        .S5_AWPROT(slave5_if.S5_AWPROT),
        .S5_AWQOS(slave5_if.S5_AWQOS),
        .S5_AWREGION(slave5_if.S5_AWREGION),
        .S5_AWUSER(slave5_if.S5_AWUSER),
        .S5_AWVALID(slave5_if.S5_AWVALID),
        .S5_AWREADY(slave5_if.S5_AWREADY),
        
        // Write Data Channel
        .S5_WDATA(slave5_if.S5_WDATA),
        .S5_WSTRB(slave5_if.S5_WSTRB),
        .S5_WLAST(slave5_if.S5_WLAST),
        .S5_WUSER(slave5_if.S5_WUSER),
        .S5_WVALID(slave5_if.S5_WVALID),
        .S5_WREADY(slave5_if.S5_WREADY),
        
        // Write Response Channel
        .S5_BID(slave5_if.S5_BID),
        .S5_BRESP(slave5_if.S5_BRESP),
        .S5_BUSER(slave5_if.S5_BUSER),
        .S5_BVALID(slave5_if.S5_BVALID),
        .S5_BREADY(slave5_if.S5_BREADY),
        
        // Read Address Channel
        .S5_ARID(slave5_if.S5_ARID),
        .S5_ARADDR(slave5_if.S5_ARADDR),
        .S5_ARLEN(slave5_if.S5_ARLEN),
        .S5_ARSIZE(slave5_if.S5_ARSIZE),
        .S5_ARBURST(slave5_if.S5_ARBURST),
        .S5_ARLOCK(slave5_if.S5_ARLOCK),
        .S5_ARCACHE(slave5_if.S5_ARCACHE),
        .S5_ARPROT(slave5_if.S5_ARPROT),
        .S5_ARQOS(slave5_if.S5_ARQOS),
        .S5_ARREGION(slave5_if.S5_ARREGION),
        .S5_ARUSER(slave5_if.S5_ARUSER),
        .S5_ARVALID(slave5_if.S5_ARVALID),
        .S5_ARREADY(slave5_if.S5_ARREADY),
        
        // Read Data Channel
        .S5_RID(slave5_if.S5_RID),
        .S5_RDATA(slave5_if.S5_RDATA),
        .S5_RRESP(slave5_if.S5_RRESP),
        .S5_RLAST(slave5_if.S5_RLAST),
        .S5_RUSER(slave5_if.S5_RUSER),
        .S5_RVALID(slave5_if.S5_RVALID),
        .S5_RREADY(slave5_if.S5_RREADY),
        
        // ===== SLAVE 6 INTERFACE (Accessible only by Master 0) =====
        // Write Address Channel
        .S6_AWID(slave6_if.S6_AWID),
        .S6_AWADDR(slave6_if.S6_AWADDR),
        .S6_AWLEN(slave6_if.S6_AWLEN),
        .S6_AWSIZE(slave6_if.S6_AWSIZE),
        .S6_AWBURST(slave6_if.S6_AWBURST),
        .S6_AWLOCK(slave6_if.S6_AWLOCK),
        .S6_AWCACHE(slave6_if.S6_AWCACHE),
        .S6_AWPROT(slave6_if.S6_AWPROT),
        .S6_AWQOS(slave6_if.S6_AWQOS),
        .S6_AWREGION(slave6_if.S6_AWREGION),
        .S6_AWUSER(slave6_if.S6_AWUSER),
        .S6_AWVALID(slave6_if.S6_AWVALID),
        .S6_AWREADY(slave6_if.S6_AWREADY),
        
        // Write Data Channel
        .S6_WDATA(slave6_if.S6_WDATA),
        .S6_WSTRB(slave6_if.S6_WSTRB),
        .S6_WLAST(slave6_if.S6_WLAST),
        .S6_WUSER(slave6_if.S6_WUSER),
        .S6_WVALID(slave6_if.S6_WVALID),
        .S6_WREADY(slave6_if.S6_WREADY),
        
        // Write Response Channel
        .S6_BID(slave6_if.S6_BID),
        .S6_BRESP(slave6_if.S6_BRESP),
        .S6_BUSER(slave6_if.S6_BUSER),
        .S6_BVALID(slave6_if.S6_BVALID),
        .S6_BREADY(slave6_if.S6_BREADY),
        
        // Read Address Channel
        .S6_ARID(slave6_if.S6_ARID),
        .S6_ARADDR(slave6_if.S6_ARADDR),
        .S6_ARLEN(slave6_if.S6_ARLEN),
        .S6_ARSIZE(slave6_if.S6_ARSIZE),
        .S6_ARBURST(slave6_if.S6_ARBURST),
        .S6_ARLOCK(slave6_if.S6_ARLOCK),
        .S6_ARCACHE(slave6_if.S6_ARCACHE),
        .S6_ARPROT(slave6_if.S6_ARPROT),
        .S6_ARQOS(slave6_if.S6_ARQOS),
        .S6_ARREGION(slave6_if.S6_ARREGION),
        .S6_ARUSER(slave6_if.S6_ARUSER),
        .S6_ARVALID(slave6_if.S6_ARVALID),
        .S6_ARREADY(slave6_if.S6_ARREADY),
        
        // Read Data Channel
        .S6_RID(slave6_if.S6_RID),
        .S6_RDATA(slave6_if.S6_RDATA),
        .S6_RRESP(slave6_if.S6_RRESP),
        .S6_RLAST(slave6_if.S6_RLAST),
        .S6_RUSER(slave6_if.S6_RUSER),
        .S6_RVALID(slave6_if.S6_RVALID),
        .S6_RREADY(slave6_if.S6_RREADY)
    );

    // ===== UVM TEST START =====
    initial begin
        // Set virtual interfaces in config database for UVM components
        uvm_config_db#(virtual M0_interface)::set(null, "*", "master0_vif", master0_if);
        uvm_config_db#(virtual M1_interface)::set(null, "*", "master1_vif", master1_if);
        uvm_config_db#(virtual M2_interface)::set(null, "*", "master2_vif", master2_if);
        uvm_config_db#(virtual M3_interface)::set(null, "*", "master3_vif", master3_if);
        
        uvm_config_db#(virtual S0_interface)::set(null, "*", "slave0_vif", slave0_if);
        uvm_config_db#(virtual S1_interface)::set(null, "*", "slave1_vif", slave1_if);
        uvm_config_db#(virtual S2_interface)::set(null, "*", "slave2_vif", slave2_if);
        uvm_config_db#(virtual S3_interface)::set(null, "*", "slave3_vif", slave3_if);
        uvm_config_db#(virtual S4_interface)::set(null, "*", "slave4_vif", slave4_if);
        uvm_config_db#(virtual S5_interface)::set(null, "*", "slave5_vif", slave5_if);
        uvm_config_db#(virtual S6_interface)::set(null, "*", "slave6_vif", slave6_if);
        
            // Set up UVM verbosity (UVM_LOW = 0)
        uvm_top.set_report_verbosity_level(0);
        
        // Enable UVM transaction recording
        uvm_top.enable_print_topology = 1;
        // Start UVM test
        run_test();
    end

    // Waveform dumping
    initial begin
        $shm_open("wave.shm");
        $shm_probe("AS");
    end
  

    // ===== MONITORING =====
    // Monitor for basic signal activity
    always @(posedge ACLK) begin
        if (ARESETn) begin
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
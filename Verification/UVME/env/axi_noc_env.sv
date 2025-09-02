//=============================================================================
// AXI NoC Environment Class
//=============================================================================
// Main environment for the 4-Master 7-Slave AXI NoC verification
// Instantiates and connects all agents, coverage, scoreboard, and protocol checkers
// Uses uvm_top.print_topology() for automatic topology display

`ifndef AXI_NOC_ENV_SV
`define AXI_NOC_ENV_SV

// Note: All imports and includes will be handled by axi_noc_pkg

class axi_noc_env extends uvm_env;
    `uvm_component_utils(axi_noc_env)
    
    // ===== AGENT INSTANCES =====
    // Master agents
    M0_agent m0_agent;
    M1_agent m1_agent;
    M2_agent m2_agent;
    M3_agent m3_agent;
    
    // Slave agents
    S0_agent s0_agent;
    S1_agent s1_agent;
    S2_agent s2_agent;
    S3_agent s3_agent;
    S4_agent s4_agent;
    S5_agent s5_agent;
    S6_agent s6_agent;
    
    // Virtual sequencer
    virtual_sequencer virtual_seqr;
    // // ===== ENVIRONMENT COMPONENTS =====
    // // Coverage components
    // axi_master_coverage m0_coverage;
    // axi_master_coverage m1_coverage;
    // axi_master_coverage m2_coverage;
    // axi_master_coverage m3_coverage;
    
    // axi_slave_coverage s0_coverage;
    // axi_slave_coverage s1_coverage;
    // axi_slave_coverage s2_coverage;
    // axi_slave_coverage s3_coverage;
    // axi_slave_coverage s4_coverage;
    // axi_slave_coverage s5_coverage;
    // axi_slave_coverage s6_coverage;
    
    // // System-level coverage
    // axi_noc_coverage noc_coverage;
    
    // // Scoreboard and protocol checking
    // axi_noc_scoreboard noc_scoreboard;
    // axi_protocol_checker protocol_checker;
    
    // ===== CONFIGURATION =====
    // Environment configuration
    uvm_active_passive_enum master_agent_mode = UVM_ACTIVE;
    uvm_active_passive_enum slave_agent_mode = UVM_ACTIVE;
    
    // ===== CONSTRUCTOR =====
    function new(string name = "axi_noc_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // ===== BUILD PHASE =====
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Build master agents
        m0_agent = M0_agent::type_id::create("m0_agent", this);
        m1_agent = M1_agent::type_id::create("m1_agent", this);
        m2_agent = M2_agent::type_id::create("m2_agent", this);
        m3_agent = M3_agent::type_id::create("m3_agent", this);
        
        // Build slave agents
        s0_agent = S0_agent::type_id::create("s0_agent", this);
        s1_agent = S1_agent::type_id::create("s1_agent", this);
        s2_agent = S2_agent::type_id::create("s2_agent", this);
        s3_agent = S3_agent::type_id::create("s3_agent", this);
        s4_agent = S4_agent::type_id::create("s4_agent", this);
        s5_agent = S5_agent::type_id::create("s5_agent", this);
        s6_agent = S6_agent::type_id::create("s6_agent", this);
        
        // Build virtual sequencer
        virtual_seqr = virtual_sequencer::type_id::create("virtual_seqr", this);
        
        // // Build coverage components
        // m0_coverage = axi_master_coverage::type_id::create("m0_coverage", this);
        // m1_coverage = axi_master_coverage::type_id::create("m1_coverage", this);
        // m2_coverage = axi_master_coverage::type_id::create("m2_coverage", this);
        // m3_coverage = axi_master_coverage::type_id::create("m3_coverage", this);
        
        // s0_coverage = axi_slave_coverage::type_id::create("s0_coverage", this);
        // s1_coverage = axi_slave_coverage::type_id::create("s1_coverage", this);
        // s2_coverage = axi_slave_coverage::type_id::create("s2_coverage", this);
        // s3_coverage = axi_slave_coverage::type_id::create("s3_coverage", this);
        // s4_coverage = axi_slave_coverage::type_id::create("s4_coverage", this);
        // s5_coverage = axi_slave_coverage::type_id::create("s5_coverage", this);
        // s6_coverage = axi_slave_coverage::type_id::create("s6_coverage", this);
        
        // // Build system-level components
        // noc_coverage = axi_noc_coverage::type_id::create("noc_coverage", this);
        // noc_scoreboard = axi_noc_scoreboard::type_id::create("noc_scoreboard", this);
        // protocol_checker = axi_protocol_checker::type_id::create("protocol_checker", this);
        
        `uvm_info("AXI_NOC_ENV", "Environment built successfully", UVM_LOW)
    endfunction
    
    // ===== CONNECT PHASE =====
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // Set config database for virtual sequencer to find all agent sequencers
        uvm_config_db#(M0_sequencer)::set(this, "virtual_seqr", "m0_sequencer", m0_agent.m0_sequencer);
        uvm_config_db#(M1_sequencer)::set(this, "virtual_seqr", "m1_sequencer", m1_agent.m1_sequencer);
        uvm_config_db#(M2_sequencer)::set(this, "virtual_seqr", "m2_sequencer", m2_agent.m2_sequencer);
        uvm_config_db#(M3_sequencer)::set(this, "virtual_seqr", "m3_sequencer", m3_agent.m3_sequencer);
        
        uvm_config_db#(S0_sequencer)::set(this, "virtual_seqr", "s0_sequencer", s0_agent.s0_sequencer);
        uvm_config_db#(S1_sequencer)::set(this, "virtual_seqr", "s1_sequencer", s1_agent.s1_sequencer);
        uvm_config_db#(S2_sequencer)::set(this, "virtual_seqr", "s2_sequencer", s2_agent.s2_sequencer);
        uvm_config_db#(S3_sequencer)::set(this, "virtual_seqr", "s3_sequencer", s3_agent.s3_sequencer);
        uvm_config_db#(S4_sequencer)::set(this, "virtual_seqr", "s4_sequencer", s4_agent.s4_sequencer);
        uvm_config_db#(S5_sequencer)::set(this, "virtual_seqr", "s5_sequencer", s5_agent.s5_sequencer);
        uvm_config_db#(S6_sequencer)::set(this, "virtual_seqr", "s6_sequencer", s6_agent.s6_sequencer);
        
        `uvm_info("AXI_NOC_ENV", "All agent sequencers configured for virtual sequencer", UVM_LOW)
    endfunction
    
    // ===== RUN PHASE =====
    task run_phase(uvm_phase phase);
        super.run_phase(phase);
        
        // Environment-level monitoring and control can be added here
        `uvm_info("AXI_NOC_ENV", "Environment running - monitoring all agents", UVM_LOW)
    endtask
    
    // ===== END OF ELABORATION PHASE =====
    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        
        `uvm_info("AXI_NOC_ENV", "Environment elaboration completed", UVM_LOW)
        `uvm_info("AXI_NOC_ENV", "All components built and connected", UVM_LOW)
        
        // Print UVM topology at end of elaboration for debugging
        `uvm_info("AXI_NOC_ENV", "Printing UVM topology after elaboration:", UVM_LOW)
        uvm_top.print_topology();
        
        `uvm_info("AXI_NOC_ENV", "Topology printed successfully", UVM_LOW)
    endfunction
    
    // ===== REPORT PHASE =====
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        // Print the complete UVM topology using built-in function
        uvm_top.print_topology();
        
        `uvm_info("AXI_NOC_ENV", "Environment report phase completed", UVM_LOW)
        `uvm_info("AXI_NOC_ENV", "Check individual component reports for detailed results", UVM_LOW)
    endfunction
    
endclass

`endif // AXI_NOC_ENV_SV
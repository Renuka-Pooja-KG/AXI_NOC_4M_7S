//=============================================================================
// AXI Agents Package
//=============================================================================
// This package includes all AXI agent definitions for the NOC verification
// environment. It provides easy access to all agent types.

`ifndef AXI_AGENTS_PKG_SV
`define AXI_AGENTS_PKG_SV

package axi_agents_pkg;

    // Include all agent files
    `include "axi_master0_agent.sv"
    `include "axi_master1_agent.sv"
    
    // Export all agent types
    export axi_master0_agent;
    export axi_master0_driver;
    export axi_master0_monitor;
    export axi_master0_sequencer;
    export axi_master0_config;
    
    export axi_master1_agent;
    export axi_master1_driver;
    export axi_master1_monitor;
    export axi_master1_sequencer;
    export axi_master1_config;
    
endpackage : axi_agents_pkg

`endif // AXI_AGENTS_PKG_SV


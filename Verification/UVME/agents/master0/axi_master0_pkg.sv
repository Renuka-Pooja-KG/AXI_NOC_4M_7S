//=============================================================================
// AXI Master 0 Package
//=============================================================================
// This package includes all Master 0 agent components for the NOC verification
// environment. It provides easy access to all Master 0 related classes.

`ifndef AXI_MASTER0_PKG_SV
`define AXI_MASTER0_PKG_SV

package axi_master0_pkg;

    // Include all Master 0 component files
    `include "axi_master0_driver.sv"
    `include "axi_master0_monitor.sv"
    `include "axi_master0_sequencer.sv"
    `include "axi_master0_config.sv"
    `include "axi_master0_agent.sv"
    
    // Export all Master 0 component types
    export axi_master0_driver;
    export axi_master0_monitor;
    export axi_master0_sequencer;
    export axi_master0_config;
    export axi_master0_agent;
    
endpackage : axi_master0_pkg

`endif // AXI_MASTER0_PKG_SV


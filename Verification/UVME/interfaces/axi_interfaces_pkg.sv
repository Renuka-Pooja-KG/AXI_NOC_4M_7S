//=============================================================================
// AXI Interfaces Package
//=============================================================================
// This package includes all AXI interface definitions for the NOC verification
// environment. It provides easy access to all interface types.

`ifndef AXI_INTERFACES_PKG_SV
`define AXI_INTERFACES_PKG_SV

package axi_interfaces_pkg;

    // Include all interface files
    `include "axi_if.sv"
    `include "axi_master0_if.sv"
    `include "axi_master1_if.sv"
    `include "axi_master2_if.sv"
    `include "axi_master3_if.sv"
    `include "axi_slave0_if.sv"
    `include "axi_slave1_if.sv"
    `include "axi_slave2_if.sv"
    `include "axi_slave3_if.sv"
    `include "axi_slave4_if.sv"
    `include "axi_slave5_if.sv"
    `include "axi_slave6_if.sv"
    
    // Export all interface types
    export axi_if;
    export axi_master0_if;
    export axi_master1_if;
    export axi_master2_if;
    export axi_master3_if;
    export axi_slave0_if;
    export axi_slave1_if;
    export axi_slave2_if;
    export axi_slave3_if;
    export axi_slave4_if;
    export axi_slave5_if;
    export axi_slave6_if;
    
endpackage : axi_interfaces_pkg

`endif // AXI_INTERFACES_PKG_SV

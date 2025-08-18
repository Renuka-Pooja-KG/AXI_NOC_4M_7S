//=============================================================================
// AXI Transactions Package
//=============================================================================
// This package includes all AXI transaction classes for the NOC verification
// environment. It provides easy access to all transaction types.

`ifndef AXI_TRANSACTIONS_PKG_SV
`define AXI_TRANSACTIONS_PKG_SV

package axi_transactions_pkg;

    // Import UVM
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Include all transaction classes
    `include "axi_transaction.sv"
    `include "axi_master_transaction.sv"
    `include "axi_slave_transaction.sv"
    
    // Include master-specific transaction classes
    `include "axi_master0_transaction.sv"
    `include "axi_master1_transaction.sv"
    `include "axi_master2_transaction.sv"
    `include "axi_master3_transaction.sv"
    
    // Include slave-specific transaction classes
    `include "axi_slave0_transaction.sv"
    `include "axi_slave1_transaction.sv"
    `include "axi_slave2_transaction.sv"
    `include "axi_slave3_transaction.sv"
    `include "axi_slave4_transaction.sv"
    `include "axi_slave5_transaction.sv"
    `include "axi_slave6_transaction.sv"
    
    // Export all transaction classes
    export axi_transaction;
    export axi_master_transaction;
    export axi_slave_transaction;
    export axi_master0_transaction;
    export axi_master1_transaction;
    export axi_master2_transaction;
    export axi_master3_transaction;
    export axi_slave0_transaction;
    export axi_slave1_transaction;
    export axi_slave2_transaction;
    export axi_slave3_transaction;
    export axi_slave4_transaction;
    export axi_slave5_transaction;
    export axi_slave6_transaction;
    
    // Export enums
    export axi_trans_type_e;
    export axi_burst_type_e;
    export axi_resp_type_e;
    export axi_lock_type_e;
    
endpackage : axi_transactions_pkg

`endif // AXI_TRANSACTIONS_PKG_SV

# AXI NOC Verification Project
## 4 Masters, 7 Slaves Network-on-Chip Verification Environment

### Project Overview
This project implements a comprehensive UVM verification environment for an AXI (Advanced eXtensible Interface) Network-on-Chip (NOC) with 4 AXI masters and 7 AXI slaves. The NOC implements sophisticated access control where Master 0 has full access to all slaves, while Masters 1, 2, and 3 have restricted access to specific slave subsets.

### Architecture Specifications

#### Master-Slave Access Control Matrix
```
                    S0    S1    S2    S3    S4    S5    S6
                 ┌─────┬─────┬─────┬─────┬─────┬─────┬─────┐
M0 (Full Access) │  ✓  │  ✓  │  ✓  │  ✓  │  ✓  │  ✓  │  ✓  │
                 ├─────┼─────┼─────┼─────┼─────┼─────┼─────┤
M1 (Limited)     │  ✗  │  ✓  │  ✗  │  ✓  │  ✓  │  ✗  │  ✗  │
                 ├─────┼─────┼─────┼─────┼─────┼─────┼─────┤
M2 (Limited)     │  ✗  │  ✓  │  ✓  │  ✗  │  ✓  │  ✗  │  ✗  │
                 ├─────┼─────┼─────┼─────┼─────┼─────┼─────┤
M3 (Limited)     │  ✗  │  ✓  │  ✗  │  ✗  │  ✗  │  ✓  │  ✓  │
                 └─────┴─────┴─────┴─────┴─────┴─────┴─────┘
```

#### Slave Address Mapping
| Slave | Base Address | Address Range | Description |
|-------|--------------|---------------|-------------|
| S0    | 0x0000_0000 | 0x0000_0000 - 0x0000_0FFF | Slave 0 |
| S1    | 0x0000_2000 | 0x0000_2000 - 0x0000_2FFF | Slave 1 |
| S2    | 0x0000_4000 | 0x0000_4000 - 0x0000_4FFF | Slave 2 |
| S3    | 0x0000_6000 | 0x0000_6000 - 0x0000_6FFF | Slave 3 |
| S4    | 0x0000_8000 | 0x0000_8000 - 0x0000_8FFF | Slave 4 |
| S5    | 0x0000_A000 | 0x0000_A000 - 0x0000_AFFF | Slave 5 |
| S6    | 0x0000_C000 | 0x0000_C000 - 0x0000_CFFF | Slave 6 |

### RTL Interface Specifications

#### Global System Signals
- **`axi_m4s7_NOC_arbiter_top_clk`** (1 bit): System clock input
- **`axi_m4s7_NOC_arbiter_top_rstn`** (1 bit): Active-low reset input

#### Master Interface Signals (M0-M3)
Each master interface contains identical signal structure with different prefixes (M0_, M1_, M2_, M3_):

**Write Address Channel (AW) - Master Driven:**
- `M*_AWID[3:0]`: Write address channel ID
- `M*_AWVALID`: Write address valid
- `M*_AWADDR[31:0]`: Write address
- `M*_AWLEN[3:0]`: Burst length
- `M*_AWBURST[1:0]`: Burst type (fixed/increment/wrap)
- `M*_AWLOCK`: Lock signal
- `M*_AWSIZE[2:0]`: Transfer size
- `M*_AWPROT[2:0]`: Protection attributes
- `M*_AWQOS[3:0]`: Quality of service
- `M*_AWREGION[3:0]`: Region identifier

**Write Data Channel (W) - Master Driven:**
- `M*_WVALID`: Write data valid
- `M*_WDATA[31:0]`: Write data
- `M*_WLAST`: Last transfer indicator
- `M*_WSTRB[3:0]`: Write strobe (byte enables)

**Write Response Channel (B) - Master Driven:**
- `M*_BREADY`: Ready for write response

**Read Address Channel (AR) - Master Driven:**
- `M*_ARID[3:0]`: Read address channel ID
- `M*_ARVALID`: Read address valid
- `M*_ARADDR[31:0]`: Read address
- `M*_ARLEN[3:0]`: Burst length
- `M*_ARBURST[1:0]`: Burst type
- `M*_ARLOCK`: Lock signal
- `M*_ARSIZE[2:0]`: Transfer size
- `M*_ARPROT[2:0]`: Protection attributes
- `M*_ARQOS[3:0]`: Quality of service
- `M*_ARREGION[3:0]`: Region identifier

**Read Data Channel (R) - Master Driven:**
- `M*_RREADY`: Ready for read data

#### Slave Interface Signals (S0-S6)
Each slave interface contains identical signal structure with different prefixes (S0_, S1_, S2_, etc.):

**Write Address Channel (AW) - Slave Driven:**
- `S*_AWREADY`: Ready to accept write address

**Write Data Channel (W) - Slave Driven:**
- `S*_WREADY`: Ready to accept write data

**Write Response Channel (B) - Slave Driven:**
- `S*_BID[5:0]`: Write response ID
- `S*_BRESP[1:0]`: Write response status
- `S*_BVALID`: Write response valid

**Read Address Channel (AR) - Slave Driven:**
- `S*_ARREADY`: Ready to accept read address

**Read Data Channel (R) - Slave Driven:**
- `S*_RID[5:0]`: Read response ID
- `S*_RDATA[31:0]`: Read data
- `S*_RRESP[1:0]`: Read response status
- `S*_RLAST`: Last transfer indicator
- `S*_RVALID`: Read data valid

### UVM Verification Architecture

#### System Overview
```
┌─────────────────────────────────────────────────────────────────┐
│                    AXI NOC Verification Environment             │
├─────────────────────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────┐ │
│  │ Master 0    │  │ Master 1    │  │ Master 2    │  │ Master 3│ │
│  │ Agent       │  │ Agent       │  │ Agent       │  │ Agent   │ │
│  │ (Active)    │  │ (Active)    │  │ (Active)    │  │(Active) │ │
│  └─────────────┘  └─────────────┘  └─────────────┘  └─────────┘ │
│           │               │               │               │     │
│           └───────────────┼───────────────┼───────────────┘     │
│                           │               │                     │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │                Virtual Sequencer                           │ │
│  │           (Coordinates Master Sequences)                   │ │
│  │           (Coordinates Slave Sequences)                    │ │
│  └─────────────────────────────────────────────────────────────┘ │
│                           │                                     │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │                Scoreboard                                  │ │
│  │        (Access Control & Transaction Verification)         │ │
│  └─────────────────────────────────────────────────────────────┘ │
│                           │                                     │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │                Coverage Collector                          │ │
│  │           (Functional Coverage Collection)                 │ │
│  └─────────────────────────────────────────────────────────────┘ │
│                           │                                     │
│  ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐     │
│  │ S0  │ │ S1  │ │ S2  │ │ S3  │ │ S4  │ │ S5  │ │ S6  │     │
│  │Agent│ │Agent│ │Agent│ │Agent│ │Agent│ │Agent│ │Agent│     │
│  │(Act)│ │(Act)│ │(Act)│ │(Act)│ │(Act)│ │(Act)│ │(Act)│     │
│  └─────┘ └─────┘ └─────┘ └─────┘ └─────┘ └─────┘ └─────┘     │
└─────────────────────────────────────────────────────────────────┘
```

### Verification Environment Architecture

#### **Flat Environment Model (Recommended)**

#### Component Details

**Total Interfaces: 11**
- Master Interfaces: 4 (M0, M1, M2, M3)
- Slave Interfaces: 7 (S0, S1, S2, S3, S4, S5, S6)

**Total Agents: 11**
- Master Agents: 4 (Active)
- Slave Agents: 7 (Active)

#### Agent Types and Configuration

**Active Agents (4 + 7):**
- **axi_master_agent m0_agent**: Master 0 - Full access to all slaves
- **axi_master_agent m1_agent**: Master 1 - Access to S1, S3, S4 only
- **axi_master_agent m2_agent**: Master 2 - Access to S1, S2, S4 only
- **axi_master_agent m3_agent**: Master 3 - Access to S1, S5, S6 only

- **axi_slave_agent s0_agent**: Slave 0 - Address range 0x0000_0000-0x0000_0FFF
- **axi_slave_agent s1_agent**: Slave 1 - Address range 0x0000_2000-0x0000_2FFF
- **axi_slave_agent s2_agent**: Slave 2 - Address range 0x0000_4000-0x0000_4FFF
- **axi_slave_agent s3_agent**: Slave 3 - Address range 0x0000_6000-0x0000_6FFF
- **axi_slave_agent s4_agent**: Slave 4 - Address range 0x0000_8000-0x0000_8FFF
- **axi_slave_agent s5_agent**: Slave 5 - Address range 0x0000_A000-0x0000_AFFF
- **axi_slave_agent s6_agent**: Slave 6 - Address range 0x0000_C000-0x0000_CFFF

#### UVM Components Structure

**Top-Level Components:**
- **axi_noc_tb_top**: Testbench top module
- **axi_noc_test**: Main test class
- **axi_noc_env**: Environment containing all agents

**Environment Components:**
- **axi_noc_env**: Main environment class
- **axi_noc_scoreboard**: Transaction verification
- **axi_noc_coverage**: Functional coverage collection
- **axi_noc_virtual_sequencer**: Coordinates multiple master sequences

**Agent Components:**
Each active master agent contains:
- **axi_master_sequencer**: Generates transaction sequences
- **axi_master_driver**: Drives AXI signals
- **axi_master_monitor**: Observes AXI signals
- **axi_master_config**: Agent-specific configuration

Each active slave agent contains:
- **axi_slave_sequencer**: Generates response transactions
- **axi_slave_driver**: Simple response generation
- **axi_slave_monitor**: Observes AXI signals
- **axi_slave_config**: Address range and response configuration

### Key Features

1. **Supports both in-order and out-of-order transactions**
2. **Parallel access to different slaves**
3. **Round-robin arbitration for shared slave access**
4. **Comprehensive access control enforcement**
5. **Full AXI4 protocol compliance**

### Design Limitations

1. **Single AXI master cannot issue back-to-back address transactions targeting different slaves**
2. **Must complete transaction to one slave (including response phase) before initiating another transaction to different slave**

#### **Why Flat Environment Model?**
- **Simpler Architecture**: Single environment manages all agents
- **Easier Configuration**: Centralized configuration management
- **Better Resource Sharing**: Shared scoreboard, checkers, and coverage
- **Reduced Complexity**: No need for multiple environment instances
- **Easier Debugging**: Single point of control and monitoring

#### **Virtual Sequencer Coordination**
**Note**: Both masters and slaves are active agents because:
- **Masters**: Generate and drive transaction requests
- **Slaves**: Generate and drive response signals (RVALID, RVALID, BVALID, etc.)

## Benefits of Flat Environment Model

1. **Centralized Control**: Single environment manages all verification components
2. **Shared Resources**: Common scoreboard, checkers, and coverage across all agents
3. **Simplified Configuration**: Easier to manage agent configurations and relationships
4. **Better Debugging**: Single point of control for all verification activities
5. **Easier Maintenance**: Less code duplication and simpler hierarchy
6. **Efficient Resource Usage**: Shared components reduce memory and simulation overhead

## Alternative Architectures (Not Recommended)

### **Hierarchical Environment Model**
- Separate environments for each master/slave group
- More complex configuration management
- Duplicate components across environments
- Harder to coordinate between different environment instances

### **Why Flat Model is Better**
- **Simplicity**: Easier to understand and maintain
- **Efficiency**: Better resource utilization
- **Scalability**: Easier to add new agents or modify existing ones
- **Debugging**: Centralized monitoring and control

### Verification Plan

#### Test Categories
1. **Basic Functionality Tests**
   - Reset behavior verification
   - Clock domain validation
   - Basic read/write operations

2. **Access Control Tests**
   - Master 0 full access verification
   - Masters 1-3 restricted access validation
   - Access violation detection

3. **Arbitration Tests**
   - Single master scenarios
   - Multi-master contention
   - Round-robin fairness verification

4. **Protocol Compliance Tests**
   - AXI handshake validation
   - Burst transaction handling
   - Address alignment verification

5. **Design Limitation Tests**
   - Back-to-back restriction validation
   - Transaction completion requirements

6. **Performance Tests**
   - Parallel access verification
   - Throughput measurement
   - Latency analysis

7. **Corner Cases**
   - Boundary address testing
   - Maximum burst length validation
   - Reset during transaction scenarios

### Coverage Goals

#### Functional Coverage
- Master-slave access combinations
- Transaction types and burst patterns
- Address range coverage
- Arbitration scenarios

#### Code Coverage
- Line coverage > 95%
- Branch coverage > 90%
- Expression coverage > 85%

#### Protocol Coverage
- AXI handshake sequences
- Response combinations
- Error scenarios

### Project Structure
```
AXI_NOC_4M_7S/
├── README.md
├── Verification/
│   ├── SIM/
│   │   ├── compile_list.f
│   │   ├── Makefile
│   └── UVME/
│       ├── interfaces/
│       ├── transactions/
│       ├── sequences/
│       ├── agents/
│       ├── env/
│       ├── tests/
│       ├── coverage/
|       └── top/
└── RTL/
    └── axi_noc_4m7s.sv
```

### Getting Started

1. **Environment Setup**
   - Ensure UVM library is available
   - Set up simulation environment (ModelSim, VCS, etc.)
   - Configure AXI interface parameters

2. **Compilation**
   - Compile UVM library
   - Compile RTL design
   - Compile verification components

3. **Simulation**
   - Run basic functionality tests
   - Execute access control verification
   - Perform comprehensive regression testing

### Dependencies

- UVM 1.2 or later
- SystemVerilog 2012 or later
- Compatible simulator (ModelSim, VCS, Xcelium, etc.)

### Contact

For questions or issues related to this verification project, please refer to the project documentation or contact the verification team.

---

**Note**: This README provides a comprehensive overview of the AXI NOC verification project. For detailed implementation specifics, refer to the individual component files and test documentation.

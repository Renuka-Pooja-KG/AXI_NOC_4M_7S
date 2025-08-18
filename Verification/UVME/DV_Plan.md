# AXI NOC Design Verification (DV) Plan
## 4 Masters, 7 Slaves Network-on-Chip Verification

---

## 1. Overview
This document outlines the comprehensive verification plan for the AXI NOC with 4 masters and 7 slaves, where Master 0 has full access to all slaves while Masters 1, 2, and 3 have restricted access to specific slaves.

---

## 2. Features to Test

### 2.1 Core AXI Protocol Features
- **AXI Channel Handshaking**: AW, W, B, AR, R channel protocols
- **Burst Transfers**: INCR, WRAP, FIXED burst types
- **Transfer Sizes**: 8-bit, 16-bit, 32-bit, 64-bit, 128-bit transfers
- **Address Alignment**: Proper address alignment for different transfer sizes
- **Response Handling**: OKAY, EXOKAY, SLVERR, DECERR responses
- **ID-based Transaction Ordering**: Proper handling of transaction IDs

### 2.2 NOC-Specific Features
- **Master Access Control**: Verification of master-slave access permissions
- **Address Decoding**: Correct routing based on address ranges
- **Arbitration**: Fair access to shared slaves
- **Concurrent Transactions**: Multiple masters accessing different slaves simultaneously
- **Crossbar Routing**: Proper signal routing through the NOC fabric

### 2.3 Performance Features
- **Throughput**: Maximum transactions per cycle
- **Latency**: End-to-end transaction latency
- **Backpressure Handling**: Ready signal management
- **FIFO Management**: Buffer overflow/underflow scenarios

---

## 3. Test Cases Matrix

| Test Category | Test Case ID | Test Name | Description | Priority | Coverage Goals |
|---------------|---------------|-----------|-------------|----------|----------------|
| **Basic Functionality** | TC_BASIC_001 | Single Write Transaction | Basic write transaction from M0 to S0 | High | 100% |
| **Basic Functionality** | TC_BASIC_002 | Single Read Transaction | Basic read transaction from M0 to S0 | High | 100% |
| **Basic Functionality** | TC_BASIC_003 | Burst Write (INCR) | INCR burst write with length 1-15 | High | 100% |
| **Basic Functionality** | TC_BASIC_004 | Burst Read (INCR) | INCR burst read with length 1-15 | High | 100% |
| **Access Control** | TC_ACCESS_001 | M0 Full Access | M0 accessing all slaves (S0-S6) | High | 100% |
| **Access Control** | TC_ACCESS_002 | M1 Restricted Access | M1 accessing only S1, S3, S4 | High | 100% |
| **Access Control** | TC_ACCESS_003 | M2 Restricted Access | M2 accessing only S2, S4, S5 | High | 100% |
| **Access Control** | TC_ACCESS_004 | M3 Restricted Access | M3 accessing only S0, S2, S6 | High | 100% |
| **Access Control** | TC_ACCESS_005 | M1 Access Denied | M1 attempting to access S0 (should fail) | High | 100% |
| **Address Decoding** | TC_ADDR_001 | S0 Address Range | Transactions to 0x0000_0000-0x0000_0FFF | High | 100% |
| **Address Decoding** | TC_ADDR_002 | S1 Address Range | Transactions to 0x0000_2000-0x0000_2FFF | High | 100% |
| **Address Decoding** | TC_ADDR_003 | S2 Address Range | Transactions to 0x0000_4000-0x0000_4FFF | High | 100% |
| **Address Decoding** | TC_ADDR_004 | S3 Address Range | Transactions to 0x0000_6000-0x0000_6FFF | High | 100% |
| **Address Decoding** | TC_ADDR_005 | S4 Address Range | Transactions to 0x0000_8000-0x0000_8FFF | High | 100% |
| **Address Decoding** | TC_ADDR_006 | S5 Address Range | Transactions to 0x0000_A000-0x0000_AFFF | High | 100% |
| **Address Decoding** | TC_ADDR_007 | S6 Address Range | Transactions to 0x0000_C000-0x0000_CFFF | High | 100% |
| **Concurrent Access** | TC_CONC_001 | M0+M1 Concurrent | M0 and M1 accessing different slaves simultaneously | Medium | 100% |
| **Concurrent Access** | TC_CONC_002 | All Masters Concurrent | All masters accessing different slaves simultaneously | Medium | 100% |
| **Concurrent Access** | TC_CONC_003 | Same Slave Access | Multiple masters accessing the same slave (arbitration) | Medium | 100% |
| **Protocol Compliance** | TC_PROT_001 | Handshake Timing | Valid/Ready handshake timing compliance | High | 100% |
| **Protocol Compliance** | TC_PROT_002 | ID Ordering | Transaction ID ordering compliance | High | 100% |
| **Protocol Compliance** | TC_PROT_003 | Burst Continuity | Burst transfer continuity compliance | High | 100% |
| **Protocol Compliance** | TC_PROT_004 | Response Codes | All response code combinations | High | 100% |
| **Error Scenarios** | TC_ERR_001 | Slave Error Response | Slave returning SLVERR response | Medium | 100% |
| **Error Scenarios** | TC_ERR_002 | Decode Error | Access to unmapped address (DECERR) | Medium | 100% |
| **Error Scenarios** | TC_ERR_003 | Timeout Scenarios | Transaction timeout handling | Medium | 100% |
| **Performance** | TC_PERF_001 | Maximum Throughput | Maximum transactions per cycle | Low | 90% |
| **Performance** | TC_PERF_002 | Latency Measurement | End-to-end transaction latency | Low | 90% |
| **Reset/Initialization** | TC_RST_001 | Power-on Reset | System behavior after power-on reset | High | 100% |
| **Reset/Initialization** | TC_RST_002 | Soft Reset | System behavior after soft reset | High | 100% |
| **Reset/Initialization** | TC_RST_003 | Reset During Transaction | Reset assertion during active transaction | Medium | 100% |

---

## 4. Signal Coverage Matrix

### 4.1 Master Interface Signals

| Signal Group | Signal Name | Width | Direction | Coverage Type | Test Cases |
|--------------|-------------|-------|-----------|---------------|------------|
| **Write Address (AW)** | m[0-3]_awid | 4 | Output | Value, Toggle | TC_BASIC_001, TC_ACCESS_001-004 |
| **Write Address (AW)** | m[0-3]_awaddr | 32 | Output | Value, Range | TC_ADDR_001-007, TC_ACCESS_001-004 |
| **Write Address (AW)** | m[0-3]_awlen | 4 | Output | Value, Range | TC_BASIC_003, TC_PROT_003 |
| **Write Address (AW)** | m[0-3]_awsize | 3 | Output | Value, Range | TC_BASIC_001-004 |
| **Write Address (AW)** | m[0-3]_awburst | 2 | Output | Value, Enum | TC_BASIC_003-004, TC_PROT_003 |
| **Write Address (AW)** | m[0-3]_awlock | 1 | Output | Value, Toggle | TC_PROT_001 |
| **Write Address (AW)** | m[0-3]_awcache | 4 | Output | Value, Range | TC_PROT_001 |
| **Write Address (AW)** | m[0-3]_awprot | 3 | Output | Value, Range | TC_PROT_001 |
| **Write Address (AW)** | m[0-3]_awqos | 4 | Output | Value, Range | TC_PROT_001 |
| **Write Address (AW)** | m[0-3]_awregion | 4 | Output | Value, Range | TC_PROT_001 |
| **Write Address (AW)** | m[0-3]_awvalid | 1 | Output | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Write Address (AW)** | m[0-3]_awready | 1 | Input | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Write Data (W)** | m[0-3]_wdata | 32 | Output | Value, Toggle | TC_BASIC_001, TC_BASIC_003 |
| **Write Data (W)** | m[0-3]_wstrb | 4 | Output | Value, Toggle | TC_BASIC_001, TC_BASIC_003 |
| **Write Data (W)** | m[0-3]_wlast | 1 | Output | Toggle, Timing | TC_BASIC_003, TC_PROT_003 |
| **Write Data (W)** | m[0-3]_wvalid | 1 | Output | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Write Data (W)** | m[0-3]_wready | 1 | Input | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Write Response (B)** | m[0-3]_bid | 4 | Input | Value, Toggle | TC_BASIC_001, TC_ERR_001-002 |
| **Write Response (B)** | m[0-3]_bresp | 2 | Input | Value, Enum | TC_ERR_001-002, TC_PROT_004 |
| **Write Response (B)** | m[0-3]_bvalid | 1 | Input | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Write Response (B)** | m[0-3]_bready | 1 | Output | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Read Address (AR)** | m[0-3]_arid | 4 | Output | Value, Toggle | TC_BASIC_002, TC_ACCESS_001-004 |
| **Read Address (AR)** | m[0-3]_araddr | 32 | Output | Value, Range | TC_ADDR_001-007, TC_ACCESS_001-004 |
| **Read Address (AR)** | m[0-3]_arlen | 4 | Output | Value, Range | TC_BASIC_004, TC_PROT_003 |
| **Read Address (AR)** | m[0-3]_arsize | 3 | Output | Value, Range | TC_BASIC_002-004 |
| **Read Address (AR)** | m[0-3]_arburst | 2 | Output | Value, Enum | TC_BASIC_004, TC_PROT_003 |
| **Read Address (AR)** | m[0-3]_arlock | 1 | Output | Value, Toggle | TC_PROT_001 |
| **Read Address (AR)** | m[0-3]_arcache | 4 | Output | Value, Range | TC_PROT_001 |
| **Read Address (AR)** | m[0-3]_arprot | 3 | Output | Value, Range | TC_PROT_001 |
| **Read Address (AR)** | m[0-3]_arqos | 4 | Output | Value, Range | TC_PROT_001 |
| **Read Address (AR)** | m[0-3]_arregion | 4 | Output | Value, Range | TC_PROT_001 |
| **Read Address (AR)** | m[0-3]_arvalid | 1 | Output | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Read Address (AR)** | m[0-3]_arready | 1 | Input | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Read Data (R)** | m[0-3]_rid | 4 | Input | Value, Toggle | TC_BASIC_002, TC_ERR_001-002 |
| **Read Data (R)** | m[0-3]_rdata | 32 | Input | Value, Toggle | TC_BASIC_002, TC_BASIC_004 |
| **Read Data (R)** | m[0-3]_rresp | 2 | Input | Value, Enum | TC_ERR_001-002, TC_PROT_004 |
| **Read Data (R)** | m[0-3]_rlast | 1 | Input | Toggle, Timing | TC_BASIC_004, TC_PROT_003 |
| **Read Data (R)** | m[0-3]_rvalid | 1 | Input | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Read Data (R)** | m[0-3]_rready | 1 | Output | Toggle, Timing | TC_PROT_001, TC_ERR_003 |

### 4.2 Slave Interface Signals

| Signal Group | Signal Name | Width | Direction | Coverage Type | Test Cases |
|--------------|-------------|-------|-----------|---------------|------------|
| **Write Address (AW)** | s[0-6]_awid | 4 | Input | Value, Toggle | TC_BASIC_001, TC_ACCESS_001-004 |
| **Write Address (AW)** | s[0-6]_awaddr | 32 | Input | Value, Range | TC_ADDR_001-007, TC_ACCESS_001-004 |
| **Write Address (AW)** | s[0-6]_awlen | 4 | Input | Value, Range | TC_BASIC_003, TC_PROT_003 |
| **Write Address (AW)** | s[0-6]_awsize | 3 | Input | Value, Range | TC_BASIC_001-004 |
| **Write Address (AW)** | s[0-6]_awburst | 2 | Input | Value, Enum | TC_BASIC_003-004, TC_PROT_003 |
| **Write Address (AW)** | s[0-6]_awlock | 1 | Input | Value, Toggle | TC_PROT_001 |
| **Write Address (AW)** | s[0-6]_awcache | 4 | Input | Value, Range | TC_PROT_001 |
| **Write Address (AW)** | s[0-6]_awprot | 3 | Input | Value, Range | TC_PROT_001 |
| **Write Address (AW)** | s[0-6]_awqos | 4 | Input | Value, Range | TC_PROT_001 |
| **Write Address (AW)** | s[0-6]_awregion | 4 | Input | Value, Range | TC_PROT_001 |
| **Write Address (AW)** | s[0-6]_awvalid | 1 | Input | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Write Address (AW)** | s[0-6]_awready | 1 | Output | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Write Data (W)** | s[0-6]_wdata | 32 | Input | Value, Toggle | TC_BASIC_001, TC_BASIC_003 |
| **Write Data (W)** | s[0-6]_wstrb | 4 | Input | Value, Toggle | TC_BASIC_001, TC_BASIC_003 |
| **Write Data (W)** | s[0-6]_wlast | 1 | Input | Toggle, Timing | TC_BASIC_003, TC_PROT_003 |
| **Write Data (W)** | s[0-6]_wvalid | 1 | Input | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Write Data (W)** | s[0-6]_wready | 1 | Output | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Write Response (B)** | s[0-6]_bid | 4 | Output | Value, Toggle | TC_BASIC_001, TC_ERR_001-002 |
| **Write Response (B)** | s[0-6]_bresp | 2 | Output | Value, Enum | TC_ERR_001-002, TC_PROT_004 |
| **Write Response (B)** | s[0-6]_bvalid | 1 | Output | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Write Response (B)** | s[0-6]_bready | 1 | Input | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Read Address (AR)** | s[0-6]_arid | 4 | Input | Value, Toggle | TC_BASIC_002, TC_ACCESS_001-004 |
| **Read Address (AR)** | s[0-6]_araddr | 32 | Input | Value, Range | TC_ADDR_001-007, TC_ACCESS_001-004 |
| **Read Address (AR)** | s[0-6]_arlen | 4 | Input | Value, Range | TC_BASIC_004, TC_PROT_003 |
| **Read Address (AR)** | s[0-6]_arsize | 3 | Input | Value, Range | TC_BASIC_002-004 |
| **Read Address (AR)** | s[0-6]_arburst | 2 | Input | Value, Enum | TC_BASIC_004, TC_PROT_003 |
| **Read Address (AR)** | s[0-6]_arlock | 1 | Input | Value, Toggle | TC_PROT_001 |
| **Read Address (AR)** | s[0-6]_arcache | 4 | Input | Value, Range | TC_PROT_001 |
| **Read Address (AR)** | s[0-6]_arprot | 3 | Input | Value, Range | TC_PROT_001 |
| **Read Address (AR)** | s[0-6]_arqos | 4 | Input | Value, Range | TC_PROT_001 |
| **Read Address (AR)** | s[0-6]_arregion | 4 | Input | Value, Range | TC_PROT_001 |
| **Read Address (AR)** | s[0-6]_arvalid | 1 | Input | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Read Address (AR)** | s[0-6]_arready | 1 | Output | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Read Data (R)** | s[0-6]_rid | 4 | Output | Value, Toggle | TC_BASIC_002, TC_ERR_001-002 |
| **Read Data (R)** | s[0-6]_rdata | 32 | Output | Value, Toggle | TC_BASIC_002, TC_BASIC_004 |
| **Read Data (R)** | s[0-6]_rresp | 2 | Output | Value, Enum | TC_ERR_001-002, TC_PROT_004 |
| **Read Data (R)** | s[0-6]_rlast | 1 | Output | Toggle, Timing | TC_BASIC_004, TC_PROT_003 |
| **Read Data (R)** | s[0-6]_rvalid | 1 | Output | Toggle, Timing | TC_PROT_001, TC_ERR_003 |
| **Read Data (R)** | s[0-6]_rready | 1 | Input | Toggle, Timing | TC_PROT_001, TC_ERR_003 |

### 4.3 Global Signals

| Signal Name | Width | Direction | Coverage Type | Test Cases |
|-------------|-------|-----------|---------------|------------|
| **clk** | 1 | Input | Toggle, Timing | All test cases |
| **rstn** | 1 | Input | Toggle, Timing | TC_RST_001-003 |

---

## 5. Coverage Goals

### 5.1 Functional Coverage
- **Master Access Control**: 100% coverage of allowed/denied master-slave combinations
- **Address Decoding**: 100% coverage of all slave address ranges
- **Transaction Types**: 100% coverage of all AXI transaction types and burst modes
- **Response Codes**: 100% coverage of all AXI response codes
- **ID Values**: 100% coverage of transaction ID combinations

### 5.2 Code Coverage
- **Statement Coverage**: >95%
- **Branch Coverage**: >90%
- **Expression Coverage**: >90%
- **Toggle Coverage**: >95%

### 5.3 Assertion Coverage
- **Protocol Compliance**: 100% assertion pass rate
- **Access Control**: 100% assertion pass rate
- **Address Validation**: 100% assertion pass rate

---

## 6. Test Environment Components

### 6.1 UVM Components Required
- **Test**: Main test class orchestrating the verification
- **Environment**: Top-level UVM environment
- **Scoreboard**: Checking transaction correctness and access control
- **Coverage Collector**: Functional and code coverage collection
- **Reference Model**: Expected behavior model for checking
- **Sequences**: Transaction generation sequences
- **Agents**: Master and slave agents (active/passive)

### 6.2 Verification IP (VIP)
- **AXI Protocol Checker**: Built-in protocol compliance checking
- **Coverage Monitors**: Automatic coverage collection
- **Assertion Libraries**: Pre-built AXI protocol assertions

---

## 7. Test Execution Strategy

### 7.1 Test Phases
1. **Basic Functionality**: Core AXI protocol verification
2. **Access Control**: Master-slave access permission verification
3. **Address Decoding**: Routing and address mapping verification
4. **Concurrent Access**: Multi-master simultaneous access verification
5. **Error Scenarios**: Error handling and recovery verification
6. **Performance**: Throughput and latency verification
7. **Reset/Initialization**: System initialization verification

### 7.2 Regression Strategy
- **Daily Regression**: Basic functionality and access control tests
- **Weekly Regression**: Full test suite execution
- **Release Regression**: Complete verification before tapeout

---

## 8. Success Criteria

### 8.1 Functional Verification
- All test cases pass with 100% success rate
- No protocol violations detected
- All access control rules verified
- All address decoding scenarios verified

### 8.2 Coverage Achievement
- Functional coverage: >95%
- Code coverage: >90%
- Assertion coverage: 100%

### 8.3 Quality Metrics
- Zero critical bugs
- Zero protocol compliance issues
- Zero access control violations
- Zero address decoding errors

---

## 9. Risk Assessment

### 9.1 High Risk Areas
- **Concurrent Access**: Complex arbitration and deadlock scenarios
- **Access Control**: Security-critical functionality
- **Address Decoding**: Routing correctness critical for system operation

### 9.2 Mitigation Strategies
- **Extensive Testing**: Comprehensive test coverage for high-risk areas
- **Formal Verification**: Use of formal methods for critical paths
- **Code Reviews**: Multiple review cycles for critical components
- **Assertion-Based Verification**: Comprehensive assertion coverage

---

## 10. Timeline and Resources

### 10.1 Development Phase
- **Week 1-2**: Basic functionality test development
- **Week 3-4**: Access control and address decoding tests
- **Week 5-6**: Concurrent access and error scenario tests
- **Week 7-8**: Performance and reset tests

### 10.2 Execution Phase
- **Week 9-10**: Initial test execution and bug fixing
- **Week 11-12**: Coverage closure and final verification
- **Week 13**: Documentation and sign-off

### 10.3 Resource Requirements
- **Verification Engineer**: 1 FTE for 13 weeks
- **Simulation Resources**: High-performance simulation environment
- **Tools**: UVM framework, coverage tools, assertion libraries

---

*This DV plan provides a comprehensive framework for verifying the AXI NOC design. Regular updates and reviews should be conducted throughout the verification process to ensure alignment with design changes and verification goals.*

# LispCircuit (LCIR) 系统需求规格说明书（SRS）

本项目旨在对标并超越 `pyCircuit`，构建一套**“面向 AI Agent 与人类架构师、一套 Lisp 语言贯穿算法设计、元编程展开、周期精确 ESL 仿真、形式化验证与可综合 SystemVerilog 生成”**的轻量级全栈硬件编译器。

---

## 一、 系统定位与核心架构全景

### 1.1 核心设计目标
1. **同源全周期（Single-Source Full-Lifecycle）**：消除算法 C/Python 模型、ESL 周期模型与 Verilog RTL 之间的重写鸿沟。
2. **宏展开与静态捕获解耦（Two-Stage Elaboration）**：克服 `pyCircuit` 因静态捕获 Python AST 导致参数化生成受限的短板——**阶段一运行图灵完备的 Lisp 宏进行拓扑展开；阶段二锁定为纯静态 Core LCIR 进行强类型检查与编译**。
3. **两阶段原子步执行语义（Work $\rightarrow$ Check $\rightarrow$ Xfer）**：所有规则在同一时钟周期内只读已提交旧状态（Committed State），全系统断言通过后原子性更新新状态，确保 ESL 仿真与综合后 RTL 100% 周期级等价（Cycle-Accurate Equivalence）。
4. **AI-Native 诊断与手术刀能力**：零 Lexer/Parser 开销，所有编译报错精确到 S-表达式节点路径，支持 AI Agent 对 AST 进行局部替换与自动重定时（Retiming）。

### 1.2 编译器数据流管线（Pipeline Architecture）

```text
[高阶 LispCircuit 源码 (.lcir)]
       │
       ▼  Pass 0: S-Exp Reader & Macro Expander (gen-for, defmacro, symcat)
[展开后的 Core LCIR AST]
       │
       ├─► Pass 1: Type & Bit-Width Checker (静态位宽推导、符号性与未定义检查)
       ├─► Pass 2: Algo Inliner (将 defalgo 纯函数内联展开为纯组合数据流 DAG)
       └─► Pass 3: Rule Scheduler & Conflict Analyzer (多 @rule 写冲突检测与使能合成)
       │
       ▼
[已验证的 Normalized Hardware IR (NHIR)]
       │
       ├─────────────────┬─────────────────┬─────────────────┐
       ▼                 ▼                 ▼                 ▼
  [Target 1: ESL]   [Target 2: C++]   [Target 3: RTL]   [Target 4: Formal]
  内存周期级解释器    GFSIM C++ 源码    SystemVerilog     SMT-LIB v2 (Z3)
  (含 VCD 波形导出)   (高速架构仿真)    (IEEE 1800-2017)  (等价性与死锁证明)
```

---

## 二、 语言层功能需求（Language Specification Requirements）

语言层分为 **四个正交子层**，开发时需按此边界定义 AST 节点规范：

### 2.1 类型系统需求（Type System — `F-TYPE`）

| 需求 ID | 类型构造符 | 语法规范 | 语义与后端映射要求 |
| :--- | :--- | :--- | :--- |
| **F-TYPE-01** | 基础标量 | `(uint W)` / `(sint W)` | $W \ge 1$。算术运算严格校验有符号/无符号一致性，禁止隐式转换。 |
| **F-TYPE-02** | 枚举类型 | `(defenum Name (S0 S1 ...))` | 自动计算最小位宽 $\lceil\log_2 N\rceil$，SV 后端映射为 `typedef enum logic [W-1:0]`。 |
| **F-TYPE-03** | 复合结构体 | `(bundle (f1 T1) (f2 T2))` | 支持嵌套，SV 后端映射为 `typedef struct packed`。通过 `(field x f1)` 访问。 |
| **F-TYPE-04** | 定长向量 | `(vec N T)` | 支持多维数组。通过 `(idx v i)` 访问，静态检查越界。 |
| **F-TYPE-05** | 握手流接口 | `(stream T)` | 一等公民流类型。自动展开为 `valid` (1b)、`ready` (反向 1b)、`bits` ($T$)。 |

### 2.2 算法与元编程层需求（Algorithm & Metaprogramming — `F-META`）
* **F-META-01 纯函数算法 (`defalgo`)**：
  * 支持局部变量绑定 `(let ((v expr) ...) body)`、条件分支 `(mux c t f)`、模式匹配 `(match sel ... (:default d))`。
  * **无状态约束**：`defalgo` 内部严禁访问或修改模块的 `:state` 或 `:tables`，确保其既能在软件仿真中直接调用，又能 100% 展开为纯组合逻辑网表。
* **F-META-02 编译期结构生成宏 (`defmacro`, `gen-for`, `cat-for`, `reduce-tree`)**：
  * 支持在模块展开期执行算术计算（`+`, `-`, `*`, `log2`）、列表生成与符号拼接 `(symcat 'prefix_ i)`。
  * 支持 `(infix ...)` 算术中缀糖（如 `(infix (a + b) & ~mask)`），在 Reader 阶段自动转为前缀 AST，降低人类与 AI 编写复杂位运算的心智负担。

### 2.3 核心硬件与原子规则层需求（Hardware & Atomic Rules — `F-CORE`）
这是对标 `pyCircuit` / Bluespec 的核心执行引擎：
* **F-CORE-01 状态存储原语 (`:state` & `:tables`)**：
  * `:state`：声明模块级寄存器 `(reg_name :type T :init val)`。
  * `:tables`：声明片上存储器/SRAM `(tbl_name :depth D :type T :ports (:r 1 :w 1) :latency (0|1))`。
    * `latency = 0`：映射为寄存器堆或分布式 LUTRAM（异步读/同拍读）。
    * `latency = 1`：映射为标准同步 SRAM / BRAM（读请求在 `Work` 阶段发出，数据在下一拍可用）。
* **F-CORE-02 原子转换规则 (`defrule`)**：
  * 语法：`(defrule name :priority P :guard expr_1b :body (stmt ...))`。
  * 语义：当 `:guard` 为真时规则激活（Fire）。`:body` 内允许使用 `(set! reg expr)`、`(table-write tbl addr data)`、`(let ...)`。
  * **双端口隔离铁律**：在同一个 `:body` 内，读取任何 `reg` 得到的值**永远是当前周期开始前的旧值（Committed State）**，哪怕前一行刚刚执行了 `(set! reg new_val)`。
* **F-CORE-03 工业级微架构原语内置库（Built-in Primitives）**：
  * 内置 `stream-slice`（`:forward` / `:backward` / `:skid`）、`sync-fifo`、`async-fifo`、`elastic-pipeline`，无需用户手写底层状态机。

### 2.4 闭环验证系统层需求（Closed Verification System — `F-SYS`）
* **F-SYS-01 自包含系统容器 (`defsystem`)**：
  * 实例化一个或多个待测模块（`:instances`），定义测试激励状态机，无需外部 Verilog Testbench 即可独立运转。
* **F-SYS-02 驱动与观测原语**：
  * `(drive inst.port expr)`：驱动子模块输入端口。
  * `(log level "key1" expr1 ...)`：格式化周期级日志输出（仅在 `Xfer` 提交阶段打印）。
  * `(check cond_1b "error_msg")`：周期级断言。若在某拍为假，立即中止当前原子步提交并抛出异常上下文。

---

## 三、 编译器中端 Pass 与静态检查需求（Middle-End Passes）

为了保证生成代码的绝对可靠以及对 AI Agent 的友好反馈，中端必须实现以下 3 个核心 Pass：

### 3.1 Pass 1：强类型与显式位宽检查器（Type & Width Checker）
* **禁止隐式截断/扩展**：`(+ a b)` 要求 `a` 和 `b` 类型与位宽完全一致，返回相同位宽；`(+w a b)` 返回 $\max(W_a, W_b) + 1$。
* **完备性检查**：检查所有 `match` 语句是否包含 `:default` 分支。
* **结构化报错协议（AI Diagnostic JSON）**：当检查失败时，不抛出编程语言原生堆栈，而是输出结构化诊断：
  ```json
  {
    "error_code": "ERR_WIDTH_MISMATCH",
    "location": "module:StreamingMAC -> rule:compute_mac -> stmt:(set! acc_reg ...)",
    "expected_type": "(sint 20)",
    "actual_type": "(sint 16)",
    "fix_suggestion": "Wrap expression with (sext <expr> 20)"
  }
  ```

### 3.2 Pass 2：多规则写冲突分析与调度器（Rule Conflict & Scheduler Pass）
当一个模块内包含多个 `defrule`（如 `rule_push` 和 `rule_pop` 同时修改 `fifo_cnt`）时，编译器必须处理双写冲突（Double-Write Hazard）：
1. **无交集规则**：若 `rule_A` 修改集合 $W_A$，`rule_B` 修改集合 $W_B$，且 $W_A \cap W_B = \emptyset$，则两规则可完全并行执行。
2. **互斥守卫识别**：若 $W_A \cap W_B \neq \emptyset$，但编译器能证明 `guard_A & guard_B == 0`（或用户声明 `:conflict-free`），则生成并行多路选择器。
3. **优先级调度（Priority Resolution）**：若两规则可能同时激活且写同一寄存器 $R$：
   * 若未指定 `:priority`，编译器报错提示存在未决写冲突（Write-Write Conflict）。
   * 若指定了优先级（如 $P_A < P_B$，数字越小优先级越高），编译器自动为寄存器 $R$ 合成带优先级的写使能与数据选择器：
     * $\text{WE}_R = \text{guard}_A \lor \text{guard}_B$
     * $\text{Next}_R = \text{guard}_A \ ? \ \text{val}_A : \text{val}_B$

### 3.3 Pass 3：组合逻辑环路检测（Combinational Loop Detector）
* 对模块内所有 `comb` 节点、内联后的 `defalgo` 以及 `stream` 的 `valid/ready` 依赖构建有向图，运行 Tarjan 强连通分量算法，若发现环路立即报错并打印环路节点链。

---

## 四、 多后端代码生成与仿真需求（Backends Specification）

### 4.1 Target 1：ESL 周期精确仿真引擎（In-Memory & C++ Backend）
* **执行循环（The Epoch Loop）**：
  1. **Eval Outputs**：基于当前 `Committed State` 计算所有模块输出与组合线网。
  2. **Work Phase**：遍历所有激活的 `defrule`，计算右值并存入临时 `Candidate State Buffer`，收集 `log` 与 `check` 队列。
  3. **Check Phase**：校验所有 `check` 队列。一旦失败，转储当前周期所有寄存器快照并退出。
  4. **Xfer Phase**：将 `Candidate State Buffer` 原子性覆盖到 `Committed State`，推进 `latency=1` 的 SRAM 读管道，输出 `log`。
* **波形导出需求（Waveform Dumping）**：支持 `--dump-vcd out.vcd` 或 `--dump-fst`，在 `Xfer` 阶段自动记录所有 `:ports` 和 `:state` 的信号变化，可直接用 GTKWave / Surfer 查看。

### 4.2 Target 2：可综合 SystemVerilog 后端（RTL Backend）
* **可读性要求（Human-Readable Codegen）**：保留 Lisp 中的变量名与层级前缀，严禁生成类似 Chisel 的满屏无意义 `_T_123` 临时变量。
* **复位与时钟门控策略**：
  * 控制寄存器（如 valid、状态机、计数器）生成同步复位 `if (rst) reg <= INIT;`。
  * 纯数据通路寄存器（如流水线 payload、SRAM 缓冲）支持配置 `:reset-less true`，仅生成 `if (we) reg <= next;`，减少 ASIC/FPGA 复位扇出并赋能自动时钟门控（Clock Gating）。
* **SystemVerilog Testbench 自动生成**：针对 `defsystem`，自动生成一个顶层 `tb_<sys_name>.sv` 文件，将 `drive`、`log`（转为 `$display`）和 `check`（转为 `assert`）完整翻译为 SV 仿真激励，用于直接调用 Verilator 进行 RTL vs ESL 一致性比对。

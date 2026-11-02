# LispCircuit (LCIR) 系统需求规格说明书（SRS）v2

本项目对标 `pyCircuit` / Bluespec，构建一套**面向 AI Agent 与人类架构师的轻量级全栈硬件编译器**：用同一份 Lisp 源码完成算法描述、元编程展开、周期精确 ESL 仿真、C++ 高速仿真、形式化检查与可综合 SystemVerilog 生成。

状态标记：✅ 已实现并有测试覆盖　🟡 部分实现（注明限制）　⏳ 规划中

---

## 一、系统定位与核心设计目标

### 1.1 核心设计目标与验收标准

| ID | 目标 | 验收标准（可执行） | 状态 |
| :--- | :--- | :--- | :--- |
| **G1** | **同源全周期**：算法模型、ESL 周期模型、RTL 不再分别重写 | 同一 `.lcir` 文件经 `sim` / `cpp` / `sv` / `smt` 四个命令得到四个目标，无需人工改写 | ✅ |
| **G2** | **两阶段展开（Two-Stage Elaboration）**：阶段一运行图灵完备的宏做拓扑展开；阶段二只处理纯静态 Core LCIR | `lcir expand` 的输出不含任何宏、`gen-for`、`if`；类型检查只针对展开结果 | ✅ |
| **G3** | **原子步执行语义（Work → Check → Xfer）**：规则只读已提交旧状态，断言全部通过后原子提交；所有目标周期级等价 | `make equiv`：对全部示例，ESL、Verilator（SV）、g++（C++）三方日志逐行相同 | ✅ |
| **G4** | **AI-Native 诊断与手术刀能力**：报错可被机器定位，AST 可被局部替换并立即复检 | 诊断 JSON 带 `node_path`；`lcir query` / `lcir patch` 可按路径读/改节点，改后自动复检，失败不落盘（`tests/patch-smoke.rkt`） | ✅ |

> 修订说明：v1 中“零 Lexer/Parser 开销”的表述不准确——Reader 仍需解析 S-表达式，并对 `(infix ...)` 做重写。v2 改为：**无需自定义词法/语法分析器，源码即数据（S-表达式），AST 节点可被稳定路径寻址**。

### 1.2 编译器数据流管线

```text
[LCIR 源码 (.lcir)]
     │  Pass 0  Reader + Macro Expander   (infix 重写, defmacro, gen-for, cat-for, reduce-tree, symcat, include)
     ▼
[Core LCIR AST]
     │  Pass 1  Type & Width Checker       (位宽/符号性/未定义/match 完备性)
     │  Pass 2  Algo Inliner               (defalgo → 纯组合 DAG)
     │  Pass 3  Rule Scheduler             (写冲突分析，合成 we / next)
     │  Pass 4  Comb-Loop Detector         (Tarjan SCC)
     ▼
[Normalized Hardware IR (NHIR)] ──flatten──► [扁平网表] ──lower-bits──► [打包位向量 IR]
     │                                          │                          │
     ▼                                          ▼                          ▼
  T3: SystemVerilog + Testbench          T1: ESL 解释器 (+VCD)      T2: C++17 仿真器
  (IEEE 1800-2017, Verilator)                                       T4: SMT-LIB v2 (QF_ABV)
```

Pass 与 Target 编号在全文统一使用上图（v1 中 §1.2 与 §3/§4 的编号互相矛盾，已修正）。

### 1.3 实现约束

* 宿主语言：Racket ≥ 8（已在 9.3 验证）。
* 可选外部工具：Verilator（SV 对拍）、g++/clang++（C++ 目标）、z3（SMT 求解）、`vcd2fst`（FST 波形）。缺失时相关命令报 `ERR_BACKEND` 并给出建议，相关测试自动跳过；不允许出现宿主语言原生堆栈。

---

## 二、源文件格式（`F-SRC`）

| 需求 ID | 要求 | 状态 |
| :--- | :--- | :--- |
| **F-SRC-01** | 源文件扩展名为 `.lcir`，内容为 S-表达式序列，`;` 行注释。 | ✅ |
| **F-SRC-02** | **Emacs Lisp Reader 兼容子集**：所有源文件（含 `lib/prims.lcir` 与 `defmacro` 体）必须能被 Emacs `read` 逐个读出。因此：布尔值写 `t` / `nil`（`#t`/`#f`/`true`/`false` 仅为兼容保留）；禁止 `[ ]`、`#\c` 字符字面量、`?c`、`#:kw`。`make emacs` 自动校验。 | ✅ |
| **F-SRC-03** | 提供 `editors/lcir-mode.el`：派生自 `lisp-data-mode`，自动关联 `.lcir`；高亮定义形式与关键字；缩进规则；`C-c C-c` 运行 `lcir check` 并通过 compilation-mode 跳转诊断位置。 | ✅ |
| **F-SRC-04** | `(include "path.lcir")` 以当前文件目录为基准展开。 | ✅ |

**为什么不直接使用 `.el` 扩展名**：`.el` 会被 Emacs、byte-compile、flycheck/flymake、package 管理器与 GitHub Linguist 当作可执行的 Emacs Lisp，从而产生大量误报（`defmodule` 未定义等），且 `defmacro`/`let` 等同名形式在两种语言中语义不同。采用“`.lcir` 扩展名 + Emacs 可读语法子集 + 专用 major mode”，可以获得 `.el` 的全部编辑器收益（paredit、`forward-sexp`、`read`、Agent 在 Emacs 内直接操纵 AST），同时不引入误报。

---

## 三、语言层功能需求

语言分为四个正交子层。完整语法见 [lang-ref.md](lang-ref.md)。

### 3.1 类型系统（`F-TYPE`）

| 需求 ID | 类型构造符 | 语法 | 语义与后端映射 | 状态 |
| :--- | :--- | :--- | :--- | :--- |
| **F-TYPE-01** | 基础标量 | `(uint W)` / `(sint W)` | $W \ge 1$。无隐式扩展/截断/符号转换。 | ✅ |
| **F-TYPE-02** | 枚举 | `(defenum Name (S0 S1 ...))` | 位宽 $\max(1, \lceil\log_2 N\rceil)$，编码从 0 递增；SV 映射 `typedef enum logic [W-1:0]`；日志打印变体名。 | ✅ |
| **F-TYPE-03** | 结构体 | `(bundle (f1 T1) (f2 T2))` | 可嵌套，第一个字段位于高位；SV 映射 `typedef struct packed`；`(field x f1)` 访问、`(pack (f e) ...)` 构造。 | ✅ |
| **F-TYPE-04** | 定长向量 | `(vec N T)` | 元素 0 位于高位；`(idx v i)` 访问，常量下标编译期越界检查（`ERR_INDEX_OOB`）；`(vlit e ...)` 构造。 | ✅ |
| **F-TYPE-05** | 握手流 | `(stream T)` | 展开为 `valid`(1b)、`ready`(反向 1b)、`bits`(T)；`(valid x)`/`(ready x)`/`(bits x)` 访问。 | ✅ |
| **F-TYPE-06** | 字面量宽度 | `(u W v)` / `(s W v)` / 裸整数 | 裸整数仅在上下文能唯一确定宽度且数值放得下时采用该类型，否则 `ERR_AMBIGUOUS_WIDTH`。 | ✅ |

### 3.2 算法与元编程层（`F-META`）

* **F-META-01 纯函数算法 `defalgo`** ✅：支持 `let`、`mux`、`match`（必须含 `:default`）。体内禁止访问 `:state` / `:tables`（`ERR_ALGO_STATEFUL`），保证可 100% 内联为组合逻辑。
* **F-META-02 编译期结构生成** ✅：`defmacro`（体为受限 Racket，参数为未求值 S-表达式）、`gen-for`、`cat-for`、`reduce-tree`（平衡树）、`symcat`、`log2`、`clog2`；参数替换后对全整数的 `+ - *` 与比较做常量折叠；条件为常量的 `if` 只保留一边，否则降为 `mux`。
* **F-META-03 中缀糖** ✅：`(infix (a + b) & ~mask)` 在 Reader 阶段重写为前缀 AST；`&&`/`||` → `and`/`or`。

### 3.3 核心硬件与原子规则层（`F-CORE`）

* **F-CORE-01 状态与存储** ✅
  * `:state`：`(r :type T :init v [:reset-less t] [:clock clk])`。
  * `:tables`：`(m :depth D :type T :ports (:r 1 :w 1) :latency 0|1)`，每表 1 读 1 写口。
    * `latency 0`：`(table-read m a)` 为组合读，读到本拍提交前的值。
    * `latency 1`：`(table-read m a)` 作为语句发出读请求，下一拍 `(table-rdata m)` 取数。
    * 同拍同地址读写：**先读后写**。
* **F-CORE-02 原子规则 `defrule`** ✅：`(defrule name [:priority P] [:conflict-free t] :guard e1 :body (stmt ...))`。语句：`set!`、`table-write`、`table-read`、`let`、`log`、`check`、`finish`、`drive`（仅 `defsystem`）。
  * **旧值铁律**：同一拍内任何读取都得到本拍开始时的已提交值，即使前面刚 `set!` 过。
  * 一条规则不得对同一寄存器/表写两次。
* **F-CORE-03 时钟与复位** ✅：默认时钟 `clk`，可用 `:clocks` 声明多时钟；复位 `rst` 隐含且同步。仿真开始前有一个静默复位周期：非 reset-less 寄存器回到 `:init`，reset-less 寄存器照常更新。ESL/C++/SMT 中所有时钟同相步进；与 RTL 对拍时把多个时钟接到同一时钟上。
* **F-CORE-04 内置微架构原语** ✅：`lib/prims.lcir` 自动加载：`stream-slice-forward/backward/skid`、`(stream-slice :forward Name W)` 宏、`sync-fifo`、`async-fifo`（格雷码指针 + 两级同步）、`elastic-pipeline`。

### 3.4 闭环验证系统层（`F-SYS`）

* **F-SYS-01 `defsystem`** ✅：实例化被测模块（`:instances`），用规则编写激励状态机，可独立运行，无需外部 Testbench。
* **F-SYS-02 驱动与观测** ✅
  * `(drive inst.port expr)`：驱动子模块输入，**下一拍**对子模块可见。
  * `(log level "k1" e1 ...)`：在提交阶段输出 `[cyc N] level k1=v1 ...`。
  * `(check cond "msg")`：为假时丢弃本拍提交，报 `ERR_CHECK`，附带全部寄存器快照（JSON），进程以非 0 退出。
  * `(finish)`：本拍提交后结束仿真。

---

## 四、中端 Pass 与静态检查（`F-PASS`）

| 需求 ID | Pass | 要求 | 状态 |
| :--- | :--- | :--- | :--- |
| **F-PASS-0** | Reader + Expander | 见 §2、§3.2；读错误转为 `ERR_PARSE` 诊断（含行列），不泄漏堆栈。 | ✅ |
| **F-PASS-1** | Type & Width | `+ - * & \| ^ ~` 两侧类型完全一致、同宽回绕；`+w`/`-w` 结果宽 $\max+1$，`*w` 为两宽之和；比较得 `(uint 1)`；`and/or/not` 只收 `(uint 1)`；`match` 必须含 `:default`；类型错误给出 `sext`/`zext`/`trunc` 修复建议。 | ✅ |
| **F-PASS-2** | Algo Inliner | `defalgo` 调用全部内联，NHIR 中不残留调用。 | ✅ |
| **F-PASS-3** | Rule Scheduler | 多规则写同一资源时依次判定：① 写集不相交 → 并行；② 守卫可证明互斥（结构/枚举穷举，≤20 位自由变量）或双方声明 `:conflict-free` → 并行 + 多路选择；③ 全部带互不相同的 `:priority`（数字小者优先）→ 合成 $\text{WE}=\lor\,\text{guard}_i$、$\text{Next}=$ 按优先级嵌套 `mux`；④ 否则 `ERR_WRITE_CONFLICT`。`:conflict-free` 的声明在 ESL/C++ 中运行时校验，在 T4 中形式化校验。 | ✅ |
| **F-PASS-4** | Comb-Loop | 对所有组合线网、内联后的算法、stream `valid/ready` 依赖建图，Tarjan SCC 发现环即报 `ERR_COMB_LOOP`，`loop` 字段列出环上信号。 | ✅ |

---

## 五、AI Agent 接口（`F-AI`）

| 需求 ID | 要求 | 状态 |
| :--- | :--- | :--- |
| **F-AI-01** | **结构化诊断**：`--diag json` 输出数组，每项字段：`error_code`、`location`（人读路径，如 `module:StreamingMAC -> rule:compute_mac -> stmt:(set! acc_reg ...)`）、`node_path`（机器路径，见 F-AI-02）、`expected_type`、`actual_type`、`message`、`fix_suggestion`、`loop`、`file`、`line`（1 起）、`col`（1 起）。文本模式输出同样信息，`at: file:line:col` 可被编辑器跳转。 | ✅ |
| **F-AI-02** | **节点路径**：以 `/` 分隔，从顶层形式开始解析，作用于展开前的源码。段：`module:X` `system:X` `enum:X` `macro:X`（顶层）、`rule:X` `algo:X`（模块内）、`state:X` `table:X` `inst:X` `port:X` `wire:X`（对应列表中的条目）、`:kw`（关键字后的值）、`N`（第 N 个子元素，0 起）。例：`module:Counter/rule:inc/:body/0/2`。 | ✅ |
| **F-AI-03** | **查询**：`lcir query FILE PATH`、`--at LINE:COL`（位置→路径）、`--list`（列出全部具名节点）。 | ✅ |
| **F-AI-04** | **手术刀替换**：`lcir patch FILE PATH --with SEXP [-o OUT \| --in-place] [--dry-run]`。按源码区间做文本替换（保留其余注释与排版），替换后立即跑完整编译流程；**只有复检通过才写盘**，否则返回诊断（`node_path` 指向新文本中的节点）且原文件不变。 | ✅ |
| **F-AI-05** | **重定时（Retiming）**：当前由 Agent 通过 F-AI-03/04 手动完成（插入寄存器 + 调整规则）；编译器内自动重定时 Pass 尚未实现。 | ⏳ |

---

## 六、多后端代码生成与仿真（`F-BE`）

### 6.1 T1：ESL 周期精确解释器 ✅
* 每个周期：**Eval**（基于已提交状态按拓扑序计算所有线网）→ **Work/Check**（校验 `check` 与 `:conflict-free`/互斥声明；失败则转储寄存器快照并退出）→ **Log** → **Xfer**（原子提交寄存器；推进 latency-1 读数据；执行表写）。
* 日志逐周期流式输出：断言失败前各拍的日志不会丢失。
* `--dump-vcd F` 记录所有端口与状态；`--dump-fst F` 需要 `vcd2fst`。

### 6.2 T2：C++ 周期仿真器 ✅（`lcir cpp FILE -o DIR [--cycles N] [--top S]`）
* 生成单文件 C++17（无第三方依赖），语义与 ESL 完全一致（同一套打包位向量降级 `lower-bits`），日志格式相同，断言失败时输出 `ERR_CHECK` 与快照并以 1 退出。
* 限制 🟡：任一值宽度 > 64 位时报 `ERR_BACKEND`（后续可改用多字表示）；运行期越界下标/地址返回 0，而 ESL 报错。

### 6.3 T3：可综合 SystemVerilog ✅（`lcir sv FILE -o DIR`）
* **可读性**：保留源码中的变量名与层级前缀，不生成无意义临时名。
* **复位策略**：控制寄存器生成 `if (rst) r <= INIT;`；`:reset-less t` 的数据寄存器只生成 `if (we) r <= next;`，便于减少复位扇出与时钟门控。
* **Testbench**：每个 `defsystem` 生成 `tb_<Sys>.sv`，`drive` → 端口激励，`log` → `$display`，`check` → 断言；可直接 `verilator --binary` 运行。

### 6.4 T4：形式化（SMT-LIB v2）🟡（`lcir smt FILE [-o OUT.smt2] [--depth K] [--top NAME] [--run]`）
* **BMC**：从复位后状态展开 K 拍；`sat` ⇔ K 拍内某个 `check` 会失败，或声明互斥/`:conflict-free` 的写者同时激活（且此前未 `finish`）。`--top` 指定模块时，其输入端口为每拍自由变量，结论对所有输入序列成立。
* **写者互斥性**：对每个多写者寄存器，查询任意两条守卫在自由状态下能否同真；`unsat` 即组合意义上互斥（可能比可达状态下的结论更保守）。
* `--run` 调用 z3 并以 `pass`/`fail` 汇总；`fail` 时输出**反例轨迹**（每拍自由输入与顶层寄存器取值，标出失败拍），供人或 Agent 直接定位；未安装 z3 时报 `ERR_BACKEND`。
* 无 z3 时，`tests/smt-smoke.rkt` 用内置的 SMT 子集求值器对系统顶层（全具体值）逐拍对比 ESL。
* 规划 ⏳：死锁/活性证明（stream `valid` 持续而 `ready` 永不到来的有界检测）、k-induction 无界证明、SV 与 NHIR 的组合等价性。

---

## 七、命令行接口（`F-CLI`）

```
racket lcir/cli.rkt check  FILE [--diag json|text]
racket lcir/cli.rkt expand FILE
racket lcir/cli.rkt sim    FILE --cycles N [--top S] [--dump-vcd F] [--dump-fst F]
racket lcir/cli.rkt sv     FILE -o DIR [--top S] [--cycles N]
racket lcir/cli.rkt cpp    FILE -o DIR [--top S] [--cycles N]
racket lcir/cli.rkt smt    FILE [-o OUT.smt2] [--top NAME] [--depth K] [--run]
racket lcir/cli.rkt query  FILE [PATH | --at LINE:COL | --list] [--diag json]
racket lcir/cli.rkt patch  FILE PATH --with SEXP [-o OUT | --in-place] [--dry-run] [--diag json]
```

退出码：0 成功；1 诊断错误（含缺少参数、`check` 失败、SMT `fail`）；2 未知命令。

## 八、错误码目录

| 错误码 | 含义 |
| :--- | :--- |
| `ERR_PARSE` | 读取失败、形式不合法、未知关键字、目标不可赋值等 |
| `ERR_MACRO` | 宏展开/`gen-for`/`reduce-tree`/`symcat` 等出错 |
| `ERR_UNDEFINED` | 未定义的名称、模块、系统或节点路径 |
| `ERR_TYPE_MISMATCH` | 类型不符 |
| `ERR_WIDTH_MISMATCH` | 位宽不符（附 `sext`/`zext`/`trunc` 建议） |
| `ERR_SIGN_MISMATCH` | 有符号/无符号混用 |
| `ERR_AMBIGUOUS_WIDTH` | 裸整数无法确定宽度或放不下 |
| `ERR_INDEX_OOB` | 常量下标越界 |
| `ERR_MATCH_NO_DEFAULT` | `match` 缺少 `:default` |
| `ERR_ALGO_STATEFUL` | `defalgo` 访问了状态或表 |
| `ERR_WRITE_CONFLICT` | 未决的多规则写冲突 |
| `ERR_COMB_LOOP` | 组合环 |
| `ERR_CHECK` | 运行期断言失败或互斥声明被违反 |
| `ERR_BACKEND` | 后端不支持的构造或缺少外部工具 |
| `ERR_INTERNAL` | 编译器内部错误（应视为缺陷上报） |

## 九、非功能需求（`NFR`）

* **NFR-1 确定性**：同一输入在任何目标上的输出逐字节可复现（不使用随机数）。
* **NFR-2 无堆栈泄漏**：所有用户可触发的错误都以诊断形式报告。
* **NFR-3 可读产物**：生成的 SV/C++ 保留源码名；SMT 符号形如 `|inst__sig@cycle|`。
* **NFR-4 编辑器友好**：见 F-SRC-02/03。

## 十、验证需求（`F-VER`）

| 命令 | 内容 |
| :--- | :--- |
| `make test` | 单元测试（类型/展开/调度/诊断）、`patch-smoke`（query/patch）、`smt-smoke`（SMT 对 ESL）、`emacs`（Emacs 可读性 + lcir-mode 字节编译） |
| `make equiv` | 全部示例 ESL = Verilator = g++ 三方日志一致 |

示例集必须覆盖：计数器、有符号 MAC、优先级写冲突、枚举 FSM、latency-1 SRAM、stream 流水线、综合数据通路（`datapath_mix`：sint 移位、bundle、向量动态下标、切片/拼接、latency-0 表、优先级规则）、异步 FIFO（`afifo`：三方对拍 + `AfifoProp` 任意输入下的 BMC 证明与变异反例）。新增语言特性时须同时扩充示例，使三方对拍覆盖之。

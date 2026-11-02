# LCIR 语言参考

LCIR 源文件（`.lcir`）是 S-表达式。`;` 开始行注释。源码必须能被 Emacs Lisp 的 `read` 读出：布尔值写 `t` / `nil`（`#t`/`#f` 仍可用但不推荐），不要用 `[ ]`、`#\c`、`?c`。`editors/lcir-mode.el` 提供高亮、缩进和 `C-c C-c` 检查。编译分两段：先展开宏和 `gen-for`，再对展开后的 Core LCIR 做强类型检查。

## 类型

| 形式 | 含义 |
| --- | --- |
| `(uint W)` | 无符号位向量，`W >= 1` |
| `(sint W)` | 二进制补码，`W >= 1` |
| `(defenum Name (V0 V1 ...))` | 枚举，位宽 `max(1, ceil(log2 N))`，编码从 0 开始 |
| `(bundle (f1 T1) (f2 T2) ...)` | 压缩结构。第一个字段是高位 |
| `(vec N T)` | 长度 `N` 的向量 |
| `(stream T)` | 握手流，展开为 `name_valid`、`name_ready`、`name_bits` |

流端口的方向：`valid`/`bits` 与端口方向相同，`ready` 相反。用 `(valid x)`、`(ready x)`、`(bits x)` 访问，`x` 可以是 `inst.port`。

没有隐式扩展或截断。`(u W v)` / `(s W v)` 是带宽度的字面量。裸整数只在上下文能唯一确定宽度、且数值放得下时采用那个类型。

## 模块

```lisp
(defmodule Name
  :params ((W 8) (DEPTH 4))
  :clocks (clk)                    ; 默认只有 clk。复位信号 rst 总是隐含的
  :ports ((in a (uint W)) (out y (uint W)))
  :state ((r :type (uint W) :init 0 :reset-less nil :clock clk))
  :tables ((mem :depth DEPTH :type (uint W) :ports (:r 1 :w 1) :latency 0))
  :instances ((child Other :params ((W W))))
  :comb ((wire t (uint W) (+ a r))
         (assign y t))
  (defrule step :guard 1 :body ((set! r (+ r 1))))
  (defalgo inc ((a (uint W))) (uint W) (+ a 1)))
```

`:reset-less t` 的寄存器综合成 `if (we) r <= next`，没有同步复位。控制寄存器保持默认同步复位。

存储器只有一个读口和一个写口。`latency 0` 的 `(table-read mem addr)` 是组合读，读到的是本拍提交前的旧值。`latency 1` 把 `(table-read mem addr)` 写成语句以发出读请求，下一拍用 `(table-rdata mem)` 取数。同拍写读同一地址时先读后写。

## 表达式

算术：`+ - * & | ^ ~` 要求两侧类型完全相同，结果同宽，溢出回绕。`+w` / `-w` 的结果宽度是 `max+1`，`*w` 的结果宽度是两边之和。比较 `== != < <= > >=` 得到 `(uint 1)`。`<<` 是逻辑左移；`>>` 对 `uint` 逻辑右移，对 `sint` 算术右移。

`(and a b)`、`(or a b)`、`(not a)` 只接受 `(uint 1)`。`(mux c t f)` 的条件是 `(uint 1)`，两个分支同类型。

`(match e (P0 e0) (P1 e1) (:default d))` 必须有 `:default`。模式是枚举变体或整数字面量。

`(zext e W)` 得到 `(uint W)`，`(sext e W)` 得到 `(sint W)`，`(trunc e W)` 保留符号性并取低 `W` 位。`(as-uint e)` / `(as-sint e)` 只重新解释位。`(bits e hi lo)` 抽出无符号切片，`hi` 是高位。`(cat a b c)` 里 `a` 是高位。

`(field e fname)`、`(idx e i)`、`(pack (f e) ...)`、`(vlit e ...)` 构造和拆开复合值。下标是常量时越界会在编译期报错。

`(let ((v e) ...) body)` 是纯组合绑定。`defalgo` 的体只能引用参数、字面量和其它算法，不能读状态或表。

`(infix (a + b) & ~mask)` 在读取后改写成 `(& (+ a b) (~ mask))`。`&&` / `||` 变成 `and` / `or`。按位或写成 `|`。

## 规则

```lisp
(defrule name
  :priority 0          ; 数字小的优先。可以不写
  :conflict-free nil
  :guard expr          ; (uint 1)
  :body ((set! r expr)
         (table-write mem addr data)
         (table-read mem addr)
         (log info "k" expr)
         (check expr "message")
         (finish)
         (drive inst.port expr)))
```

同一条规则里，寄存器右值读到的永远是本拍开始时的旧值，即使前面刚 `set!` 过。一条规则不能对同一寄存器、同一张表写两次。

几条规则写同一资源时：

1. 写集合不相交则并行。
2. 守卫可证明互斥，或双方都声明了 `:conflict-free`，则并行，并用多路选择合并。
3. 否则每条规则都要有不同的 `:priority`，按优先级合成 `we` 和 `next`。都没有则报 `ERR_WRITE_CONFLICT`。

`drive` 只出现在 `defsystem` 里。它写入的值下一拍才被子模块看到。

## 宏

`defmacro` 的体是受限的 Racket（`racket/base` + `racket/list`，另有 `t`、`nil` 两个常量）。参数是未求值的 S-表达式，返回值会再展开。宏体也要遵守 Emacs 可读子集，例如 `let` 用圆括号写 `(let ((s e)) ...)`。

```lisp
(defmacro regs (n)
  (gen-for 0 n (lambda (i) `(,(symcat 'r i) :type (uint 8) :init 0))))
```

源码里也可以写：

- `(gen-for (i lo hi) body ...)`：`i` 从 `lo` 到 `hi`（不含），结果拼进周围的列表。
- `(cat-for (i lo hi) expr)` → `(cat e0 e1 ...)`。
- `(reduce-tree op (i lo hi) expr)` 或 `(reduce-tree op e0 e1 ...)`：平衡树。
- `(symcat 'prefix_ i)`、`(log2 n)`、`(clog2 n)`。`clog2(1)` 为 0。
- 参数替换之后，全是整数的 `+ - *` 和比较会在展开期折叠。`(if cond a b)` 的条件是常量时只保留一边，否则变成 `mux`。

## 系统与仿真

```lisp
(defsystem Tb
  :instances ((dut Name :params ((W 8))))
  :state ((n :type (uint 8) :init 0))
  (defrule step
    :guard (< n 4)
    :body ((drive dut.a 1)
           (log info "y" dut.y)
           (check (< dut.y 100) "range")))
  (defrule stop
    :guard (== n 4)
    :body ((finish))))
```

每个周期：用已提交状态算组合输出，规则只读旧值并产生候选，断言失败则丢弃本拍并退出，否则原子提交。日志在提交阶段打印，格式是 `[cyc N] level key=value`。开始前有一个静默的同步复位周期。

```
racket lcir/cli.rkt check  file.lcir --diag json
racket lcir/cli.rkt expand file.lcir
racket lcir/cli.rkt sim    file.lcir --cycles 20 --dump-vcd out.vcd
racket lcir/cli.rkt sv     file.lcir -o build/sv --cycles 20
racket lcir/cli.rkt cpp    file.lcir -o build/cpp --cycles 20   # 然后 g++ -std=c++17 build/cpp/<Sys>.cpp
racket lcir/cli.rkt smt    file.lcir -o out.smt2 --depth 20 [--top Module] [--run]
```

`--dump-fst` 需要本机有 `vcd2fst`。仿真日志逐拍输出；`check` 失败时之前各拍的日志已经打印。

`cpp` 生成单文件 C++17 仿真器，日志与 ESL 逐行相同。所有值必须不超过 64 位。

`smt` 生成 SMT-LIB v2（QF_ABV）。第一个查询是从复位后状态展开 `--depth` 拍的有界模型检查：`unsat` 表示这些拍内没有 `check` 会失败、互斥写者也不会同时激活。`--top` 指定一个模块时，它的输入端口在每拍都是自由变量。之后每个多写者寄存器一个查询，`unsat` 表示写者守卫互斥。`--run` 调用 z3。BMC 为 `sat` 时会再取模型，打印反例轨迹：每拍的自由输入和顶层寄存器，最后一拍标出失败的 `check`（`--diag json` 时在 `trace` 字段）。`examples/afifo.lcir` 里的 `AfifoProp` 是一个完整的形式化测试台写法。

## 给 Agent 的接口

节点路径从顶层形式开始，以 `/` 分隔，作用于宏展开前的源码：

| 段 | 含义 |
| --- | --- |
| `module:X` `system:X` `enum:X` `macro:X` | 顶层定义 |
| `rule:X` `algo:X` | 模块里的 `defrule` / `defalgo` |
| `state:X` `table:X` `inst:X` `port:X` `wire:X` | `:state` `:tables` `:instances` `:ports` `:comb` 里的条目 |
| `:kw` | 关键字后面的值 |
| `N` | 第 N 个子元素，从 0 开始 |

```
racket lcir/cli.rkt query examples/counter.lcir --list
racket lcir/cli.rkt query examples/counter.lcir module:Counter/rule:inc/:body/0
racket lcir/cli.rkt query examples/counter.lcir --at 9:20
racket lcir/cli.rkt patch examples/counter.lcir module:Counter/rule:inc/:body/0 \
    --with '(set! c (+ c 2))' --in-place
```

`patch` 只替换该节点的源码区间，其余注释和排版保持不变。替换后会完整编译一遍，通过才写盘；不通过时返回诊断，原文件不动。不给 `-o` / `--in-place` 时打印新文本。

## 内置模块

`lib/prims.lcir` 会自动加载：`stream-slice-forward`、`stream-slice-backward`、`stream-slice-skid`、`sync-fifo`、`async-fifo`、`elastic-pipeline`。`(stream-slice :forward Name W)` 展开成一个按 `W` 包好的转发切片。

`async-fifo` 有 `clk_w` 和 `clk_r`。ESL 让两个时钟同时步进；和 RTL 对拍时把它们接在同一个时钟上。指针用格雷码，经过两级同步触发器。

## 诊断

失败时给出 JSON（`--diag json`）或文本。`line`/`col` 从 1 开始。`node_path` 是上面的机器路径，可以直接交给 `query` / `patch`。`location` 是给人看的路径，例如 `module:StreamingMAC -> rule:compute_mac -> stmt:(set! acc_reg ...)`。宽度不符时 `fix_suggestion` 会建议 `sext`、`zext` 或 `trunc`。组合环的 `loop` 字段是环上的信号名。

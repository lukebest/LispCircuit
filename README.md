# LispCircuit

一个用 Racket 实现的硬件编译器：同一份 LCIR 源码做宏展开、位宽检查、周期精确仿真，并生成可综合的 SystemVerilog、C++ 仿真器和 SMT-LIB 形式化查询。诊断和 `query`/`patch` 命令让 AI Agent 能按节点路径定位和修改源码。

```
racket lcir/cli.rkt check  examples/counter.lcir
racket lcir/cli.rkt sim    examples/counter.lcir --cycles 8
racket lcir/cli.rkt sv     examples/counter.lcir -o build/sv --cycles 8
racket lcir/cli.rkt cpp    examples/counter.lcir -o build/cpp --cycles 8
racket lcir/cli.rkt smt    examples/counter.lcir --depth 8 -o build/counter.smt2
racket lcir/cli.rkt query  examples/counter.lcir --list
make test     # 单元、query/patch、SMT、Emacs 可读性
make equiv    # ESL = Verilator = g++ 三方对拍
```

Emacs 用户：`(add-to-list 'load-path "editors") (require 'lcir-mode)`。

语言说明见 [docs/lang-ref.md](docs/lang-ref.md)，需求见 [docs/srs.md](docs/srs.md)。

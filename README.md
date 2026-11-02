# LispCircuit

一个用 Racket 实现的硬件编译器：同一份 LCIR 源码做宏展开、位宽检查、周期精确仿真，并生成可综合的 SystemVerilog。

```
racket lcir/cli.rkt check  examples/counter.lcir
racket lcir/cli.rkt sim    examples/counter.lcir --cycles 8
racket lcir/cli.rkt sv     examples/counter.lcir -o build/sv --cycles 8
make test
make equiv
```

语言说明见 [docs/lang-ref.md](docs/lang-ref.md)，需求见 [docs/srs.md](docs/srs.md)。

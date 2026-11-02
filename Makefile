RACKET ?= racket
EMACS ?= emacs
CLI = $(RACKET) lcir/cli.rkt
EXAMPLES = counter streaming_mac fifo_counter fsm_enum sram_lat1 stream_pipeline datapath_mix

.PHONY: test unit patch smt emacs equiv examples cpp

test: unit patch smt emacs

unit:
	$(RACKET) tests/run-tests.rkt

patch:
	$(RACKET) tests/patch-smoke.rkt

smt:
	$(RACKET) tests/smt-smoke.rkt

# Every source must stay readable by the Emacs Lisp reader; lcir-mode must
# byte-compile cleanly. Skipped when Emacs is not installed.
emacs:
	@if command -v $(EMACS) >/dev/null; then \
	  $(EMACS) --batch -l tests/emacs-read.el -f lcir-test-read examples/*.lcir lib/prims.lcir && \
	  $(EMACS) --batch -l tests/emacs-read.el -f lcir-test-mode examples/*.lcir lib/prims.lcir 2>&1 | grep -v '^Indenting' ; \
	  rm -f editors/lcir-mode.elc; \
	else echo "emacs not found: skipping"; fi

# ESL == Verilator (SV) == g++ (C++) logs for every example.
equiv: test
	$(RACKET) tests/equiv.rkt

examples: test
	@for e in $(EXAMPLES); do echo "== $$e"; $(CLI) sim examples/$$e.lcir --cycles 20 || exit 1; done

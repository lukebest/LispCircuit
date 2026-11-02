RACKET ?= racket

.PHONY: test equiv examples

test:
	$(RACKET) tests/run-tests.rkt

equiv: test
	$(RACKET) tests/equiv.rkt

examples: test
	$(RACKET) lcir/cli.rkt sim examples/counter.lcir --cycles 8
	$(RACKET) lcir/cli.rkt sim examples/streaming_mac.lcir --cycles 20
	$(RACKET) lcir/cli.rkt sim examples/fifo_counter.lcir --cycles 20
	$(RACKET) lcir/cli.rkt sim examples/fsm_enum.lcir --cycles 20
	$(RACKET) lcir/cli.rkt sim examples/sram_lat1.lcir --cycles 20
	$(RACKET) lcir/cli.rkt sim examples/stream_pipeline.lcir --cycles 20

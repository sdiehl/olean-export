LEAN ?= lean
NL_FAST ?= nl-fast
PREFIX := $(shell $(LEAN) --print-prefix)
EXPORT := cargo run -q --release --manifest-path ../Cargo.toml --
export LEAN_PATH := build:$(PREFIX)/lib/lean

all: build/hello.ndjson
	head -3 $<

build/Hello.olean: Hello.lean
	mkdir -p build
	$(LEAN) -o $@ $<

build/hello.ndjson: build/Hello.olean
	$(EXPORT) Hello -c double_two -o $@

check: build/hello.ndjson
	$(NL_FAST) $<

clean:
	rm -rf build

.PHONY: all check clean

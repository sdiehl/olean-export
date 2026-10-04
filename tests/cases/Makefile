LEAN ?= lean
SRCS := $(wildcard *.lean)

all: $(SRCS:%.lean=build/%.olean)

build/%.olean: %.lean
	@mkdir -p build
	LEAN_PATH=build $(LEAN) -o $@ $<
	rm -f build/*.ir build/*.ir.sig

build/Top.olean: build/Base.olean

clean:
	rm -rf build

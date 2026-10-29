LEAN ?= lean
SRCS := $(wildcard *.lean)

all: $(SRCS:%.lean=build/%.olean) build/edit/Top.olean

build/%.olean: %.lean
	@mkdir -p build
	LEAN_PATH=build $(LEAN) -o $@ $<
	rm -f build/*.ir build/*.ir.sig

build/Top.olean: build/Base.olean

build/edit/Top.olean: edit/Top.lean build/Base.olean
	@mkdir -p build/edit
	LEAN_PATH=build $(LEAN) --root=edit -o $@ $<
	rm -f build/edit/*.ir build/edit/*.ir.sig

clean:
	rm -rf build

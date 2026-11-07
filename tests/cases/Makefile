LEAN ?= lean
SRCS := $(wildcard *.lean)

all: $(SRCS:%.lean=build/%.olean) build/edit/Top.olean build/edit/Hidden.olean

build/edit/%.olean: edit/%.lean build/Base.olean
	@mkdir -p build/edit
	cd edit && LEAN_PATH=../build $(LEAN) -o ../$@ $*.lean
	rm -f build/edit/*.ir build/edit/*.ir.sig

build/%.olean: %.lean
	@mkdir -p build
	LEAN_PATH=build $(LEAN) -o $@ $<
	rm -f build/*.ir build/*.ir.sig

build/Top.olean build/Hidden.olean: build/Base.olean

clean:
	rm -rf build

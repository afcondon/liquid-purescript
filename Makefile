.PHONY: build examples verify bundle test clean

build:
	spago build

examples:
	cd examples && spago build

verify: build examples
	spago run --quiet -- verify-all --output examples/output --include lib/prelude.lps

bundle:
	spago bundle

test:
	./test/run.sh

clean:
	rm -rf output .spago bin examples/output examples/.spago

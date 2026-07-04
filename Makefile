.PHONY: build examples verify test clean

build:
	spago build

examples:
	cd examples && spago build

verify: build examples
	spago run --quiet -- verify --output examples/output Demo

test:
	./test/run.sh

clean:
	rm -rf output .spago examples/output examples/.spago

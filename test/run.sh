#!/bin/sh
# Golden test: build the examples to CoreFn, run the verifier, diff the
# verdicts against test/golden.txt, and check the exit code is 1 (the demo
# deliberately contains an UNSAFE function).
set -u
cd "$(dirname "$0")/.."

(cd examples && spago build) >/dev/null 2>&1 || { echo "examples build failed"; exit 1; }
spago build >/dev/null 2>&1 || { echo "lps build failed"; exit 1; }

demo=$(spago run --quiet -- verify --output examples/output Demo 2>/dev/null)
demo_status=$?
p1=$(spago run --quiet -- verify --output examples/output P1 2>/dev/null)
p1_status=$?
actual=$(printf '%s\n%s' "$demo" "$p1")

if [ "$demo_status" -ne 1 ] || [ "$p1_status" -ne 1 ]; then
  echo "FAIL: expected exit code 1 from both modules (each contains a deliberate failure), got Demo=$demo_status P1=$p1_status"
  exit 1
fi

if ! printf '%s\n' "$actual" | diff -u test/golden.txt -; then
  echo "FAIL: verdicts differ from test/golden.txt"
  exit 1
fi

echo "golden test passed"

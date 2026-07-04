#!/bin/sh
# Golden test: build the examples to CoreFn, run the verifier, diff the
# verdicts against test/golden.txt, and check the exit code is 1 (the demo
# deliberately contains an UNSAFE function).
set -u
cd "$(dirname "$0")/.."

(cd examples && spago build) >/dev/null 2>&1 || { echo "examples build failed"; exit 1; }
spago build >/dev/null 2>&1 || { echo "lps build failed"; exit 1; }

actual=$(spago run --quiet -- verify --output examples/output Demo 2>/dev/null)
status=$?

if [ "$status" -ne 1 ]; then
  echo "FAIL: expected exit code 1 (demo contains an UNSAFE function), got $status"
  exit 1
fi

if ! printf '%s\n' "$actual" | diff -u test/golden.txt -; then
  echo "FAIL: verdicts differ from test/golden.txt"
  exit 1
fi

echo "golden test passed"

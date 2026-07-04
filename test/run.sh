#!/bin/sh
# Golden test: build the examples to CoreFn, verify every module that has
# a .lps spec (with the shared Prelude corpus included), diff the verdicts
# against test/golden.txt, and check the exit code is 1 (the examples
# deliberately contain UNSAFE and mismatched functions).
set -u
cd "$(dirname "$0")/.."

(cd examples && spago build) >/dev/null 2>&1 || { echo "examples build failed"; exit 1; }
spago build >/dev/null 2>&1 || { echo "lps build failed"; exit 1; }

actual=$(spago run --quiet -- verify-all --output examples/output --include lib/prelude.lps 2>/dev/null)
status=$?

if [ "$status" -ne 1 ]; then
  echo "FAIL: expected exit code 1 (examples contain deliberate failures), got $status"
  exit 1
fi

if ! printf '%s\n' "$actual" | diff -u test/golden.txt -; then
  echo "FAIL: verdicts differ from test/golden.txt"
  exit 1
fi

echo "golden test passed"

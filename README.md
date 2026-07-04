# Liquid PureScript

Liquid Haskell-style refinement type verification for PureScript, as an
external tool over CoreFn — no compiler fork. Written in PureScript; solves
with Z3.

You write ordinary PureScript; a sibling `.lps` file refines the types of
the functions you care about; `lps verify` proves the refinements hold or
shows a counterexample.

```purescript
-- Demo.purs
abs :: Int -> Int
abs n = if n > 0 then n else 0 - n

bad :: Int -> Int
bad n = n - 1
```

```
-- Demo.lps
type Nat = { v : Int | v >= 0 }

abs :: Int -> Nat
bad :: Int -> Nat
```

```
$ make verify
Demo.abs  ✓ SAFE
Demo.bad  ✗ UNSAFE
    at src/Demo.purs:9:9
    cannot prove: ((n - 1) >= 0)
    counterexample: n = 0
```

## Status

**Phase 1 core** (2026-07-04): first-order `Int`/`Boolean` functions with
if/guards/case (including multi-alternative Int-literal cases), `let`,
dependent specs across argument binders
(`clamp :: {lo:Int} -> {hi:Int|hi>=lo} -> ...`), **calls to spec'd
functions** (preconditions checked at the call site, postconditions assumed
— see `callBad` refute below), **recursion** (assumes the function's own
spec), and **`assume` specs** for imported/FFI functions. `--smt2-dir`
dumps every obligation as a replayable artifact. Everything outside the
fragment reports UNSUPPORTED, never a silent pass. See `docs/PLAN.md` for
architecture, semantics, and the phased roadmap.

```
P1.callBad  ✗ UNSAFE
    at src/P1.purs:21:13
    cannot prove: (n >= 0)
    counterexample: n = (- 1)
```

## Requirements

purs 0.15.x, spago@next, node, and a `z3` binary on the PATH.

## Usage

```sh
make examples          # compile examples/ to CoreFn (spago backend trick)
make verify            # run the verifier over the demo module
make test              # golden test
```

Direct invocation:

```sh
spago run -- verify --output <output-dir> <ModuleName> [--spec <file.lps>]
```

The spec file defaults to the module's source path with `.purs` → `.lps`.

To emit CoreFn from any spago project, add a no-op backend to its
`spago.yaml` (this is how `examples/` is set up):

```yaml
workspace:
  backend:
    cmd: "true"
```

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

**Phase 2 first cut** (same day): user data types with **measures** —
declare the shape and a logic-level measure in the spec file, and the
verifier reasons inductively about constructors:

```
-- P2.lps
data IntList = INil | ICons Int IntList

measure len :: IntList -> { v : Int | v >= 0 }
  INil = 0
  ICons x xs = 1 + len xs

count  :: { l : IntList } -> { v : Int | v == len l }
append :: { a : IntList } -> { b : IntList } -> { v : IntList | len v == len a + len b }
```

Both prove (`count` by assuming its own spec at the recursive call;
`append` through constructor-application facts), and the version of
`count` that forgets the `+ 1` refutes with a countermodel.

**Arrays** work through a built-in `length` measure (element types are
erased — only length is visible to the logic) plus trusted specs for
`Data.Array` functions in `lib/arrays.lps`:

```
mid :: { xs : Array | length xs > 0 } -> { v : Int | v >= 0 && v < length xs }
```

proves (`mid xs = length xs / 2`), and the same body without the
non-empty precondition refutes with the empty array.

## Requirements

purs 0.15.x, spago@next, node, and a `z3` binary on the PATH.

## Usage

```sh
make examples          # compile examples/ to CoreFn (spago backend trick)
make verify            # verify every example module that has a .lps spec
make test              # golden test
make bundle            # standalone bin/lps.mjs (node, no spago needed)
```

Direct invocation:

```sh
lps verify     --output <dir> <ModuleName> [--spec <file.lps>]
               [--include <file.lps>]... [--smt2-dir <dir>]
lps verify-all --output <dir> [--include <file.lps>]... [--smt2-dir <dir>]
```

(`lps` = `spago run --` or `node bin/lps.mjs` after `make bundle`.)

- The spec file defaults to the module's source path with `.purs` → `.lps`;
  `verify-all` scans the output directory and verifies every module whose
  spec file exists.
- `--include` prepends shared spec corpora — start with `lib/prelude.lps`
  (trusted `assume` specs for `min`, `max`, `abs`, `signum`, `clamp` on Int).
- Specs are cross-checked against the module's `docs.json` type signatures:
  arity or base-type disagreement fails the function before any solving.
- `--smt2-dir` dumps every obligation as a replayable `.smt2` artifact.

To emit CoreFn from any spago project, add a backend to its `spago.yaml`
(this is how `examples/` is set up):

```yaml
workspace:
  backend:
    cmd: "true"   # no-op: just emit corefn.json
```

To verify on every build instead, make the verifier the backend:

```yaml
workspace:
  backend:
    cmd: "node"
    args: [ "../bin/lps.mjs", "verify-all", "--output", "output",
            "--include", "../lib/prelude.lps" ]
```

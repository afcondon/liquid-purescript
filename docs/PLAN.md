# Liquid PureScript — Implementation Plan

**Status**: active
**Created**: 2026-07-04
**Supersedes nothing; builds on**: `purescript-polyglot/docs/kb/research/liquid-purescript-feasibility.md` (2026-01-29)

## What this is

A Liquid Haskell-style refinement type verifier for PureScript, built as an
**external tool consuming CoreFn** — no compiler fork. You write ordinary
PureScript; alongside each module you write a `.lps` spec file refining the
types of some of its functions; the tool proves (via Z3) that the code
satisfies the refinements, or reports where and why it doesn't, with a
counterexample.

```
-- Demo.purs (ordinary PureScript, unchanged)
abs :: Int -> Int
abs n = if n > 0 then n else 0 - n

-- Demo.lps (the refinement layer)
type Pos = { v : Int | v >= 0 }
abs :: Int -> Pos
```

```
$ lps verify --output output Demo
Demo.abs  ✓ SAFE
```

Decisions locked in 2026-07-04 (Andrew): external tool; **written in
PureScript** (house style — ADTs everywhere, runs on Node); annotations in
**separate `.lps` spec files** (not comments); repo at
**`afc-work/liquid-purescript`**. This session's goal: this plan plus a
**vertical slice** — one thin path through every layer.

## Ground truth (probed 2026-07-04, purs 0.15.15 / spago 1.0.3)

These facts were verified against a live compile, and they shape the design:

1. **Getting CoreFn out of spago**: spago rejects `--purs-args "--codegen corefn"`;
   the supported route is a custom backend in `spago.yaml`
   (`workspace.backend.cmd`), which makes spago compile with corefn codegen and
   then invoke the command. `cmd: "true"` (no-op) works; eventually
   `cmd: "lps verify"` makes the verifier *be* the backend step.
2. **Externs are CBOR now** (`externs.cbor`, not `externs.json`). But
   `docs.json` in the same output directory carries full type ASTs as JSON for
   every top-level declaration. For the slice we don't need either — the `.lps`
   file declares the shapes we check — but Phase 1's signature cross-checking
   should read `docs.json`, not fight CBOR.
3. **Type-class methods are floated**. `n > 0` in source does not appear as an
   application of `Data.Ord.greaterThan` at the use site. The compiler emits a
   synthetic module-local decl —
   `Probe.greaterThan = Data.Ord.greaterThan ordInt` — and the use site is
   `App (App (Var Probe.greaterThan) (Var n)) (Lit 0)`. So the verifier needs a
   **resolution pass**: scan module decls for the shape
   `App (Var <known class method>) (Var <known dictionary>)` and build a table
   mapping local names to primitive SMT operations. Same for `sub`/`add`/`mul`
   (Ring/Semiring + ringInt), `div`/`mod` (EuclideanRing + euclideanRingInt),
   comparisons (Ord + ordInt), `eq`/`notEq` (Eq + eqInt/eqBoolean),
   `&&`/`||`/`not` (HeytingAlgebra + heytingAlgebraBoolean).
4. **`if/then/else` desugars to `Case`** with a `LiteralBinder true` alternative
   and a `NullBinder` fallback. Guards appear as `isGuarded` alternatives.
   Source spans are present on every annotation node.
5. Toolchain available: purs 0.15.15, spago 1.0.3, node 22, **z3 4.15.3 binary**
   (homebrew) and z3-solver 4.16.0 (WASM) on npm.

## Architecture

```
  spago build (backend: lps)          Demo.lps
        │                                │
        ▼                                ▼
  output/<Mod>/corefn.json        ┌──────────────┐
        │                         │ Spec.Parser  │  (purescript-parsing)
        ▼                         └──────┬───────┘
  ┌──────────────┐                       │ SpecFile: aliases + fn specs
  │ CoreFn.Decode│                       │
  └──────┬───────┘                       │
         │ Module (ADT)                  │
         ▼                               │
  ┌──────────────┐                       │
  │   Resolve    │  float-alias table →  │
  └──────┬───────┘  PrimOp per local Var │
         │                               │
         ▼                               ▼
  ┌─────────────────────────────────────────┐
  │                  Vc                     │
  │  checking-mode traversal of each        │
  │  spec'd decl → [Obligation]             │
  └──────────────────┬──────────────────────┘
                     │ Obligation = {ctx :: Array Pred, goal :: Pred, span}
                     ▼
  ┌──────────────┐        ┌──────────────┐
  │  Logic.Smt   │ ─────► │  Solver.Z3   │  (spawnSync `z3 -in` / .smt2 file)
  │  SMT-LIB2    │        └──────┬───────┘
  └──────────────┘               │ Unsat → SAFE / Sat + model → UNSAFE
                                 ▼
                          ┌──────────────┐
                          │    Report    │  verdict + source span + countermodel
                          └──────────────┘
```

Every arrow is a plain ADT-to-ADT function; the only effects are reading files
and spawning z3. The SMT boundary is **text** (SMT-LIB2), so every obligation
can be dumped as a `.smt2` artifact and replayed by hand — the same
inspectability principle as the backends family's differential conformance.

### Repo layout

```
liquid-purescript/
├── docs/
│   ├── PLAN.md                  (this file)
│   └── adr/                     (Jurist-style ADR discipline)
├── spago.yaml                   (workspace)
├── lps/                         package: core library + CLI main
│   ├── spago.yaml
│   └── src/Lps/
│       ├── CoreFn/Types.purs    CoreFn subset as ADTs
│       ├── CoreFn/Decode.purs   Json → Module (hand-written decoders)
│       ├── Spec/Syntax.purs     RType, Pred, SpecFile ADTs
│       ├── Spec/Parser.purs     .lps text → SpecFile
│       ├── Logic.purs           Pred / Term / Sort (shared with Spec)
│       ├── Logic/Smt.purs       Obligation → SMT-LIB2 text
│       ├── Resolve.purs         float-alias → PrimOp table
│       ├── Vc.purs              CoreFn expr → obligations
│       ├── Solver/Z3.purs       FFI: spawnSync z3
│       ├── Report.purs          verdict rendering
│       └── Main.purs            CLI: lps verify
└── examples/                    package: demo modules + .lps specs
    ├── spago.yaml               (backend cmd: "true" → emits corefn)
    └── src/Demo.purs, Demo.lps
```

## The refinement language

### Slice grammar (`.lps` files)

```
specfile  ::= { decl }
decl      ::= "type" CONID [ vars ] "=" rtype        -- alias
            | VARID "::" fnspec                      -- function spec
fnspec    ::= rtype { "->" rtype }
rtype     ::= "{" VARID ":" base "|" pred "}"        -- refined base
            | base                                   -- unrefined (pred = true)
            | CONID                                  -- alias reference
base      ::= "Int" | "Boolean"
pred      ::= pred ("&&" | "||") pred
            | "not" pred | "(" pred ")"
            | term ("==" | "/=" | "<" | "<=" | ">" | ">=") term
            | "true" | "false"
term      ::= term ("+" | "-") term | term "*" term
            | INT | VARID | "(" term ")"
```

Binders in earlier arguments scope over later refinements — argument names in
the spec are binding positions:

```
myDiv :: Int -> { d : Int | d /= 0 } -> Int
clamp :: { lo : Int } -> { hi : Int | hi >= lo } -> Int -> { v : Int | v >= lo && v <= hi }
```

The logic stays inside **QF_LIA + Bool** (quantifier-free linear integer
arithmetic) so Z3 is a decision procedure, not a heuristic: multiplication of
two variables is rejected at spec-parse time (literal·var is fine).
Phase 2 widens to QF_UFLIA when measures arrive.

### Semantics: checking mode, weakest-precondition flavour

For a spec `f :: t1 -> t2 -> tr` and CoreFn decl `f = Abs x1 (Abs x2 body)`:

1. Bind `x1 : t1`, `x2 : t2`; their refinements enter the context Γ as
   assumptions (spec binder names are α-renamed to the CoreFn binder names).
2. Traverse `body` accumulating **path conditions**:
   - `Case scrut alts` where scrut is Boolean-valued: alternative with
     `LiteralBinder true` extends Γ with `⟦scrut⟧`; `LiteralBinder false` or
     the `NullBinder` fallback extends Γ with `¬⟦scrut⟧` (more precisely, with
     the negation of all earlier binders — the fallback of a multi-alt case
     gets the conjunction of negations).
   - Guarded alternatives: each guard is a path condition for its expression;
     later guards additionally assume the negations of earlier ones.
   - `Let`: slice supports non-recursive value binds of *embeddable*
     expressions — bind an equality `x == ⟦e⟧` into Γ. Anything not
     embeddable binds an unconstrained fresh variable (sound, imprecise).
3. At each leaf `e` (an embeddable expression in tail position), emit an
   **obligation**: `Γ ⊢ pred_r[v := ⟦e⟧]` where `pred_r` is the result
   refinement.
4. **Embedding ⟦·⟧** maps CoreFn expressions to logic terms: literals,
   variables, and applications of resolved PrimOps. Applications of *spec'd*
   functions use their spec: argument refinements become obligations at the
   call site, and the call's value gets the (instantiated) result refinement
   as an assumption via a fresh variable. Applications of unknown functions
   embed as fresh unconstrained variables (sound, imprecise — the LH move).
5. Each obligation discharges as one Z3 query:
   `(assert Γ) (assert (not goal)) (check-sat)` — **unsat ⇒ SAFE**;
   **sat ⇒ UNSAFE** with `(get-model)` as the counterexample.

Recursion (Phase 1, not slice): recursive calls assume the function's own
spec — standard inductive reasoning; termination is out of scope (LH's
approach too, unless you opt into termination checking).

Trust boundaries: FFI (`foreign import`) and un-spec'd imports are assumed —
their specs, if given via `assume` declarations (Phase 1), are taken on faith.

### Worked slice example

`bad :: Int -> Pos` with `bad n = n - 1`, `Pos = { v : Int | v >= 0 }`:

- Γ = { true } (argument `n` unrefined)
- body embeds to `n - 1` (after Resolve maps the floated `Demo.sub` to `-`)
- obligation: `true ⊢ n - 1 >= 0`
- SMT: `(declare-const n Int) (assert (not (>= (- n 1) 0))) (check-sat)`
  → **sat**, model `n = 0` → `Demo.bad UNSAFE at Demo.purs:8:1 — counterexample: n = 0`

`abs` with the same result type: two obligations,
`n > 0 ⊢ n >= 0` and `¬(n > 0) ⊢ 0 - n >= 0` — both unsat when negated → SAFE.

## Design decisions (ADR summaries)

**ADR-001 — External tool over compiler fork.** CoreFn JSON + docs.json carry
everything needed; a fork is a maintenance treadmill. (Carried over from the
feasibility study; confirmed by probe.)

**ADR-002 — PureScript host.** House style; the verifier is one long
ADT-to-ADT pipeline, which is exactly what PureScript is good at. Node runtime
is fine for the performance envelope (per-module verification, dozens of
small Z3 queries).

**ADR-003 — `.lps` spec files, not comment pragmas.** CoreFn's `comments`
field does not reliably carry positioned comments; comment pragmas would force
us to re-parse `.purs` sources. A sibling spec file keeps the parser
standalone and sources untouched. Revisit if locality hurts in practice
(the AST is front-end-agnostic; pragmas could be added later).

**ADR-004 — SMT transport is SMT-LIB2 text to the `z3` binary
(`spawnSync`).** Tiny FFI surface, artifact-per-obligation on disk when
`--keep-smt2` is set, trivially replayable. The z3-solver WASM package stays
on the roadmap for the *playground* integration (browser, no binary), which is
where Liquid PureScript joins the typed-feedback-loop vision — the Logic.Smt
boundary is designed so the transport is swappable.

**ADR-005 — Decidable fragment only, enforced at parse time.** QF_LIA for the
slice; grow the logic only alongside a decision procedure (UF for measures in
Phase 2). Never hand Z3 a problem where "unknown" is a possible answer.

**ADR-006 — Sound-but-imprecise defaults.** Unknown calls and un-embeddable
lets become unconstrained fresh variables. The tool may reject good code
(imprecision) but must never bless bad code within the trusted fragment.

## Roadmap

**Phase 0 — vertical slice (this session).** One path through every layer:
first-order `Int`/`Boolean` functions, if/case-on-Boolean path conditions,
PrimOp resolution for Ord/Ring/Semiring/EuclideanRing/Eq/HeytingAlgebra on
Int/Boolean, `.lps` aliases + fn specs, z3 verdicts with spans and
countermodels, golden test over `examples/`.

**Phase 1 — minimal viable verifier (the feasibility study's 4–6 wk).**
Multi-equation functions and full pattern binders on Int literals; guarded
alternatives; `Let` (incl. recursive with spec assumption); calls to spec'd
functions with binder instantiation; `assume` declarations for FFI/imports;
signature cross-check against `docs.json`; `lps` as a spago backend cmd;
error messages worth reading (span + obligation pretty-printed + model).

**Phase 2 — measures and data (6–8 wk).** ADT scrutinees and constructor
binders; measures (`length`, user-defined) as uninterpreted functions with
constructor axioms; `Array` refinements (`NonEmpty`); parametric polymorphism
with trivially-lifted refinements; records (flat, no row-poly refinements yet).

**Phase 3 — higher-order (8–12 wk).** Abstract refinements, refinement
inference for lambdas, `map`/`filter`/`fold` specs.

**Phase 4 — type classes (research).** Bounded refinements, per-instance
specs. Genuinely open; also where row-polymorphic record refinements live.

**Cross-cutting, when it earns its keep**: playground integration (z3 WASM,
per-binding property display), Minard overlay (which functions are verified —
verification coverage as a cartography layer), purerl parity check (CoreFn is
backend-agnostic, so verified specs hold for Erlang output too — relevant to
Trieste/live-coding where a pattern that proves `{ v : Int | 0 <= v && v < 128 }`
is a MIDI-safe pattern).

## Testing strategy

- **Golden verdicts**: `examples/` modules each carry a `.lps` and an expected
  verdict table; `spago test` runs the pipeline and diffs. SAFE cases and
  UNSAFE cases in equal measure — a verifier that says SAFE to everything
  passes half a naive suite.
- **Parser round-trip**: pretty-print ∘ parse = id on `.lps` corpus.
- **Obligation snapshots**: `.smt2` outputs are committed for the examples, so
  a VC-generation regression shows up as a text diff before it shows up as a
  verdict flip.

## Open questions (parked, not blocking)

- **Name.** `lps` as CLI is fine; if it wants a proper name in the
  Jurist/Pythia/Gnomon family, something from the judgment/oracle register —
  *Themis* has the right flavour. Decide at first publish.
- Whether Phase 1 signature cross-checking should hard-fail on spec/type
  mismatch or warn.
- Spec inheritance for re-exports.
- How verification interacts with `spago publish` (ship `.lps` in the tarball?).

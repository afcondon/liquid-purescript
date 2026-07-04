# Website brief — Liquid PureScript documentation site

**For**: a future Claude (Opus/Sonnet) session building a documentation
site for this project, before the Phase 4 research work begins.
**Decided**: Andrew, 2026-07-04.

## What the site is

A documentation/showcase site for Liquid PureScript: what refinement
types buy a PureScript programmer, how this tool works, and where the
project is going. Audience: PureScript community members and
verification-curious functional programmers. It should read as an
invitation to try the tool, not a paper.

## Style

Andrew's standing preference: light theme, Swiss/International
Typographic Style — clean grids, generous whitespace, sans-serif,
restrained palette, hierarchy through type scale and weight, no
decoration. Look at `code-typography/specimen` and
`elements-of-purescript-style` for the house aesthetic at its best.
Likely deploy target: Cloudflare Pages (see `cloudflare-sites/` for the
family pattern).

## Content inventory (all in this repo)

- `README.md` — elevator pitch, worked examples with real verdicts.
- `docs/PLAN.md` — architecture diagram, refinement-language grammar,
  checking-mode semantics, six ADRs, the phased roadmap with dated
  status notes, and the research-validation-by-test-corpus strategy.
- `examples/src/*.{purs,lps}` — paired code/spec files, each verdict
  reproducible with `make verify`. The demos in escalating order:
  `Demo` (basics + counterexamples), `P1` (compositional: call-site
  preconditions, recursion, assume), `P2` (inductive ADTs via measures),
  `Arrays` (built-in length measure, library specs).
- `lib/*.lps` — the starter spec corpora (Prelude, Data.Array).
- `test/golden.txt` — the full verdict table, always current.
- Marginalia project 246 notes — the day-by-day narrative of the build,
  including the bugs worth telling (the parser swallowing `type` as a
  measure argument; `Array` colliding with SMT-LIB's array theory).

## Suggested shape (adapt freely)

1. **Hero**: one paired code/spec block and its verdict, including a
   counterexample — the UNSAFE verdicts are more persuasive than the
   SAFE ones. `badMid` (empty-array refutation) or `callBad` are good.
2. **How it works**: the pipeline diagram from PLAN.md (CoreFn → specs →
   VCs → Z3), pitched at a reader who knows PureScript but not SMT.
3. **The spec language**: grammar by example — refinements, dependent
   binders, `assume`, `data`/`measure`.
4. **Live verdicts**: the golden table, grouped by module, SAFE/UNSAFE
   badges.
5. **Roadmap + research**: the phase status notes, and the
   soundness-trap corpus idea as the story of how open research gets
   validated without a peer reviewer.
6. **Getting started**: Requirements + Usage from the README.

## Honesty constraints (do not soften)

- This verifies a *fragment*: first-order Int/Boolean/measured-data
  code. Everything outside reports UNSUPPORTED. Do not imply generality
  the tool doesn't have.
- `assume` specs are trusted, not checked. Say so where they appear.
- Phase 3 (higher-order) and Phase 4 (type classes, row-polymorphic
  records) do not exist yet; the site describes them as roadmap.

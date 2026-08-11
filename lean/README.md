# Lean-checked deduction core

This pinned Lean 4 project formalizes the finite and algebraic core of the
`0.673195` simple-zero deduction in the parent repository. It uses
[`anthropics/zeta-23-lean`](https://github.com/anthropics/zeta-23-lean) at
commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510` as its analytic and
linear-algebra base.

The project checks:

- the exact perturbed window constants and 21-weight capacity identities;
- the sharp square-root spectral profile and realizing correlation matrices;
- the large-span pressure branch and compact small-span branch;
- matrix block deduction, pinching, offset averaging, and endpoint losses;
- separate stability and block approximation errors;
- the final strict comparison with `673195 / 10^6`; and
- the conditional dyadic and cumulative zeta statements.

It does **not** claim an unconditional formalization of the paper's theorem.
The Arb certificates, arbitrary-window stability and Gram asymptotics, and
retained-set/error packaging remain hypotheses in
`CurrentZetaAnalyticInputs`. There are no `sorry`, `admit`, or new axioms in
the current-result modules.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake update
lake exe cache get
lake build Zeta23Ext
lake env lean Zeta23Ext/PrintCurrentAxioms.lean
```

The expected axiom audit contains only Lean/Mathlib's standard `propext`,
`Classical.choice`, and `Quot.sound` dependencies.

The code in this directory is distributed under Apache-2.0; see `LICENSE`
and `NOTICE`. The parent repository's Python verifier, paper, and supporting
files remain MIT-licensed.

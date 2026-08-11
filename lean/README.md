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

The extension also discharges the normalized-span component unconditionally
from the upstream Riemann--von Mangoldt theorem: the explicit span error and
its pressure-weighted contribution are proved to be `o(N)`. A reduced
analytic bridge derives the aggregate guarded block inequality from pairwise
compact Gram control and derives the stability seam from primitive
count/trace/Frobenius bounds. A kernel-checked interval-tree verifier proves
subdivision coverage and exact leaf arithmetic for future proof-producing
numeric certificates.
The first transcendental component is also kernel-checked: a general sine
Taylor remainder theorem, explicit rational degree-seven enclosures, and
cell-centered rational bounds. These are the foundation for formally proving
the kernel-table entries rather than trusting Arb.

It does **not** claim an unconditional formalization of the paper's theorem.
Still external are: the full `WindowCertificate` (range, monotonicity, and the
`H` lower bound); semantic bounds for the kernel tables; the `RealBridge`,
production search tree, and its future Lean decoding/connection theorem;
admissibility of the current ramped window in the upstream analytic API; a
current-kernel pairwise squared-energy estimate (and its derivation from
entrywise compact Gram convergence); and construction of the retained
Gram/moment data with its remaining `o(N)` errors. The old
Montgomery--Taylor Gram theorem is not reused as if it applied to the current
window. There are no `sorry`, `admit`, or new axioms in the current-result
modules.

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

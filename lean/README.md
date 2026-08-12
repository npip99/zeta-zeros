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
count/trace/Frobenius bounds. Ordinary entrywise closeness now implies the
required squared-energy estimate with explicit loss `2*err`. A
kernel-checked 324-root forest verifier, production-format decoder, integer
objective, and real-score transfer prove all structural replay steps.
The current ramped window's full upstream `AdmWindow` witness—including C²,
support, and all four derivative-integral bounds—is derived from the finite
shape certificate. Its first two scaled moments are proved to converge to the
exact current-window mass and square mass, and the needed autocorrelation
comparison is now discharged. For zeta, the
native coefficient family `c_N=-Lambda(N), D(s)=s` satisfies the complete
generic coefficient hypotheses; its matrix is exactly the standard zeta
prime-side matrix, and the explicit formula supplies trace transfer. Thus
zeta `GzMoments` follow without xi-prime `XiEF` or re-expansion. The exact
integral kernel is proved equal to the
verifier's seven-term entire sinc expression. Kernel-checked sine, cosine,
sinc, and square-root rational enclosures provide the transcendental
foundation for the remaining tables.

It does **not** claim an unconditional formalization of the paper's theorem.
Still external are: the away-cell monotonicity portion of
`WindowCertificate`; semantic bounds for the kernel and tangent tables; and
the typed tangent-leaf evidence needed to replay the recorded production topology;
completion of the retained Gram/moment assembly and its remaining `o(N)`
errors.  The actual-scale infinite-kernel limit, endpoint rho-tail estimate,
ordered interior compression, and its `o(NIprime)` deletion loss are proved.
What remains is an eventual-data interface (avoiding a circular all-height
positivity premise), the concrete central tail/moment rebasing, and final error
assembly.  The strict endpoint `H` normalization is not currently cold-build
checked, so that module is excluded from the umbrella target. The old
Montgomery--Taylor Gram theorem is not reused as if it applied to the current
window. There are no `sorry`, `admit`, or new axioms in the current-result
modules.

See [`END_TO_END_TODO.md`](END_TO_END_TODO.md) for the canonical list of
completed components and the exact theorem arguments still to eliminate.

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

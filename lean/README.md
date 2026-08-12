# Lean-checked zeta deduction

This pinned Lean 4 project formalizes the analytic and finite deduction of the
`0.673195` simple-zero bound in the parent repository. It uses
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
- the dyadic and cumulative zeta statements, conditional only on replaying
  the finite numerical certificate.

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

It does **not** yet claim an unconditional formalization of the paper's
theorem. `CurrentEndToEnd.current_zeta_cumulative_target` has exactly one
remaining argument, `FiniteWindowInputs`. The strict endpoint `H` inequality,
actual-scale Gram limit, endpoint deletion, central moment rebasing, and final
`o(N)` assembly are now kernel checked. What remains is entirely finite:
generate and replay the compact hybrid monotonicity table, and replay the
recorded local seven-point search, including semantic kernel tables and the
406,186 convex-tangent leaves. The old Montgomery--Taylor Gram theorem is not
reused as if it applied to the current window. There are no `sorry`, `admit`,
or new axioms in the current-result modules.

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

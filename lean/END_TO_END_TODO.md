# End-to-end Lean proof status

Last audited: 2026-08-11.

The finite deduction is kernel checked, but the theorem about zeta zeros is
still conditional. This is the canonical checklist for removing the remaining
theorem arguments. An item is complete only when the current window and
constants are instantiated, not merely when a generic interface exists.

No percentage-complete or calendar ETA is currently authoritative. The
remaining analytic seams may dominate the total proof effort; they must be
de-risked theorem by theorem before an end-to-end ETA is credible.

## Complete

- [x] Exact constants, 21 weighted coefficients, pressure capacities, and
  window-summation bookkeeping.
- [x] Sharp square-root defect profile, matrix inequality, and realizing
  correlation matrices.
- [x] Large-span/small-span block split, pinching, offset averaging, endpoint
  losses, and finite error arithmetic.
- [x] Strict `0.673195` comparison and conditional dyadic/cumulative capstone.
- [x] Unconditional zeta Riemann--von Mangoldt span estimate and its
  pressure-weighted `o(N)` consequence.
- [x] Current ramped-window `AdmWindow`/`AdmFamily` admissibility, including
  support, global `C^2`, and all derivative-integral bounds.
- [x] Exact seven-term sinc formula for the current kernel.
- [x] Exact finite formulas for the square and distance masses, reducing
  `H(window)` to the integral-free seven-by-seven expression `closedH`.
- [x] Ordinary entrywise Gram closeness implies the squared-energy block bound,
  with explicit loss `2 * err` and block loss `2 * m^2 * err`.
- [x] Concrete retained-matrix definitions `V` and `Q`, column bounds, exact
  matrix identity, normalized ordering/span, and retained-count domination.
- [x] Multi-root tree verifier, production-format decoder, integer objective,
  initialization/real-domain bridge, and exact pressure cutoff.
- [x] Recorded grid-4000 production topology: 324 roots, 1,739,356 nodes,
  869,516 splits, and 869,840 leaves.
- [x] Kernel-checked Taylor foundations for sine, cosine, sinc, `sqrt 2`, and
  `pi`, plus the first Boolean rational sine-cell checker.
- [x] Window endpoint bound `3/4 <= v(1/2)`.
- [x] Exact origin-cell monotonicity inequality; generated monotonicity data
  now starts at `1/16384` through `AwayMonotonicityTable`.
- [x] Tight rational endpoint bounds and the final compact numeric inequality
  underlying `ClosedHLower`.
- [x] Exact normalization of the 49-term closed masses and the strengthened
  strict certificate `67245701/10^8 <= H(window)`, hence
  `Hcert < H(window)`.
- [x] Exact-rational shadow replay of every non-tangent production leaf and
  every uncovered initialization cell at common dyadic precisions 48, 56,
  64, and 80 bits.

## Finite and numerical certificate

- [ ] Extend the rational sine/cosine-cell checker and weighted-sum combiner to
  the grouped seven-term derivative cells, then instantiate
  `AwayMonotonicityTable` for the current window.
- [x] Kernel-check `ClosedHLower` by normalizing the 49-term closed masses to
  the compact numeric inequality.
- [ ] Generate exact dyadic kernel and second-derivative table artifacts and
  prove `DyadicKernelTable.Sound` for the current closed kernel.
- [ ] Formalize exact convex-tangent/LDL leaf evidence for the 406,186
  tangent-pruned leaves. A tangent-free production rerun is currently
  impractical; three representative roots exceeded two million nodes each.
- [ ] Convert the compact tree, root boxes, table data, and tangent evidence to
  checked Lean values and prove the concrete `Forest.check = true` and
  `InitialRootEvidence` facts.
- [ ] Combine those facts into an inhabitant of
  `CurrentWindow.FiniteWindowInputs`.

The production checker must be heterogeneous: ordinary interval leaves use
the integer lower score, while tangent leaves prove the final real inequality
directly. `VerifiedAnnotatedForest` supplies this sound generic interface;
the remaining work is the semantic tangent witness and annotated artifact.

The compact topology and root-box artifacts are recorded. The 186 MB raw trace
is retained locally for certificate generation but is not intended as the
long-term Git artifact.

## Analytic instantiation

- [x] Prove the zeta-native exact matrix route for the coefficient family
  `c_N=-Lambda(N)`: `GpC=Gp`, eventual `Gz=GpC`, and the resulting trace
  transfer. This avoids the xi-prime `D1` specialization.
- [ ] Complete `CoeffMoments` for the zeta-native family `c_N=-Lambda(N)`,
  `D(s)=s`, using the current-window autocorrelation estimate. Show its
  endpoint constant is `c1(window)` and use the proved strict `H` margin to
  choose one fixed `lambda<1` with `kappa <= 2-Hcert`.
- [ ] Construct the central all-simple atom decomposition, prove its exact
  inertia/count seam, then compress to the retained interior subset and charge
  the deleted atoms explicitly as `o(N)`. `CurrentRetainedWithLoss` proves the
  generic positive-index and stability algebra; do not use the older exact
  post-deletion `DeletionSeam` as the end-to-end interface.
- [ ] Prove compact-uniform Gram convergence for the actual retained vectors,
  using ordinates scaled by `P.L T` (not the endpoint `l T` when
  `lambda<1`).
- [ ] Package the resulting moment, stability, Gram, span, and endpoint errors
  into `AsymptoticEntrywiseAnalyticInputs.errorsAreSmall`, including eventual
  `delta_small`.
- [ ] Instantiate the already-proved zeta and cumulative capstones and run the
  final adversarial theorem/axiom audit.

## Validation invariant

Every current-result module must build with no `sorry`, `admit`,
`native_decide`, `unsafe`, or new axioms. `PrintCurrentAxioms.lean` should show
only Lean/Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`
dependencies.

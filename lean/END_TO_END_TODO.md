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

## Finite and numerical certificate

- [ ] Extend the rational trig-cell checker from its first sine-cell slice to
  the grouped seven-term derivative cells, then instantiate
  `MonotonicityTable` for the current window.
- [ ] Prove the closed form for `windowDistanceMass`, reduce `H(window)` to a
  finite expression, and kernel-check `Hcert <= H(window)`.
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

The compact topology and root-box artifacts are recorded. The 186 MB raw trace
is retained locally for certificate generation but is not intended as the
long-term Git artifact.

## Analytic instantiation

- [ ] Choose and instantiate the current `Params`/coefficient family and prove
  the displayed current-window `ThmD.cRatio` limit.
- [ ] Instantiate `XiPrime.XiEF` and the required `XiPrime.Reexpansion` for the
  chosen current window/coefficient family.
- [ ] Construct the eventual retained family and prove the concrete
  `RetainedZeroData.DeletionSeam`: Hermitianity, the positive-index/inertia
  bound, and the count seam after deleting exceptional zeros.
- [ ] Prove `CompactUniformCurrentGram` for the actual retained evaluation
  vectors and the current normalized kernel.
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

# End-to-end Lean proof status

Last audited: 2026-08-12.

The analytic deduction and finite bookkeeping are kernel checked, but the
theorem about zeta zeros still awaits replay of its finite certificate. This
is the canonical checklist for removing the remaining theorem argument. An
item is complete only when the current window and constants are instantiated,
not merely when a generic interface exists.

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
  now starts at `1/4096` through `AwayMonotonicityTable`, matching the first
  four origin cells in the numerical verifier.
- [x] Uniform-grid coverage and endpoint handling for monotonicity; generated
  data now supplies only the finitely many derivative centre inequalities.
- [x] Semantic seven-sine centre rows: checked rational range reductions and
  Taylor errors now imply each uniform-grid derivative inequality.
- [x] A hybrid finite certificate can cover an initial interval using
  `v'' <= 0` cells and the remainder using `v' <= 0` cells, allowing a much
  smaller adaptive certificate than 8,188 uniform derivative rows.
- [x] Hybrid rows are fully semantic: rational cosine witnesses discharge the
  `v''` cells and rational sine witnesses discharge the `v'` cells.
- [x] A Boolean rational interval checker now proves every current-window
  frequency argument lies in its generated `k*pi` Taylor cell.
- [x] Tight rational endpoint bounds and the compact numeric inequality
  needed after normalizing the 49-term expression.
- [x] Exact-rational shadow replay of every non-tangent production leaf and
  every uncovered initialization cell at common dyadic precisions 48, 56,
  64, and 80 bits.
- [x] Zeta-native coefficient, autocorrelation, and trace-transfer route for
  `c_N=-Lambda(N), D(s)=s`, avoiding the xi-prime specialization.
- [x] Canonical all-simple central decomposition, positive-index/count loss,
  and ordinate-ordered central selection in the actual `P.L T` scale.
- [x] Global normalized infinite-kernel convergence with explicit error, plus
  an interior endpoint selection whose normalized Poisson tail tends to zero.
- [x] The extra endpoint deletion is `o(N)` and `o(NIprime)`; its ordered
  compression matrix is identified with the matching retained-zero matrix.
- [x] A Boolean rational sinc-jet checker and one fully checked delicate
  production row, plus the normalization bound
  `0.918707 <= sinc(sqrt 2/2) <= 0.918744`.
- [x] An eventual one-height interior Gram package: for every locally positive
  interior selection it combines the endpoint tail and infinite-kernel limit
  into explicit `EntrywiseGramData`, with no filler atoms or global positivity
  assumption.

## Finite and numerical certificate

- [x] Generate and kernel-check the compact hybrid monotonicity table. Its 32
  curvature cells cover `[0,1/8]`, its five derivative cells cover
  `[1/8,1/2]`, and exact rational sine/cosine witnesses imply the full global
  monotonicity and `WindowCertificate`.
- [x] Kernel-check the strict `Hcert < H(window)` endpoint inequality.  The
  scalable proof normalizes all 49 closed-mass entries, proves independent
  rational Taylor bounds, and derives the strengthened rational lower bound
  `67245701 / 10^8 <= closedH`.
- [ ] Generate exact dyadic kernel and second-derivative table artifacts and
  prove `DyadicKernelTable.Sound` for the current closed kernel.
- [ ] Formalize exact convex-tangent/LDL leaf evidence for the 406,186
  tangent-pruned leaves. A tangent-free production rerun is currently
  impractical; three representative roots exceeded two million nodes each.
  The generic sinc/sinc'/sinc'' checker, the `K,K',K'' -> w''` combiner, and
  the `K(0)` bound are complete.  All 14 actual production argument rows and
  their weighted composition are checked for cell 4376, yielding the exact
  recorded binary64 lower bound throughout that cell.
  The scalable ordinary-cell checker proves total sinc-jet bounds from Boolean
  rational witnesses, while a pole-free Taylor checker covers all 12 cells
  adjacent to the six removable periodic arguments.
- [x] Localize tangent semantics to the checked leaf, bind its objective to
  the actual current `F6`, and derive line continuity and both derivatives
  from the all-real total kernel derivative theorems.  The remaining producer
  facts are finite value/gradient enclosures and the exact 20-row Hessian
  comparison.
- [x] Connect the heterogeneous annotated forest and existing initialization
  bridge directly to `CurrentWindow.LocalCertificate`, with a convenience
  capstone accepting only the finite tangent producer facts.
- [x] Decode the strict `Z23ANN1` leaf-tagged topology format in Lean,
  resolving every 64-bit tangent payload index and validating the exact root,
  node, and tangent-leaf counts before replay.
- [ ] Convert the compact tree, root boxes, table data, and tangent evidence to
  checked Lean values and prove the concrete `Forest.check = true` and
  `InitialRootEvidence` facts.
- [ ] Combine those facts into `CurrentWindow.LocalCertificate`. The window
  half of `FiniteWindowInputs` is now unconditional.

The production checker must be heterogeneous: ordinary interval leaves use
the integer lower score, while tangent leaves prove the final real inequality
directly. `VerifiedAnnotatedForest` supplies this sound generic interface;
the remaining work is the semantic tangent witness and annotated artifact.

The compact topology and root-box artifacts are recorded. The 186 MB raw trace
is retained locally for certificate generation but is not intended as the
long-term Git artifact.

## Analytic instantiation

- [x] Prove the zeta-native exact matrix and moment route for
  `c_N=-Lambda(N), D(s)=s`, including the current-window autocorrelation
  estimate, `GpC=Gp`, eventual `Gz=GpC`, and trace transfer.
- [x] Prove `cWin id 1 window = c1(window)` and continuity below the endpoint;
  a strict endpoint `H` certificate then selects one fixed `lambda<1` with
  `kappa < 2-Hcert`.
- [x] Construct the central all-simple atom decomposition and exact lossy
  inertia/count seam, then define the ordered interior compression and charge
  its deletion as `o(NIprime)`.
- [x] Prove the actual-scale infinite-kernel limit and the uniform endpoint
  rho-tail bound for the interior family.  The coordinate is `P.L T`, not the
  obsolete endpoint `l T` coordinate.
- [x] Replace the all-heights positive-cardinality requirement with a sound
  eventual/one-height interface, and package the ordered interior rho-tail and
  matrix equality into concrete actual-scale `EntrywiseGramData` for every
  locally positive height.
- [x] Resolve local interior positivity non-circularly: the lossy stability
  seam and little-o moment/deletion errors force the interior cardinality to
  be positive eventually, before retained data or Gram bounds are constructed.
- [x] Discharge the concrete central `Az` moment/tail premise and rebase its
  count and error terms to `NIprime`, including both explicit trace and
  Frobenius little-o rates.
- [x] Package the moment, stability, Gram, span, endpoint, positivity, and
  deletion errors into the exact lossy finite records and final asymptotic
  target.  The analytic theorem now reduces cleanly to the concrete central
  `Az` moment premise with two little-o error rates.
- [x] Instantiate the zeta dyadic and cumulative capstones, discharge the
  strict endpoint inequality, and complete the window certificate. The
  strongest theorem now depends only on `CurrentWindow.LocalCertificate`.

## Validation invariant

Every current-result module must build with no `sorry`, `admit`,
`native_decide`, `unsafe`, or new axioms. `PrintCurrentAxioms.lean` should show
only Lean/Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`
dependencies.

# Proof-producing certificate prototype

`export_interval_tree.py` defines and validates a compact binary format that
mirrors the forest structure checked by
`lean/Zeta23Ext/VerifiedCertificateForest.lean`.  That Lean module now contains
an executable decoder and connection theorem specialized to the recorded
six-gap, 324-root, 1,739,356-node production layout.

This is proof-certificate infrastructure, not yet a complete kernel replay.
An instrumented Arb rerun has now exported the 1,739,356-node search forest
and root boxes. The run uses convex tangent pruning, so a complete Lean replay
still needs formal semantics for those leaf payloads. Formal lower bounds for
the two transcendental kernel tables remain another principal trust-boundary
theorem.

A production trace writes one gzip-compressed event stream per initial root,
so parallel workers never share an output file. Tangent-pruned leaves also get
per-root streams containing the box, rational midpoint/radius data, exact
floating-point Hessian coefficients, Arb LDL pivots, value/gradient intervals,
and the final Arb lower interval. Generate and assemble it with:

```bash
.venv/bin/zeta-ext-verify main --grid 4000 --workers 6 \
  --trace-dir certificates/weighted-p1-grid4000-trace
.venv/bin/python -m proof_certificate.export_interval_tree from-root-dir \
  certificates/weighted-p1-grid4000-trace \
  certificates/weighted-p1-grid4000.tree --q 6 --roots 324
```

The traced grid-4000 rerun produced:

- `certificates/weighted-p1-grid4000.tree` (SHA-256
  `fade5dc139b490d9a6d017c26546a72ea4553a1a2d9dbe7bc74aa2e38bdc5bc0`);
- `certificates/weighted-p1-grid4000.roots.json` (SHA-256
  `8e3a77ae54fa85becf4f17329a25fba15652692b24fb1bf160f3156c8a15947e`);
- a local `certificates/weighted-p1-grid4000-trace/`, containing the compressed
  per-root event and tangent-evidence streams. This 186 MiB raw trace is not
  committed to ordinary Git history.

The run exactly reproduced 1,739,356 nodes, 869,516 splits, 869,840 leaves,
the three pruning counts, and both table hashes in the recorded report. The
Lean decoder accepts the topology as a 324-root `ProductionForest`. Full leaf
replay remains conditional on exact dyadic table data and formal treatment of
the 406,186 tangent leaves.

A tangent-free sample is not competitive at this grid: roots 61, 182, and 74
each exceeded a 2,000,000-node cap (versus 67,427, 66,679, and 60,581 nodes
with tangent pruning), while root 0 completed at 16,443 nodes. No full
tangent-free rerun was launched.

Useful checks:

```bash
.venv/bin/python -m proof_certificate.export_interval_tree audit-report \
  certificates/weighted-p1-eps509-100000-grid4000.txt
.venv/bin/python -m proof_certificate.export_interval_tree demo /tmp/z23-demo.tree
```

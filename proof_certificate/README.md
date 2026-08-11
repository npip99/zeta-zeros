# Proof-producing certificate prototype

`export_interval_tree.py` defines and validates a compact binary format that
mirrors the tree structure checked by `lean/Zeta23Ext/VerifiedCertificate.lean`.
The Lean-side binary decoder and connection theorem have not yet been written.

This is infrastructure, not yet the production certificate. The existing Arb
run retained only aggregate counts, so an instrumented rerun is required to
export its 1,739,356-node search forest. Moreover, the current run uses convex
tangent pruning: a complete Lean replay must either export proof data for
those leaves or use a tangent-free rerun. Formal lower bounds for the two
transcendental kernel tables remain the principal trust-boundary theorem.

Useful checks:

```bash
python -m proof_certificate.export_interval_tree audit-report \
  certificates/weighted-p1-eps509-100000-grid4000.txt
python -m proof_certificate.export_interval_tree demo /tmp/z23-demo.tree
```

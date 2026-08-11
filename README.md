# A 67.3195% lower bound for simple zeros of the Riemann zeta function

This repository proves and reproducibly verifies

$$
\liminf_{T\to\infty}\frac{N_0^s(T,2T)}{N(T,2T)}
\;\ge\; 0.673195198901\ldots \;>\; \frac{673195}{10^6},
$$

where $N(T,2T)$ counts nontrivial zeros with multiplicity and $N_0^s(T,2T)$
counts simple zeros on the critical line.

**[Paper (PDF)](paper/main.pdf)** · [LaTeX source](paper/main.tex) · [Certificates](certificates/)

## Lineage

| Result | Bound |
| --- | ---: |
| Anthropic Theorem D ([paper](https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf)) | 0.672500703679… |
| [ainta/zeta-simple-zeros](https://github.com/ainta/zeta-simple-zeros) (stability refinement, 7-point certificate) | 0.673008527927… |
| [trmdy/zeta-simple-zeros-673137](https://github.com/trmdy/zeta-simple-zeros-673137) (re-optimized window, weighted 7-point, sharp square-root tail profile) | 0.673137630699… |
| **this repository** | **0.673195198901…** |

This work certifies a stronger constant in the weighted seven-point
inequality of trmdy/zeta-simple-zeros-673137: $F \ge 509/100000 = 0.00509$,
where $1/200 = 0.005$ was certified previously (the observed minimum of $F$
is $\approx 0.0050910$), and re-optimizes the block length to $m = 250$. The
window, pair weights, pressure, block profile, and deduction follow that
repository. The headline target is certified at grid $1/4000$ (1,739,356
nodes, depth 57, recorded in `certificates/`) and repeated at grid $1/8000$.
These are separate runs of the same implementation, not independent formal
proofs.

## Verify it yourself

Python ≥ 3.10; the only dependency is `python-flint` (ships Arb). With
[uv](https://docs.astral.sh/uv/):

```bash
uv venv .venv
uv pip install -e . --python .venv/bin/python

# window bounds, monotonicity, H(v), final arithmetic (Arb-certified)
.venv/bin/zeta-ext-verify fast

# the main certificate F >= 509/100000 (~10 min on 6-8 cores)
.venv/bin/zeta-ext-verify main --workers 8

# the previous-generation verifier (this repo's morning result, 67.30255%)
.venv/bin/zeta-zero-verify seven
```

Recorded runs are in [`certificates/`](certificates/). The verifier under
`src/zeta_ext/` is vendored (MIT) from
[trmdy/zeta-simple-zeros-673137](https://github.com/trmdy/zeta-simple-zeros-673137)
with the strengthened target, optimized block length, and an explicit window
monotonicity check; `src/zeta_simple_zeros/` is the
previous-generation verifier from
[ainta/zeta-simple-zeros](https://github.com/ainta/zeta-simple-zeros) with
this repository's tightened constants.

## Lean formalization

The pinned Lean 4 project under [`lean/`](lean/) checks the finite and
algebraic core of the `0.673195` deduction: the exact window constants and
21-weight table, the sharp square-root profile and realizing correlation
matrices, the large-span/small-span block split, pinching and offset
averaging, error bookkeeping, the final strict numerical comparison, and the
conditional dyadic-to-cumulative passage.

```bash
cd lean
lake update
lake exe cache get
lake build Zeta23Ext
lake env lean Zeta23Ext/PrintCurrentAxioms.lean
```

The capstone remains conditional, but the normalized-span error and its
pressure contribution are now discharged from the upstream unconditional
Riemann--von Mangoldt theorem. The remaining explicit hypotheses are the
full numeric window certificate and kernel-table/search soundness (including
the real-domain bridge and production-tree decoding), current-window
admissibility and squared-energy Gram asymptotics, and retained Gram/moment
construction with the remaining `o(N)` errors; see
[`CurrentAnalyticBridge`](lean/Zeta23Ext/CurrentAnalyticBridge.lean) and
[`VerifiedCertificate`](lean/Zeta23Ext/VerifiedCertificate.lean). The
repository does not claim these remaining external inputs have been replayed
in the Lean kernel. The Lean project pins the upstream base at an immutable
commit and retains Apache-2.0 licensing and attribution in
[`lean/LICENSE`](lean/LICENSE) and [`lean/NOTICE`](lean/NOTICE); the rest of
this repository remains MIT-licensed.

## Trust base

All new finite claims are certified by rigorous interval computation. Arb
encloses transcendental evaluations. The range-minimum path uses
outward-rounded binary64 lower bounds and directed-rounded nonnegative
arithmetic; the convex-tangent path uses Arb enclosures for signed
derivatives, gradients, and its LDL test. The committed certificates are
reproducibility records, not trusted inputs. The imported analytic inputs (explicit formula, arbitrary-
window trace asymptotics, tail bounds, Gram-entry asymptotics, and the
stability rank–trace layer) are identified precisely in §1 of the paper. The
paper also verifies that this particular ramped profile satisfies the cited
arbitrary-window hypotheses.

## References

- [Anthropic research article](https://www.anthropic.com/research/riemann-zeta)
- [Anthropic full paper](https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf)
- [ainta/zeta-simple-zeros](https://github.com/ainta/zeta-simple-zeros)
- [trmdy/zeta-simple-zeros-673137](https://github.com/trmdy/zeta-simple-zeros-673137)

## License

MIT, except for the Lean project under `lean/`, which retains its
Apache-2.0 license and notices.

# A 67.3188% lower bound for simple zeros of the Riemann zeta function

This repository proves and reproducibly verifies

$$
\liminf_{T\to\infty}\frac{N_0^s(T,2T)}{N(T,2T)}
\;\ge\; 0.673188803503\ldots \;>\; \frac{673188}{10^6},
$$

where $N(T,2T)$ counts nontrivial zeros with multiplicity and $N_0^s(T,2T)$
counts simple zeros on the critical line.

**[Paper (PDF)](paper/main.pdf)** · [LaTeX source](paper/main.tex) · [Certificates](certificates/)

## Lineage

| Result | Bound |
| --- | ---: |
| Anthropic Theorem D ([paper](https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf), [Lean artifact](https://github.com/anthropics/zeta-23-lean)) | 0.672500703679… |
| [ainta/zeta-simple-zeros](https://github.com/ainta/zeta-simple-zeros) (stability refinement, 7-point certificate) | 0.673008527927… |
| this repository, morning revision (tightened certificate, grid 8000) | 0.673025467453… |
| [trmdy/zeta-simple-zeros-673137](https://github.com/trmdy/zeta-simple-zeros-673137) (re-optimized window, weighted 7-point, sharp $\sqrt{\phantom{E}}$-tail profile) | 0.673137630699… |
| **this repository** | **0.673188803503…** |

The improvement over trmdy is a single change: their weighted seven-point
inequality is certified at the stronger target $F \ge 127/25000 = 0.00508$
(previously $1/200 = 0.005$; the observed minimum of $F$ is
$\approx 0.005091$), and the block length is re-optimized to $m = 251$.
Everything else — the 7-term window, the pair weights, the pressure
$1/2300$, the sharp block profile, and the deduction — is theirs, used
unchanged. Two independent runs of the identical interval decision procedure
certified the raised target.

## Verify it yourself

Python ≥ 3.10; the only dependency is `python-flint` (ships Arb). With
[uv](https://docs.astral.sh/uv/):

```bash
uv venv .venv
uv pip install -e . --python .venv/bin/python

# window bounds, H(v), final arithmetic (~1 min, Arb-certified)
.venv/bin/zeta-ext-verify fast

# the main certificate F >= 127/25000 (~8 min on 6-8 cores)
.venv/bin/zeta-ext-verify main --workers 8

# the previous-generation verifier (this repo's morning result, 67.30255%)
.venv/bin/zeta-zero-verify seven
```

Recorded runs are in [`certificates/`](certificates/). The verifier under
`src/zeta_ext/` is vendored (MIT) from
[trmdy/zeta-simple-zeros-673137](https://github.com/trmdy/zeta-simple-zeros-673137)
with only the design constants changed; `src/zeta_simple_zeros/` is the
previous-generation verifier from
[ainta/zeta-simple-zeros](https://github.com/ainta/zeta-simple-zeros) with
this repository's tightened constants.

## Lean 4 formalization

A Lean 4 formalization of the stability-defect framework, built on
[zeta-23-lean](https://github.com/anthropics/zeta-23-lean), is nearing
completion and will be added under `lean/`: the stability rank–trace lemma,
the aggregation/pinching layer, the kernel-limit asymptotics with explicit
errors, and a β-parametric capstone theorem — plus a kernel-checked 3-point
certificate and a coarse 7-point certificate in final verification. The
capstone takes the certified seven-point constant as its only hypothesis, so
the constants of this repository drop in mechanically.

## Trust base

All new finite claims are certified by Arb interval arithmetic over exact
rational inputs; the committed certificates are reproducibility records, not
trusted inputs. The imported analytic inputs (explicit formula, Gabor trace
asymptotics, tail bounds, Gram-entry asymptotics, and the stability
rank–trace layer) are those of the Anthropic paper/Lean artifact and of
ainta's artifact, independently audited in the trmdy campaign.

## References

- [Anthropic research article](https://www.anthropic.com/research/riemann-zeta)
- [Anthropic full paper](https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf)
- [Lean 4 artifact (zeta-23-lean)](https://github.com/anthropics/zeta-23-lean)
- [ainta/zeta-simple-zeros](https://github.com/ainta/zeta-simple-zeros)
- [trmdy/zeta-simple-zeros-673137](https://github.com/trmdy/zeta-simple-zeros-673137)

## License

MIT

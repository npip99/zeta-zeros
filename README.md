# A 67.30255% lower bound for simple zeros of the Riemann zeta function

This repository proves and reproducibly verifies

$$
\liminf_{T\to\infty}\frac{N_0^s(T,2T)}{N(T,2T)}
\ge \frac{267\cdot10^{9}\,H_{\mathrm{MT}}-5.32\cdot10^{8}}{266{,}001{,}357{,}363}
= 0.673025467453\ldots,
$$

where $N(T,2T)$ counts zeros of the Riemann zeta function with multiplicity,
$N_0^s(T,2T)$ counts simple zeros on the critical line, and
$H_{\mathrm{MT}} = \tfrac32-\tfrac1{\sqrt2}\cot\tfrac1{\sqrt2} = 0.6725007\ldots$
is the Montgomery–Taylor constant of Anthropic's Theorem D.

Credit: this work builds directly on
[ainta/zeta-simple-zeros](https://github.com/ainta/zeta-simple-zeros)
(the stability-defect argument and verifier) and on Anthropic's
[paper](https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf)
and [Lean 4 artifact](https://github.com/anthropics/zeta-23-lean) (Theorem D and
its analytic inputs).

**[Proof (PDF)](paper/riemann.pdf)** · [LaTeX source](paper/riemann.tex) · [Verifier](docs/verifier.md)

## Argument

The rank–trace step in the Anthropic paper uses the rank, inertia, and two
traces of a Hermitian matrix. Its equality case permits the vectors associated
with simple zeros to be mutually orthogonal. For the vectors produced by the
optimized test family, however, each inner product is determined by the
Montgomery–Taylor kernel at the difference of two zero ordinates — and seven
consecutive zeros have 21 pairwise differences determined by only six gaps. The
kernel's positive zero set is sum-free, so the differences cannot all sit at
kernel zeros. A stability refinement of the rank–trace inequality keeps the
resulting Gram-matrix defect, and a certified 7-point inequality

$$
F_6(g_1,\ldots,g_6)\ \ge\ \frac{3{,}826{,}217}{10^9}
$$

makes it quantitative (grid $1/8000$, exhaustive subdivision, Arb interval
arithmetic; the target is maximal on the $10^{-9}$ lattice at this grid — the
true minimum of $F_6$ is $\approx 0.0038262312$, attained near the alternating
gap pattern $(1.045, 1.977, 1.042, 1.986, 1.989, 1.046)$). Aggregating over
blocks of $m = 267$ consecutive zeros yields the bound.

See [`docs/proof.md`](docs/proof.md) for the deduction with exact constants and
[`paper/riemann.pdf`](paper/riemann.pdf) for the full proof.

A Lean 4 formalization of the extension, building on
[zeta-23-lean](https://github.com/anthropics/zeta-23-lean), is in progress and
will be added under `lean/`.

## Proof and verification

| Component | Contents |
| --- | --- |
| [`paper/riemann.pdf`](paper/riemann.pdf) ([source](paper/riemann.tex)) | Full proof and exact constants |
| Anthropic paper and [Lean artifact](https://github.com/anthropics/zeta-23-lean) | Theorem D, the optimized test family, the zero-side decomposition, and the prime-side trace estimates |
| [`docs/proof.md`](docs/proof.md) | Short web outline of the argument |
| [`docs/verifier.md`](docs/verifier.md) | Interval enclosures, subdivision algorithms, and trust base |
| [`src/`](src/) | Verifier source |
| [`certificates/three-point.txt`](certificates/three-point.txt) | Recorded 3-point verification |
| [`certificates/seven-point.txt`](certificates/seven-point.txt) | Recorded 7-point verification |

The verifier checks the two finite inequalities used by the argument. It
reconstructs every transcendental enclosure from the formulas on each run; the
committed certificates are reproducibility records, not trusted inputs.

## Run the verifier

Python 3.9 or later is required. With [uv](https://docs.astral.sh/uv/):

```bash
uv venv .venv
uv pip install -e . --python .venv/bin/python

# Fast 3-point verification
.venv/bin/zeta-zero-verify three

# Exhaustive 7-point verification; a couple of minutes
.venv/bin/zeta-zero-verify seven --progress-every 1000000
```

Run the tests with:

```bash
.venv/bin/python -m unittest discover -s tests -v
```

## Status

Research artifact. Independent verification and peer review are welcome.

## References

- [Anthropic research article](https://www.anthropic.com/research/riemann-zeta)
- [Anthropic full paper](https://www-cdn.anthropic.com/564f962e60643842f5fcb4a17c9dbc8f608f1c37.pdf)
- [Lean 4 artifact (zeta-23-lean)](https://github.com/anthropics/zeta-23-lean)
- [Original artifact (ainta/zeta-simple-zeros)](https://github.com/ainta/zeta-simple-zeros)

## License

MIT

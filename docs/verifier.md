# Verifier design

The current certificate code is under `src/zeta_ext/`. The older
`src/zeta_simple_zeros/` package is retained only as a regression gate.

## Fast checks

`zeta-ext-verify fast` uses 192-bit `python-flint`/Arb enclosures to verify:

- $3/4\le v\le1$ on an 8192-cell cover of $[0,1/2]$;
- $v'\le0$ there (using $v''<0$ on the four origin-adjacent cells and a
  direct enclosure of $v'$ elsewhere);
- $H(v)\ge672457/10^6$ from closed-form integrals;
- the final exact-radical deduction exceeds $673195/10^6$.

The output is recorded in `certificates/fast-parts-eps509.txt`.

## Weighted seven-point search

`zeta-ext-verify main --workers 8` proves
$F(g_1,\ldots,g_6)\ge509/100000$ for every nonnegative gap vector. It uses:

- one-body pruning from the nonnegative pressure and kernel terms;
- Arb enclosures for the normalized kernel and its derivatives on grid cells;
- outward conversion of Arb lower endpoints to binary64 for the nonnegative
  range-minimum path;
- a separate convex-tangent path using Arb enclosures for signed derivatives,
  gradients, and its LDL positivity test;
- exhaustive bisection of unresolved boxes;
- failure if any terminal cell remains unresolved.

The committed grid-$4000$ run has 1,739,356 nodes and depth 57. A second run
of the same implementation at grid $8000$ has 1,736,620 nodes and depth 57.
The second run is a resolution cross-check, not an independent implementation.

## Trust base

The finite verifier trusts Python, IEEE-754 binary64 semantics,
`python-flint`/Arb/FLINT, the operating system and hardware, and the short
source in this repository. It does not trust exploratory optimization, cached
tables, or committed run logs: those logs are reproducibility records, while
the program regenerates the bounds and fails on an unresolved cell.

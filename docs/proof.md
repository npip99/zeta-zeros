# Proof map and exact constants

The complete deduction is in [`paper/main.tex`](../paper/main.tex). This file
is only a map of the argument; it intentionally does not maintain a second,
potentially divergent proof.

## External analytic interface

The paper isolates two cited inputs:

1. normalized retained ordinates have total span at most $N(T,2T)+o(N)$,
   by the Riemann--von Mangoldt formula;
2. the arbitrary-window trace asymptotics of Claude, combined with ainta's
   stability refinement, give
   $$S\ge H(v)N+\operatorname{tr}\Psi(M)-o(N).$$

The paper verifies the applicability of the second input to the present
profile. The `fast` verifier proves $3/4\le v\le1$, $v'\le0$ on
$[0,1/2]$, and $H(v)\ge672457/10^6$. The monotonicity and the standard smooth
boundary ramp imply the required compact support, $C^2$ regularity, variation
bounds, and second-derivative estimates for both the taper and its square.

## New finite input

For six nonnegative gaps, the weighted seven-point functional in §4 of the
paper satisfies

$$
F(g_1,\ldots,g_6)\ge\varepsilon_0=\frac{509}{100000}.
$$

The exhaustive verifier establishes this at grids $1/4000$ and $1/8000$.
The two runs share an implementation and serve as a resolution cross-check.

## Deduction

The exact parameters are

$$
m=250,\qquad p=\frac1{2300},\qquad B_p=6p=\frac3{1150},
$$

$$
A=\varepsilon_0(m-6)=\frac{31049}{25000},\qquad
R=2\sqrt A-1,\qquad \eta=\frac RA.
$$

Summing the local inequality over seven-point windows gives, for every
$m$-point block,

$$
2\sum_{i<j}k_v(y_j-y_i)^2+B_p\operatorname{span}(B)\ge A.
$$

Blocks with span at least
$A/B_p=714127/1500$ are handled by the pressure term alone. On smaller
blocks, the Gram-entry asymptotic is uniform on a fixed compact interval and
converts the kernel energy to Gram energy with a uniform $o(1)$ error. The
sharp profile

$$
\operatorname{tr}\Psi(G)\ge h(E),\qquad
h(E)=\begin{cases}E,&E\le1,\\2\sqrt E-1,&E\ge1,
\end{cases}
$$

then gives a block defect of $R-o(1)$. Explicit shifted-block pinching and
span bookkeeping yield

$$
\operatorname{tr}\Psi(M)\ge
\frac RmS-\eta B_p\frac{m-1}{m}N-o(N).
$$

Substitution into the analytic interface gives

$$
\liminf_{T\to\infty}\frac{S}{N}
\ge\frac{mH_{\rm cert}-\eta B_p(m-1)}{m-R}
=0.6731951989015205755\ldots>
\frac{673195}{10^6}.
$$

The `fast` verifier encloses the final arithmetic directly.

# igusa-special results log

Task: special half of T28 (`det (yv f) = 0`), interface `T28.SeparationBothSpecial`
(ZInQKernel/Contrib/T28/Generic.lean, task igusa-generic), assuming `T28.YvCovariance` (to be
proved by igusa-generic in Contrib/T28/Covariance.lean).

Tools: no sympy/PARI on this host (`~/pyenv` missing, no network); `poly.py` is a pure-python
sparse polynomial library over Q that parses the Lean definitions `y?c?`, `J2..J6`, `j10Data`.

## Computations (VERIFIED, exact arithmetic, `python3 -I scratch/igusa-special/t*.py`)

- t2/t4: for `N = x(x-1)(x-l)(x-m)(x-n)` (sextic with roots `∞,0,1,l,m,n`),
  `det yv(N) = (1/384433593750) · ∏_{15 synthemes s} D_s`, `D_s = det` of the coefficient
  vectors of the three quadratics of `s` (4 random rational points; then as a polynomial identity
  in `e1,e2,e3`, see next item).
- t4: in the elementary symmetric functions `e1,e2,e3` of `l,m,n` (`Ne e1 e2 e3` =
  `![0, e3, -(e2+e3), e1+e2, -(1+e1), 1, 0]`): `det yv(Ne) = C·T1·T2·T3·T4`, `C = 1/384433593750`,
  `T_c` = product of `D_s` over the S3-orbit `c` of synthemes, written in `e`'s
  (6, 9, 9, 41 terms). Classes and representatives `D_s` (in `l,m,n`):
  1. `(∞0)(1l)(mn)`, 3 synthemes, `D = mn - l`;
  2. `(∞1)(0l)(mn)`, 3, `D = l - m - n + mn`;
  3. `(∞l)(01)(mn)`, 3, `D = l - lm - ln + mn`;
  4. `(∞l)(0m)(1n)`, 6, `D = lm - l - ln + n`.
  Sizes: `yv(Ne)` entries 11/33/73 terms, `det yv(Ne)` 380 terms.
- t5/t6: on `E(a,b) = x⁶ + a x⁴ + b x² + 1` (vector `![1,0,b,0,a,0,1]`), with `u = ab`,
  `v = a³+b³`: `J2 = -32u - 480`, `J4 = -128v + 32u² + 2624u + 5280`,
  `J6 = 128·J4 - 131072(3u+5)`,
  `J10 = -262144(v²-2u³) + 131072u²v - 16384u⁴ + 2359296uv - 1114112u³ - 3538944v - 4423680u²
  + 15925248u - 11943936`.
- t6/t8: if `J(E(a',b')) = r·J(E(a,b))` (weights 1,2,3,5), then with `s = u+15`:
  `u' + 15 = r s`; `128(1-r)·E3 = h6 - 128 h4 - 12288 h2` where
  `E3 = r²J4(u,v) - 1024(3rs(1+r) - 40(1+r+r²))`; and, eliminating `v, u', v'`,
  the `J10` equation becomes `G = -2^38 r⁴ (1-r)³ (r²u² - 2r(16+r)u + (16-r)²)`.
  So `r = 1` (then `(u',v') = (u,v)`) or `ru = (4∓√r)²`, i.e. `u = t²`, `r = 16/(1+t)²`:
  the D4 sub-family `a = b = t` up to the order-6 group, with the second involution class giving
  `t' = (15-t)/(1+t)`: `(1-X)⁶E(t,t)((1+X)/(1-X)) = 2(1+t)·E(t',t')` (hand computation).

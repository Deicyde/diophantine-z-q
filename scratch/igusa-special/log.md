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

## Lean (VERIFIED, `lake env lean`)

- `ZInQKernel/Contrib/T28/Special/Family.lean`: compiles (~10 s). `Eqv` (equivalence via `actC`)
  with refl/symm/trans, `Eqv.J` (transformation law), `J*_E`, `fam_alg`, `E_rot`, `E_swap`,
  `E_orbit`, `E_D4`, `E_sep` (separation in the family, weighted equality of invariants).
- `ZInQKernel/Contrib/T28/Special/Bolza.lean`: compiles (2m55). `det_yv_Ne`, `det_yv_Nr`
  (product over the 15 synthemes), `J10_Nr = 256·disc`, `J10_zero_56`, `J10_zero_01`,
  `even_to_E`, `inv_E`, `cls1_E … cls4_E`, `special_Nr`.
- t14.py: `T_c(e(l,m,n)) = ∏` of `D_c` over the listed permutations (ratio 1 for all four
  classes); `J10(Nr l m n) = 256 ∏ (differences of ∞-free roots)²`.
- `ZInQKernel/Contrib/T28/Special/NormalForm.lean`: compiles (~7 s). `root2…root6`,
  `cubic_split`, `step_inf`, `step_zero`, `step_one`, `exists_Nr`.
- `ZInQKernel/Contrib/T28/Special.lean`: compiles (~5 s). `Eqv.det_yv` (from igusa-generic's
  `T28.det_yv_actC`), `special_to_E`, `separationBothSpecial : T28.SeparationBothSpecial`.
- `ZInQKernel/Contrib/T28/Assemble.lean`: compiles. `T28.igusaClebschSeparation_proved :
  PkgI1.IgusaClebschSeparation` (leaf T28), `T28.igusaSeparationEq_proved`,
  `T28.separationSpecial_proved : PkgI1.SeparationSpecial`.
- `lake build ZInQKernel.Contrib.T28.Assemble`: success (after merging origin/main 6c225515 and
  wip/igusa-generic 73bbe461). `scratch/igusa-special/Axioms.lean`: every theorem listed there
  depends only on `[propext, Classical.choice, Quot.sound]`.
- `diffcheck2.py`: MOD-UNNOTED 0, NOTE-ONLY 0 (no vendored file touched).

## Notes

- `ring` in a `Field` without `[CharZero K]` cannot cancel numeral inverses (first attempt of
  `y1c0_Ne` failed); all `y?c?` identities need `[CharZero K]`.
- One-shot `ring` for `det yv (Ne …)` (unfolding all 86-term `y3` chunks inside the 3×3
  determinant) passed 8.7 GB after 8 min (stopped); staging (`y?c?_Ne` first, 11/33/73-term
  results, then the determinant) takes 2m22 in total.
- `ring` as a `first | ring | …` alternative never fails (falls back to `ring_nf`); use `ring1`.

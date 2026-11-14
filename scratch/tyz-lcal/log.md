# tyz-lcal results log

Task: the three L-leaves `TYZThm11Integral`, `TYZLcalOne`, `TYZLemma29Mod2`
(`ZInQKernel/Contrib/TYZDecomp/Leaves.lean`). TYZ source not on this host.

## Environment (2026-11-13 22:45 PST)
- No PARI/cypari2, sympy or mpmath on this host (`~/pyenv` absent, uv offline cache lacks them): numerics in
  pure Python 3 (`lcal_check.py`).
- `lake build ZInQKernel.Contrib.TYZDecomp.Leaves ZInQKernel.Contrib.HeckeAll.Provider`: success (VERIFIED).

## N1. Numerical audit (`lcal_check.py`, output `out_lcal_check.txt`), first 30 squarefree m = 1,3 (mod 8), m <= 155
- omegaInt = 2.622057554292 by quadrature and by pi/AGM(1, sqrt 2) (lemniscate constant) (VERIFIED, computed).
- L(C_m, 1) by 2 sum a_n/n exp(-2 pi n/sqrt(32 m^2)) (root number +1), a_n from point counts + twist.
- lcalSq(m) = L/(2^{2k-3} (2/sqrt m) omegaInt) is an integer square to <= 4e-15 for all 30 (VERIFIED):
  values 1 (most), 4 (17, 73, 89, 97, 155), 9 (43, 107, 131), 16 (113), 0 (41, 65, 137, 145).
  lcalSq(1) = 1 (L(C_1,1) = 0.6555143886 = omegaInt/4).
- LemmaTwoEight (both halves, m > 1) holds mod 2 for ell = sqrt(lcalSq), g = h/2^{t-1} by reduced forms:
  29/29 ok (VERIFIED, computed).
- Tunnell cross-check: |ell(m)| = |a_T(m)| / 2^k for all 30, a_T = coefficients of eta(8z)eta(16z)theta(2z)
  (VERIFIED, computed). I.e. TYZ's normalisation of lcal agrees with Tunnell's L(E_m,1) = omegaInt a_T(m)^2/(4 sqrt m)
  (Tunnell's formula as recalled; reference Invent. Math. 72 (1983) 323-334, statement UNVERIFIED from memory).

## L1. `TYZLcal.lean` part 1 (compiled, `lake env lean`, no errors, 2026-11-13 22:52)
- `gCl_three : gCl 3 = 1`, `gNat_three : gNat 3 = 1` (QNeg 3 is `IsCyclotomicExtension {3} ℚ` via
  zeta3 = ⟨-1/2, 1/2⟩; Mathlib `IsCyclotomicExtension.Rat.three_pid`; `card_classGroup_eq_one_iff`). VERIFIED.
- `lcalSq_one : lcalSq 1 = lValOne 1 / (omegaInt / 4)`. VERIFIED.
- `ell_one_odd (h11) (h29) : (a:ℂ)^2 = lcalSq 1 → Odd a` (LemmaTwoEight second half at m = 3). VERIFIED.
- `LValOneBound : Prop := ‖lValOne 1‖ < 9/4 * omegaInt` (glue, numerical).
- `lcalOne_of_leaves (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hB : LValOneBound) : TYZLcalOne`. VERIFIED.

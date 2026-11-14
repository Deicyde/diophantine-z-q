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

## L2. `TYZLcal.lean` complete (single file; `LBound.lean` draft merged and removed). Compiled 2026-11-13 23:07,
`lake env lean scratch/tyz-lcal/TYZLcal.lean`: no errors, no sorry. `#print axioms` of the ten main declarations:
`[propext, Classical.choice, Quot.sound]` (VERIFIED).
- `gaussLambda_one_eq : Λ_{a,b}(1) = ∫_{Ioi 1} θ_{a,b} + ∫_{Ioi 1} θ^dual_{a,b}` (mellin split, `mellin_comp_inv`).
- `norm_integral_Ioi_one_le`: ‖f‖ ≤ C e^{-c(x-1)} on (1,∞) ⇒ ‖∫_{Ioi 1} f‖ ≤ C/c.
- `isLContinuation_Fone : IsLContinuation (curveC 1) (Fexp 4 cU)` (explicit Hecke continuation; DeuringCd 1 from
  `GaussFE.gaussPointCount`; `LSeries_cd_eq`).
- `lValOne_one_eq : lValOne 1 = Σ_{j ∈ (Fin 4)²} cU(j) · ¼ · π · Λ_{j/4}(1)`.
- exp bounds: e^{-π} ≤ 1/20, e^{-π/4} ≤ 0.48, e^{-π/16} ≤ 0.83, e^{-9π/16} ≤ 0.18, e^{-3π/2} ≤ 1/50, e^{-5π/2} ≤ 1/1000.
- kernel majorants for x ≥ 1: |oddKernel(1/4)| ≤ 0.37 e^{-π(x-1)/16}; |evenKernel 0|, |evenKernel ½|, |cosKernel b| ≤ 1.11;
  |sinKernel a| ≤ 0.112 e^{-π(x-1)}.
- `norm_gaussLambda_le_A/B : ‖Λ_{a,b}(1)‖ ≤ 6.7/π` on the eight classes with unitOf ≠ 0.
- `norm_lValOne_one_le : ‖lValOne 1‖ ≤ 3.35` (true value 0.6555). `omegaInt_ge_two : 2 ≤ omegaInt`.
- `lValOneBound : LValOneBound` (3.35 < 4.5 ≤ 9/4·omegaInt).
- **`tyzLcalOne_of_leaves (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) : TYZLcalOne`**.
- `tyzThm35ReadingA_of_three_leaves (h11) (h29) (hG : TYZGenusPackage) : TYZThm35ReadingA`.
- `genusPackage_iff_readingA_of_two (h11) (h29) : TYZGenusPackage ↔ TYZThm35ReadingA`.

## L3. §9 sign independence (compiled 23:15, same file, standard axioms)
- `lemmaTwoEight_congr`: LemmaTwoEight ℓ → LemmaTwoEight ℓ' if ℓ ≡ ℓ' (mod 2) on squarefree classes 1, 3.
- `parity_eq_of_sq`, `lemma29Mod2_iff (h11) : TYZLemma29Mod2 ↔ LemmaTwoEight (ellOf h11)`. VERIFIED.

## F. Findings on the three statements
- F1 `TYZThm11Integral`: a consequence of TYZ Theorem 1.1 (integrality) on odd n ≡ 1,3, n = 1 included (Theorem 1.1
  covers n = 1, nt-tyz §1.2). Normalisation 2^{2k-3}, Ω_m = (2/√m)∫ pinned numerically: integer squares on 30 inputs,
  agreeing with Tunnell (|𝓛| = |a_T|/2^k) and with rv-pn-encoding's Tunnell check (A−2B)/2^{k+1}. Over Mathlib's
  L-series = true L(C_m,s) (HeckeAll/LocalCd: model minimal everywhere, additive at p | 2m). Not stronger. Genuinely TYZ.
- F2 `TYZLcalOne`: NOT an independent leaf: `tyzLcalOne_of_leaves` derives it from F1 (m = 1, 3) and F3 (m = 3).
- F3 `TYZLemma29Mod2`: consequence of TYZ Lemma 2.9 + Prop 2.3 mod 2; at m = 3 the printed Lemma 2.9 and Theorem 2.1
  differ by w_K = 3 (rv-nt-tyz B1) — odd, so the mod-2 leaf holds under either. Universal ℓ immaterial
  (`lemma29Mod2_iff`). Genuinely TYZ (L-values mod 2 vs class numbers); no reduction from definitions/PSide found:
  PSide's results are about a_p, which do not determine L(C_m,1) mod 2 without the Waldspurger input.
- tyzLcalOne_of_leaves' (h11) (h11b : TYZThm11Mod2) : TYZLcalOne (compiled 23:20).

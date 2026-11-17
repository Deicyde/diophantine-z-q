import ZInQKernel.Contrib.OneProof.H.TailZ19

/-! theta-direct: copied verbatim from origin/wip/theta-fold (8e3dbdea) `ZInQKernel/Contrib/OneProof/LinYangSplit.lean`;
   only the import lines are changed (this base has no theta-fold modules). -/

/-! # theta-fold (2/4): theta-split's reduction of `ThetaRatiosAtQM` to symmetric functions of `θ⁸`

theta-split's scratch/theta-split/ThetaUse.lean §2-§7 (verbatim through igusa-alg and linyang-printed). Its §1
(`ThetaRatiosAtQM`, `thetaPointOfFibre_of_qm_atQM`) is in `ZInQKernel/Contrib/OneProof/H/TailK.lean`, where the chain's
consumer `gluePieces_of_open4` uses it. docs/research/theta-fold.md. -/

noncomputable section

namespace HDec.HSyn.G0Split.ThetaPt.ThetaSplit

open CategoryTheory AlgebraicGeometry Limits
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open _root_.ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst
  absLogHeight)
open Complex Polynomial

/-! ## 2. Reduction to symmetric functions of `θ⁸` along the curve -/

/-- The multiset of the ten `θ_m(Ω)⁸`, `m` even (pkg-I1's theta constants). -/
def thetaEight (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Multiset ℂ :=
  PkgI1.evenChars.val.map (fun m => PkgI1.thetaConst m Ω ^ 8)

theorem card_thetaEight (Ω : Matrix (Fin 2) (Fin 2) ℂ) : (thetaEight Ω).card = 10 := by
  rw [thetaEight, Multiset.card_map, Finset.card_val, PkgI1.card_evenChars]

/-- **GLUE (symmetric functions of the even `θ⁸` along the QM curve are rational in `j_θ`).** There
are `R_0, …, R_10 ∈ ℚ[X]` such that for every `τ` in the upper half-plane with `Σ_m θ_m(Ω(τ))⁸ ≠ 0`,
the `k`-th elementary symmetric function of the ten `θ_m(Ω(τ))⁸` (`m` even) is
`R_k(j_θ(Ω(τ)))·(Σ_m θ_m(Ω(τ))⁸)^k`.

Why true (model argument, no human review; locators UNVERIFIED): `e_k(θ_m⁸)` is a Siegel modular form of
weight `4k` for `Sp₄(ℤ)` (the theta transformation formula permutes the `θ_m⁸` with the common factor
`det(CΩ+D)⁴`; Igusa, *Theta functions*, 1972, Ch. V), with rational Fourier coefficients, hence a
polynomial over `ℚ` in Igusa's `ψ₄, ψ₆, χ₁₀, χ₁₂` (Igusa, Amer. J. Math. 84 (1962), 86 (1964)); along the
QM curve `[ψ₄ : ψ₆ : 2¹²3⁵χ₁₀ : 2¹²3⁶χ₁₂] = [j : j² : j³ : j³(j+1)]` weighted-projectively (Lin–Yang,
arXiv:1807.00466v1, Example 29; Baba–Granath, Canad. J. Math. 60 (2008), Prop. 3.6; the manuscript's F1
input, as restated in scratch/h-v14/igusa_check.py), and `ψ₄ = Σθ⁸/4`. This needs the same identification
of `τ ↦ Ω(τ)` with the QM locus as F1 (`FibreQMPeriod`, `PkgI1.QMHauptmodul`). The explicit
`R_k` are in `qmR` (`QMThetaSymmetricCore`). -/
def QMThetaSymmetric : Prop :=
  ∃ R : ℕ → Polynomial ℚ, ∀ τ : ℂ, 0 < τ.im → PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 →
    ∀ k ≤ 10, (thetaEight (PkgI1.Omega τ)).esymm k =
      Polynomial.aeval (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)) (R k) *
        PkgI1.thetaSum8 (PkgI1.Omega τ) ^ k

/-- A root of a monic polynomial over `ℂ` whose elementary symmetric functions are rational is
algebraic (Vieta + lifting of monic polynomials). -/
theorem isAlgebraic_of_esymm (s : Multiset ℂ) (r : ℕ → ℚ)
    (hs : ∀ k ≤ Multiset.card s, s.esymm k = (r k : ℂ)) {y : ℂ} (hy : y ∈ s) :
    IsAlgebraic ℚ y := by
  have hmon : (s.map (fun t => X - C t)).prod.Monic :=
    monic_multiset_prod_of_monic _ _ (fun t _ => monic_X_sub_C t)
  have hlift : (s.map (fun t => X - C t)).prod ∈ lifts (algebraMap ℚ ℂ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ Multiset.card s
    · rw [Multiset.prod_X_sub_C_coeff s hn, hs _ (Nat.sub_le _ _)]
      exact ⟨(-1) ^ (Multiset.card s - n) * r (Multiset.card s - n), by simp⟩
    · rw [coeff_eq_zero_of_natDegree_lt]
      · exact ⟨0, by simp⟩
      · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hlift hmon
  refine ⟨Q, hQm.ne_zero, ?_⟩
  rw [aeval_def, eval₂_eq_eval_map, hQ, eval_multiset_prod]
  apply Multiset.prod_eq_zero
  rw [Multiset.map_map]
  exact Multiset.mem_map.mpr ⟨y, hy, by simp⟩

theorem zero_mem_evenChars : ((0, 0) : Char2) ∈ PkgI1.evenChars := by decide

theorem isOddChar_of_not_even {m : Char2} (hm : m ∉ PkgI1.evenChars) : IsOddChar m := by
  unfold IsOddChar
  simp only [PkgI1.evenChars, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  omega

/-- **The use form from the symmetric-function glue (proved).** With `S = Σθ_m⁸ ≠ 0` (from
`jDen ≠ 0`), each `θ_m⁸/S` is a root of `∏_m (X − θ_m⁸/S)`, whose coefficients `±e_k/S^k = ±R_k(q)`
are rational; `θ_{(0,0)} ≠ 0` (from `jNum ≠ 0`), so `(θ_m/θ_{(0,0)})⁸` is algebraic; odd `θ_m` vanish. -/
theorem thetaRatiosAtQM_of_symmetric (h : QMThetaSymmetric) : ThetaRatiosAtQM := by
  obtain ⟨R, hR⟩ := h
  intro τ hτ q hq hJ
  have hDen : PkgI1.jDen (PkgI1.Omega τ) ≠ 0 := by
    intro h0; rw [h0, div_zero] at hJ; exact hq (by exact_mod_cast hJ.symm)
  have hNum : PkgI1.jNum (PkgI1.Omega τ) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hJ; exact hq (by exact_mod_cast hJ.symm)
  have hS : PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 := by
    intro h0; apply hDen; rw [PkgI1.jDen, h0]; ring
  have hProd : PkgI1.thetaProd2 (PkgI1.Omega τ) ≠ 0 := by
    intro h0; apply hNum; rw [PkgI1.jNum, h0]; ring
  set S := PkgI1.thetaSum8 (PkgI1.Omega τ) with hSdef
  -- conversion to pkg-I1's theta constants
  have hconv : ∀ m, thetaConst (BPAnalytic.QM.Omega τ) m = PkgI1.thetaConst m (PkgI1.Omega τ) :=
    fun m => by rw [thetaConst_eq_pkgI1, omega_eq]
  have h00 : PkgI1.thetaConst (0, 0) (PkgI1.Omega τ) ≠ 0 := by
    have := (Finset.prod_ne_zero_iff.mp hProd) _ zero_mem_evenChars
    exact fun h0 => this (by rw [h0]; ring)
  -- the scaled multiset has rational elementary symmetric functions
  set s' := (thetaEight (PkgI1.Omega τ)).map (fun t => S⁻¹ • t) with hs'
  have hcard : Multiset.card s' = 10 := by rw [hs', Multiset.card_map, card_thetaEight]
  have hesymm : ∀ k ≤ Multiset.card s', s'.esymm k = ((Polynomial.eval q (R k) : ℚ) : ℂ) := by
    intro k hk
    rw [hcard] at hk
    rw [hs', ← Multiset.pow_smul_esymm, hR τ hτ hS k hk, hJ, smul_eq_mul]
    have : Polynomial.aeval (q : ℂ) (R k) = ((Polynomial.eval q (R k) : ℚ) : ℂ) := by
      rw [← map_ratCast (algebraMap ℚ ℂ) q, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      simp
    rw [this, inv_pow, ← mul_assoc, mul_comm _ ((Polynomial.eval q (R k) : ℚ) : ℂ), mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hS), mul_one]
  have halg8 : ∀ m ∈ PkgI1.evenChars, IsAlgebraic ℚ (S⁻¹ * PkgI1.thetaConst m (PkgI1.Omega τ) ^ 8) :=
    fun m hm => isAlgebraic_of_esymm s' _ hesymm
      (Multiset.mem_map.mpr ⟨_, Multiset.mem_map.mpr ⟨m, hm, rfl⟩, rfl⟩)
  refine ⟨(0, 0), by rw [hconv]; exact h00, fun m => ?_⟩
  rw [hconv, hconv]
  by_cases hm : m ∈ PkgI1.evenChars
  · apply IsAlgebraic.of_pow (n := 8) (by norm_num)
    have : (PkgI1.thetaConst m (PkgI1.Omega τ) / PkgI1.thetaConst (0, 0) (PkgI1.Omega τ)) ^ 8 =
        (S⁻¹ * PkgI1.thetaConst m (PkgI1.Omega τ) ^ 8) *
          (S⁻¹ * PkgI1.thetaConst (0, 0) (PkgI1.Omega τ) ^ 8)⁻¹ := by
      field_simp
    rw [this]
    exact (halg8 m hm).mul (halg8 _ zero_mem_evenChars).inv
  · have h0 : PkgI1.thetaConst m (PkgI1.Omega τ) = 0 := by
      rw [← hconv]; exact thetaConst_odd _ m (isOddChar_of_not_even hm)
    rw [h0, zero_div]
    exact isAlgebraic_zero

/-! ## 3. The explicit polynomials -/

/-- The polynomials `R_k` (`py/fit_hp.py`, 80-digit numerics; rational reconstruction with residual
`≤ 5·10⁻⁷⁵` at independent points): `E_k/E_1^k = R_k(j)` along the QM curve. -/
def qmR : ℕ → Polynomial ℚ
  | 0 => 1
  | 1 => 1
  | 2 => C (3 / 8)
  | 3 => C (283 / 3888) + C (1 / 972) * X
  | 4 => C (1529 / 186624) - C (1 / 1458) * X
  | 5 => C (13 / 23328) + C (17 / 314928) * X
  | 6 => C (521 / 22674816) + C (95 / 5668704) * X + C (1 / 2834352) * X ^ 2
  | 7 => C (19 / 34012224) + C (313 / 272097792) * X - C (1 / 2834352) * X ^ 2
  | 8 => C (1 / 136048896) + C (107 / 3673320192) * X + C (49 / 1836660096) * X ^ 2
  | 9 => C (1 / 24794911296) * (1 + C (9 / 8) * X + C (1 / 4) * X ^ 2 + X ^ 3)
  | 10 => C (1 / 14281868906496) * X ^ 2
  | _ => 0

/-- **GLUE (explicit form of `QMThetaSymmetric`, `2 ≤ k ≤ 9`; numerically VERIFIED, not proved).**
For `τ` in the upper half-plane with `Σθ_m(Ω(τ))⁸ ≠ 0` and `2 ≤ k ≤ 9`:
`e_k(θ_m(Ω(τ))⁸) = R_k(j_θ(Ω(τ)))·(Σθ_m(Ω(τ))⁸)^k` with the explicit `R_k = qmR k`. For `k = 2` this is
the global Siegel identity `Σθ_m¹⁶ = (Σθ_m⁸)²/4` (weight 8 has dimension 1; Igusa 1964, UNVERIFIED);
for `3 ≤ k ≤ 9` it is the restriction to the QM curve of Igusa's expressions of `e_k(θ⁸)` with
Lin–Yang's vector (see `QMThetaSymmetric`); `k = 3` was cross-checked against Lin–Yang's vector
(`py/lycheck.py`). Checked numerically at 30 points (`py/verify.py`). -/
def QMThetaSymmetricCore : Prop :=
  ∀ τ : ℂ, 0 < τ.im → PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 → ∀ k, 2 ≤ k → k ≤ 9 →
    (thetaEight (PkgI1.Omega τ)).esymm k =
      Polynomial.aeval (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)) (qmR k) *
        PkgI1.thetaSum8 (PkgI1.Omega τ) ^ k

/-- `k = 1`: `e_1 = Σθ⁸` (definition). -/
theorem esymm_one (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    (thetaEight Ω).esymm 1 = PkgI1.thetaSum8 Ω := by
  rw [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
  simp only [Function.comp_def, Multiset.prod_singleton, Multiset.map_id']
  rw [thetaEight, Finset.sum_map_val]
  rfl

/-- `k = 10`: `e_10 = ∏θ⁸ = j²S¹⁰/3779136²` when `S ≠ 0` (definitions of `jNum`, `jDen`). -/
theorem esymm_ten (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hS : PkgI1.thetaSum8 Ω ≠ 0) :
    (thetaEight Ω).esymm 10 =
      (1 / 14281868906496 : ℂ) * (PkgI1.jNum Ω / PkgI1.jDen Ω) ^ 2 * PkgI1.thetaSum8 Ω ^ 10 := by
  have hcard := card_thetaEight Ω
  have hprod : (thetaEight Ω).esymm 10 = (thetaEight Ω).prod := by
    rw [← hcard, Multiset.esymm, Multiset.powersetCard_self, Multiset.map_singleton,
      Multiset.sum_singleton]
  have hprodP : (thetaEight Ω).prod = PkgI1.thetaProd2 Ω ^ 4 := by
    rw [thetaEight, Finset.prod_map_val, PkgI1.thetaProd2, ← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun m _ => by ring)
  rw [hprod, hprodP, PkgI1.jNum, PkgI1.jDen]
  field_simp
  ring

/-- The explicit identities for all `k ≤ 10` from the core (`k = 0, 1, 10` are identities). -/
theorem qmR_identity (h : QMThetaSymmetricCore) (τ : ℂ) (hτ : 0 < τ.im)
    (hS : PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0) (k : ℕ) (hk : k ≤ 10) :
    (thetaEight (PkgI1.Omega τ)).esymm k =
      Polynomial.aeval (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)) (qmR k) *
        PkgI1.thetaSum8 (PkgI1.Omega τ) ^ k := by
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · interval_cases k
    · simp [qmR]
    · simp [qmR, esymm_one]
  · rcases Nat.lt_or_ge k 10 with h10 | h10
    · exact h τ hτ hS k h2 (by omega)
    · obtain rfl : k = 10 := by omega
      rw [esymm_ten _ hS]
      simp [qmR]

/-- **`QMThetaSymmetric` from the explicit core (proved):** `R = qmR`. -/
theorem qmThetaSymmetric_of_core (h : QMThetaSymmetricCore) : QMThetaSymmetric :=
  ⟨qmR, qmR_identity h⟩

/-! ## 4. Summary -/

/-- **`ThetaPointOfFibre` from `FibreQMPeriod` and the explicit core (proved).** -/
theorem thetaPointOfFibre_of_qm_core (hQM : FibreQMPeriod) (h : QMThetaSymmetricCore) :
    ThetaPointOfFibre :=
  thetaPointOfFibre_of_qm_atQM hQM (thetaRatiosAtQM_of_symmetric (qmThetaSymmetric_of_core h))


/-! theta-split's §5 (Route 2: Shimura's CM theorem and interpolation) and §6 (the CM nodes) are not needed by the
fold and are not copied (scratch/linyang-printed/LinYangPrintedFull.lean keeps them). -/

/-! ## 7. Splitting off the global identity `k = 2`

`e_2(θ⁸) = (3/8)(Σθ⁸)²` is the global identity `Σθ_m¹⁶ = (Σθ_m⁸)²/4` on all of `𝔥₂`; the content of the
core that is specific to the QM curve is `3 ≤ k ≤ 9`. -/

theorem esymm_one' (s : Multiset ℂ) : s.esymm 1 = s.sum := by
  rw [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
  simp

theorem esymm_cons_succ (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

theorem two_esymm_two (s : Multiset ℂ) : 2 * s.esymm 2 = s.sum ^ 2 - (s.map (· ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [esymm_cons_succ, esymm_one', Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
    linear_combination ih

/-- **GLUE (global Siegel identity in genus 2; numerically VERIFIED).** For every `Ω ∈ 𝔥₂`,
`Σ_{m even} θ_m(Ω)¹⁶ = (Σ_{m even} θ_m(Ω)⁸)²/4`. Derivation (locators UNVERIFIED): both sides are Siegel
modular forms of weight 8 for `Sp₄(ℤ)` (the theta transformation formula permutes the `θ_m⁸` with the factor
`det(CΩ+D)⁴`), the space of such forms is `ℂ·ψ₄²` (Igusa, Amer. J. Math. 84 (1962)), and the constant is `1/4`
(as `Ω → i∞` the four `θ_{(0,b)}` tend to `1`, the others to `0`). Checked at 16 random `Ω ∈ 𝔥₂` to
`10⁻⁷⁷` (`py/global_ids.py`). -/
def ThetaEightSquare : Prop :=
  ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω →
    ∑ m ∈ PkgI1.evenChars, PkgI1.thetaConst m Ω ^ 16 =
      (∑ m ∈ PkgI1.evenChars, PkgI1.thetaConst m Ω ^ 8) ^ 2 / 4

/-- **GLUE (the QM-curve-specific part of the core; numerically VERIFIED).** `QMThetaSymmetricCore` for
`3 ≤ k ≤ 9`. Derivation: §3 of docs/research/theta-split.md (Igusa's theta expressions and structure theorem
with Lin–Yang's Igusa vector on the QM curve); `k = 3` is cross-checked against Lin–Yang's vector
(`py/lycheck.py`) and every constant term `R_k(0)` against the product point `diag(i, i)`
(`py/check_j0.py`). -/
def QMThetaSymmetricCurve : Prop :=
  ∀ τ : ℂ, 0 < τ.im → PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 → ∀ k, 3 ≤ k → k ≤ 9 →
    (thetaEight (PkgI1.Omega τ)).esymm k =
      Polynomial.aeval (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)) (qmR k) *
        PkgI1.thetaSum8 (PkgI1.Omega τ) ^ k

/-- **The core from the global identity and the curve part (proved).** -/
theorem qmThetaSymmetricCore_of (h2 : ThetaEightSquare) (hC : QMThetaSymmetricCurve) :
    QMThetaSymmetricCore := by
  intro τ hτ hS k hk2 hk9
  rcases Nat.lt_or_ge k 3 with h3 | h3
  · obtain rfl : k = 2 := by omega
    have hsq := h2 (PkgI1.Omega τ) (isSiegel_Omega hτ)
    have h := two_esymm_two (thetaEight (PkgI1.Omega τ))
    have hsum : (thetaEight (PkgI1.Omega τ)).sum = PkgI1.thetaSum8 (PkgI1.Omega τ) := by
      rw [← esymm_one', esymm_one]
    have hsq' : ((thetaEight (PkgI1.Omega τ)).map (· ^ 2)).sum =
        ∑ m ∈ PkgI1.evenChars, PkgI1.thetaConst m (PkgI1.Omega τ) ^ 16 := by
      rw [thetaEight, Multiset.map_map, Finset.sum_map_val]
      exact Finset.sum_congr rfl (fun m _ => by simp only [Function.comp_apply]; ring)
    rw [hsum, hsq', hsq] at h
    simp only [qmR, map_div₀, Polynomial.aeval_C]
    unfold PkgI1.thetaSum8 at h ⊢
    simp only [eq_ratCast, Rat.cast_ofNat]
    linear_combination h / 2
  · exact hC τ hτ hS k h3 hk9

/-- **Route 1, final form (proved):** `ThetaPointOfFibre` from `FibreQMPeriod`, the global identity and
the curve part. -/
theorem thetaPointOfFibre_of_qm_curve (hQM : FibreQMPeriod) (h2 : ThetaEightSquare)
    (hC : QMThetaSymmetricCurve) : ThetaPointOfFibre :=
  thetaPointOfFibre_of_qm_core hQM (qmThetaSymmetricCore_of h2 hC)

end HDec.HSyn.G0Split.ThetaPt.ThetaSplit

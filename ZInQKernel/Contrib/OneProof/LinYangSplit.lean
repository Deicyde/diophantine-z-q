import ZInQKernel.OneProof.H.TailZ19

/-! # theta-fold (2/4): theta-split's reduction of `ThetaRatiosAtQM` to symmetric functions of `θ⁸`

theta-split's scratch/theta-split/ThetaUse.lean §2-§7 (verbatim through igusa-alg and linyang-printed). Its §1
(`ThetaRatiosAtQM`, `thetaPointOfFibre_of_qm_atQM`) is in `ZInQKernel/OneProof/H/TailK.lean`, where the chain's
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


/-! ## 5. Route 2: Shimura's CM theorem and interpolation (the arithmetic input at CM points only)

`QMThetaSymmetric` asks for polynomials over `ℚ`; algebraicity only needs algebraic coefficients. Those
follow from the *shape* of the identity (an analytic statement, `QMThetaShape`) and the values at four
CM points of the curve, where Shimura's theorem on theta-nulls at CM points applies
(`ShimuraCMThetaAlgebraic`): Lagrange interpolation. -/

/-- The lattice `Ωℤ² + ℤ²` is stable under multiplication by the scalar `w` (for `w ∉ ℝ`: the
principally polarized torus `ℂ²/(Ωℤ² + ℤ²)` has complex multiplication by the imaginary quadratic
order `ℤ[w]` acting by scalars, so it is isogenous to `E²` for a CM elliptic curve `E`). -/
def ScalarCM (Ω : Matrix (Fin 2) (Fin 2) ℂ) (w : ℂ) : Prop :=
  ∀ a b : Fin 2 → ℤ, ∃ c d : Fin 2 → ℤ,
    w • (Ω.mulVec (fun i => (a i : ℂ)) + fun i => (b i : ℂ)) =
      Ω.mulVec (fun i => (c i : ℂ)) + fun i => (d i : ℂ)

/-- **LEAF (consequence of Shimura's theorem on theta-null values at CM points).** For `Ω ∈ 𝔥₂` whose
period lattice `Ωℤ² + ℤ²` is stable under a non-real scalar `w`, every theta-constant ratio
`θ_m(0, Ω)/θ_{m'}(0, Ω)` with `θ_{m'}(0, Ω) ≠ 0` is an algebraic number.

Sources (locators UNVERIFIED, no network): Shimura, *Theta functions with complex multiplication*,
Duke Math. J. 43 (1976), 673–696 (theta values at CM points are algebraic, with reciprocity), equivalently
Shimura's theorem that Siegel modular functions with algebraic Fourier coefficients take algebraic values
at CM points (Shimura, Ann. of Math. 102 (1975); `θ_m/θ_{m'}` is a modular function of level `(4,8)`
with coefficients in `ℚ(ζ₈)`). The hypothesis makes `ℂ²/(Ωℤ²+ℤ²)` of CM type: `Λ ⊗ ℚ` is a 2-dimensional
`K = ℚ(w)`-space on which `K ⊗ ℝ = ℂ` acts by scalars, so the torus is isogenous to `(ℂ/𝒪_K)²`
(elementary). Form: the published statement restricted to this kind of CM point (weaker). -/
def ShimuraCMThetaAlgebraic : Prop :=
  ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → ∀ w : ℂ, w.im ≠ 0 → ScalarCM Ω w →
    ∀ m m' : Char2, thetaConst Ω m' ≠ 0 → IsAlgebraic ℚ (thetaConst Ω m / thetaConst Ω m')

/-- **GLUE (analytic; the shape of `QMThetaSymmetric`).** There are `R_k ∈ ℂ[X]` of degree `≤ 3` with
`e_k(θ_m(Ω(τ))⁸) = R_k(j_θ(Ω(τ)))·(Σθ_m(Ω(τ))⁸)^k` for all `τ ∈ ℍ` with `Σθ_m⁸ ≠ 0`, `k ≤ 10`.
No arithmetic: `E_k/E_1^k ∘ Ω` is invariant under `Γ*` (theta transformation formula through the
modular embedding `Ω(γτ) = M_γ·Ω(τ)`, pkg-I1 §4), meromorphic on the compact curve `Γ*\ℍ` with
Hauptmodul `j_θ ∘ Ω` (`PkgI1.QMHauptmodul`), with poles only at the zeros of `E_1 ∘ Ω`, so a polynomial in
`j_θ`; degree `⌊k/3⌋ ≤ 3` (observed numerically, `py/fit_hp.py`). It follows from `QMThetaSymmetricCore`
(`qmThetaShape_of_core`). -/
def QMThetaShape : Prop :=
  ∃ R : ℕ → Polynomial ℂ, (∀ k, (R k).natDegree ≤ 3) ∧
    ∀ τ : ℂ, 0 < τ.im → PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 →
      ∀ k ≤ 10, (thetaEight (PkgI1.Omega τ)).esymm k =
        (R k).eval (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)) *
          PkgI1.thetaSum8 (PkgI1.Omega τ) ^ k

/-- **GLUE (four CM points on the curve).** There are `τ₁, …, τ₄ ∈ ℍ` such that each `Ω(τᵢ)` has
scalar CM, `Σθ_m(Ω(τᵢ))⁸ ≠ 0`, and the values `j_θ(Ω(τᵢ))` are pairwise distinct. Candidates
(`py/cmnodes.py`, numerically): the fixed points of `ι(μ)` for `μ ∈ 𝒪` of discriminants `−4, −19, −24,
−40`, with `j_θ = 0, 81/64, −16/27, 1296/125` (Elkies' values); the scalar is `w = cτ + d` for
`ι(μ) = [[a, b], [c, d]]`, since `ι(x)·w(τ,1)ᵀ = ι(xμ)(τ,1)ᵀ ∈ ι(𝒪)(τ,1)ᵀ` and `F'(τ)` is `ℂ`-linear. -/
def QMCMNodes : Prop :=
  ∃ τ : Fin 4 → ℂ, (∀ i, 0 < (τ i).im) ∧
    (∀ i, ∃ w : ℂ, w.im ≠ 0 ∧ ScalarCM (PkgI1.Omega (τ i)) w) ∧
    (∀ i, PkgI1.thetaSum8 (PkgI1.Omega (τ i)) ≠ 0) ∧
    Function.Injective (fun i => PkgI1.jNum (PkgI1.Omega (τ i)) / PkgI1.jDen (PkgI1.Omega (τ i)))

/-- The explicit core gives the shape (`R_k = qmR k` mapped to `ℂ`; degrees `≤ 3`). -/
theorem qmThetaShape_of_core (h : QMThetaSymmetricCore) : QMThetaShape := by
  refine ⟨fun k => (qmR k).map (algebraMap ℚ ℂ), fun k => ?_, fun τ hτ hS k hk => ?_⟩
  · refine natDegree_map_le.trans ?_
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp only [qmR] <;>
      compute_degree!
  · rw [eval_map_algebraMap]
    exact qmR_identity h τ hτ hS k hk

local notation "𝔸" => algebraicClosure ℚ ℂ

/-- A root of a monic polynomial whose elementary symmetric functions are algebraic is algebraic. -/
theorem mem_of_esymm_mem (s : Multiset ℂ) (hs : ∀ k ≤ Multiset.card s, s.esymm k ∈ 𝔸) {y : ℂ}
    (hy : y ∈ s) : y ∈ 𝔸 := by
  have hmon : (s.map (fun t => X - C t)).prod.Monic :=
    monic_multiset_prod_of_monic _ _ (fun t _ => monic_X_sub_C t)
  have hlift : (s.map (fun t => X - C t)).prod ∈ lifts (algebraMap 𝔸 ℂ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ Multiset.card s
    · rw [Multiset.prod_X_sub_C_coeff s hn]
      have : (-1 : ℂ) ^ (Multiset.card s - n) * s.esymm (Multiset.card s - n) ∈ 𝔸 :=
        mul_mem (pow_mem (neg_mem (one_mem _)) _) (hs _ (Nat.sub_le _ _))
      exact ⟨⟨_, this⟩, rfl⟩
    · rw [coeff_eq_zero_of_natDegree_lt]
      · exact ⟨0, by simp⟩
      · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hlift hmon
  have hA : IsAlgebraic 𝔸 y := by
    refine ⟨Q, hQm.ne_zero, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, hQ, eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map]
    exact Multiset.mem_map.mpr ⟨y, hy, by simp⟩
  exact mem_algebraicClosure_iff.mpr (hA.restrictScalars ℚ)

/-- Elementary symmetric functions of algebraic numbers are algebraic. -/
theorem esymm_mem (s : Multiset ℂ) (h : ∀ x ∈ s, x ∈ 𝔸) (k : ℕ) : s.esymm k ∈ 𝔸 := by
  unfold Multiset.esymm
  refine multiset_sum_mem _ (fun x hx => ?_)
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  exact multiset_prod_mem _ (fun y hy => h y (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hy))

/-- **Interpolation:** a polynomial of degree `≤ 3` with algebraic values at four distinct algebraic
points has algebraic values at algebraic points. -/
theorem eval_mem_of_nodes (R : Polynomial ℂ) (hdeg : R.natDegree ≤ 3) (x : Fin 4 → ℂ)
    (hx : Function.Injective x) (hxA : ∀ i, x i ∈ 𝔸) (hv : ∀ i, R.eval (x i) ∈ 𝔸) {q : ℂ}
    (hq : q ∈ 𝔸) : R.eval q ∈ 𝔸 := by
  have hdeg' : R.degree < (Finset.univ : Finset (Fin 4)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact (degree_le_of_natDegree_le hdeg).trans_lt (by exact_mod_cast (show (3 : ℕ) < 4 by norm_num))
  rw [Lagrange.eq_interpolate (s := Finset.univ) (v := x) (hx.injOn) hdeg']
  simp only [Lagrange.interpolate, LinearMap.coe_mk, AddHom.coe_mk, eval_finsetSum, eval_mul,
    eval_C]
  refine sum_mem (fun i _ => mul_mem (hv i) ?_)
  rw [Lagrange.basis, eval_prod]
  refine prod_mem (fun j _ => ?_)
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  exact mul_mem (inv_mem (sub_mem (hxA i) (hxA j))) (sub_mem hq (hxA j))

/-- At a scalar-CM point with `Σθ⁸ ≠ 0`: `j_θ` and every `e_k(θ⁸)/(Σθ⁸)^k` are algebraic. -/
theorem node_values (hCM : ShimuraCMThetaAlgebraic) {τ : ℂ} (hτ : 0 < τ.im) {w : ℂ} (hw : w.im ≠ 0)
    (hsc : ScalarCM (PkgI1.Omega τ) w) (hS : PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0) :
    PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) ∈ 𝔸 ∧
      ∀ k, (thetaEight (PkgI1.Omega τ)).esymm k / PkgI1.thetaSum8 (PkgI1.Omega τ) ^ k ∈ 𝔸 := by
  set Ω := PkgI1.Omega τ with hΩ
  -- a nonvanishing even theta constant
  obtain ⟨m', hm', hc⟩ : ∃ m' ∈ PkgI1.evenChars, PkgI1.thetaConst m' Ω ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hS
    unfold PkgI1.thetaSum8
    exact Finset.sum_eq_zero (fun m hm => by rw [hall m hm]; ring)
  set c := PkgI1.thetaConst m' Ω with hcdef
  have hr : ∀ m, PkgI1.thetaConst m Ω / c ∈ 𝔸 := by
    intro m
    have := hCM Ω (isSiegel_Omega hτ) w hw hsc m m' (by rw [thetaConst_eq_pkgI1]; exact hc)
    rw [thetaConst_eq_pkgI1, thetaConst_eq_pkgI1] at this
    exact mem_algebraicClosure_iff.mpr this
  have hc8 : c ^ 8 ≠ 0 := pow_ne_zero _ hc
  -- scaled multiset
  have hscaled : ∀ k, (c ^ 8)⁻¹ ^ k * (thetaEight Ω).esymm k ∈ 𝔸 := by
    intro k
    have e := Multiset.pow_smul_esymm ((c ^ 8)⁻¹) k (thetaEight Ω)
    simp only [smul_eq_mul] at e
    rw [e]
    refine esymm_mem _ (fun x hx => ?_) k
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨m, -, rfl⟩ := Multiset.mem_map.mp hy
    have : (c ^ 8)⁻¹ * PkgI1.thetaConst m Ω ^ 8 = (PkgI1.thetaConst m Ω / c) ^ 8 := by
      field_simp
    rw [this]; exact pow_mem (hr m) _
  have hS' : (c ^ 8)⁻¹ * PkgI1.thetaSum8 Ω ∈ 𝔸 := by
    have := hscaled 1
    rwa [pow_one, esymm_one] at this
  have hS'0 : (c ^ 8)⁻¹ * PkgI1.thetaSum8 Ω ≠ 0 := mul_ne_zero (inv_ne_zero hc8) hS
  constructor
  · have hP : (c ^ 20)⁻¹ * PkgI1.thetaProd2 Ω ∈ 𝔸 := by
      have : (c ^ 20)⁻¹ * PkgI1.thetaProd2 Ω =
          ∏ m ∈ PkgI1.evenChars, (PkgI1.thetaConst m Ω / c) ^ 2 := by
        rw [PkgI1.thetaProd2]
        simp_rw [div_pow]
        rw [Finset.prod_div_distrib, Finset.prod_const, PkgI1.card_evenChars, ← pow_mul,
          div_eq_mul_inv, mul_comm]
      rw [this]; exact prod_mem (fun m _ => pow_mem (hr m) _)
    have : PkgI1.jNum Ω / PkgI1.jDen Ω =
        3779136 * ((c ^ 20)⁻¹ * PkgI1.thetaProd2 Ω) ^ 2 / ((c ^ 8)⁻¹ * PkgI1.thetaSum8 Ω) ^ 5 := by
      rw [PkgI1.jNum, PkgI1.jDen]
      field_simp
    rw [this]
    exact div_mem (mul_mem (by exact_mod_cast (𝔸).algebraMap_mem (3779136 : ℚ)) (pow_mem hP _))
      (pow_mem hS' _)
  · intro k
    have : (thetaEight Ω).esymm k / PkgI1.thetaSum8 Ω ^ k =
        ((c ^ 8)⁻¹ ^ k * (thetaEight Ω).esymm k) / ((c ^ 8)⁻¹ * PkgI1.thetaSum8 Ω) ^ k := by
      rw [mul_pow, mul_div_mul_left _ _ (pow_ne_zero _ (inv_ne_zero hc8))]
    rw [this]
    exact div_mem (hscaled k) (pow_mem hS' _)

/-- **Route 2 (proved):** the use form from the analytic shape, four CM nodes and Shimura's CM theorem. -/
theorem thetaRatiosAtQM_of_cm (hSh : QMThetaShape) (hN : QMCMNodes)
    (hCM : ShimuraCMThetaAlgebraic) : ThetaRatiosAtQM := by
  obtain ⟨R, hdeg, hR⟩ := hSh
  obtain ⟨τ₀, hτ₀, hcm, hS₀, hinj⟩ := hN
  -- `R_k(q)` is algebraic for every rational `q`
  have hRq : ∀ k ≤ 10, ∀ q : ℚ, (R k).eval (q : ℂ) ∈ 𝔸 := by
    intro k hk q
    have hnode : ∀ i, PkgI1.jNum (PkgI1.Omega (τ₀ i)) / PkgI1.jDen (PkgI1.Omega (τ₀ i)) ∈ 𝔸 ∧
        ∀ k, (thetaEight (PkgI1.Omega (τ₀ i))).esymm k /
          PkgI1.thetaSum8 (PkgI1.Omega (τ₀ i)) ^ k ∈ 𝔸 := fun i => by
      obtain ⟨w, hw, hsc⟩ := hcm i
      exact node_values hCM (hτ₀ i) hw hsc (hS₀ i)
    refine eval_mem_of_nodes (R k) (hdeg k) _ hinj (fun i => (hnode i).1) (fun i => ?_)
      (by exact_mod_cast (𝔸).algebraMap_mem q)
    have h1 := (hnode i).2 k
    rw [hR (τ₀ i) (hτ₀ i) (hS₀ i) k hk, mul_div_cancel_right₀ _ (pow_ne_zero _ (hS₀ i))] at h1
    exact h1
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
  have hconv : ∀ m, thetaConst (BPAnalytic.QM.Omega τ) m = PkgI1.thetaConst m (PkgI1.Omega τ) :=
    fun m => by rw [thetaConst_eq_pkgI1, omega_eq]
  have h00 : PkgI1.thetaConst (0, 0) (PkgI1.Omega τ) ≠ 0 := by
    have := (Finset.prod_ne_zero_iff.mp hProd) _ zero_mem_evenChars
    exact fun h0 => this (by rw [h0]; ring)
  set s' := (thetaEight (PkgI1.Omega τ)).map (fun t => S⁻¹ • t) with hs'
  have hcard : Multiset.card s' = 10 := by rw [hs', Multiset.card_map, card_thetaEight]
  have hesymm : ∀ k ≤ Multiset.card s', s'.esymm k ∈ 𝔸 := by
    intro k hk
    rw [hcard] at hk
    rw [hs', ← Multiset.pow_smul_esymm, hR τ hτ hS k hk, hJ, smul_eq_mul, inv_pow, ← mul_assoc,
      mul_comm _ ((R k).eval (q : ℂ)), mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hS), mul_one]
    exact hRq k hk q
  have halg8 : ∀ m ∈ PkgI1.evenChars, S⁻¹ * PkgI1.thetaConst m (PkgI1.Omega τ) ^ 8 ∈ 𝔸 :=
    fun m hm => mem_of_esymm_mem s' hesymm
      (Multiset.mem_map.mpr ⟨_, Multiset.mem_map.mpr ⟨m, hm, rfl⟩, rfl⟩)
  refine ⟨(0, 0), by rw [hconv]; exact h00, fun m => ?_⟩
  rw [hconv, hconv]
  by_cases hm : m ∈ PkgI1.evenChars
  · apply IsAlgebraic.of_pow (n := 8) (by norm_num)
    have : (PkgI1.thetaConst m (PkgI1.Omega τ) / PkgI1.thetaConst (0, 0) (PkgI1.Omega τ)) ^ 8 =
        (S⁻¹ * PkgI1.thetaConst m (PkgI1.Omega τ) ^ 8) /
          (S⁻¹ * PkgI1.thetaConst (0, 0) (PkgI1.Omega τ) ^ 8) := by
      field_simp
    rw [this]
    exact mem_algebraicClosure_iff.mp (div_mem (halg8 m hm) (halg8 _ zero_mem_evenChars))
  · have h0 : PkgI1.thetaConst m (PkgI1.Omega τ) = 0 := by
      rw [← hconv]; exact thetaConst_odd _ m (isOddChar_of_not_even hm)
    rw [h0, zero_div]
    exact isAlgebraic_zero

/-- **`ThetaPointOfFibre` by Route 2 (proved).** -/
theorem thetaPointOfFibre_of_qm_cm (hQM : FibreQMPeriod) (hSh : QMThetaShape) (hN : QMCMNodes)
    (hCM : ShimuraCMThetaAlgebraic) : ThetaPointOfFibre :=
  thetaPointOfFibre_of_qm_atQM hQM (thetaRatiosAtQM_of_cm hSh hN hCM)


/-! ## 6. The CM clause of `QMCMNodes`, proved for four explicit nodes

For `μ = x + y·i + z·j ∈ 𝒪` (`z > 0`, `s² = 3z² − 2y² > 0`) the fixed point of `ι(μ)` in `ℍ` is
`τ = (y√2 + i s)/z`, with `ι(μ)(τ, 1)ᵀ = w(τ, 1)ᵀ`, `w = x + i s`. Then `w·ι(b)(τ,1)ᵀ = ι(bμ)(τ,1)ᵀ`, so
`w` preserves the QM lattice `ι(𝒪)(τ,1)ᵀ`, hence (through the `ℂ`-linear `F'(τ)`) the lattice
`Ω(τ)ℤ² + ℤ²`: `ScalarCM (Ω(τ)) w`. -/

theorem iota_add' (p q : BPAnalytic.QM.B) : BPAnalytic.QM.iota (p + q) = BPAnalytic.QM.iota p + BPAnalytic.QM.iota q := by
  unfold BPAnalytic.QM.iota
  simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, Rat.cast_add, add_smul]
  abel

theorem iota_zsmul (n : ℤ) (q : BPAnalytic.QM.B) : BPAnalytic.QM.iota ((n : ℚ) • q) = (n : ℝ) • BPAnalytic.QM.iota q := by
  unfold BPAnalytic.QM.iota
  simp only [QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul, Rat.cast_mul, Rat.cast_intCast, mul_smul, smul_add]

theorem iota_mul' (p q : BPAnalytic.QM.B) : BPAnalytic.QM.iota (p * q) = BPAnalytic.QM.iota p * BPAnalytic.QM.iota q := by
  unfold BPAnalytic.QM.iota
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj] <;> ring_nf <;>
    (try simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) <;> (try ring_nf)

theorem latVec_add' (p q : BPAnalytic.QM.B) (τ : ℂ) : BPAnalytic.QM.latVec (p + q) τ = BPAnalytic.QM.latVec p τ + BPAnalytic.QM.latVec q τ := by
  unfold BPAnalytic.QM.latVec
  rw [iota_add', ← Matrix.add_mulVec]
  congr 1
  ext i j
  simp

theorem latVec_zsmul (n : ℤ) (q : BPAnalytic.QM.B) (τ : ℂ) : BPAnalytic.QM.latVec ((n : ℚ) • q) τ = (n : ℂ) • BPAnalytic.QM.latVec q τ := by
  unfold BPAnalytic.QM.latVec
  rw [iota_zsmul]
  have : ((n : ℝ) • BPAnalytic.QM.iota q).map (fun r : ℝ => (r : ℂ)) =
      (n : ℂ) • (BPAnalytic.QM.iota q).map (fun r : ℝ => (r : ℂ)) := by
    ext i j; simp
  rw [this, Matrix.smul_mulVec]

theorem latVec_sum (n : Fin 4 → ℤ) (τ : ℂ) :
    BPAnalytic.QM.latVec (∑ l, (n l : ℚ) • BPAnalytic.QM.oBasis l) τ =
      ∑ l, (n l : ℂ) • BPAnalytic.QM.qmVec τ l := by
  simp only [Fin.sum_univ_four, latVec_add', latVec_zsmul, BPAnalytic.QM.qmVec]

theorem latVec_mul (p μ : BPAnalytic.QM.B) (τ : ℂ) :
    BPAnalytic.QM.latVec (p * μ) τ =
      ((BPAnalytic.QM.iota p).map (fun r : ℝ => (r : ℂ))).mulVec (BPAnalytic.QM.latVec μ τ) := by
  unfold BPAnalytic.QM.latVec
  rw [iota_mul', Matrix.mulVec_mulVec]
  congr 1
  exact Matrix.map_mul (f := Complex.ofRealHom)

/-- **The lattice-stability criterion (proved).** If `w` maps each generator `ι(b_k)(τ,1)ᵀ` into the
QM lattice, then `Ω(τ)` has scalar CM by `w`. -/
theorem scalarCM_of_stable {τ : ℂ} (hτ : τ.im ≠ 0) (w : ℂ)
    (hst : ∀ k, w • BPAnalytic.QM.qmVec τ k ∈ BPAnalytic.QM.qmLattice hτ) : ScalarCM (PkgI1.Omega τ) w := by
  have hst' : ∀ z ∈ BPAnalytic.QM.qmLattice hτ, w • z ∈ BPAnalytic.QM.qmLattice hτ := by
    intro z hz
    rw [BPAnalytic.QM.qmLattice_eq] at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hst k
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  have hdet := BPAnalytic.QM.det_im_Omega_ne_zero hτ
  intro a b
  have hx : (BPAnalytic.QM.Omega τ).mulVec (fun i => (a i : ℂ)) + (fun i => (b i : ℂ)) ∈
      BPAnalytic.periodLattice (BPAnalytic.QM.Omega τ) hdet :=
    (BPAnalytic.mem_periodLattice_iff _ hdet _).mpr ⟨a, b, rfl⟩
  have hF : ∀ y, y ∈ BPAnalytic.periodLattice (BPAnalytic.QM.Omega τ) hdet ↔ BPAnalytic.QM.FpEquiv hτ y ∈ BPAnalytic.QM.qmLattice hτ := by
    intro y
    rw [← BPAnalytic.QM.map_periodLattice_Omega hτ, Submodule.mem_map]
    constructor
    · intro hy; exact ⟨y, hy, rfl⟩
    · rintro ⟨y', hy', he⟩
      have : y' = y := (BPAnalytic.QM.FpEquiv hτ).injective he
      rwa [← this]
  have hwx := (hF _).mpr (by rw [map_smul]; exact hst' _ ((hF _).mp hx))
  obtain ⟨c, d, hcd⟩ := (BPAnalytic.mem_periodLattice_iff _ hdet _).mp hwx
  exact ⟨c, d, hcd⟩

/-- The node `τ = (y√2 + i s)/z`, `s = √(3z² − 2y²)`. -/
def nodeTau (y z : ℚ) : ℂ :=
  ((y : ℂ) * (√2 : ℝ) + Complex.I * (√(3 * (z : ℝ) ^ 2 - 2 * (y : ℝ) ^ 2) : ℝ)) / (z : ℂ)

/-- The eigenvalue `w = x + i s`. -/
def nodeW (x y z : ℚ) : ℂ := (x : ℂ) + Complex.I * (√(3 * (z : ℝ) ^ 2 - 2 * (y : ℝ) ^ 2) : ℝ)

theorem nodeTau_im {y z : ℚ} (hz : 0 < z) (hs : 0 < 3 * (z : ℝ) ^ 2 - 2 * (y : ℝ) ^ 2) :
    0 < (nodeTau y z).im := by
  unfold nodeTau
  have h1 : ((z : ℚ) : ℂ) = ((z : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, Complex.div_ofReal_im]
  have : (0 : ℝ) < √(3 * (z : ℝ) ^ 2 - 2 * (y : ℝ) ^ 2) := Real.sqrt_pos.mpr hs
  have hz' : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  apply div_pos _ hz'
  simpa using this


theorem latVec_node (x y z : ℚ) (hz : z ≠ 0) (hs : 0 ≤ 3 * (z : ℝ) ^ 2 - 2 * (y : ℝ) ^ 2) :
    BPAnalytic.QM.latVec ⟨x, y, z, 0⟩ (nodeTau y z) = nodeW x y z • ![nodeTau y z, 1] := by
  have hr : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have ht : ((√(3 * (z : ℝ) ^ 2 - 2 * (y : ℝ) ^ 2) : ℝ) : ℂ) ^ 2 = 3 * (z : ℂ) ^ 2 - 2 * (y : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hs]; push_cast; ring
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  set r : ℂ := ((√2 : ℝ) : ℂ) with hrdef
  set t : ℂ := ((√(3 * (z : ℝ) ^ 2 - 2 * (y : ℝ) ^ 2) : ℝ) : ℂ) with htdef
  ext i
  fin_cases i
  · simp only [BPAnalytic.QM.latVec, BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, nodeTau, nodeW]
    simp [← hrdef, ← htdef]
    field_simp
    have hI : I ^ 2 = -1 := Complex.I_sq
    linear_combination (y : ℂ) ^ 2 * hr - I ^ 2 * ht + (2 * (y : ℂ) ^ 2 - 3 * (z : ℂ) ^ 2) * hI
  · simp only [BPAnalytic.QM.latVec, BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, nodeTau, nodeW]
    simp [← hrdef, ← htdef]
    field_simp
    ring


/-- The four nodes: `μᵢ = xᵢ + yᵢ·i + zᵢ·j ∈ 𝒪` of discriminants `−4, −19, −40, −43`. -/
def nodeX : Fin 4 → ℚ := ![0, 1/2, 0, 1/2]
def nodeY : Fin 4 → ℚ := ![1, 1, 1, 2]
def nodeZ : Fin 4 → ℚ := ![1, 3/2, 2, 5/2]

/-- Right multiplication by `μᵢ` in N5's basis of `𝒪`: `b_k μᵢ = Σ_l nodeN i k l · b_l`
(`py/nodes_lean.py`). -/
def nodeN : Fin 4 → Fin 4 → Fin 4 → ℤ := ![
  ![![-1, 1, 2, 0], ![2, -1, 0, 2], ![-2, 1, 1, -1], ![2, -2, -2, 1]],
  ![![-1, 1, 3, 0], ![2, -1, 0, 3], ![-3, 1, 2, -1], ![2, -3, -2, 2]],
  ![![-2, 1, 4, 0], ![2, -2, 0, 4], ![-4, 1, 2, -1], ![2, -4, -2, 2]],
  ![![-2, 2, 5, 0], ![4, -2, 0, 5], ![-5, 2, 3, -2], ![4, -5, -4, 3]]]

/-- The CM nodes `τᵢ = (yᵢ√2 + i√(3zᵢ² − 2yᵢ²))/zᵢ`: `√2 + i`, `(2√2 + i√19)/3`, `(√2 + i√10)/2`,
`(4√2 + i√43)/5`. -/
def cmTau (i : Fin 4) : ℂ := nodeTau (nodeY i) (nodeZ i)

theorem node_mul (i k : Fin 4) :
    BPAnalytic.QM.oBasis k * (⟨nodeX i, nodeY i, nodeZ i, 0⟩ : BPAnalytic.QM.B) =
      ∑ l, (nodeN i k l : ℚ) • BPAnalytic.QM.oBasis l := by
  fin_cases i <;> fin_cases k <;> ext <;>
    simp [BPAnalytic.QM.oBasis, Fin.sum_univ_four, nodeN, nodeX, nodeY, nodeZ] <;> norm_num

theorem node_pos (i : Fin 4) :
    0 < nodeZ i ∧ 0 < 3 * ((nodeZ i : ℚ) : ℝ) ^ 2 - 2 * ((nodeY i : ℚ) : ℝ) ^ 2 := by
  fin_cases i <;> norm_num [nodeZ, nodeY]

theorem cmTau_im (i : Fin 4) : 0 < (cmTau i).im := nodeTau_im (node_pos i).1 (node_pos i).2

theorem nodeW_im (i : Fin 4) : (nodeW (nodeX i) (nodeY i) (nodeZ i)).im ≠ 0 := by
  unfold nodeW
  have : (0 : ℝ) < √(3 * ((nodeZ i : ℚ) : ℝ) ^ 2 - 2 * ((nodeY i : ℚ) : ℝ) ^ 2) :=
    Real.sqrt_pos.mpr (node_pos i).2
  simpa using this.ne'

/-- **Each `Ω(τᵢ)` has scalar CM by `wᵢ = xᵢ + i√(3zᵢ² − 2yᵢ²)` (proved).** -/
theorem scalarCM_cmTau (i : Fin 4) :
    ScalarCM (PkgI1.Omega (cmTau i)) (nodeW (nodeX i) (nodeY i) (nodeZ i)) := by
  have hτ := (cmTau_im i).ne'
  apply scalarCM_of_stable hτ
  intro k
  have h1 : nodeW (nodeX i) (nodeY i) (nodeZ i) • BPAnalytic.QM.qmVec (cmTau i) k =
      BPAnalytic.QM.latVec (BPAnalytic.QM.oBasis k *
        (⟨nodeX i, nodeY i, nodeZ i, 0⟩ : BPAnalytic.QM.B)) (cmTau i) := by
    rw [latVec_mul, cmTau, latVec_node _ _ _ (node_pos i).1.ne' (node_pos i).2.le,
      Matrix.mulVec_smul]
    rfl
  rw [h1, node_mul, latVec_sum]
  refine sum_mem (fun l _ => ?_)
  rw [BPAnalytic.QM.qmLattice_eq, Int.cast_smul_eq_zsmul ℂ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

/-- **GLUE (numerical facts at the four explicit nodes).** At `τ₁, …, τ₄` (`cmTau`):
`Σθ_m(Ω(τᵢ))⁸ ≠ 0`, and the four values `j_θ(Ω(τᵢ))` are pairwise distinct. Numerically
(`py/verify_nodes.py`, 80 digits): `j_θ = 0, 81/64, 1296/125, 194481/1000000` (the rational CM values of
discriminants `−4, −19, −40, −43` on `X₆/W`, Elkies 1998, UNVERIFIED locator) and `|Σθ⁸|` bounded away
from `0`. A closed statement about four explicit points; provable in principle by certified evaluation of
the theta series. -/
def QMCMNodesNumeric : Prop :=
  (∀ i, PkgI1.thetaSum8 (PkgI1.Omega (cmTau i)) ≠ 0) ∧
    Function.Injective (fun i =>
      PkgI1.jNum (PkgI1.Omega (cmTau i)) / PkgI1.jDen (PkgI1.Omega (cmTau i)))

/-- **`QMCMNodes` from the numerical facts (proved):** the CM clause is `scalarCM_cmTau`. -/
theorem qmCMNodes_of_numeric (h : QMCMNodesNumeric) : QMCMNodes :=
  ⟨cmTau, cmTau_im, fun i => ⟨_, nodeW_im i, scalarCM_cmTau i⟩, h.1, h.2⟩

/-- **Route 2, final form (proved):** `ThetaPointOfFibre` from `FibreQMPeriod`, the analytic shape,
the numerical node facts and Shimura's CM theorem. -/
theorem thetaPointOfFibre_of_qm_cm' (hQM : FibreQMPeriod) (hSh : QMThetaShape)
    (hN : QMCMNodesNumeric) (hCM : ShimuraCMThetaAlgebraic) : ThetaPointOfFibre :=
  thetaPointOfFibre_of_qm_cm hQM hSh (qmCMNodes_of_numeric hN) hCM


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

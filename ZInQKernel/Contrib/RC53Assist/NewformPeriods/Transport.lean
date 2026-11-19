import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.WeakWeil

/-!
# Period transport between levels (all PROVED)

This file proves the elementary part of the reduction of `NewformPeriodsRational`
(`ZInQ.Contrib.CloudB3RC53.ModularWeil.NewformPeriodsRational`): the passage from a period
statement at **some** level `M` (for some cusp form `g` with the coefficients of `L(E, s)`) to the
exact target, at the level `N = newformLevel E` and for the given form `f`. No conductor equality
and no newform theory are used.

Write `F_h = eichlerPotential h`, so `F_h(τ) = Σ_{m ≥ 1} (a_m(h)/m) qᵐ = 2πi ∫_{i∞}^τ h(z) dz`.

* `one_mem_strictPeriods_Gamma0`: `1` is a strict period of `Γ₀(N)` (it contains `T`).
* `normalizedDeriv_eichlerPotential`: `(2πi)⁻¹ d/dτ F_f = f` for a cusp form `f` on `Γ₀(N)`.
* `eichlerPotential_period_indep` (weight-two transformation law): for `γ ∈ Γ₀(N)` the period
  `F_f(γτ) − F_f(τ)` does not depend on `τ`. Proof: by `f(γτ) = (cτ + d)² f(τ)` and the chain rule
  (Mathlib's `normalizedDerivOfComplex_SL_slash` at weight `0`), `τ ↦ F_f(γτ) − F_f(τ)` has zero
  derivative on the connected upper half-plane.
* `eichlerPotential_pow_smul_sub`: hence `F_f(γⁿτ) − F_f(τ) = n · (F_f(γτ) − F_f(τ))`.
* `pow_natCard_mem_Gamma0`: for `M > 0` and every `γ ∈ SL(2, ℤ)`, `γ^d ∈ Γ(M) ⊆ Γ₀(M)` with the
  uniform exponent `d = #SL(2, ℤ/Mℤ) > 0` (Lagrange's theorem in the finite group).
* `coe_eq_of_qExpansion_coeff_eq`: two cusp forms (of possibly different levels) whose positive
  width-one coefficients agree are equal as functions on `ℍ` (zero constant terms and convergence
  of the `q`-expansions).
* `isParamScale_of_level_zero`: at the degenerate level `0` every period vanishes (`Γ₀(0)` acts by
  integer translations and `F_f` has period `1`), so the scale `1` works for every lattice.
* `isParamScale_transport`: if `c₀ · Π_M(g) ⊆ Λ` and `f = g` as functions, `f` on `Γ₀(N)`, then
  `(d c₀) · Π_N(f) ⊆ Λ`.
* `SomeLevelPeriodsRational` (an intermediate interface, not a print) and
  **`newformPeriodsRational_of_someLevel`**: `SomeLevelPeriodsRational → NewformPeriodsRational`.

Classification: every theorem here is PROVED; `SomeLevelPeriodsRational` is the interface that the
printed leaves and the named translation steps (`Leaves.lean`, `Glue.lean`) supply.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.NewformPeriods

open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.ModularWeil
open ZInQ.Manuscript.PoleS12
open UpperHalfPlane CongruenceSubgroup ModularForm
open Derivative
open scoped MatrixGroups Manifold

/-- `1` is a strict period of `Γ₀(N)` (it contains `T = [[1, 1], [0, 1]]`). -/
theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have hT : ModularGroup.T ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simp [ModularGroup.T]
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

section Potential

variable {N : ℕ} (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)

/-- The Eichler potential of a cusp form on `Γ₀(N)` is holomorphic on `ℍ`. -/
theorem mdifferentiable_eichlerPotential : MDiff (eichlerPotential f) := by
  have : Fact (IsCusp OnePoint.infty (Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods_Gamma0 N)⟩
  exact TauCeti.mdifferentiable_eichlerIntegral one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods_Gamma0 N))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) 1

/-- `(2πi)⁻¹ d/dτ F_f = f`. -/
theorem normalizedDeriv_eichlerPotential : D (eichlerPotential f) = f := by
  have h := TauCeti.CuspFormClass.iterate_normalizedDerivOfComplex_eichlerIntegral f one_pos
    (one_mem_strictPeriods_Gamma0 N) 0
  have he : eichlerPotential (⇑f) = TauCeti.eichlerIntegral 1 1 ⇑f := rfl
  rw [he]
  simpa using h

/-- **Weight-two transformation law.** For `γ ∈ Γ₀(N)` the period `F_f(γτ) − F_f(τ)` does not
depend on `τ`. -/
theorem eichlerPotential_period_indep {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (τ τ' : ℍ) :
    eichlerPotential f (γ • τ) - eichlerPotential f τ =
      eichlerPotential f (γ • τ') - eichlerPotential f τ' := by
  set F : ℍ → ℂ := eichlerPotential f with hFdef
  have hF : MDiff F := mdifferentiable_eichlerPotential f
  have hslash : (F ∣[(0 : ℤ)] γ) = fun z => F (γ • z) := by
    funext z
    simp [SL_slash_apply]
  set G : ℍ → ℂ := fun z => F (γ • z) - F z with hGdef
  have hGeq : G = (F ∣[(0 : ℤ)] γ) - F := by
    rw [hslash]
    rfl
  have hFs : MDiff (F ∣[(0 : ℤ)] γ) := by
    rw [SL_slash]
    exact hF.slash 0 _
  have hGmd : MDiff G := by
    rw [hGeq]
    exact hFs.sub hF
  have hfγ : (⇑f ∣[(2 : ℤ)] γ) = ⇑f := by
    rw [SL_slash]
    exact SlashInvariantForm.slash_action_eqn f _ (Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩)
  have hDG : D G = 0 := by
    rw [hGeq, normalizedDerivOfComplex_sub _ _ hFs hF, normalizedDerivOfComplex_SL_slash hF,
      normalizedDeriv_eichlerPotential]
    funext z
    have h2 : ((0 : ℤ) + 2) = 2 := by norm_num
    simp only [Pi.sub_apply, Pi.zero_apply, Int.cast_zero, zero_mul]
    rw [h2, hfγ]
    ring
  have hderiv : Set.EqOn (deriv (G ∘ ofComplex)) 0 {w : ℂ | 0 < w.im} := by
    intro w hw
    have h1 := congrFun hDG ⟨w, hw⟩
    simp only [Derivative.normalizedDerivOfComplex, Pi.zero_apply] at h1
    have hne : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    simpa [hne] using h1
  have hdiffOn : DifferentiableOn ℂ (G ∘ ofComplex) {w : ℂ | 0 < w.im} :=
    mdifferentiable_iff.mp hGmd
  have hconst := isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero
    (convex_halfSpace_im_gt 0).isPreconnected hdiffOn hderiv τ.im_pos τ'.im_pos
  simpa [hGdef, Function.comp_apply, ofComplex_apply] using hconst

/-- **Periods along powers.** For `γ ∈ Γ₀(N)`, `F_f(γⁿτ) − F_f(τ) = n · (F_f(γτ) − F_f(τ))`. -/
theorem eichlerPotential_pow_smul_sub {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (τ : ℍ) (n : ℕ) :
    eichlerPotential f ((γ ^ n) • τ) - eichlerPotential f τ =
      (n : ℂ) * (eichlerPotential f (γ • τ) - eichlerPotential f τ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul]
    have hstep := eichlerPotential_period_indep f hγ ((γ ^ n) • τ) τ
    calc eichlerPotential f (γ • (γ ^ n) • τ) - eichlerPotential f τ
        = (eichlerPotential f (γ • (γ ^ n) • τ) - eichlerPotential f ((γ ^ n) • τ)) +
            (eichlerPotential f ((γ ^ n) • τ) - eichlerPotential f τ) := by ring
      _ = (eichlerPotential f (γ • τ) - eichlerPotential f τ) +
            (n : ℂ) * (eichlerPotential f (γ • τ) - eichlerPotential f τ) := by rw [hstep, ih]
      _ = ((n + 1 : ℕ) : ℂ) * (eichlerPotential f (γ • τ) - eichlerPotential f τ) := by
            push_cast; ring

end Potential

/-- **Uniform finite-index exponent.** For `M > 0` and `γ ∈ SL(2, ℤ)`, `γ^d ∈ Γ₀(M)` with
`d = #SL(2, ℤ/Mℤ)`. -/
theorem pow_natCard_mem_Gamma0 (M : ℕ) (γ : SL(2, ℤ)) :
    γ ^ Nat.card (SL(2, ZMod M)) ∈ Gamma0 M := by
  have hΓ : γ ^ Nat.card (SL(2, ZMod M)) ∈ Gamma M := by
    rw [Gamma_mem', map_pow]
    exact pow_card_eq_one'
  rw [Gamma_mem] at hΓ
  rw [Gamma0_mem]
  exact hΓ.2.2.1

/-- The exponent `#SL(2, ℤ/Mℤ)` is positive for `M > 0`. -/
theorem natCard_SL_pos (M : ℕ) [NeZero M] : 0 < Nat.card (SL(2, ZMod M)) :=
  Nat.card_pos

/-- **Cusp forms are determined by their positive coefficients**, across levels: if the positive
width-one coefficients of `f` on `Γ₀(N)` and `g` on `Γ₀(M)` agree, then `f = g` on `ℍ`. -/
theorem coe_eq_of_qExpansion_coeff_eq {N M : ℕ}
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) :
    (⇑f : ℍ → ℂ) = ⇑g := by
  funext τ
  have hf1 := one_mem_strictPeriods_Gamma0 N
  have hg1 := one_mem_strictPeriods_Gamma0 M
  have : Fact (IsCusp OnePoint.infty (Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hf1⟩
  have : Fact (IsCusp OnePoint.infty (Gamma0 M : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hg1⟩
  have hsf := ModularForm.hasSum_qExpansion f one_pos hf1 τ
  have hsg := ModularForm.hasSum_qExpansion g one_pos hg1 τ
  have hcoef : ∀ m : ℕ, (qExpansion 1 f).coeff m = (qExpansion 1 g).coeff m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [CuspFormClass.qExpansion_coeff_zero f one_pos hf1,
        CuspFormClass.qExpansion_coeff_zero g one_pos hg1]
    · exact h m hm
  simp_rw [hcoef] at hsf
  exact hsf.unique hsg

/-- **The degenerate level `0`.** `Γ₀(0)` consists of `±[[1, b], [0, 1]]`, which act on `ℍ` by
integer translations; `F_f` has period `1`, so every period vanishes and the scale `1` works. -/
theorem isParamScale_of_level_zero {N : ℕ} (hN : N = 0)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (Lat : PeriodPair) :
    IsParamScale N f Lat ((1 : ℚ) : ℂ) := by
  subst hN
  refine ⟨by norm_num, fun γ hγ τ => ?_⟩
  rw [Gamma0_mem] at hγ
  have hc : γ 1 0 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 0).mp hγ
    simpa using this
  have hdet : γ 0 0 * γ 1 1 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at h
    exact h
  have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one' hdet |>.elim
    (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  have ha : γ 0 0 = γ 1 1 := by
    rcases hd with hd | hd <;> rw [hd] at hdet ⊢ <;> linarith
  -- `γ • τ = τ + n` with `n = γ 0 1 * γ 1 1`
  have hsmul : ((γ • τ : ℍ) : ℂ) = (τ : ℂ) + ((γ 0 1 * γ 1 1 : ℤ) : ℂ) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [algebraMap_int_eq, eq_intCast, hc, ha, Int.cast_zero, Complex.ofReal_zero, zero_mul,
      zero_add]
    rcases hd with hd | hd
    · rw [hd]; push_cast; ring
    · rw [hd]; push_cast; ring
  have hper : Function.Periodic (eichlerPotential f ∘ ofComplex) 1 :=
    TauCeti.periodic_eichlerIntegral_comp_ofComplex one_ne_zero 1
  have heq : eichlerPotential f (γ • τ) = eichlerPotential f τ := by
    have h1 := (hper.int_mul (γ 0 1 * γ 1 1)) (τ : ℂ)
    rw [mul_one, ← hsmul] at h1
    simpa only [Function.comp_apply, ofComplex_apply] using h1
  rw [heq, sub_self, mul_zero]
  exact Lat.lattice.zero_mem

/-- **Level transport.** Let `f` be a cusp form on `Γ₀(N)` that equals `g` on `ℍ`, where `g` is a
cusp form on `Γ₀(M)`, `M > 0`, with `c₀ · Π_M(g) ⊆ Λ`. Then `(d c₀) · Π_N(f) ⊆ Λ` for
`d = #SL(2, ℤ/Mℤ)`. -/
theorem isParamScale_transport {N M : ℕ} (hM : 0 < M)
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2) (hfg : (⇑f : ℍ → ℂ) = ⇑g)
    (Lat : PeriodPair) (c₀ : ℚ) (hc₀ : IsParamScale M g Lat (c₀ : ℂ)) :
    IsParamScale N f Lat (((Nat.card (SL(2, ZMod M)) : ℚ) * c₀ : ℚ) : ℂ) := by
  have : NeZero M := ⟨hM.ne'⟩
  have hd : 0 < Nat.card (SL(2, ZMod M)) := natCard_SL_pos M
  obtain ⟨hc0ne, hc0⟩ := hc₀
  refine ⟨?_, fun γ hγ τ => ?_⟩
  · have hd' : ((Nat.card (SL(2, ZMod M)) : ℚ)) ≠ 0 := by exact_mod_cast hd.ne'
    have hc0q : c₀ ≠ 0 := by exact_mod_cast hc0ne
    exact_mod_cast mul_ne_zero hd' hc0q
  · have hpow := pow_natCard_mem_Gamma0 M γ
    have hmem := hc0 _ hpow τ
    rw [← hfg] at hmem
    rw [eichlerPotential_pow_smul_sub f hγ τ] at hmem
    have : (((Nat.card (SL(2, ZMod M)) : ℚ) * c₀ : ℚ) : ℂ) *
        (eichlerPotential (⇑f) (γ • τ) - eichlerPotential (⇑f) τ) =
        (c₀ : ℂ) * ((Nat.card (SL(2, ZMod M)) : ℂ) *
          (eichlerPotential (⇑f) (γ • τ) - eichlerPotential (⇑f) τ)) := by
      push_cast; ring
    rw [this]
    exact hmem

/-- **Some-level period statement** (an interface, not a print): every elliptic `E/ℚ` which has a
matching cusp form at some positive level has, at some positive level `M`, a cusp form `g` on
`Γ₀(M)` with the coefficients of `L(E, s)` such that for every period lattice `Lat` of `E` some
nonzero rational `c` scales the periods of `2πi g dτ` into `Lat`. -/
def SomeLevelPeriodsRational : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic → IsModular E →
    ∃ (M : ℕ) (_ : 0 < M) (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2),
      (∀ n : ℕ, 0 < n → (qExpansion 1 g).coeff n = (E.LFunction n : ℂ)) ∧
      ∀ Lat : PeriodPair, IsLatticeOf E Lat → ∃ c : ℚ, IsParamScale M g Lat (c : ℂ)

/-- If the least matching level is positive, `E` is modular in the sense of `IsModular`. -/
theorem isModular_of_newformLevel_pos {E : WeierstrassCurve ℚ} (h : 0 < newformLevel E) :
    IsModular E := by
  have hne : {N : ℕ | 0 < N ∧ HasCuspFormAtLevel E N}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : newformLevel E = 0 := by
      simp only [newformLevel, hemp, Nat.sInf_empty]
    omega
  obtain ⟨N, hN, f, hf⟩ := hne
  exact ⟨N, hN, f, hf⟩

/-- **`SomeLevelPeriodsRational → NewformPeriodsRational`** (PROVED: `q`-expansion identity,
weight-two period law and finite-index transport; the degenerate level `0` directly). -/
theorem newformPeriodsRational_of_someLevel (h : SomeLevelPeriodsRational) :
    NewformPeriodsRational := by
  intro E hE f hf Lat hLat
  rcases Nat.eq_zero_or_pos (newformLevel E) with h0 | hpos
  · exact ⟨1, isParamScale_of_level_zero h0 f Lat⟩
  · obtain ⟨M, hM, g, hg, hscale⟩ := h E hE (isModular_of_newformLevel_pos hpos)
    obtain ⟨c₀, hc₀⟩ := hscale Lat hLat
    have hfg : (⇑f : ℍ → ℂ) = ⇑g :=
      coe_eq_of_qExpansion_coeff_eq f g fun n hn => by rw [hf n hn, hg n hn]
    exact ⟨_, isParamScale_transport hM f g hfg Lat c₀ hc₀⟩

end ZInQ.Contrib.RC53Assist.NewformPeriods

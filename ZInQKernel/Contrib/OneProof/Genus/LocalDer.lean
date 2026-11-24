import ZInQKernel.Contrib.CurvesG.GenusSplit
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.CanonicalDegree
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.Dim.Basic
import ZInQKernel.Contrib.RLeaf.BelyiX1
import ZInQKernel.Contrib.RLeaf.T40
import ZInQKernel.Contrib.HDecomp.ModCurves.X1Belyi
import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.SmoothFibre.Basic
import ZInQKernel.Contrib.OneProof.Genus.GenusBound

/-! (genus-fold) Part 3 of `scratch/genus-route/Closed.lean` (its lines 2460-end): the elementary genus bound, `localDerivation` and `dimJ1Le`. Namespace `GenusRoute` renamed `GenusFold`. -/

set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section
open CategoryTheory AlgebraicGeometry
noncomputable section

/-! ## An elementary genus bound: `g(F) ≤ [F : ℚ(j)]` for a Belyi function, without Riemann–Hurwitz

`fieldGenus F` is bounded by an explicit injection, using only the leaf `LocalDerivation` (the
derivative with respect to a local parameter preserves the valuation ring). No Riemann–Roch, no
Riemann–Hurwitz, no identification of `fieldGenus` with another genus. -/

namespace GenusFold

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

section ElemLeaf

/-- **Leaf: the derivative with respect to a local parameter preserves the valuation ring.**
For `F` finite over `ℚ(j)` with `ℚ` algebraically closed in `F` (Stichtenoth's standing
assumption that `ℚ` is the full constant field), a place `P` of `F/ℚ` and a local parameter `π` of
`P` (`π ≠ 0`,
`π ∈ 𝔪_P`, every element of `𝔪_P` is `π · y` with `y ∈ 𝒪_P`), there is a derivation
`δ = d/dπ : F → F` over `ℚ` with `δ π = 1` and `δ 𝒪_P ⊆ 𝒪_P`.
Published: Stichtenoth, *Algebraic Function Fields and Codes*, §4.1 (the `t`-derivative `δ_t` for a
separating element `t`; a prime element of a place is separating, and `δ_t(𝒪_P) ⊆ 𝒪_P` for a
`P`-prime element `t`), Prop. 4.1.8 (number UNVERIFIED); equivalently, `Ω_{𝒪_P/ℚ}` is free with basis
`dπ` (`𝒪_P` is the local ring of a smooth curve over `ℚ` at a closed point: Hartshorne II.8.8 with
II.8.7 and II.6.7, numbers UNVERIFIED), and `δ` is `dπ ↦ 1` extended to `F`. -/
def LocalDerivation : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F → ∀ (P : Place F) (π : F), π ≠ 0 → π ∈ P.w.nonunits → (∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = π * y) →
      ∃ δ : Derivation ℚ F F, δ π = 1 ∧ ∀ x ∈ P.w, δ x ∈ P.w

/-- **The genus bound for Belyi functions in the weak form the proof needs**:
`g(F) ≤ [F : ℚ(j)]` (proved below from `LocalDerivation`). -/
def GenusLeDegree : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F → IsBelyiFunction ℚ F (algebraMap Qj F (RatFunc.X / 1728)) →
      fieldGenus F ≤ Module.finrank Qj F

end ElemLeaf

section ElemVal

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- Nonzero rationals are units at every place. -/
theorem val_rat (P : Place F) {c : ℚ} (hc : c ≠ 0) : P.w.valuation (algebraMap ℚ F c) = 1 := by
  have h1 : P.w.valuation (algebraMap ℚ F c) ≤ 1 := (P.w.valuation_le_one_iff _).2 (P.rat_mem c)
  have h2 : P.w.valuation (algebraMap ℚ F c⁻¹) ≤ 1 := (P.w.valuation_le_one_iff _).2 (P.rat_mem _)
  have h3 : P.w.valuation (algebraMap ℚ F c) * P.w.valuation (algebraMap ℚ F c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : P.w.ValueGroup) = _ := h3.symm
    _ ≤ P.w.valuation (algebraMap ℚ F c) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

/-- **Derivative of `u π^(m+1)` (proved).** For a derivation `δ` preserving `𝒪_P` with `δ π = 1`,
`π ∈ 𝔪_P`, and a unit `u` of `𝒪_P`: `δ(u π^(m+1)) = π^m c` with `c` a unit of `𝒪_P` (in
characteristic `0`, `c = π δu + (m+1) u`). -/
theorem deriv_unit_pow (P : Place F) (δ : Derivation ℚ F F) (hδ : ∀ x ∈ P.w, δ x ∈ P.w) {π : F}
    (hπ : π ∈ P.w.nonunits) (hδπ : δ π = 1) {u : F} (hu : P.w.valuation u = 1) (m : ℕ) :
    ∃ c : F, c ≠ 0 ∧ c ∈ P.w ∧ c⁻¹ ∈ P.w ∧ δ (u * π ^ (m + 1)) = π ^ m * c := by
  have huw : u ∈ P.w := (P.w.valuation_le_one_iff u).1 hu.le
  set c : F := π * δ u + (algebraMap ℚ F ((m : ℚ) + 1)) * u with hc
  have hval : P.w.valuation c = 1 := by
    have hlt : P.w.valuation (π * δ u) < P.w.valuation (algebraMap ℚ F ((m : ℚ) + 1) * u) := by
      rw [map_mul, map_mul, val_rat P (by positivity), hu, one_mul]
      calc P.w.valuation π * P.w.valuation (δ u) ≤ P.w.valuation π * 1 :=
            mul_le_mul_right ((P.w.valuation_le_one_iff _).2 (hδ u huw)) _
        _ = P.w.valuation π := mul_one _
        _ < 1 := P.w.mem_nonunits_iff.mp hπ
    rw [hc, Valuation.map_add_eq_of_lt_right _ hlt, map_mul, val_rat P (by positivity), hu, one_mul]
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hval; exact zero_ne_one hval
  refine ⟨c, hc0, (P.w.valuation_le_one_iff c).1 hval.le, (P.w.valuation_le_one_iff _).1 ?_, ?_⟩
  · rw [map_inv₀, hval, inv_one]
  · rw [Derivation.leibniz, Derivation.leibniz_pow, hδπ, hc]
    simp only [smul_eq_mul, nsmul_eq_mul, mul_one, Nat.add_sub_cancel, map_add, map_natCast,
      map_one, Nat.cast_add, Nat.cast_one]
    ring

/-- **Decomposition at a uniformizer (proved).** A nonzero `z ∈ 𝔪_P` is `u π^(m+1)` with `u` a unit,
for a uniformizer `π` in the form of `exists_uniformizer`. -/
theorem decomp_nonunit (P : Place F) {π : Fˣ} (hπ : (π : F) ∈ P.w) (hπu : π ∉ P.w.unitGroup)
    (hdvr : ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup) {z : F} (hz0 : z ≠ 0)
    (hz : z ∈ P.w.nonunits) :
    ∃ (u : F) (m : ℕ), P.w.valuation u = 1 ∧ z = u * (π : F) ^ (m + 1) := by
  have hvπ1 : P.w.valuation (π : F) ≤ 1 := (P.w.valuation_le_one_iff _).2 hπ
  have hvπ : P.w.valuation (π : F) < 1 :=
    lt_of_le_of_ne hvπ1 (fun h => hπu ((P.w.mem_unitGroup_iff π).2 h))
  obtain ⟨n, hn⟩ := hdvr (Units.mk0 z hz0)
  rw [ValuationSubring.mem_unitGroup_iff] at hn
  have hπ0 : (π : F) ≠ 0 := π.ne_zero
  have hvz : P.w.valuation z < 1 := P.w.mem_nonunits_iff.mp hz
  -- `n ≥ 1`
  have hn1 : 1 ≤ n := by
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ : ∃ k : ℕ, -n = k := ⟨(-n).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hval : P.w.valuation z * P.w.valuation (π : F) ^ k = 1 := by
      have := hn
      simp only [Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, hk, zpow_natCast,
        Units.val_pow_eq_pow_val, map_mul, map_pow] at this
      exact this
    have : P.w.valuation z * P.w.valuation (π : F) ^ k < 1 := by
      calc P.w.valuation z * P.w.valuation (π : F) ^ k ≤ P.w.valuation z * 1 :=
            mul_le_mul_right (pow_le_one' hvπ1 k) _
        _ = P.w.valuation z := mul_one _
        _ < 1 := hvz
    rw [hval] at this
    exact lt_irrefl _ this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  refine ⟨z * ((π : F) ^ (m + 1))⁻¹, m, ?_, ?_⟩
  · have := hn
    simp only [Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, hm] at this
    rwa [neg_add, zpow_add₀ hπ0, zpow_neg, zpow_neg, zpow_natCast, zpow_one, ← mul_inv,
      ← pow_succ] at this
  · field_simp

/-- The leaf's local-parameter conditions for a uniformizer in the form of `exists_uniformizer`. -/
theorem localParam_of (P : Place F) {π : Fˣ} (hπ : (π : F) ∈ P.w) (hπu : π ∉ P.w.unitGroup)
    (hdvr : ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup) :
    (π : F) ∈ P.w.nonunits ∧ ∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = (π : F) * y := by
  have hvπ1 : P.w.valuation (π : F) ≤ 1 := (P.w.valuation_le_one_iff _).2 hπ
  have hvπ : P.w.valuation (π : F) < 1 :=
    lt_of_le_of_ne hvπ1 (fun h => hπu ((P.w.mem_unitGroup_iff π).2 h))
  refine ⟨P.w.mem_nonunits_iff.mpr hvπ, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · exact ⟨0, P.w.zero_mem, by rw [hx0, mul_zero]⟩
  obtain ⟨u, m, hu, rfl⟩ := decomp_nonunit P hπ hπu hdvr hx0 hx
  refine ⟨u * (π : F) ^ m, Subring.mul_mem _ ((P.w.valuation_le_one_iff u).1 hu.le)
    (Subring.pow_mem _ hπ m), by ring⟩

end ElemVal

section ElemMain

open IsDedekindDomain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F]

attribute [local instance] isDedekind_intCl isFractionRing_intCl

local notation "OF" => integralClosure (Polynomial ℚ) F

/-- **Every place has a uniformizer (proved)**: `exists_uniformizer` at places containing `t`, and for
the twisted structure `j ↦ 1/j` at the others. -/
theorem exists_uniformizer_all (P : Place F) :
    ∃ π : Fˣ, (π : F) ∈ P.w ∧ π ∉ P.w.unitGroup ∧
      ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup := by
  by_cases ht : (tF : F) ∈ P.w
  · exact exists_uniformizer P ht
  · haveI := twist_finiteDimensional (F := F)
    refine @exists_uniformizer F _ (twistAlg (F := F)) _ twist_finiteDimensional P ?_
    have hs : (sF : F) ∉ P.w := by
      intro hs; apply ht; rw [tF_eq_mul]; exact Subring.mul_mem _ (P.rat_mem _) hs
    have hinv : (sF : F)⁻¹ ∈ P.w := (P.w.mem_or_inv_mem _).resolve_left hs
    have : @tF F _ (twistAlg (F := F)) = algebraMap ℚ F (1 / 1728) * (sF : F)⁻¹ := by
      rw [@tF_eq_mul F _ (twistAlg (F := F)), sF_twist]
    rw [this]
    exact Subring.mul_mem _ (P.rat_mem _) hinv

omit [Algebra (Polynomial ℚ) F] [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F] in
/-- `D_P`: a derivation preserving `𝒪_P` maps the differentials regular at `P` into `𝒪_P`. -/
theorem lift_mem_of_regularAt (P : Place F) (δ : Derivation ℚ F F) (hδ : ∀ x ∈ P.w, δ x ∈ P.w)
    {ω : Ω[F⁄ℚ]} (hω : ω ∈ regularAt F P.w) : δ.liftKaehlerDifferential ω ∈ P.w := by
  induction hω using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hx
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul]
    exact Subring.mul_mem _ ha (hδ b hb)
  | zero => rw [map_zero]; exact P.w.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact Subring.neg_mem _ hx

omit [Algebra (Polynomial ℚ) F] [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F] in
theorem sF_eq_mul : (sF : F) = algebraMap ℚ F 1728 * (tF : F) := by
  rw [tF_eq_mul, ← mul_assoc, ← map_mul]; norm_num

omit [Algebra (Polynomial ℚ) F] [IsScalarTower (Polynomial ℚ) Qj F] in
/-- `s − 1728 ≠ 0` in `F`. -/
theorem sF_sub_ne_zero : (sF : F) - algebraMap ℚ F 1728 ≠ 0 := by
  intro h
  have h' : algebraMap Qj F (RatFunc.X - algebraMap ℚ Qj 1728) = 0 := by
    rw [map_sub, ← RingHom.comp_apply, algebraMap_rat_comp]; exact h
  rw [map_eq_zero_iff _ (algebraMap Qj F).injective, sub_eq_zero, map_ofNat] at h'
  apply RatFunc.transcendental_X (K := ℚ)
  refine ⟨Polynomial.X - Polynomial.C 1728, Polynomial.X_sub_C_ne_zero _, ?_⟩
  simp [h']

omit [Algebra (Polynomial ℚ) F] [IsScalarTower (Polynomial ℚ) Qj F] in
theorem sF_ne_zero : (sF : F) ≠ 0 := by
  intro h
  rw [sF, map_eq_zero_iff _ (algebraMap Qj F).injective] at h
  exact RatFunc.X_ne_zero h

/-- **The local conditions (proved).** If `h • ds` is regular at every place, then
`h s (s − 1728)` lies in every place containing `s`, and `h (s − 1728) ∈ 𝔪_P` at every place not
containing `s`. -/
theorem local_conditions (hL : LocalDerivation) (hK : ConstantFieldIsQ F) (hB : IsBelyiFunction ℚ F (tF : F)) (h : F)
    (hω : ∀ P : Place F, h • KaehlerDifferential.D ℚ F (sF : F) ∈ regularAt F P.w) :
    (∀ P : Place F, (sF : F) ∈ P.w →
        h * ((sF : F) * ((sF : F) - algebraMap ℚ F 1728)) ∈ P.w) ∧
      (∀ P : Place F, (sF : F) ∉ P.w → h * ((sF : F) - algebraMap ℚ F 1728) ∈ P.w.nonunits) := by
  have key : ∀ (P : Place F) (π : F) (δ : Derivation ℚ F F), δ π = 1 → (∀ x ∈ P.w, δ x ∈ P.w) →
      h * δ (sF : F) ∈ P.w := by
    intro P π δ _ hδ
    have := lift_mem_of_regularAt P δ hδ (hω P)
    rwa [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul] at this
  have h1728 : ∀ (δ : Derivation ℚ F F), δ ((sF : F) - algebraMap ℚ F 1728) = δ (sF : F) := by
    intro δ; rw [map_sub, Derivation.map_algebraMap, sub_zero]
  constructor
  · intro P hs
    have hs1728 : (sF : F) - algebraMap ℚ F 1728 ∈ P.w := Subring.sub_mem _ hs (P.rat_mem _)
    -- the three cases at a finite place
    by_cases h0 : (sF : F) ∈ P.w.nonunits
    · -- over `j = 0`
      obtain ⟨π, hπ, hπu, hdvr⟩ := exists_uniformizer_all P
      obtain ⟨hπn, hπd⟩ := localParam_of P hπ hπu hdvr
      obtain ⟨δ, hδπ, hδ⟩ := hL F hK P π π.ne_zero hπn hπd
      obtain ⟨u, m, hu, hsu⟩ := decomp_nonunit P hπ hπu hdvr sF_ne_zero h0
      obtain ⟨c, hc0, hcw, hciw, hδs⟩ := deriv_unit_pow P δ hδ hπn hδπ hu m
      have hk := key P π δ hδπ hδ
      rw [hsu, hδs] at hk
      have huw : u ∈ P.w := (P.w.valuation_le_one_iff u).1 hu.le
      have heq : h * ((sF : F) * ((sF : F) - algebraMap ℚ F 1728)) =
          (h * ((π : F) ^ m * c)) * ((π : F) * u * c⁻¹) * ((sF : F) - algebraMap ℚ F 1728) := by
        rw [hsu]; field_simp; ring
      rw [heq]
      exact Subring.mul_mem _ (Subring.mul_mem _ hk
        (Subring.mul_mem _ (Subring.mul_mem _ hπ huw) hciw)) hs1728
    by_cases h1 : (sF : F) - algebraMap ℚ F 1728 ∈ P.w.nonunits
    · -- over `j = 1728`
      obtain ⟨π, hπ, hπu, hdvr⟩ := exists_uniformizer_all P
      obtain ⟨hπn, hπd⟩ := localParam_of P hπ hπu hdvr
      obtain ⟨δ, hδπ, hδ⟩ := hL F hK P π π.ne_zero hπn hπd
      obtain ⟨u, m, hu, hsu⟩ := decomp_nonunit P hπ hπu hdvr sF_sub_ne_zero h1
      obtain ⟨c, hc0, hcw, hciw, hδs⟩ := deriv_unit_pow P δ hδ hπn hδπ hu m
      have hk := key P π δ hδπ hδ
      rw [← h1728 δ, hsu, hδs] at hk
      have huw : u ∈ P.w := (P.w.valuation_le_one_iff u).1 hu.le
      have heq : h * ((sF : F) * ((sF : F) - algebraMap ℚ F 1728)) =
          (h * ((π : F) ^ m * c)) * ((π : F) * u * c⁻¹) * (sF : F) := by
        rw [hsu]; field_simp; ring
      rw [heq]
      exact Subring.mul_mem _ (Subring.mul_mem _ hk
        (Subring.mul_mem _ (Subring.mul_mem _ hπ huw) hciw)) hs
    · -- unramified: the Belyi property gives a uniformizer `q(t)`
      have ht : (tF : F) ∈ P.w := by
        rw [tF_eq_mul]; exact Subring.mul_mem _ (P.rat_mem _) hs
      have hpr := polyIdeal_isPrime P ht
      obtain ⟨q, hqm, hqi, hqI⟩ := exists_monic_irreducible_mem (polyIdeal P ht)
        (polyIdeal_ne_bot P ht hB.1)
      have hqI' : Polynomial.aeval (tF : F) q ∈ P.w.nonunits := hqI
      have hX : q ≠ Polynomial.X := by
        rintro rfl
        rw [Polynomial.aeval_X] at hqI'
        apply h0
        rw [sF_eq_mul]
        exact mul_mem_nonunits P.w (P.rat_mem _) hqI'
      have hX1 : q ≠ Polynomial.X - 1 := by
        rintro rfl
        rw [map_sub, Polynomial.aeval_X, map_one] at hqI'
        apply h1
        rw [sF_eq_mul, show algebraMap ℚ F 1728 * (tF : F) - algebraMap ℚ F 1728 =
          algebraMap ℚ F 1728 * ((tF : F) - 1) by ring]
        exact mul_mem_nonunits P.w (P.rat_mem _) hqI'
      have hgen := hB.2 P.w P.rat_mem ht q hqm hqi hX hX1 hqI'
      have hq0 : Polynomial.aeval (tF : F) q ≠ 0 := fun h0' => hB.1 ⟨q, hqm.ne_zero, h0'⟩
      obtain ⟨δ, hδπ, hδ⟩ := hL F hK P _ hq0 hqI' hgen
      have hk := key P _ δ hδπ hδ
      -- `δ(q(t)) = q'(t) δ t = 1`
      have hdq : Polynomial.aeval (tF : F) (Polynomial.derivative q) * δ (tF : F) = 1 := by
        rw [← hδπ, Derivation.map_aeval, smul_eq_mul]
      have hds : δ (sF : F) = algebraMap ℚ F 1728 * δ (tF : F) := by
        rw [sF_eq_mul, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
          smul_eq_mul]
      have hq'w : Polynomial.aeval (tF : F) (Polynomial.derivative q) ∈ P.w := aeval_mem P ht _
      have hh : h ∈ P.w := by
        have heq : h = (h * δ (sF : F)) * (Polynomial.aeval (tF : F) (Polynomial.derivative q) *
            algebraMap ℚ F (1 / 1728)) := by
          rw [hds]
          have h1728ne : algebraMap ℚ F 1728 * algebraMap ℚ F (1 / 1728) = 1 := by
            rw [← map_mul]; norm_num
          calc h = h * (Polynomial.aeval (tF : F) (Polynomial.derivative q) * δ (tF : F)) *
                (algebraMap ℚ F 1728 * algebraMap ℚ F (1 / 1728)) := by rw [hdq, h1728ne]; ring
            _ = _ := by ring
        rw [heq]
        exact Subring.mul_mem _ hk (Subring.mul_mem _ hq'w (P.rat_mem _))
      exact Subring.mul_mem _ hh (Subring.mul_mem _ hs hs1728)
  · -- at infinity: `z = 1/(sF : F) ∈ 𝔪_P`
    intro P hs
    have hz : (sF : F)⁻¹ ∈ P.w.nonunits :=
      P.w.inv_mem_nonunits_iff.mpr (Or.inr hs)
    have hzw : (sF : F)⁻¹ ∈ P.w := (P.w.mem_or_inv_mem _).resolve_left hs
    obtain ⟨π, hπ, hπu, hdvr⟩ := exists_uniformizer_all P
    obtain ⟨hπn, hπd⟩ := localParam_of P hπ hπu hdvr
    obtain ⟨δ, hδπ, hδ⟩ := hL F hK P π π.ne_zero hπn hπd
    obtain ⟨u, m, hu, hzu⟩ := decomp_nonunit P hπ hπu hdvr (inv_ne_zero sF_ne_zero) hz
    obtain ⟨c, hc0, hcw, hciw, hδz⟩ := deriv_unit_pow P δ hδ hπn hδπ hu m
    have hk := key P π δ hδπ hδ
    have hs0 : (sF : F) ≠ 0 := sF_ne_zero
    have hδs : δ (sF : F) = -((sF : F) ^ 2) * δ (sF : F)⁻¹ := by
      rw [Derivation.leibniz_inv, smul_eq_mul]; field_simp
    have hu0 : u ≠ 0 := by intro h0; rw [h0, map_zero] at hu; exact zero_ne_one hu
    have hπ0 : (π : F) ≠ 0 := π.ne_zero
    have huw : u ∈ P.w := (P.w.valuation_le_one_iff u).1 hu.le
    have heq : h * ((sF : F) - algebraMap ℚ F 1728) =
        (h * δ (sF : F)) * (-(π : F) * u * (1 - algebraMap ℚ F 1728 * (sF : F)⁻¹) * c⁻¹) := by
      have hs' : (sF : F) = (u * (π : F) ^ (m + 1))⁻¹ := by rw [← hzu, inv_inv]
      rw [hδs, hzu, hδz, hs']
      field_simp
      ring
    rw [heq]
    refine mul_mem_nonunits P.w hk ?_
    have h' : -(π : F) * u * (1 - algebraMap ℚ F 1728 * (sF : F)⁻¹) * c⁻¹ =
        (-(u * (1 - algebraMap ℚ F 1728 * (sF : F)⁻¹) * c⁻¹)) * (π : F) := by ring
    rw [h']
    refine mul_mem_nonunits P.w ?_ hπn
    refine Subring.neg_mem _ (Subring.mul_mem _ (Subring.mul_mem _ huw ?_) hciw)
    exact Subring.sub_mem _ P.w.one_mem (Subring.mul_mem _ (P.rat_mem _) hzw)

end ElemMain

end GenusFold

namespace GenusFold

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

section ElemDiff

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F]

omit [FiniteDimensional Qj F] in
/-- `d(a) ∈ F · ds` for `a ∈ ℚ(j)` (quotient rule). -/
theorem D_algebraMap_mem_span (a : Qj) :
    KaehlerDifferential.D ℚ F (algebraMap Qj F a) ∈
      Submodule.span F {KaehlerDifferential.D ℚ F (sF : F)} := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial ℚ) a
  have hp : ∀ r : Polynomial ℚ,
      algebraMap Qj F (algebraMap (Polynomial ℚ) Qj r) = Polynomial.aeval (sF : F) r := by
    intro r
    have h2 : (algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj) =
        (Polynomial.aeval (sF : F)).toRingHom := by
      refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
      simp [RatFunc.algebraMap_X]
    exact congrArg (fun φ : Polynomial ℚ →+* F => φ r) h2
  rw [map_div₀, hp p, hp q, Derivation.leibniz_div, Derivation.map_aeval, Derivation.map_aeval]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_) <;>
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

/-- **`Ω_{F/ℚ} = F · ds` (proved)**: `F/ℚ(j)` is finite separable, so `Ω_{F/ℚ(j)} = 0` and
`F ⊗ Ω_{ℚ(j)/ℚ} → Ω_{F/ℚ}` is onto; `Ω_{ℚ(j)/ℚ}` is generated by the `d a`. -/
theorem mem_span_D_sF (ω : Ω[F⁄ℚ]) :
    ω ∈ Submodule.span F {KaehlerDifferential.D ℚ F (sF : F)} := by
  haveI : Algebra.IsSeparable Qj F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyUnramified Qj F := Algebra.FormallyUnramified.of_isSeparable Qj F
  have hC : ∀ c : ℚ, algebraMap Qj F (RatFunc.C c) = algebraMap ℚ F c := fun c =>
    congrArg (fun φ : ℚ →+* F => φ c) (RingHom.ext_rat ((algebraMap Qj F).comp RatFunc.C) _)
  haveI : IsScalarTower ℚ Qj F := ⟨fun c a x => by
    rw [RatFunc.smul_eq_C_mul]; simp only [Algebra.smul_def, map_mul, hC, mul_assoc]⟩
  have hker : ω ∈ LinearMap.ker (KaehlerDifferential.map ℚ Qj F F) := by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  rw [← KaehlerDifferential.range_mapBaseChange] at hker
  obtain ⟨t, rfl⟩ := hker
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul f η =>
    rw [KaehlerDifferential.mapBaseChange_tmul]
    refine Submodule.smul_mem _ f ?_
    have hη : η ∈ Submodule.span Qj (Set.range (KaehlerDifferential.D ℚ Qj)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hη using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [KaehlerDifferential.map_D]; exact D_algebraMap_mem_span a
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [map_smul, ← algebraMap_smul F c]
      exact Submodule.smul_mem _ _ hx
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

end ElemDiff

section ElemSpace

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- **The space `V`**: `h` with `h s (s − 1728)` in every place containing `s` and
`h (s − 1728) ∈ 𝔪_P` at every place not containing `s` (`s = j` in `F`). -/
def Vspace (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] : Submodule ℚ F where
  carrier := {h | (∀ P : Place F, (sF : F) ∈ P.w →
      h * ((sF : F) * ((sF : F) - algebraMap ℚ F 1728)) ∈ P.w) ∧
    (∀ P : Place F, (sF : F) ∉ P.w → h * ((sF : F) - algebraMap ℚ F 1728) ∈ P.w.nonunits)}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun P hP => by rw [add_mul]; exact Subring.add_mem _ (ha1 P hP) (hb1 P hP),
      fun P hP => ?_⟩
    rw [add_mul, P.w.mem_nonunits_iff]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _)
      (max_lt (P.w.mem_nonunits_iff.mp (ha2 P hP)) (P.w.mem_nonunits_iff.mp (hb2 P hP)))
  zero_mem' := ⟨fun P _ => by rw [zero_mul]; exact P.w.zero_mem,
    fun P _ => by rw [zero_mul, P.w.mem_nonunits_iff, map_zero]; exact zero_lt_one⟩
  smul_mem' := by
    rintro c h ⟨h1, h2⟩
    refine ⟨fun P hP => ?_, fun P hP => ?_⟩
    · rw [Algebra.smul_def, mul_assoc]; exact Subring.mul_mem _ (P.rat_mem c) (h1 P hP)
    · rw [Algebra.smul_def, mul_assoc]; exact mul_mem_nonunits P.w (P.rat_mem c) (h2 P hP)

/-- **Elements in every place are rational (proved)**, when `ℚ` is algebraically closed in `F`:
`ℚ` is then integrally closed in `F`, and an element outside an integrally closed subring is
outside some valuation subring containing it (Mathlib, Stacks 090P). -/
theorem mem_rat_of_all_places (hK : ConstantFieldIsQ F) {k : F} (hk : ∀ P : Place F, k ∈ P.w) :
    k ∈ Set.range (algebraMap ℚ F) := by
  by_contra hnot
  let R : Subring F := (algebraMap ℚ F).range
  have hkR : k ∉ R := fun h => hnot (by obtain ⟨c, hc⟩ := RingHom.mem_range.mp h; exact ⟨c, hc⟩)
  have hratHom : ratHom F = algebraMap ℚ F := RingHom.ext_rat _ _
  haveI : IsIntegrallyClosedIn R F := by
    rw [Subring.isIntegrallyClosedIn_iff]
    intro x hx
    obtain ⟨p, hpm, hp⟩ := hx
    let e : ℚ ≃+* R := RingEquiv.ofBijective (algebraMap ℚ F).rangeRestrict
      ⟨(algebraMap ℚ F).injective.codRestrict _, RingHom.rangeRestrict_surjective _⟩
    have hcomp : (algebraMap R F).comp e.toRingHom = algebraMap ℚ F := RingHom.ext_rat _ _
    have hf : p.map e.symm.toRingHom ≠ 0 :=
      (Polynomial.map_ne_zero_iff e.symm.injective).mpr hpm.ne_zero
    have hev : (p.map e.symm.toRingHom).eval₂ (ratHom F) x = 0 := by
      rw [hratHom, Polynomial.eval₂_map, ← hcomp, RingHom.comp_assoc]
      have : e.toRingHom.comp e.symm.toRingHom = RingHom.id R := by
        ext r; simp
      rw [this, RingHom.comp_id]; exact hp
    obtain ⟨c, hc⟩ := hK x ⟨_, hf, hev⟩
    rw [← hc, hratHom]; exact RingHom.mem_range_self _ _
  obtain ⟨V, hRV, hkV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hkR
  have hV : V ≠ ⊤ := fun h => hkV (h ▸ ValuationSubring.mem_top _)
  exact hkV (hk ⟨V, hV, fun c => hRV (RingHom.mem_range_self _ c)⟩)

/-- There is a place over `j = ∞` (from the fundamental identity at `∞`). -/
theorem exists_place_inf [FiniteDimensional Qj F] : ∃ P : Place F, (sF : F) ∉ P.w := by
  obtain ⟨hfin, hsum⟩ := fundamentalIdentityQj F {P : Place F | (tF : F) ∉ P.w} (by simp)
  by_contra hne
  push Not at hne
  have hempty : hfin.toFinset = ∅ := by
    ext P
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.notMem_empty, iff_false, not_not]
    rw [tF_eq_mul]; exact Subring.mul_mem _ (P.rat_mem _) (hne P)
  rw [hempty, Finset.sum_empty] at hsum
  exact (Module.finrank_pos (R := Qj) (M := F)).ne hsum

end ElemSpace

section ElemCount

open IsDedekindDomain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F]

attribute [local instance] isDedekind_intCl isFractionRing_intCl

local notation "OF" => integralClosure (Polynomial ℚ) F

/-- **Elements in every place containing `s` are integral over `ℚ[s]` (proved)**: `OF` is a Dedekind
domain, its height-one primes are the places containing `s`. -/
theorem mem_OF_of_places {x : F} (hx : ∀ P : Place F, (sF : F) ∈ P.w → x ∈ P.w) : x ∈ OF := by
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := OF) F x (fun v => by
    have h := hx (placeOf v) (sF_mem_placeOf v)
    change x ∈ (v.valuation F).valuationSubring at h
    exact (Valuation.mem_valuationSubring_iff _ _).mp h)
  rw [← hr]; exact r.2

theorem algebraMap_poly_C (c : ℚ) : algebraMap (Polynomial ℚ) F (Polynomial.C c) = algebraMap ℚ F c := by
  have : (algebraMap (Polynomial ℚ) F).comp Polynomial.C = algebraMap ℚ F := RingHom.ext_rat _ _
  exact congrArg (fun φ : ℚ →+* F => φ c) this

theorem algebraMap_poly_X : algebraMap (Polynomial ℚ) F Polynomial.X = (sF : F) := by
  rw [IsScalarTower.algebraMap_apply (Polynomial ℚ) Qj F, RatFunc.algebraMap_X]

/-- **`dim_ℚ V ≤ [F : ℚ(j)]` (proved).** `h ↦ h s (s − 1728) mod s·OF` injects `V` into
`OF / s·OF ≅ ℚ^d` (`OF` is free of rank `d` over `ℚ[s]`): if `h s (s − 1728) = s k` with `k ∈ OF`, then
`k = h (s − 1728)` lies in every place and in `𝔪_P` over `∞`, so `k ∈ ℚ` and `k = 0`. -/
theorem finrank_Vspace_le (hK : ConstantFieldIsQ F) :
    FiniteDimensional ℚ (Vspace F) ∧ Module.finrank ℚ (Vspace F) ≤ Module.finrank Qj F := by
  haveI := isSeparable_Qj (F := F)
  haveI : Module.IsTorsionFree (Polynomial ℚ) F := .trans_faithfulSMul (Polynomial ℚ) Qj F
  haveI : Module.Free (Polynomial ℚ) OF := IsIntegralClosure.module_free (Polynomial ℚ) Qj F OF
  haveI : Module.Finite (Polynomial ℚ) OF := IsIntegralClosure.finite (Polynomial ℚ) Qj F OF
  have hrank : Module.finrank (Polynomial ℚ) OF = Module.finrank Qj F :=
    IsIntegralClosure.rank (Polynomial ℚ) Qj F OF
  let ι := Module.Free.ChooseBasisIndex (Polynomial ℚ) OF
  let b := Module.Free.chooseBasis (Polynomial ℚ) OF
  have hcard : Fintype.card ι = Module.finrank Qj F := by
    rw [← hrank, Module.finrank_eq_card_chooseBasisIndex]
  let x : Vspace F → OF := fun h =>
    ⟨h.1 * ((sF : F) * ((sF : F) - algebraMap ℚ F 1728)), mem_OF_of_places h.2.1⟩
  have hxadd : ∀ h1 h2, x (h1 + h2) = x h1 + x h2 := fun h1 h2 => Subtype.ext (by
    simp only [x, Submodule.coe_add, Subalgebra.coe_add]; ring)
  have hxsmul : ∀ (c : ℚ) h, x (c • h) = Polynomial.C c • x h := fun c h => Subtype.ext (by
    rw [SetLike.val_smul]
    simp only [x, Submodule.coe_smul, Algebra.smul_def, algebraMap_poly_C]
    ring)
  let Ψ : Vspace F →ₗ[ℚ] (ι → ℚ) :=
    { toFun := fun h i => (b.repr (x h) i).eval 0
      map_add' := fun h1 h2 => by
        ext i; simp only [hxadd, map_add, Finsupp.add_apply, Polynomial.eval_add, Pi.add_apply]
      map_smul' := fun c h => by
        ext i
        simp only [hxsmul, map_smul, Finsupp.smul_apply, smul_eq_mul, Polynomial.eval_mul,
          Polynomial.eval_C, RingHom.id_apply, Pi.smul_apply] }
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h hΨ
    have hdvd : ∀ i, (Polynomial.X : Polynomial ℚ) ∣ b.repr (x h) i := fun i => by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
      exact congrFun hΨ i
    choose q hq using hdvd
    let k : OF := ∑ i, q i • b i
    have hxk : x h = (Polynomial.X : Polynomial ℚ) • k := by
      conv_lhs => rw [← b.sum_repr (x h)]
      simp only [k, Finset.smul_sum, smul_smul, hq]
    have hkF : (k : F) = h.1 * ((sF : F) - algebraMap ℚ F 1728) := by
      have h1 := congrArg (fun y : OF => (y : F)) hxk
      simp only [SetLike.val_smul] at h1
      simp only [x, Algebra.smul_def, algebraMap_poly_X] at h1
      have hs0 : (sF : F) ≠ 0 := sF_ne_zero
      refine mul_left_cancel₀ hs0 ?_
      rw [← h1]; ring
    have hkall : ∀ P : Place F, (k : F) ∈ P.w := by
      intro P
      by_cases hs : (sF : F) ∈ P.w
      · exact intCl_mem P hs k
      · rw [hkF]
        exact (P.w.valuation_le_one_iff _).mp (P.w.mem_nonunits_iff.mp (h.2.2 P hs)).le
    obtain ⟨c, hc⟩ := mem_rat_of_all_places hK hkall
    obtain ⟨P, hP⟩ := exists_place_inf (F := F)
    have hkP := h.2.2 P hP
    rw [← hkF, ← hc] at hkP
    have hc0 : c = 0 := by
      by_contra hc0
      rw [P.w.mem_nonunits_iff, val_rat P hc0] at hkP
      exact lt_irrefl _ hkP
    rw [hc0, map_zero] at hc
    rw [← hc] at hkF
    have : h.1 = 0 := by
      rcases mul_eq_zero.mp hkF.symm with h0 | h0
      · exact h0
      · exact absurd h0 sF_sub_ne_zero
    exact Subtype.ext this
  haveI : FiniteDimensional ℚ (Vspace F) := Module.Finite.of_injective Ψ hinj
  refine ⟨this, ?_⟩
  calc Module.finrank ℚ (Vspace F) ≤ Module.finrank ℚ (ι → ℚ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℚ
    _ = _ := hcard

/-- **`g(F) ≤ [F : ℚ(j)]` (proved from `LocalDerivation`).** Every holomorphic differential is
`h · ds` (`mem_span_D_sF`) with `h ∈ V` (`local_conditions`), and `dim V ≤ [F : ℚ(j)]`. -/
theorem genus_le_finrank (hL : LocalDerivation) (hK : ConstantFieldIsQ F)
    (hB : IsBelyiFunction ℚ F (tF : F)) : fieldGenus F ≤ Module.finrank Qj F := by
  obtain ⟨hfd, hle⟩ := finrank_Vspace_le hK
  let φ : F →ₗ[ℚ] Ω[F⁄ℚ] :=
    (LinearMap.toSpanSingleton F Ω[F⁄ℚ] (KaehlerDifferential.D ℚ F (sF : F))).restrictScalars ℚ
  have hsub : holoDiff F ≤ (Vspace F).map φ := by
    refine Submodule.span_le.mpr fun ω hω => ?_
    obtain ⟨h, rfl⟩ := Submodule.mem_span_singleton.mp (mem_span_D_sF ω)
    exact ⟨h, local_conditions hL hK hB h (fun P => hω P.w P.rat_mem), rfl⟩
  haveI : Module.Finite ℚ ((Vspace F).map φ) := Module.Finite.map _ _
  calc fieldGenus F = Module.finrank ℚ (holoDiff F) := rfl
    _ ≤ Module.finrank ℚ ((Vspace F).map φ) := Submodule.finrank_mono hsub
    _ ≤ Module.finrank ℚ (Vspace F) := Submodule.finrank_map_le φ (Vspace F)
    _ ≤ _ := hle

end ElemCount

/-- **`GenusLeDegree` from `LocalDerivation` (proved).** -/
theorem genusLeDegree_of_localDerivation (hL : LocalDerivation) : GenusLeDegree := by
  intro F _ _ _ _ hK hB
  letI : Algebra (Polynomial ℚ) F :=
    ((algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj)).toAlgebra
  haveI : IsScalarTower (Polynomial ℚ) Qj F := IsScalarTower.of_algebraMap_eq' rfl
  exact genus_le_finrank hL hK hB

/-- **`DimJ1Le` (the only use of T34) from `DimJacobianEqGenus` and `LocalDerivation` (proved).**
No Riemann–Hurwitz, no `GenusX1Field`, no `X0Transitive`. -/
theorem dimJ1Le_of_localDerivation (h1 : DimJacobianEqGenus) (hL : LocalDerivation) : DimJ1Le := by
  rintro N J hN ⟨X, P₀, aj, ⟨hC, hI, P, hP, he⟩, hJ⟩
  have hK : ConstantFieldIsQ (fieldX1 P) := constantFieldIsQ_of_curve X hC (fieldX1 P) he.some
  obtain ⟨hBel, hdeg⟩ := ZInQ.RLeaf.belyiX1 N P hN hP
  have hg := genusLeDegree_of_localDerivation hL (fieldX1 P) hK hBel
  exact ⟨fieldGenus (fieldX1 P), h1 X hC P₀ J aj hJ hI (fieldX1 P) he, hg.trans hdeg⟩

end GenusFold


/-! ## `LocalDerivation`, proved -/

namespace GenusFold

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

section LDBasic

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F]

omit [FiniteDimensional Qj F] in
theorem isScalarTower_Q_Qj : IsScalarTower ℚ Qj F := by
  have hC : ∀ c : ℚ, algebraMap Qj F (RatFunc.C c) = algebraMap ℚ F c := fun c =>
    congrArg (fun φ : ℚ →+* F => φ c) (RingHom.ext_rat ((algebraMap Qj F).comp RatFunc.C) _)
  exact ⟨fun c a x => by
    rw [RatFunc.smul_eq_C_mul]; simp only [Algebra.smul_def, map_mul, hC, mul_assoc]⟩

/-- `F` is essentially of finite type over `ℚ`. -/
theorem essFiniteType_QF : Algebra.EssFiniteType ℚ F := by
  haveI := isScalarTower_Q_Qj (F := F)
  haveI : Algebra.EssFiniteType (Polynomial ℚ) Qj :=
    Algebra.EssFiniteType.of_isLocalization Qj (nonZeroDivisors (Polynomial ℚ))
  haveI : Algebra.EssFiniteType ℚ Qj := Algebra.EssFiniteType.comp ℚ (Polynomial ℚ) Qj
  exact Algebra.EssFiniteType.comp ℚ Qj F

omit [FiniteDimensional Qj F] in
/-- `s = j` is transcendental over `ℚ` in `F`. -/
theorem sF_transcendental : Transcendental ℚ (sF : F) := by
  rintro ⟨p, hp0, hp⟩
  have key : ∀ φ : ℚ →+* Qj, Polynomial.eval₂ φ RatFunc.X p = 0 := by
    intro φ
    apply (algebraMap Qj F).injective
    rw [map_zero, Polynomial.hom_eval₂,
      show (algebraMap Qj F).comp φ = algebraMap ℚ F from RingHom.ext_rat _ _, ← Polynomial.aeval_def]
    exact hp
  exact RatFunc.transcendental_X (K := ℚ) ⟨p, hp0, key _⟩

/-- `Ω_{F/ℚ} ≠ 0`: otherwise `F/ℚ` is formally unramified, hence separable algebraic. -/
theorem nontrivial_kaehler : Nontrivial Ω[F⁄ℚ] := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  haveI : Algebra.FormallyUnramified ℚ F := ⟨h⟩
  haveI := essFiniteType_QF (F := F)
  haveI : Algebra.IsSeparable ℚ F := (Algebra.FormallyUnramified.iff_isSeparable ℚ F).mp inferInstance
  exact sF_transcendental (Algebra.IsAlgebraic.isAlgebraic (sF : F))

theorem D_sF_ne_zero : KaehlerDifferential.D ℚ F (sF : F) ≠ 0 := by
  intro h0
  haveI := nontrivial_kaehler (F := F)
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄ℚ])
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (mem_span_D_sF ω)
  rw [h0, smul_zero] at hω; exact hω rfl

/-- **`d/ds` (proved).** -/
theorem exists_deriv_s : ∃ δ : Derivation ℚ F F, δ (sF : F) = 1 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one F (D_sF_ne_zero (F := F))
  exact ⟨f.compDer (KaehlerDifferential.D ℚ F), by simpa using hf⟩

/-- Every derivation is determined by its value at `s`: `δ x = δ_s(x) · δ(s)`. -/
theorem deriv_eq_mul (δs δ : Derivation ℚ F F) (hδs : δs (sF : F) = 1) (x : F) :
    δ x = δs x * δ (sF : F) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (mem_span_D_sF (KaehlerDifferential.D ℚ F x))
  have h1 := congrArg δ.liftKaehlerDifferential hc
  have h2 := congrArg δs.liftKaehlerDifferential hc
  simp only [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul, hδs, mul_one] at h1 h2
  rw [← h1, h2]

end LDBasic

section LDPlace

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- For a uniformizer `π` (leaf form) and `π₀` (exponent form), some power of `π` brings any element
into `𝒪_P`. -/
theorem exists_pow_mul_mem (P : Place F) {π : F} (hπn : π ∈ P.w.nonunits)
    (hπd : ∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = π * y) {π₀ : Fˣ} (hπ₀ : (π₀ : F) ∈ P.w)
    (hπ₀u : π₀ ∉ P.w.unitGroup) (hdvr : ∀ x : Fˣ, ∃ n : ℤ, x * π₀ ^ (-n) ∈ P.w.unitGroup) (y : F) :
    ∃ N : ℕ, π ^ N * y ∈ P.w := by
  by_cases hy : y ∈ P.w
  · exact ⟨0, by rw [pow_zero, one_mul]; exact hy⟩
  have hy0 : y ≠ 0 := fun h => hy (h ▸ P.w.zero_mem)
  have hyi : y⁻¹ ∈ P.w.nonunits := P.w.inv_mem_nonunits_iff.mpr (Or.inr hy)
  obtain ⟨u, m, hu, hyu⟩ := decomp_nonunit P hπ₀ hπ₀u hdvr (inv_ne_zero hy0) hyi
  -- `π₀ = π c`, `c ∈ 𝒪_P`
  have hπ₀n : (π₀ : F) ∈ P.w.nonunits := (localParam_of P hπ₀ hπ₀u hdvr).1
  obtain ⟨c, hc, hπ₀c⟩ := hπd _ hπ₀n
  have hu0 : u ≠ 0 := by intro h0; rw [h0, map_zero] at hu; exact zero_ne_one hu
  refine ⟨m + 1, ?_⟩
  have hyeq : y = (u * (π₀ : F) ^ (m + 1))⁻¹ := by rw [← hyu, inv_inv]
  -- `π^(m+1) y = π^(m+1) / (u (π c)^(m+1))`; we need `c` to be a unit: `π = π₀ c'`
  obtain ⟨c', hc', hπc'⟩ := (localParam_of P hπ₀ hπ₀u hdvr).2 π hπn
  have hπ0 : π ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hπ₀c; exact π₀.ne_zero hπ₀c
  have hcc' : c * c' = 1 := by
    have : π = π * (c * c') := by rw [← mul_assoc, ← hπ₀c, ← hπc']
    exact (mul_eq_left₀ hπ0).mp this.symm
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc'
  have hci : c⁻¹ = c' := (eq_inv_of_mul_eq_one_right hcc').symm
  have huinv : u⁻¹ ∈ P.w := (P.w.valuation_le_one_iff _).1 (by rw [map_inv₀, hu, inv_one])
  have : π ^ (m + 1) * y = u⁻¹ * c' ^ (m + 1) := by
    have hc1 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
    have hcm : c ^ m * c⁻¹ ^ m = 1 := by rw [← mul_pow, hc1, one_pow]
    rw [hyeq, hπ₀c, ← hci]; field_simp
    linear_combination (-(π * π ^ m * (c ^ m * c⁻¹ ^ m))) * hc1 + (-(π * π ^ m)) * hcm
  rw [this]
  exact Subring.mul_mem _ huinv (Subring.pow_mem _ hc' _)

end LDPlace

end GenusFold

namespace GenusFold

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

section LDFin

open IsDedekindDomain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F]

attribute [local instance] isDedekind_intCl isFractionRing_intCl

local notation "OF" => integralClosure (Polynomial ℚ) F

/-- Elements of `𝒪_P` are fractions `a / b` with `a, b ∈ OF`, `b` outside the center of `P`. -/
theorem frac_rep (P : Place F) (hs : (sF : F) ∈ P.w) {x : F} (hx : x ∈ P.w) :
    ∃ a b : OF, b ∉ (centerHS P hs).asIdeal ∧ x = (a : F) * (b : F)⁻¹ := by
  have hw : P.w = HeightOneSpectrum.valuationSubringAtPrime F (centerHS P hs) := by
    rw [w_eq_valuationSubring P hs, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rw [hw] at hx
  obtain ⟨a, b, hb, rfl⟩ := hx
  exact ⟨a, b, hb, rfl⟩

/-- An element of `OF` outside the center is a unit of `𝒪_P`. -/
theorem inv_mem_of_not_mem_center (P : Place F) (hs : (sF : F) ∈ P.w) {b : OF}
    (hb : b ∉ (centerHS P hs).asIdeal) : ((b : F))⁻¹ ∈ P.w ∧ (b : F) ≠ 0 := by
  have hbw : (b : F) ∈ P.w := intCl_mem P hs b
  have hbn : (b : F) ∉ P.w.nonunits := fun h => hb ((mem_centerHS P hs b).mpr h)
  have hv1 : P.w.valuation (b : F) = 1 := by
    refine le_antisymm ((P.w.valuation_le_one_iff _).2 hbw) ?_
    by_contra hlt; push Not at hlt
    exact hbn (P.w.mem_nonunits_iff.mpr hlt)
  refine ⟨(P.w.valuation_le_one_iff _).1 (by rw [map_inv₀, hv1, inv_one]), ?_⟩
  intro h0; rw [h0, map_zero] at hv1; exact zero_ne_one hv1

/-- `δ(p(s)) = p'(s) δ(s)`. -/
theorem deriv_algebraMap_poly (δ : Derivation ℚ F F) (c : Polynomial ℚ) :
    δ (algebraMap (Polynomial ℚ) F c) =
      algebraMap (Polynomial ℚ) F (Polynomial.derivative c) * δ (sF : F) := by
  rw [algebraMap_poly_eq, algebraMap_poly_eq, Derivation.map_aeval, smul_eq_mul]

/-- **The derivative `d/ds` is bounded on `𝒪_P` (proved).** -/
theorem deriv_bound (P : Place F) (hs : (sF : F) ∈ P.w) (δs : Derivation ℚ F F)
    (hδs : δs (sF : F) = 1) {π : F} (hπn : π ∈ P.w.nonunits)
    (hπd : ∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = π * y) :
    ∃ N : ℕ, ∀ x ∈ P.w, π ^ N * δs x ∈ P.w := by
  classical
  haveI : Algebra.IsSeparable Qj F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.IsTorsionFree (Polynomial ℚ) F := .trans_faithfulSMul (Polynomial ℚ) Qj F
  haveI : Module.Free (Polynomial ℚ) OF := IsIntegralClosure.module_free (Polynomial ℚ) Qj F OF
  haveI : Module.Finite (Polynomial ℚ) OF := IsIntegralClosure.finite (Polynomial ℚ) Qj F OF
  obtain ⟨π₀, hπ₀, hπ₀u, hdvr⟩ := exists_uniformizer_all P
  have hπw : π ∈ P.w := (P.w.valuation_le_one_iff _).1 (P.w.mem_nonunits_iff.mp hπn).le
  let ι := Module.Free.ChooseBasisIndex (Polynomial ℚ) OF
  let b := Module.Free.chooseBasis (Polynomial ℚ) OF
  have hNi : ∀ i : ι, ∃ N : ℕ, π ^ N * δs (b i : F) ∈ P.w := fun i =>
    exists_pow_mul_mem P hπn hπd hπ₀ hπ₀u hdvr _
  choose Nf hNf using hNi
  let N₀ := Finset.univ.sup Nf
  have hb : ∀ i, π ^ N₀ * δs (b i : F) ∈ P.w := by
    intro i
    have hle : Nf i ≤ N₀ := Finset.le_sup (Finset.mem_univ i)
    have : π ^ N₀ * δs (b i : F) = π ^ (N₀ - Nf i) * (π ^ Nf i * δs (b i : F)) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [this]; exact Subring.mul_mem _ (Subring.pow_mem _ hπw _) (hNf i)
  have hOF : ∀ a : OF, π ^ N₀ * δs (a : F) ∈ P.w := by
    intro a
    have ha : (a : F) = ∑ i, algebraMap (Polynomial ℚ) F (b.repr a i) * (b i : F) := by
      conv_lhs => rw [← b.sum_repr a]
      simp only [AddSubmonoidClass.coe_finset_sum, Algebra.smul_def, Subalgebra.coe_mul,
        Subalgebra.coe_algebraMap]
    rw [ha, map_sum, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Derivation.leibniz, deriv_algebraMap_poly, hδs, smul_eq_mul, smul_eq_mul, mul_one]
    have h1 : algebraMap (Polynomial ℚ) F (b.repr a i) ∈ P.w := by
      rw [algebraMap_poly_eq]; exact aeval_mem P hs _
    have h2 : algebraMap (Polynomial ℚ) F (Polynomial.derivative (b.repr a i)) ∈ P.w := by
      rw [algebraMap_poly_eq]; exact aeval_mem P hs _
    have h3 : (b i : F) ∈ P.w := intCl_mem P hs _
    have : π ^ N₀ * (algebraMap (Polynomial ℚ) F (b.repr a i) * δs (b i : F) +
        (b i : F) * algebraMap (Polynomial ℚ) F (Polynomial.derivative (b.repr a i))) =
        algebraMap (Polynomial ℚ) F (b.repr a i) * (π ^ N₀ * δs (b i : F)) +
          π ^ N₀ * ((b i : F) * algebraMap (Polynomial ℚ) F (Polynomial.derivative (b.repr a i))) := by
      ring
    rw [this]
    exact Subring.add_mem _ (Subring.mul_mem _ h1 (hb i))
      (Subring.mul_mem _ (Subring.pow_mem _ hπw _) (Subring.mul_mem _ h3 h2))
  refine ⟨N₀, fun x hx => ?_⟩
  obtain ⟨a, c, hc, rfl⟩ := frac_rep P hs hx
  obtain ⟨hci, hc0⟩ := inv_mem_of_not_mem_center P hs hc
  have haw : (a : F) ∈ P.w := intCl_mem P hs a
  rw [Derivation.leibniz, Derivation.leibniz_inv, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have : π ^ N₀ * ((a : F) * (-(c : F)⁻¹ ^ 2 * δs (c : F)) + (c : F)⁻¹ * δs (a : F)) =
      (c : F)⁻¹ * (π ^ N₀ * δs (a : F)) - (a : F) * (c : F)⁻¹ * (c : F)⁻¹ * (π ^ N₀ * δs (c : F)) := by
    ring
  rw [this]
  exact Subring.sub_mem _ (Subring.mul_mem _ hci (hOF a))
    (Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ haw hci) hci) (hOF c))

end LDFin

end GenusFold

namespace GenusFold

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

section LDRes

open IsDedekindDomain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F]

attribute [local instance] isDedekind_intCl isFractionRing_intCl

local notation "OF" => integralClosure (Polynomial ℚ) F

/-- **Residue structure (proved).** At a place containing `s` there is `θ ∈ 𝒪_P` and `g ∈ ℚ[T]` with
`g(θ) ∈ 𝔪_P`, `g'(θ)` a unit, and every `x ∈ 𝒪_P` congruent to some `p(θ)` modulo `𝔪_P`. (The residue
field `OF/𝔭` is a finitely generated `ℚ`-algebra and a field, hence finite over `ℚ` (Zariski); take a
primitive element and its minimal polynomial.) -/
theorem residue_structure (P : Place F) (hs : (sF : F) ∈ P.w) :
    ∃ θ : F, θ ∈ P.w ∧ ∃ g : Polynomial ℚ, Polynomial.aeval θ g ∈ P.w.nonunits ∧
      (Polynomial.aeval θ (Polynomial.derivative g))⁻¹ ∈ P.w ∧
      Polynomial.aeval θ (Polynomial.derivative g) ≠ 0 ∧
      ∀ x ∈ P.w, ∃ p : Polynomial ℚ, x - Polynomial.aeval θ p ∈ P.w.nonunits := by
  classical
  haveI : Algebra.IsSeparable Qj F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.Finite (Polynomial ℚ) OF := IsIntegralClosure.finite (Polynomial ℚ) Qj F OF
  letI : Algebra ℚ OF := ((algebraMap (Polynomial ℚ) OF).comp (algebraMap ℚ (Polynomial ℚ))).toAlgebra
  haveI : IsScalarTower ℚ (Polynomial ℚ) OF := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType ℚ OF :=
    Algebra.FiniteType.trans (S := Polynomial ℚ) inferInstance inferInstance
  set 𝔭 := centerHS P hs with h𝔭
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isPrime.isMaximal 𝔭.ne_bot
  letI : Field (OF ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  haveI : Module.Finite ℚ (OF ⧸ 𝔭.asIdeal) := finite_of_finite_type_of_isJacobsonRing ℚ _
  haveI : Algebra.IsSeparable ℚ (OF ⧸ 𝔭.asIdeal) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ (OF ⧸ 𝔭.asIdeal)
  have hint : IsIntegral ℚ α := IsIntegral.of_finite ℚ α
  have hpoly : ∀ y : OF ⧸ 𝔭.asIdeal, ∃ p : Polynomial ℚ, Polynomial.aeval α p = y := by
    intro y
    have hy : y ∈ (IntermediateField.adjoin ℚ {α}).toSubalgebra := by rw [hα]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, hp⟩ := hy
    exact ⟨p, hp⟩
  obtain ⟨θ, hθ⟩ := Ideal.Quotient.mk_surjective α
  have hmk : ∀ p : Polynomial ℚ, Ideal.Quotient.mk 𝔭.asIdeal (Polynomial.aeval θ p) =
      Polynomial.aeval α p := by
    intro p
    rw [← hθ]
    exact (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℚ 𝔭.asIdeal) θ p).symm
  have hcoe : ∀ p : Polynomial ℚ, ((Polynomial.aeval θ p : OF) : F) = Polynomial.aeval (θ : F) p := by
    intro p
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    have h := Polynomial.hom_eval₂ p (algebraMap ℚ OF) (OF).val.toRingHom θ
    rw [show (OF).val.toRingHom.comp (algebraMap ℚ OF) = algebraMap ℚ F from RingHom.ext_rat _ _] at h
    exact h
  set g := minpoly ℚ α with hg
  have hg0 : Polynomial.aeval α g = 0 := minpoly.aeval ℚ α
  have hg'0 : Polynomial.aeval α (Polynomial.derivative g) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable ℚ α).aeval_derivative_ne_zero hg0
  refine ⟨(θ : F), intCl_mem P hs θ, g, ?_, ?_⟩
  · rw [← hcoe, ← mem_centerHS P hs, ← Ideal.Quotient.eq_zero_iff_mem, hmk, hg0]
  have hnot : Polynomial.aeval θ (Polynomial.derivative g) ∉ 𝔭.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hmk]; exact hg'0
  obtain ⟨hinv, hne⟩ := inv_mem_of_not_mem_center P hs hnot
  rw [hcoe] at hinv hne
  refine ⟨hinv, hne, fun x hx => ?_⟩
  obtain ⟨a, c, hc, rfl⟩ := frac_rep P hs hx
  obtain ⟨hci, hc0⟩ := inv_mem_of_not_mem_center P hs hc
  have hc' : Ideal.Quotient.mk 𝔭.asIdeal c ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hc
  obtain ⟨p, hp⟩ := hpoly (Ideal.Quotient.mk 𝔭.asIdeal a * (Ideal.Quotient.mk 𝔭.asIdeal c)⁻¹)
  refine ⟨p, ?_⟩
  have hmem : a - Polynomial.aeval θ p * c ∈ 𝔭.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hmk, hp]
    field_simp
    ring
  have hmemF := (mem_centerHS P hs _).mp hmem
  have heq : (a : F) * (c : F)⁻¹ - Polynomial.aeval (θ : F) p =
      (c : F)⁻¹ * ((a - Polynomial.aeval θ p * c : OF) : F) := by
    rw [Subalgebra.coe_sub, Subalgebra.coe_mul, hcoe]
    field_simp
  rw [heq]
  exact mul_mem_nonunits P.w hci hmemF

end LDRes

end GenusFold

namespace GenusFold

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

section LDMain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F]

/-- **`LocalDerivation` at a place containing `s` (proved).** With `δ_s = d/ds`: (i) `δ_s` is bounded
on `𝒪_P` (`deriv_bound`); (ii) writing `x = p(θ) + π y` and `g(θ) = π z` (`residue_structure`),
`δ_s x ∈ 𝒪_P δ_s(π) + π (𝒪_P δ_s z + δ_s y)`; iterating, `π^N (δ_s x − a δ_s π) ∈ π^k 𝒪_P` for all `k`.
For `x = s` this forces `δ_s π ≠ 0`, and then `δ = δ_s / δ_s(π)` maps `𝒪_P` into `𝒪_P`. -/
theorem localDer_fin (P : Place F) (hs : (sF : F) ∈ P.w) (π : F) (hπ0 : π ≠ 0)
    (hπn : π ∈ P.w.nonunits) (hπd : ∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = π * y) :
    ∃ δ : Derivation ℚ F F, δ π = 1 ∧ ∀ x ∈ P.w, δ x ∈ P.w := by
  obtain ⟨δs, hδs⟩ := exists_deriv_s (F := F)
  obtain ⟨N, hN⟩ := deriv_bound P hs δs hδs hπn hπd
  obtain ⟨θ, hθ, g, hg, hg'i, hg'0, hres⟩ := residue_structure P hs
  have hπw : π ∈ P.w := (P.w.valuation_le_one_iff _).1 (P.w.mem_nonunits_iff.mp hπn).le
  have hdec : ∀ x ∈ P.w, ∃ A ∈ P.w, ∃ B ∈ P.w, ∃ z ∈ P.w, ∃ y ∈ P.w,
      δs x = A * δs π + π * (B * δs z + δs y) := by
    intro x hx
    obtain ⟨p, hp⟩ := hres x hx
    obtain ⟨y, hy, hxy⟩ := hπd _ hp
    obtain ⟨z, hz, hgz⟩ := hπd _ hg
    have hθd : Polynomial.aeval θ (Polynomial.derivative g) * δs θ = π * δs z + z * δs π := by
      rw [← smul_eq_mul, ← Derivation.map_aeval, hgz, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hθd' : δs θ = (Polynomial.aeval θ (Polynomial.derivative g))⁻¹ * (π * δs z + z * δs π) := by
      rw [← hθd]; field_simp
    have hx' : x = Polynomial.aeval θ p + π * y := by rw [← hxy]; ring
    have hp'w : Polynomial.aeval θ (Polynomial.derivative p) ∈ P.w := aeval_mem P hθ _
    refine ⟨Polynomial.aeval θ (Polynomial.derivative p) *
        (Polynomial.aeval θ (Polynomial.derivative g))⁻¹ * z + y,
      Subring.add_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hp'w hg'i) hz) hy,
      Polynomial.aeval θ (Polynomial.derivative p) * (Polynomial.aeval θ (Polynomial.derivative g))⁻¹,
      Subring.mul_mem _ hp'w hg'i, z, hz, y, hy, ?_⟩
    rw [hx', map_add, Derivation.map_aeval, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hθd']
    ring
  have hQ : ∀ k : ℕ, ∀ x ∈ P.w, ∃ a ∈ P.w, ∃ r ∈ P.w, π ^ N * (δs x - a * δs π) = π ^ k * r := by
    intro k
    induction k with
    | zero => intro x hx; exact ⟨0, P.w.zero_mem, π ^ N * δs x, hN x hx, by ring⟩
    | succ k ih =>
      intro x hx
      obtain ⟨A, hA, B, hB, z, hz, y, hy, hxe⟩ := hdec x hx
      obtain ⟨az, haz, rz, hrz, hz'⟩ := ih z hz
      obtain ⟨ay, hay, ry, hry, hy'⟩ := ih y hy
      refine ⟨A + π * (B * az + ay),
        Subring.add_mem _ hA (Subring.mul_mem _ hπw (Subring.add_mem _ (Subring.mul_mem _ hB haz) hay)),
        B * rz + ry, Subring.add_mem _ (Subring.mul_mem _ hB hrz) hry, ?_⟩
      rw [hxe]
      linear_combination π * B * hz' + π * hy'
  have hδπ : δs π ≠ 0 := by
    intro h0
    obtain ⟨a, ha, r, hr, he⟩ := hQ (N + 1) (sF : F) hs
    rw [h0, mul_zero, sub_zero, hδs, mul_one] at he
    have h1 : π * r = 1 := by
      have hπN : π ^ N ≠ 0 := pow_ne_zero _ hπ0
      apply mul_left_cancel₀ hπN
      calc π ^ N * (π * r) = π ^ (N + 1) * r := by ring
        _ = π ^ N := he.symm
        _ = π ^ N * 1 := (mul_one _).symm
    have h2 := mul_mem_nonunits P.w hr hπn
    rw [mul_comm, h1, P.w.mem_nonunits_iff, map_one] at h2
    exact lt_irrefl _ h2
  obtain ⟨π₀, hπ₀, hπ₀u, hdvr⟩ := exists_uniformizer_all P
  obtain ⟨k, hk⟩ := exists_pow_mul_mem P hπn hπd hπ₀ hπ₀u hdvr (π ^ N * δs π)⁻¹
  refine ⟨(δs π)⁻¹ • δs, ?_, fun x hx => ?_⟩
  · rw [Derivation.smul_apply, smul_eq_mul, inv_mul_cancel₀ hδπ]
  obtain ⟨a, ha, r, hr, he⟩ := hQ k x hx
  have hπN : π ^ N ≠ 0 := pow_ne_zero _ hπ0
  have : ((δs π)⁻¹ • δs) x = a + (π ^ k * (π ^ N * δs π)⁻¹) * r := by
    rw [Derivation.smul_apply, smul_eq_mul]
    have hx' : δs x = a * δs π + π ^ k * r / π ^ N := by
      rw [← he]; field_simp; ring
    rw [hx']
    field_simp
  rw [this]
  exact Subring.add_mem _ ha (Subring.mul_mem _ hk hr)

end LDMain

/-- **`LocalDerivation`, proved.** At places containing `s = j` by `localDer_fin`; at the places over
`j = ∞` by `localDer_fin` for the twisted structure `j ↦ 1/j`. -/
theorem localDerivation : LocalDerivation := by
  intro F _ _ _ _ _ P π hπ0 hπn hπd
  by_cases hs : (sF : F) ∈ P.w
  · letI : Algebra (Polynomial ℚ) F :=
      ((algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj)).toAlgebra
    haveI : IsScalarTower (Polynomial ℚ) Qj F := IsScalarTower.of_algebraMap_eq' rfl
    exact localDer_fin P hs π hπ0 hπn hπd
  · letI : Algebra (Polynomial ℚ) F :=
      ((@algebraMap Qj F _ _ (twistAlg (F := F))).comp (algebraMap (Polynomial ℚ) Qj)).toAlgebra
    have htw : @IsScalarTower (Polynomial ℚ) Qj F _ (twistAlg (F := F)).toSMul _ := by
      letI := twistAlg (F := F)
      exact IsScalarTower.of_algebraMap_eq' rfl
    have hs' : @sF F _ (twistAlg (F := F)) ∈ P.w := by
      rw [sF_twist]; exact (P.w.mem_or_inv_mem _).resolve_left hs
    exact @localDer_fin F _ (twistAlg (F := F)) _ _ htw twist_finiteDimensional P hs' π hπ0 hπn hπd

/-- **The genus bound with no leaf (proved).** -/
theorem genusLeDegree : GenusLeDegree := genusLeDegree_of_localDerivation localDerivation

/-- **`DimJ1Le` (the only use of T34) from `DimJacobianEqGenus` alone (proved).** -/
theorem dimJ1Le_of_dimJacobianEqGenus (h1 : DimJacobianEqGenus) : DimJ1Le :=
  dimJ1Le_of_localDerivation h1 localDerivation

end GenusFold

end



namespace GenusFold

/-- **`DimJ1Le` (the only use of T34) with no hypothesis (proved)**: dimjac-glue's
`GenusFold.DimJac.dimJacobianEqGenus` (copied verbatim above) and `dimJ1Le_of_dimJacobianEqGenus`. -/
theorem dimJ1Le : DimJ1Le := dimJ1Le_of_dimJacobianEqGenus GenusFold.DimJac.dimJacobianEqGenus

end GenusFold

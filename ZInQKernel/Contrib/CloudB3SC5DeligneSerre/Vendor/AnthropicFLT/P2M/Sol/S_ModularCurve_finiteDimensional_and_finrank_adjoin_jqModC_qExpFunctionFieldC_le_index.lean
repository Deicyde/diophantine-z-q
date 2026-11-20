/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index (git blob 0a396f062837f8b5b3684eb44c7511277d390895, sha256 5ffab5aa6bceed503ee50324fce046d431ccce8808d4e709b5f9c63eddaf5d91).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0ModL
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Ramification
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_ReductionMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_transcendental_jqModC
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

namespace P2MKcQExpDeg

open ModularCurve IntermediateField Polynomial

section Transfer

variable {κ k : Type*} [Field κ] [Field k] (φ : κ →+* k)

abbrev Φ : LaurentSeries κ →+* LaurentSeries k := coeffMap φ

theorem Φ_injective : Function.Injective (Φ φ) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries k => s.coeff n) h
  simp only [coeffMap_coeff] at h1
  exact φ.injective h1

theorem Φ_ne_zero_iff (x : LaurentSeries κ) : Φ φ x ≠ 0 ↔ x ≠ 0 := by
  rw [Ne, ← map_zero (Φ φ), (Φ_injective φ).eq_iff]

theorem Φ_intSeriesC (p : PowerSeries ℤ) : Φ φ (intSeriesC κ p) = intSeriesC k p := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem algebraMap_laurentSeries_eq_C {K : Type*} [Field K] (a : K) :
    algebraMap K (LaurentSeries K) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']
  have h1 : algebraMap K (PowerSeries K) a = PowerSeries.C a := by simp
  rw [h1, HahnSeries.ofPowerSeries_C]

theorem Φ_algebraMap (a : κ) :
    Φ φ (algebraMap κ (LaurentSeries κ) a) = algebraMap k (LaurentSeries k) (φ a) := by
  rw [algebraMap_laurentSeries_eq_C, algebraMap_laurentSeries_eq_C, HahnSeries.C_apply, HahnSeries.C_apply,
    coeffMap_single]

theorem coe_mem_adjoin_of_mem_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]
    (F : IntermediateField K L) (x : F) {y : F} (hy : y ∈ adjoin K ({x} : Set F)) :
    (y : L) ∈ adjoin K ({(x : L)} : Set L) := by
  have h : (y : L) ∈ (adjoin K ({x} : Set F)).map F.val := ⟨y, hy, rfl⟩
  rwa [adjoin_map, Set.image_singleton] at h

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

theorem image_intFormRatiosC : (Φ φ) '' intFormRatiosC κ Γ = intFormRatiosC k Γ := by
  ext z
  constructor
  · rintro ⟨y, ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    refine ⟨w, f, g, pf, pg, hf, hg, ?_, ?_⟩
    · rw [← Φ_intSeriesC φ]; exact (Φ_ne_zero_iff φ _).mpr hg0
    · rw [map_div₀, Φ_intSeriesC, Φ_intSeriesC]
  · rintro ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩
    refine ⟨intSeriesC κ pf / intSeriesC κ pg, ⟨w, f, g, pf, pg, hf, hg, ?_, rfl⟩, ?_⟩
    · rw [← Φ_ne_zero_iff φ, Φ_intSeriesC]; exact hg0
    · rw [map_div₀, Φ_intSeriesC, Φ_intSeriesC]

variable {Γ}

theorem map_mem_adjoin {S : Set (LaurentSeries κ)} {y : LaurentSeries κ} (hy : y ∈ adjoin κ S) :
    Φ φ y ∈ adjoin k ((Φ φ) '' S) := by
  have hy' : y ∈ (adjoin κ S).toSubfield := hy
  rw [adjoin_toSubfield] at hy'
  have hle : Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ)) ∪ S) ≤
      (adjoin k ((Φ φ) '' S)).toSubfield.comap (Φ φ) := by
    rw [Subfield.closure_le]
    rintro z (⟨a, rfl⟩ | hz)
    · change Φ φ (algebraMap κ (LaurentSeries κ) a) ∈ adjoin k ((Φ φ) '' S)
      rw [Φ_algebraMap]
      exact IntermediateField.algebraMap_mem _ _
    · change Φ φ z ∈ adjoin k ((Φ φ) '' S)
      exact subset_adjoin k _ ⟨z, hz, rfl⟩
  exact hle hy'

theorem map_mem_qExpFunctionFieldC {y : LaurentSeries κ} (hy : y ∈ qExpFunctionFieldC κ Γ) :
    Φ φ y ∈ qExpFunctionFieldC k Γ := by
  have h := map_mem_adjoin φ hy
  rwa [image_intFormRatiosC] at h

variable (Γ)




include φ in

theorem transfer (x : (qExpFunctionFieldC κ Γ)) (hx : (x : LaurentSeries κ) = jqModC κ)
    (x' : (qExpFunctionFieldC k Γ)) (hx' : (x' : LaurentSeries k) = jqModC k)
    (hfd : FiniteDimensional (adjoin κ ({x} : Set (qExpFunctionFieldC κ Γ))) (qExpFunctionFieldC κ Γ)) :
    FiniteDimensional (adjoin k ({x'} : Set (qExpFunctionFieldC k Γ))) (qExpFunctionFieldC k Γ) ∧
      Module.finrank (adjoin k ({x'} : Set (qExpFunctionFieldC k Γ))) (qExpFunctionFieldC k Γ) ≤ Module.finrank (adjoin κ ({x} : Set (qExpFunctionFieldC κ Γ))) (qExpFunctionFieldC κ Γ) := by
  classical
  have hjk : jqModC k ∈ (qExpFunctionFieldC k Γ) := intFormRatiosC_subset k Γ (ModularCurve.jqModC_mem_intFormRatiosC k Γ)
  have hΦx : Φ φ (x : LaurentSeries κ) = jqModC k := by rw [hx, coeffMap_jqModC]

  set Lκ : IntermediateField κ (qExpFunctionFieldC κ Γ) := adjoin κ ({x} : Set (qExpFunctionFieldC κ Γ)) with hLκ
  set K₀ : IntermediateField k (qExpFunctionFieldC k Γ) := adjoin k ({x'} : Set (qExpFunctionFieldC k Γ)) with hK₀
  set K₁ : IntermediateField k (LaurentSeries k) := adjoin k ({jqModC k} : Set (LaurentSeries k)) with hK₁
  haveI : FiniteDimensional Lκ (qExpFunctionFieldC κ Γ) := hfd

  let ψ₀ : Lκ →+* LaurentSeries k :=
    (Φ φ).comp (((qExpFunctionFieldC κ Γ).val : (qExpFunctionFieldC κ Γ) →+* LaurentSeries κ).comp (algebraMap Lκ (qExpFunctionFieldC κ Γ)))
  have hψ₀ : ∀ a : Lκ, ψ₀ a = Φ φ ((a : (qExpFunctionFieldC κ Γ)) : LaurentSeries κ) := fun a => rfl
  have hLκmap : ∀ a : Lκ, ((a : (qExpFunctionFieldC κ Γ)) : LaurentSeries κ) ∈
      adjoin κ ({(x : LaurentSeries κ)} : Set (LaurentSeries κ)) :=
    fun a => coe_mem_adjoin_of_mem_adjoin (qExpFunctionFieldC κ Γ) x a.2
  have hψ₀mem : ∀ a : Lκ, ψ₀ a ∈ K₁ := by
    intro a
    rw [hψ₀]
    have h := map_mem_adjoin φ (hLκmap a)
    rwa [Set.image_singleton, hΦx] at h
  let ψ : Lκ →+* K₁ := ψ₀.codRestrict K₁ hψ₀mem
  have hψval : ∀ a : Lκ, ((ψ a : K₁) : LaurentSeries k) = Φ φ ((a : (qExpFunctionFieldC κ Γ)) : LaurentSeries κ) :=
    fun a => rfl

  set n := Module.finrank Lκ (qExpFunctionFieldC κ Γ) with hn
  let v := Module.finBasis Lκ (qExpFunctionFieldC κ Γ)
  let w : Fin n → LaurentSeries k := fun i => Φ φ ((v i : (qExpFunctionFieldC κ Γ)) : LaurentSeries κ)
  set S : Submodule K₁ (LaurentSeries k) := Submodule.span K₁ (Set.range w) with hS
  haveI hSfin : Module.Finite K₁ S := Module.Finite.span_of_finite K₁ (Set.finite_range w)
  have hSrank : Module.finrank K₁ S ≤ n := (finrank_range_le_card w).trans (by simp)

  have hsub : ∀ y : LaurentSeries κ, y ∈ (qExpFunctionFieldC κ Γ) → Φ φ y ∈ S := by
    intro y hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Lκ).mp
      (show (⟨y, hy⟩ : (qExpFunctionFieldC κ Γ)) ∈ Submodule.span Lκ (Set.range v) by rw [v.span_eq]; trivial)
    have hy' : y = ∑ i, ((c i : (qExpFunctionFieldC κ Γ)) : LaurentSeries κ) * ((v i : (qExpFunctionFieldC κ Γ)) : LaurentSeries κ) := by
      have h := congrArg (fun z : (qExpFunctionFieldC κ Γ) => (z : LaurentSeries κ)) hc
      simp only at h
      rw [← h, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [IntermediateField.smul_def, smul_eq_mul, MulMemClass.coe_mul]
    rw [hy', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_mul]
    have : Φ φ ((c i : (qExpFunctionFieldC κ Γ)) : LaurentSeries κ) * w i = (ψ (c i)) • w i := by
      rw [IntermediateField.smul_def, smul_eq_mul, hψval]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have hone : (1 : LaurentSeries k) ∈ S := by
    have h := hsub 1 (one_mem _)
    rwa [map_one] at h
  have hww : ∀ i j, w i * w j ∈ S := by
    intro i j
    have h := hsub (((v i : (qExpFunctionFieldC κ Γ)) : LaurentSeries κ) * ((v j : (qExpFunctionFieldC κ Γ)) : LaurentSeries κ))
      (mul_mem (v i).2 (v j).2)
    rwa [map_mul] at h
  have hmul : ∀ a b : LaurentSeries k, a ∈ S → b ∈ S → a * b ∈ S := by
    intro a b ha hb
    induction ha using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨i, rfl⟩ := ht
      induction hb using Submodule.span_induction with
      | mem t' ht' => obtain ⟨j, rfl⟩ := ht'; exact hww i j
      | zero => rw [mul_zero]; exact zero_mem _
      | add b₁ b₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
      | smul r b _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h
    | zero => rw [zero_mul]; exact zero_mem _
    | add a₁ a₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul r a _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h

  have hinv : ∀ a : LaurentSeries k, a ∈ S → a⁻¹ ∈ S := by
    intro a ha
    by_cases ha0 : a = 0
    · rw [ha0, inv_zero]; exact zero_mem _
    let μ : S →ₗ[K₁] S :=
      { toFun := fun s => ⟨a * s, hmul a s ha s.2⟩
        map_add' := fun s t => by apply Subtype.ext; simp [mul_add]
        map_smul' := fun r s => by
          apply Subtype.ext
          simp only [SetLike.val_smul, RingHom.id_apply]
          rw [mul_smul_comm] }
    have hμinj : Function.Injective μ := by
      intro s t h
      have h' := congrArg Subtype.val h
      simp only [μ, LinearMap.coe_mk, AddHom.coe_mk] at h'
      exact Subtype.ext (mul_left_cancel₀ ha0 h')
    have hμsurj : Function.Surjective μ := LinearMap.injective_iff_surjective.mp hμinj
    obtain ⟨t, ht⟩ := hμsurj ⟨1, hone⟩
    have ht' : a * (t : LaurentSeries k) = 1 := congrArg Subtype.val ht
    have : a⁻¹ = t := by rw [inv_eq_of_mul_eq_one_right ht']
    rw [this]; exact t.2

  let SF : IntermediateField k (LaurentSeries k) :=
    { carrier := S
      mul_mem' := fun {a b} ha hb => hmul a b ha hb
      one_mem' := hone
      add_mem' := fun {a b} ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      algebraMap_mem' := fun r => by
        show algebraMap k (LaurentSeries k) r ∈ S
        rw [IsScalarTower.algebraMap_apply k K₁ (LaurentSeries k) r, Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ _ hone
      inv_mem' := fun a ha => hinv a ha }
  have hFkS : (qExpFunctionFieldC k Γ) ≤ SF := by
    show adjoin k (intFormRatiosC k Γ) ≤ SF
    rw [adjoin_le_iff, ← image_intFormRatiosC φ Γ]
    rintro _ ⟨y, hy, rfl⟩
    exact hsub y (intFormRatiosC_subset κ Γ hy)

  have hK₁F : K₁ ≤ (qExpFunctionFieldC k Γ) := by
    rw [hK₁, adjoin_le_iff, Set.singleton_subset_iff]
    exact hjk
  let N₁ : IntermediateField K₁ (LaurentSeries k) := extendScalars hK₁F
  have hN₁S : Subalgebra.toSubmodule N₁.toSubalgebra ≤ S := by
    intro z hz
    have hz' : z ∈ (qExpFunctionFieldC k Γ) := hz
    exact hFkS hz'
  haveI hfdN : FiniteDimensional K₁ N₁ :=
    Module.Finite.of_injective (Submodule.inclusion hN₁S) (Submodule.inclusion_injective hN₁S)
  have hrankN : Module.finrank K₁ N₁ ≤ n := by
    have h1 : Module.finrank K₁ (Subalgebra.toSubmodule N₁.toSubalgebra) ≤ Module.finrank K₁ S :=
      Submodule.finrank_mono hN₁S
    exact h1.trans hSrank

  have hmap : K₀.map (qExpFunctionFieldC k Γ).val = K₁ := by
    have h := adjoin_map k ({x'} : Set (qExpFunctionFieldC k Γ)) (qExpFunctionFieldC k Γ).val
    rw [Set.image_singleton] at h
    rw [show (qExpFunctionFieldC k Γ).val x' = jqModC k from hx'] at h
    exact h
  let e₀ : K₀ ≃ₐ[k] K₁ := (K₀.equivMap (qExpFunctionFieldC k Γ).val).trans (equivOfEq hmap)
  have he₀ : ∀ b : K₀, ((e₀ b : K₁) : LaurentSeries k) = ((b : (qExpFunctionFieldC k Γ)) : LaurentSeries k) := by
    intro b
    rfl
  let e₂ : N₁ ≃+* (qExpFunctionFieldC k Γ) := RingEquiv.refl (qExpFunctionFieldC k Γ)
  have hcomm : (algebraMap K₀ (qExpFunctionFieldC k Γ)).comp e₀.symm.toRingEquiv.toRingHom =
      e₂.toRingHom.comp (algebraMap K₁ N₁) := by
    refine RingHom.ext fun a => ?_
    apply Subtype.ext
    change (((e₀.symm a : K₀) : (qExpFunctionFieldC k Γ)) : LaurentSeries k) = (a : LaurentSeries k)
    rw [← he₀ (e₀.symm a), AlgEquiv.apply_symm_apply]
  refine ⟨Module.Finite.of_equiv_equiv (A₁ := K₁) (B₁ := N₁) (A₂ := K₀) (B₂ := (qExpFunctionFieldC k Γ))
    e₀.symm.toRingEquiv e₂ hcomm, ?_⟩
  rw [← Algebra.finrank_eq_of_equiv_equiv (R₀ := K₁) (S₀ := N₁) (R₁ := K₀) (S₁ := (qExpFunctionFieldC k Γ))
    e₀.symm.toRingEquiv e₂ hcomm]
  exact hrankN

end Transfer

section Residue

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

include hA in
theorem isAlgebraic_residueField :
    letI : CharP (IsLocalRing.ResidueField A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def
      (Fact.out : p.Prime) hA
    letI := ZMod.algebra (IsLocalRing.ResidueField A) p
    Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField A) := by
  letI : CharP (IsLocalRing.ResidueField A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def
    (Fact.out : p.Prime) hA
  letI := ZMod.algebra (IsLocalRing.ResidueField A) p
  have hp : p.Prime := Fact.out
  refine ⟨fun ybar => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective ybar

  have hyQ : IsAlgebraic ℚ (y : AlgebraicClosure ℚ) := by
    have h := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic (y : AlgebraicClosure ℚ)
    convert h using 2
  have hyalg : IsAlgebraic ℤ (y : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr hyQ
  obtain ⟨P, hP0, hPy⟩ := hyalg
  set Q := P.primPart with hQ
  have hc0 : P.content ≠ 0 := fun h => hP0 (content_eq_zero_iff.mp h)
  have hQy : aeval (y : AlgebraicClosure ℚ) Q = 0 := by
    have h1 : aeval (y : AlgebraicClosure ℚ) (C P.content * Q) = 0 := by
      rw [← eq_C_content_mul_primPart]; exact hPy
    rw [map_mul, aeval_C, mul_eq_zero] at h1
    exact h1.resolve_left ((map_ne_zero_iff _ (RingHom.injective_int _)).mpr hc0)

  have hQyA : eval₂ (Int.castRingHom A) y Q = 0 := by
    have hinj : Function.Injective A.subtype := Subtype.val_injective
    apply hinj
    rw [hom_eval₂, map_zero]
    have h2 : (A.subtype.comp (Int.castRingHom A)) = algebraMap ℤ (AlgebraicClosure ℚ) := RingHom.ext_int _ _
    rw [h2]
    exact hQy

  set Qbar := Q.map (Int.castRingHom (ZMod p)) with hQbar
  have hQbar0 : Qbar ≠ 0 := by
    intro h0
    have hdvd : ∀ i, (p : ℤ) ∣ Q.coeff i := by
      intro i
      have hi := congrArg (fun R : (ZMod p)[X] => R.coeff i) h0
      simp only [hQbar, coeff_map, coeff_zero, eq_intCast] at hi
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hi
    have hunit : IsUnit (p : ℤ) := (isPrimitive_primPart P) (p : ℤ) ((C_dvd_iff_dvd_coeff _ _).mpr hdvd)
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hunit
    exact hp.one_lt.ne' hunit
  refine ⟨Qbar, hQbar0, ?_⟩
  rw [aeval_def, hQbar, eval₂_map]
  have h3 : (algebraMap (ZMod p) (IsLocalRing.ResidueField A)).comp (Int.castRingHom (ZMod p)) =
      (IsLocalRing.residue A).comp (Int.castRingHom A) := RingHom.ext_int _ _
  rw [h3, ← hom_eval₂, hQyA, map_zero]

end Residue

section CharZero

variable (K : Type*) [Field K]

theorem coe_eq_zero_of_mem_maximalIdeal_top {a : (⊤ : ValuationSubring K)}
    (ha : a ∈ IsLocalRing.maximalIdeal (⊤ : ValuationSubring K)) : (a : K) = 0 := by
  by_contra h
  apply (IsLocalRing.mem_maximalIdeal _).mp ha
  refine ⟨⟨a, ⟨(a : K)⁻¹, trivial⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ h)
  · exact Subtype.ext (inv_mul_cancel₀ h)

def residueTopHom : IsLocalRing.ResidueField (⊤ : ValuationSubring K) →+* K :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal (⊤ : ValuationSubring K)) (⊤ : ValuationSubring K).subtype
    fun _ ha => coe_eq_zero_of_mem_maximalIdeal_top K ha

end CharZero

section Bound

open ModularCurve IntermediateField

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
  (hT : ModularGroup.T ∈ Γ)
  (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ')
  (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)

include hT hΓ' hneg in

theorem bound_of_isAlgClosed (K' : Type*) [Field K'] [IsAlgClosed K']
    (x' : qExpFunctionFieldC K' Γ) (hx' : (x' : LaurentSeries K') = jqModC K') :
    FiniteDimensional (adjoin K' ({x'} : Set (qExpFunctionFieldC K' Γ))) (qExpFunctionFieldC K' Γ) ∧
      Module.finrank (adjoin K' ({x'} : Set (qExpFunctionFieldC K' Γ)))
        (qExpFunctionFieldC K' Γ) ≤ Γ'.index := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K'
  rcases CharP.char_is_prime_or_zero K' p with hp | rfl
  ·
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp⟩
    haveI : CharP (IsLocalRing.ResidueField A) p :=
      ValuationSubring.charP_residueField_of_liesOverPrime_def hp hA
    letI := ZMod.algebra (IsLocalRing.ResidueField A) p
    letI := ZMod.algebra K' p
    haveI : Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField A) :=
      isAlgebraic_residueField p A hA
    let φ : IsLocalRing.ResidueField A →+* K' :=
      (IsAlgClosed.lift (R := ZMod p) (S := IsLocalRing.ResidueField A) (M := K')).toRingHom
    obtain ⟨xκ, hxκ, -, hfd, hle⟩ :=
      ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
        (AlgebraicClosure ℚ) A Γ hT

    have hy : jqModC (AlgebraicClosure ℚ) ∈
        laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) := by
      have h := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (F₀ := qExpFunctionFieldC ℚ Γ)
        (intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ))
      rwa [coeffEmb, coeffMap_jqModC] at h
    have hb := hle ⟨_, hy⟩ rfl
    have hidx := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
      (AlgebraicClosure ℚ) Γ hT Γ' hΓ' hneg ⟨_, hy⟩ rfl
    obtain ⟨hfd', hle'⟩ := transfer φ Γ xκ hxκ x' hx' hfd
    exact ⟨hfd', hle'.trans (hb.trans hidx)⟩
  ·
    haveI : CharZero K' := CharP.charP_to_charZero K'
    obtain ⟨xκ, hxκ, -, hfd, hle⟩ :=
      ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
        K' (⊤ : ValuationSubring K') Γ hT
    have hy : jqModC K' ∈ laurentBaseChange K' (qExpFunctionFieldC ℚ Γ) := by
      have h := coeffEmb_mem_laurentBaseChange K' (F₀ := qExpFunctionFieldC ℚ Γ)
        (intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ))
      rwa [coeffEmb, coeffMap_jqModC] at h
    have hb := hle ⟨_, hy⟩ rfl
    have hidx := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
      K' Γ hT Γ' hΓ' hneg ⟨_, hy⟩ rfl
    obtain ⟨hfd', hle'⟩ := transfer (residueTopHom K') Γ xκ hxκ x' hx' hfd
    exact ⟨hfd', hle'.trans (hb.trans hidx)⟩

end Bound

end P2MKcQExpDeg

end

open P2MKcQExpDeg ModularCurve IntermediateField in

theorem solution
    (K : Type*) [Field K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ)
    (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ')
    (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
    (x : ModularCurve.qExpFunctionFieldC K Γ)
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K) :
    FiniteDimensional
        (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ) ∧
      Module.finrank
          (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
          (ModularCurve.qExpFunctionFieldC K Γ) ≤ Γ'.index := by
  classical

  have hjK' : jqModC (AlgebraicClosure K) ∈ qExpFunctionFieldC (AlgebraicClosure K) Γ :=
    intFormRatiosC_subset (AlgebraicClosure K) Γ
      (ModularCurve.jqModC_mem_intFormRatiosC (AlgebraicClosure K) Γ)
  obtain ⟨hfd', hle'⟩ := bound_of_isAlgClosed Γ hT Γ' hΓ' hneg (AlgebraicClosure K) ⟨_, hjK'⟩ rfl
  haveI := hfd'
  have hxt : Transcendental K (x : LaurentSeries K) := by rw [hx]; exact transcendental_jqModC K
  have hxx' : ((⟨_, hjK'⟩ : qExpFunctionFieldC (AlgebraicClosure K) Γ) :
      LaurentSeries (AlgebraicClosure K)) =
      coeffMap (algebraMap K (AlgebraicClosure K)) (x : LaurentSeries K) := by
    rw [hx, coeffMap_jqModC]
  obtain ⟨hfdK, hleK⟩ :=
    ModularCurve.finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
      (algebraMap K (AlgebraicClosure K)) Γ x ⟨_, hjK'⟩ hxt hxx'
  exact ⟨hfdK, hleK.trans hle'⟩

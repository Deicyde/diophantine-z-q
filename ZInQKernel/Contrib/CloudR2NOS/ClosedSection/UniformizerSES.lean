/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section GM11 sub-gap (G3) `UniformizerSequence`, PROVED natively (W07 + Mathlib only, no
FLT blueprint). SOURCE ONLY, UNCOMPILED. Native HELD. No kernel/ABI/admission grade.

For `X` flat over a DVR `C`, an invertible `F` and an irreducible `ϖ`, the literal sequence
`0 → F --ϖ--> F --η--> i_* i^* F → 0` (`i = f.fiberι (closedPoint C)`, `η` the adjunction unit) is
short exact. Everything is checked on sections over small AFFINE opens `W`:
* W07 `bijective_sectionsModuleBaseChange` on the literal closed-fibre square identifies
  `Γ(i^*F, i⁻¹W)` with `κ ⊗_C Γ(F, W)`, and `η_W` with `m ↦ 1 ⊗ m`;
* `C → κ(s)` is surjective with kernel `𝔪 = (ϖ)` (Mathlib `Spec.residueFieldIso`,
  `Ideal.algebraMap_residueField_surjective`, `Ideal.algebraMap_residueField_eq_zero`,
  `irreducible_iff_uniformizer`), so `1 ⊗ m = 0 ⇔ m ∈ ϖ Γ(F, W)` (Mathlib
  `quotTensorEquivQuotSMul`) and `m ↦ 1 ⊗ m` is onto;
* `ϖ` acts injectively on `Γ(F, W)` by W07 `isFlatOver_of_isInvertible` and Mathlib
  `Module.Flat.isSMulRegular_of_nonZeroDivisors`;
* sheaf-level exactness / mono / epi from the section statements: W07 `exact_of_exact_sectionsAb`
  (with Mathlib `ShortComplex.exact_iff_mono`) and W07 `Hom.epi_of_locally_surjective`;
* the composite vanishes by W07 `pullbackSection_smul_appTop` (since `ϖ ↦ 0` in `κ(s)`).
No properness, Noetherian, dimension or characteristic hypothesis.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step3Gaps
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.BaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Exactness
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Flat
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.ExactSequence
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.UniformizerSES

/-! ### Commutative algebra of `m ↦ 1 ⊗ m` along a surjection -/

section TensorAlgebra

variable {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M]

/-- Along a surjective algebra map every tensor is `1 ⊗ m`. -/
theorem exists_one_tmul (hsurj : Function.Surjective (algebraMap A B)) (t : B ⊗[A] M) :
    ∃ m : M, (1 : B) ⊗ₜ[A] m = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul b m =>
    obtain ⟨c, rfl⟩ := hsurj b
    exact ⟨c • m, by rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]⟩
  | add t t' ht ht' =>
    obtain ⟨m, rfl⟩ := ht
    obtain ⟨m', rfl⟩ := ht'
    exact ⟨m + m', TensorProduct.tmul_add _ _ _⟩

/-- Along a surjective algebra map `A → B` with kernel `I`, `1 ⊗ m = 0` in `B ⊗_A M` forces
`m ∈ I • M`. -/
theorem mem_ker_smul_top_of_one_tmul_eq_zero (hsurj : Function.Surjective (algebraMap A B))
    (m : M) (h : (1 : B) ⊗ₜ[A] m = 0) :
    m ∈ (RingHom.ker (algebraMap A B)) • (⊤ : Submodule A M) := by
  let e : (A ⧸ RingHom.ker (Algebra.ofId A B)) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hsurj
  let E : B ⊗[A] M ≃ₗ[A] M ⧸ (RingHom.ker (Algebra.ofId A B)) • (⊤ : Submodule A M) :=
    (TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl A M)).trans
      (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker (Algebra.ofId A B)))
  have he1 : e.symm (1 : B) = Ideal.Quotient.mk (RingHom.ker (Algebra.ofId A B)) (1 : A) := by
    rw [map_one, map_one]
  have h1 : E ((1 : B) ⊗ₜ[A] m) = Submodule.Quotient.mk m := by
    change TensorProduct.quotTensorEquivQuotSMul M _
      ((TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl A M)) ((1 : B) ⊗ₜ[A] m)) = _
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply, he1,
      TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  rw [h, map_zero] at h1
  exact (Submodule.Quotient.mk_eq_zero _).mp h1.symm

/-- Membership in `(r) • M` is divisibility by `r`. -/
theorem exists_smul_eq_of_mem_span_singleton_smul {r : A} {m : M}
    (hm : m ∈ (Ideal.span {r} : Ideal A) • (⊤ : Submodule A M)) : ∃ m' : M, r • m' = m := by
  rw [Submodule.ideal_span_singleton_smul] at hm
  obtain ⟨m', -, hm'⟩ := (Submodule.mem_smul_pointwise_iff_exists m r ⊤).mp hm
  exact ⟨m', hm'⟩

end TensorAlgebra

/-! ### The residue map at the closed point -/

section Residue

variable (C : Type u) [CommRing C] [IsLocalRing C]

/-- The ring map `C → κ(s)` underlying `fromSpecResidueField` at the closed point. -/
noncomputable def resMap :
    CommRingCat.of C ⟶ (Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C) :=
  CommRingCat.ofHom (algebraMap C (IsLocalRing.closedPoint C).asIdeal.ResidueField) ≫
    (Scheme.Spec.residueFieldIso (CommRingCat.of C) (IsLocalRing.closedPoint C)).inv

theorem fromSpecResidueField_closedPoint_eq :
    (Spec (CommRingCat.of C)).fromSpecResidueField (IsLocalRing.closedPoint C) =
      Spec.map (resMap C) := by
  rw [resMap, Spec.map_comp, Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]

theorem resMap_surjective : Function.Surjective (resMap C) := by
  haveI : (IsLocalRing.closedPoint C).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal C
  intro y
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.Spec.residueFieldIso (CommRingCat.of C) (IsLocalRing.closedPoint C)).inv).2 y
  obtain ⟨c, rfl⟩ := Ideal.algebraMap_residueField_surjective (IsLocalRing.closedPoint C).asIdeal z
  exact ⟨c, hz⟩

theorem resMap_eq_zero_iff (c : C) : resMap C c = 0 ↔ c ∈ IsLocalRing.maximalIdeal C := by
  have hinj := (ConcreteCategory.bijective_of_isIso
    (Scheme.Spec.residueFieldIso (CommRingCat.of C) (IsLocalRing.closedPoint C)).inv).1
  change (Scheme.Spec.residueFieldIso (CommRingCat.of C) (IsLocalRing.closedPoint C)).inv
    (algebraMap C (IsLocalRing.closedPoint C).asIdeal.ResidueField c) = 0 ↔ _
  constructor
  · intro h
    have h' : algebraMap C (IsLocalRing.closedPoint C).asIdeal.ResidueField c = 0 :=
      hinj (h.trans (map_zero _).symm)
    exact Ideal.algebraMap_residueField_eq_zero.mp h'
  · intro h
    rw [(Ideal.algebraMap_residueField_eq_zero (I := (IsLocalRing.closedPoint C).asIdeal)).mpr h,
      map_zero]

/-- On global sections, `fromSpecResidueField` at the closed point is the residue map. -/
theorem appTop_fromSpecResidueField_inv (c : C) :
    ((Spec (CommRingCat.of C)).fromSpecResidueField (IsLocalRing.closedPoint C)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c) =
      (Scheme.ΓSpecIso _).inv (resMap C c) := by
  rw [fromSpecResidueField_closedPoint_eq]
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (resMap C)) c).symm

end Residue

/-! ### (G3) -/

/-- **(G3) proved.** -/
theorem uniformizerSequence : UniformizerSequence.{u} := by
  intro C _ _ _ X f _ F _ ϖ hϖ
  -- the literal closed-fibre square
  let g := (Spec (CommRingCat.of C)).fromSpecResidueField (IsLocalRing.closedPoint C)
  let i := f.fiberι (IsLocalRing.closedPoint C)
  have cart : IsPullback i (f.fiberToSpecResidueField (IsLocalRing.closedPoint C)) f g :=
    IsPullback.of_hasPullback f g
  letI : Algebra Γ(Spec (CommRingCat.of C), ⊤)
      Γ(Spec ((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C)), ⊤) :=
    g.appTop.hom.toAlgebra
  have hg : algebraMap Γ(Spec (CommRingCat.of C), ⊤)
      Γ(Spec ((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C)), ⊤) =
        g.appTop.hom := rfl
  haveI : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F :=
    SheafOfModules.IsInvertible.isQuasicoherent inferInstance
  let ϖ' : Γ(Spec (CommRingCat.of C), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of C)).inv ϖ
  let a : Γ(X, ⊤) := f.appTop ϖ'
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal C := (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  have hspan : IsLocalRing.maximalIdeal C = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  -- (F1) `Γ(Spec C) → Γ(Spec κ)` is surjective
  have hsurj : Function.Surjective (algebraMap Γ(Spec (CommRingCat.of C), ⊤)
      Γ(Spec ((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C)), ⊤)) := by
    intro y
    obtain ⟨c, hc⟩ := resMap_surjective C ((Scheme.ΓSpecIso _).hom y)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of C)).inv c, ?_⟩
    change g.appTop ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c) = y
    rw [appTop_fromSpecResidueField_inv C, hc, Iso.hom_inv_id_apply]
  -- (F2) its kernel is generated by `ϖ'`
  have hker : RingHom.ker (algebraMap Γ(Spec (CommRingCat.of C), ⊤)
      Γ(Spec ((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C)), ⊤)) ≤
        Ideal.span {ϖ'} := by
    intro r hr
    rw [RingHom.mem_ker] at hr
    change g.appTop r = 0 at hr
    have hr' : g.appTop ((Scheme.ΓSpecIso (CommRingCat.of C)).inv
        ((Scheme.ΓSpecIso (CommRingCat.of C)).hom r)) = 0 := by
      rw [Iso.hom_inv_id_apply]
      exact hr
    rw [appTop_fromSpecResidueField_inv C] at hr'
    have h0 : resMap C ((Scheme.ΓSpecIso (CommRingCat.of C)).hom r) = 0 :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1 (hr'.trans (map_zero _).symm)
    rw [resMap_eq_zero_iff, hspan, Ideal.mem_span_singleton'] at h0
    obtain ⟨d, hd⟩ := h0
    refine Ideal.mem_span_singleton'.2 ⟨(Scheme.ΓSpecIso (CommRingCat.of C)).inv d, ?_⟩
    rw [← Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of C)) r, ← hd, map_mul]
  -- (F3) `ϖ'` dies in the residue field
  have hϖ0 : algebraMap Γ(Spec (CommRingCat.of C), ⊤)
      Γ(Spec ((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C)), ⊤) ϖ' = 0 := by
    change g.appTop ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ϖ) = 0
    rw [appTop_fromSpecResidueField_inv C, (resMap_eq_zero_iff C ϖ).2 hϖm, map_zero]
  -- `ϖ'` is a non-zero-divisor
  haveI : IsDomain Γ(Spec (CommRingCat.of C), ⊤) :=
    MulEquiv.isDomain C (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv.toMulEquiv
  have hϖ'ne : ϖ' ≠ 0 := by
    intro h0
    apply hϖ.ne_zero
    have h := congrArg (fun x => (Scheme.ΓSpecIso (CommRingCat.of C)).hom x)
      (show (Scheme.ΓSpecIso (CommRingCat.of C)).inv ϖ = 0 from h0)
    simp only at h
    rwa [Iso.inv_hom_id_apply, map_zero] at h
  have hϖnzd : ϖ' ∈ nonZeroDivisors Γ(Spec (CommRingCat.of C), ⊤) :=
    mem_nonZeroDivisors_of_ne_zero hϖ'ne
  -- `a •` is injective on sections over affine opens (relative flatness)
  have hinj : ∀ W : X.Opens, IsAffineOpen W → ∀ m : Γ(F, W),
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op a • m = 0 → m = 0 := by
    intro W hW m hm
    letI : Module Γ(Spec (CommRingCat.of C), ⊤) Γ(F, W) :=
      Module.compHom _ (f.appLE ⊤ W (by simp)).hom
    haveI : Module.Flat Γ(Spec (CommRingCat.of C), ⊤) Γ(F, W) :=
      Scheme.Modules.isFlatOver_of_isInvertible f F ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ (by simp)
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(F, W)) hϖnzd
    exact hreg (show ϖ' • m = ϖ' • (0 : Γ(F, W)) by rw [smul_zero]; exact hm)
  -- the composite vanishes
  have w : F.smulHom a ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F = 0 := by
    ext U m
    have key : Scheme.Modules.pullbackSection i
        ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f.appTop ϖ')) • m) = 0 := by
      rw [Scheme.Modules.pullbackSection_smul_appTop cart F hg, hϖ0, map_zero, map_zero,
        zero_smul]
    simpa [Scheme.Modules.pullbackSection] using key
  refine ⟨w, ?_⟩
  -- mono
  haveI : Mono (F.smulHom a) := by
    let S0 : ShortComplex X.Modules :=
      ShortComplex.mk (0 : (0 : X.Modules) ⟶ F) (F.smulHom a) zero_comp
    refine (ShortComplex.exact_iff_mono (S := S0) rfl).1 ?_
    refine Scheme.Modules.exact_of_exact_sectionsAb S0 fun x V hxV => ?_
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
    refine ⟨W, hxW, hWV, ?_⟩
    rw [ShortComplex.ab_exact_iff]
    intro m hm
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact (hinj W hW m hm).symm
  -- epi
  haveI : Epi ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F) := by
    refine Scheme.Modules.Hom.epi_of_locally_surjective _ fun W0 y x hx => ?_
    obtain ⟨W, hW, hxW, hWW0⟩ := exists_isAffineOpen_mem_and_subset hx
    refine ⟨W, hWW0, hxW, ?_⟩
    obtain ⟨t, ht⟩ := (Scheme.Modules.bijective_sectionsModuleBaseChange cart F hg hW).2
      (((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F)).presheaf.map
        (homOfLE hWW0).op y)
    obtain ⟨m, rfl⟩ := exists_one_tmul hsurj t
    refine ⟨m, ?_⟩
    rw [← ht, Scheme.Modules.sectionsModuleBaseChange_tmul, one_smul]
    rfl
  -- exactness in the middle
  have hexact : (ShortComplex.mk _ _ w).Exact := by
    refine Scheme.Modules.exact_of_exact_sectionsAb _ fun x V hxV => ?_
    obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
    refine ⟨W, hxW, hWV, ?_⟩
    rw [ShortComplex.ab_exact_iff]
    intro m hm
    have h1 : (1 : Γ(Spec ((Spec (CommRingCat.of C)).residueField (IsLocalRing.closedPoint C)), ⊤))
        ⊗ₜ[Γ(Spec (CommRingCat.of C), ⊤)] (m : Scheme.Modules.sectionsModule f F W) = 0 := by
      apply (Scheme.Modules.bijective_sectionsModuleBaseChange cart F hg hW).1
      rw [Scheme.Modules.sectionsModuleBaseChange_tmul, one_smul, map_zero]
      exact hm
    obtain ⟨m', hm'⟩ := exists_smul_eq_of_mem_span_singleton_smul
      (Submodule.smul_mono_left hker (mem_ker_smul_top_of_one_tmul_eq_zero hsurj _ h1))
    exact ⟨m', hm'⟩
  exact ShortComplex.ShortExact.mk' hexact inferInstance inferInstance

end ZInQ.Contrib.CloudR2NOS.ClosedSection.UniformizerSES

/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero (git blob 1e58d6e1ff0c28bbeaaf1012f96118c00471bc21, sha256 282b4bc9c2695c01cb67f7b99807a6d87a4155ff79dfaec7a8efe53c220358e6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DifferentialPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_constantFieldDescent_correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Differential_map_correspondence_regularDifferentials_of_constantFieldExtension
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_baseChange
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_baseChange_correspondence_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_constantFieldExtension
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_normFormulaAlong
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace A1F45R2

universe u v w x

section FreeAlgebraFacts

theorem lift_comp_reindex {α β A : Type*} [Semiring A] [Algebra ℤ A] (e : α → β) (g : β → A) :
    (FreeAlgebra.lift ℤ g).comp (FreeAlgebra.lift ℤ (fun a => FreeAlgebra.ι ℤ (e a))) =
      FreeAlgebra.lift ℤ (g ∘ e) := by
  apply FreeAlgebra.hom_ext
  funext a
  simp

theorem lift_reindex_apply {α β A : Type*} [Semiring A] [Algebra ℤ A] (e : α → β) (g : β → A)
    (q : FreeAlgebra ℤ α) :
    FreeAlgebra.lift ℤ g (FreeAlgebra.lift ℤ (fun a => FreeAlgebra.ι ℤ (e a)) q) =
      FreeAlgebra.lift ℤ (g ∘ e) q := by
  rw [← lift_comp_reindex e g]; rfl

theorem exists_finset_reindex {ι : Type*} (p : FreeAlgebra ℤ ι) :
    ∃ (s : Finset ι) (q : FreeAlgebra ℤ (↥s)),
      FreeAlgebra.lift ℤ (fun j : ↥s => FreeAlgebra.ι ℤ (j : ι)) q = p := by
  classical
  induction p using FreeAlgebra.induction with
  | grade0 r => exact ⟨∅, algebraMap ℤ _ r, by simp⟩
  | grade1 i =>
      exact ⟨{i}, FreeAlgebra.ι ℤ ⟨i, Finset.mem_singleton_self i⟩, by simp⟩
  | mul a b ha hb =>
      obtain ⟨s, qa, rfl⟩ := ha
      obtain ⟨t, qb, rfl⟩ := hb
      refine ⟨s ∪ t,
        FreeAlgebra.lift ℤ (fun j : ↥s => FreeAlgebra.ι ℤ
          (⟨(j : ι), Finset.mem_union_left t j.2⟩ : ↥(s ∪ t))) qa *
        FreeAlgebra.lift ℤ (fun j : ↥t => FreeAlgebra.ι ℤ
          (⟨(j : ι), Finset.mem_union_right s j.2⟩ : ↥(s ∪ t))) qb, ?_⟩
      rw [map_mul, lift_reindex_apply, lift_reindex_apply]
      rfl
  | add a b ha hb =>
      obtain ⟨s, qa, rfl⟩ := ha
      obtain ⟨t, qb, rfl⟩ := hb
      refine ⟨s ∪ t,
        FreeAlgebra.lift ℤ (fun j : ↥s => FreeAlgebra.ι ℤ
          (⟨(j : ι), Finset.mem_union_left t j.2⟩ : ↥(s ∪ t))) qa +
        FreeAlgebra.lift ℤ (fun j : ↥t => FreeAlgebra.ι ℤ
          (⟨(j : ι), Finset.mem_union_right s j.2⟩ : ↥(s ∪ t))) qb, ?_⟩
      rw [map_add, lift_reindex_apply, lift_reindex_apply]
      rfl

theorem unop_lift_equivariant {ι R R' V W : Type*} [Semiring R] [Semiring R'] [AddCommGroup V]
    [AddCommGroup W] [Module R V] [Module R' W] (f : V →+ W)
    (T : ι → Module.End R V) (S : ι → Module.End R' W) (h : ∀ i v, f (T i v) = S i (f v))
    (q : FreeAlgebra ℤ ι) (v : V) :
    f (MulOpposite.unop (FreeAlgebra.lift ℤ (fun i => MulOpposite.op (T i)) q) v) =
      MulOpposite.unop (FreeAlgebra.lift ℤ (fun i => MulOpposite.op (S i)) q) (f v) := by
  induction q using FreeAlgebra.induction generalizing v with
  | grade0 r =>
      rw [AlgHom.commutes, AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op,
        MulOpposite.algebraMap_apply, MulOpposite.unop_op, eq_intCast, eq_intCast,
        Module.End.intCast_apply, Module.End.intCast_apply, map_zsmul]
  | grade1 i =>
      simp only [FreeAlgebra.lift_ι_apply, MulOpposite.unop_op, h]
  | mul a b ha hb =>
      simp only [map_mul, MulOpposite.unop_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
      simp only [map_add, MulOpposite.unop_add, LinearMap.add_apply, ha, hb]

end FreeAlgebraFacts

section Curve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem hfg_along
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (ψ : F →ₐ[K] F') (hfin : FiniteAlong K ψ) :
    ∃ y : F', Transcendental K y ∧
      FiniteDimensional (IntermediateField.adjoin K ({y} : Set F')) F' := by
  obtain ⟨x, hx, hxfin⟩ := hfg
  letI : Algebra F F' := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI : Module.Finite F F' := hfin
  set Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hKx
  set y : F' := ψ x with hy_def
  set Ky : IntermediateField K F' := IntermediateField.adjoin K ({y} : Set F') with hKy
  have hy : Transcendental K y := fun h =>
    hx ((isAlgebraic_algHom_iff ψ ψ.toRingHom.injective).mp h)
  have hmap : ∀ z ∈ Kx, ψ z ∈ Ky := by
    intro z hz
    have hKxy : Kx.map ψ = Ky := by
      rw [hKx, IntermediateField.adjoin_map, Set.image_singleton]
    rw [← hKxy]
    exact ⟨z, hz, rfl⟩
  let f : Kx →+* Ky := ψ.toRingHom.restrict Kx Ky hmap
  letI algKxF' : Algebra Kx F' := ((algebraMap F F').comp (algebraMap Kx F)).toAlgebra
  haveI : IsScalarTower Kx F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite Kx F' := Module.Finite.trans F F'
  letI : Algebra Kx Ky := f.toAlgebra
  haveI : IsScalarTower Kx Ky F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfd : FiniteDimensional Ky F' := Module.Finite.of_restrictScalars_finite Kx Ky F'
  exact ⟨y, hy, hfd⟩

theorem isCurveOver_along [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (ψ : F →ₐ[K] F') (hfin : FiniteAlong K ψ) : IsCurveOver K F' := by
  obtain ⟨y, hy, hfd⟩ := hfg_along hfg ψ hfin
  haveI := hfd
  have hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({y} : Set F')) F' := inferInstance
  exact AlgebraicCurve.isCurveOver_of_transcendental hy hfd hsep

theorem isIntegral_of_finiteAlong (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) :
    φ.toRingHom.IsIntegral := by
  letI : Algebra F F' := algebraAlong φ
  haveI : Module.Finite F F' := hfin
  intro z
  exact (Algebra.IsIntegral.of_finite F F').isIntegral z

end Curve

end A1F45R2

open A1F45R2 in
theorem solution
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type*} (F' : ι → Type*) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    [∀ i, HasPrincipalDivisors K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hψ : ∀ i, (ψ i).toRingHom.IsIntegral)
    (hFI : ∀ i, FundamentalIdentityAlong K (φ i) (hφ i))
    (hfin : ∀ i, FiniteAlong K (ψ i)) (hN : ∀ i, NormFormulaAlong K (ψ i) (hfin i))
    (p : FreeAlgebra ℤ ι)
    (hp : ∀ ω ∈ regularDifferentials K F,
      MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun i => MulOpposite.op (Differential.correspondence (φ i) (ψ i))) p) ω = 0) :
    FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)).toIntLinearMap) p = 0 := by
  classical

  obtain ⟨s, q, rfl⟩ := exists_finset_reindex p
  rw [lift_reindex_apply]

  have hq : ∀ ω ∈ regularDifferentials K F,
      MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun j : ↥s => MulOpposite.op (Differential.correspondence (φ j) (ψ j))) q) ω = 0 := by
    intro ω hω
    have := hp ω hω
    rwa [lift_reindex_apply] at this

  clear hp

  haveI hcurve' : ∀ j : ↥s, IsCurveOver K (F' j) := fun j => isCurveOver_along hfg (ψ j) (hfin j)
  have hfg' : ∀ j : ↥s, ∃ y : F' j, Transcendental K y ∧
      FiniteDimensional (IntermediateField.adjoin K ({y} : Set (F' j))) (F' j) :=
    fun j => hfg_along hfg (ψ j) (hfin j)

  obtain ⟨K₀, F₀, F'₀, instK₀, instF₀, instF'₀, algK₀K, algK₀ℂ, hK₀ac, hK₀cnt, algK₀F₀, algF₀F,
      algK₀F, towK₀KF, towK₀F₀F, hcurve₀, algK₀F'₀, algF'₀F', algK₀F', towK₀KF', towK₀F'₀F',
      hcurve'₀, φ₀, ψ₀, hfg₀, hgenF, hfg'₀, hgen', hφcomm, hψcomm, hfinφ₀, hfinψ₀⟩ :=
    AlgebraicCurve.exists_constantFieldDescent_correspondence K F hfg (fun j : ↥s => F' j)
      (fun j => φ j) (fun j => ψ j) (fun j => hφ j) (fun j => hfin j)
  haveI : CharZero K₀ := RingHom.charZero (algebraMap K₀ K)
  haveI : CharZero F₀ := charZero_of_injective_algebraMap (algebraMap K₀ F₀).injective

  have hφ₀ : ∀ j, (φ₀ j).toRingHom.IsIntegral := fun j => isIntegral_of_finiteAlong (φ₀ j) (hfinφ₀ j)
  have hψ₀ : ∀ j, (ψ₀ j).toRingHom.IsIntegral := fun j => isIntegral_of_finiteAlong (ψ₀ j) (hfinψ₀ j)
  have hsepφ₀ : ∀ j, SeparableAlong K₀ (φ₀ j) := fun j =>
    AlgebraicCurve.separableAlong_of_charZero (φ₀ j) (hφ₀ j)
  have hsepψ₀ : ∀ j, SeparableAlong K₀ (ψ₀ j) := fun j =>
    AlgebraicCurve.separableAlong_of_charZero (ψ₀ j) (hψ₀ j)
  have hFI₀ : ∀ j, FundamentalIdentityAlong K₀ (φ₀ j) (hφ₀ j) := fun j =>
    AlgebraicCurve.fundamentalIdentityAlong (φ₀ j) (hφ₀ j) (hfinφ₀ j) (hsepφ₀ j)
  have hN₀ : ∀ j, NormFormulaAlong K₀ (ψ₀ j) (hfinψ₀ j) := fun j =>
    AlgebraicCurve.normFormulaAlong (ψ₀ j) (hfinψ₀ j) (hsepψ₀ j)

  haveI : SMulCommClass K F₀ F :=
    ⟨fun k f y => by simp only [Algebra.smul_def]; ring⟩
  have hidint₀ : (AlgHom.id K₀ F₀).toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ Function.surjective_id
  have hidintK : (AlgHom.id K F).toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ Function.surjective_id

  obtain ⟨-, hinjK, hregK, -⟩ :=
    AlgebraicCurve.Differential.map_correspondence_regularDifferentials_of_constantFieldExtension
      K₀ F₀ hfg₀ F₀ hfg₀ (AlgHom.id K₀ F₀) (AlgHom.id K₀ F₀) hidint₀ hidint₀ K F hfg hgenF F hfg
      hgenF (AlgHom.id K F) (AlgHom.id K F) (fun _ => rfl) (fun _ => rfl) hidintK hidintK

  have hbcK : ∀ (j : ↥s) (ω : Ω[F₀⁄K₀]),
      KaehlerDifferential.map K₀ K F₀ F (Differential.correspondence (φ₀ j) (ψ₀ j) ω) =
        Differential.correspondence (φ j) (ψ j) (KaehlerDifferential.map K₀ K F₀ F ω) := fun j =>
    (AlgebraicCurve.Differential.map_correspondence_regularDifferentials_of_constantFieldExtension
      K₀ F₀ hfg₀ (F'₀ j) (hfg'₀ j) (φ₀ j) (ψ₀ j) (hφ₀ j) (hψ₀ j) K F hfg hgenF (F' j) (hfg' j)
      (hgen' j) (φ j) (ψ j) (hφcomm j) (hψcomm j) (hφ j) (hψ j)).1
  have hq₀ : ∀ ω ∈ regularDifferentials K₀ F₀,
      MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun j : ↥s => MulOpposite.op (Differential.correspondence (φ₀ j) (ψ₀ j))) q) ω = 0 := by
    intro ω hω
    apply hinjK
    rw [map_zero]
    have := unop_lift_equivariant (KaehlerDifferential.map K₀ K F₀ F).toAddMonoidHom
      (fun j : ↥s => Differential.correspondence (φ₀ j) (ψ₀ j))
      (fun j : ↥s => Differential.correspondence (φ j) (ψ j))
      (fun j v => hbcK j v) q ω
    simp only [LinearMap.toAddMonoidHom_coe] at this
    rw [this]
    exact hq _ (hregK ω hω)
  clear hq hbcK hinjK hregK

  obtain ⟨x₀, hx₀, hx₀fin⟩ := hfg₀
  haveI : Algebra.EssFiniteType K₀ F₀ :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx₀ hx₀fin
  haveI : HasCanonicalDivisor (K := K₀) (F := F₀) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver (K := K₀) (F := F₀)
  have hfg₀ : ∃ x : F₀, Transcendental K₀ x ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀ := ⟨x₀, hx₀, hx₀fin⟩
  obtain ⟨Fℂ, instFℂ, algℂFℂ, algF₀Fℂ, algK₀Fℂ, towK₀ℂFℂ, towK₀F₀Fℂ, hcurveℂ, hcanℂ, hfgℂ,
      hgenℂ⟩ := AlgebraicCurve.exists_constantFieldExtension K₀ F₀ ℂ hfg₀

  have hbcT := fun j : ↥s =>
    AlgebraicCurve.exists_baseChange_correspondence_of_constantFieldExtension K₀ F₀ hfg₀ (F'₀ j)
      (φ₀ j) (ψ₀ j) (hφ₀ j) (hψ₀ j) (hFI₀ j) (hfinψ₀ j) (hN₀ j) ℂ Fℂ hfgℂ hgenℂ
  choose F'ℂ instF'ℂ algℂF'ℂ algF'₀F'ℂ algK₀F'ℂ towK₀ℂF'ℂ towK₀F'₀F'ℂ hcurve'ℂ φℂ ψℂ hφℂ hψℂ hFIℂ
    hfinℂ hNℂ hrestℂ using hbcT
  have hfg'ℂ : ∀ j, ∃ x' : F'ℂ j, Transcendental ℂ x' ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x'} : Set (F'ℂ j))) (F'ℂ j) :=
    fun j => (hrestℂ j).1
  have hgen'ℂ : ∀ j, IntermediateField.adjoin ℂ (Set.range (algebraMap (F'₀ j) (F'ℂ j))) = ⊤ :=
    fun j => (hrestℂ j).2.1
  have hφcommℂ : ∀ j (f : F₀), φℂ j (algebraMap F₀ Fℂ f) = algebraMap (F'₀ j) (F'ℂ j) (φ₀ j f) :=
    fun j => (hrestℂ j).2.2.1
  have hψcommℂ : ∀ j (f : F₀), ψℂ j (algebraMap F₀ Fℂ f) = algebraMap (F'₀ j) (F'ℂ j) (ψ₀ j f) :=
    fun j => (hrestℂ j).2.2.2.1
  clear hrestℂ

  haveI : SMulCommClass ℂ F₀ Fℂ :=
    ⟨fun k f y => by simp only [Algebra.smul_def]; ring⟩
  have hidintℂ : (AlgHom.id ℂ Fℂ).toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ Function.surjective_id
  obtain ⟨-, -, -, hspanℂ⟩ :=
    AlgebraicCurve.Differential.map_correspondence_regularDifferentials_of_constantFieldExtension
      K₀ F₀ hfg₀ F₀ hfg₀ (AlgHom.id K₀ F₀) (AlgHom.id K₀ F₀) hidint₀ hidint₀ ℂ Fℂ hfgℂ hgenℂ Fℂ
      hfgℂ hgenℂ (AlgHom.id ℂ Fℂ) (AlgHom.id ℂ Fℂ) (fun _ => rfl) (fun _ => rfl) hidintℂ hidintℂ
  have hbcℂ : ∀ (j : ↥s) (ω : Ω[F₀⁄K₀]),
      KaehlerDifferential.map K₀ ℂ F₀ Fℂ (Differential.correspondence (φ₀ j) (ψ₀ j) ω) =
        Differential.correspondence (φℂ j) (ψℂ j) (KaehlerDifferential.map K₀ ℂ F₀ Fℂ ω) :=
    fun j =>
    (AlgebraicCurve.Differential.map_correspondence_regularDifferentials_of_constantFieldExtension
      K₀ F₀ hfg₀ (F'₀ j) (hfg'₀ j) (φ₀ j) (ψ₀ j) (hφ₀ j) (hψ₀ j) ℂ Fℂ hfgℂ hgenℂ (F'ℂ j) (hfg'ℂ j)
      (hgen'ℂ j) (φℂ j) (ψℂ j) (hφcommℂ j) (hψcommℂ j) (hφℂ j) (hψℂ j)).1
  have hqℂ : ∀ η ∈ regularDifferentials ℂ Fℂ,
      MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun j : ↥s => MulOpposite.op (Differential.correspondence (φℂ j) (ψℂ j))) q) η = 0 := by
    intro η hη
    set L : Module.End ℂ (Ω[Fℂ⁄ℂ]) := MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun j : ↥s => MulOpposite.op (Differential.correspondence (φℂ j) (ψℂ j))) q) with hL
    suffices hle : Submodule.span ℂ (KaehlerDifferential.map K₀ ℂ F₀ Fℂ ''
        (regularDifferentials K₀ F₀ : Set (Ω[F₀⁄K₀]))) ≤ LinearMap.ker L from
      LinearMap.mem_ker.1 (hle (hspanℂ η hη))
    rw [Submodule.span_le]
    rintro _ ⟨ω, hω, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hL]
    have := unop_lift_equivariant (KaehlerDifferential.map K₀ ℂ F₀ Fℂ).toAddMonoidHom
      (fun j : ↥s => Differential.correspondence (φ₀ j) (ψ₀ j))
      (fun j : ↥s => Differential.correspondence (φℂ j) (ψℂ j))
      (fun j v => hbcℂ j v) q ω
    simp only [LinearMap.toAddMonoidHom_coe] at this
    rw [← this, hq₀ ω hω, map_zero]
  clear hbcℂ hspanℂ hq₀

  haveI : ∀ j, HasPrincipalDivisors ℂ (F'ℂ j) := fun j => IsCurveOver.hasPrincipalDivisors
  have hℂ : FreeAlgebra.lift ℤ (fun j : ↥s =>
      (Pic0.correspondence (φℂ j) (ψℂ j) (hφℂ j) (hψℂ j) (hFIℂ j) (hfinℂ j) (hNℂ j)).toIntLinearMap)
        q = 0 :=
    AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex
      Fℂ hfgℂ (fun j : ↥s => F'ℂ j) φℂ ψℂ hφℂ hψℂ hFIℂ hfinℂ hNℂ q hqℂ

  haveI : ∀ j, HasPrincipalDivisors K₀ (F'₀ j) := fun j => IsCurveOver.hasPrincipalDivisors
  have h₀ : FreeAlgebra.lift ℤ (fun j : ↥s =>
      (Pic0.correspondence (φ₀ j) (ψ₀ j) (hφ₀ j) (hψ₀ j) (hFI₀ j) (hfinψ₀ j) (hN₀ j)).toIntLinearMap)
        q = 0 :=
    AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_baseChange K₀ F₀ hfg₀
      (fun j : ↥s => F'₀ j) φ₀ ψ₀ hφ₀ hψ₀ hFI₀ hfinψ₀ hN₀ q ℂ Fℂ hfgℂ hgenℂ (fun j : ↥s => F'ℂ j)
      hfg'ℂ hgen'ℂ φℂ ψℂ hφcommℂ hψcommℂ hφℂ hψℂ hFIℂ hfinℂ hNℂ hℂ

  exact AlgebraicCurve.Pic0.freeAlgebra_lift_baseChange_correspondence_eq_zero K₀ F₀ hfg₀
    (fun j : ↥s => F'₀ j) φ₀ ψ₀ hφ₀ hψ₀ hFI₀ hfinψ₀ hN₀ q h₀ K F hfg hgenF (fun j : ↥s => F' j)
    hfg' hgen' (fun j => φ j) (fun j => ψ j) hφcomm hψcomm (fun j => hφ j) (fun j => hψ j)
    (fun j => hFI j) (fun j => hfin j) (fun j => hN j)

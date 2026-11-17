/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex (git blob 7919c8cc4c885da3a6aec5cd18f373eead4b6501, sha256 fbea014c1187e4dc03299ed599db2802f91d75fa15360bd73b21a57e66a53101).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DifferentialPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex.A1F45C
end P2MW.S_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex.A1F45C

namespace P2MW.S_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex

set_option autoImplicit false

noncomputable section

open AlgebraicCurve
open scoped Manifold

namespace A1F45C

section Transfer

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] (V : Submodule K W)
variable {ι : Type*}

def cRes (T : ι → Module.End K W) (hT : ∀ i, ∀ w ∈ V, T i w ∈ V) (i : ι) :
    (Module.End K V)ᵐᵒᵖ :=
  MulOpposite.op ((T i).restrict (hT i))

theorem restrict_lift (T : ι → Module.End K W) (hT : ∀ i, ∀ w ∈ V, T i w ∈ V)
    (p : FreeAlgebra ℤ ι) (v : V) :
    ((MulOpposite.unop (FreeAlgebra.lift ℤ (cRes V T hT) p) v : V) : W) =
      MulOpposite.unop (FreeAlgebra.lift ℤ (fun i => MulOpposite.op (T i)) p) (v : W) := by
  induction p using FreeAlgebra.induction generalizing v with
  | grade0 r =>
      rw [AlgHom.commutes, AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op,
        MulOpposite.algebraMap_apply, MulOpposite.unop_op, eq_intCast, eq_intCast,
        Module.End.intCast_apply, Module.End.intCast_apply, Submodule.coe_smul_of_tower]
  | grade1 i =>
      simp only [FreeAlgebra.lift_ι_apply, cRes, MulOpposite.unop_op, LinearMap.coe_restrict_apply]
  | mul a b ha hb =>
      simp only [map_mul, MulOpposite.unop_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb =>
      simp only [map_add, MulOpposite.unop_add, LinearMap.add_apply, Submodule.coe_add, ha, hb]

theorem lift_cRes_eq_zero (T : ι → Module.End K W) (hT : ∀ i, ∀ w ∈ V, T i w ∈ V)
    (p : FreeAlgebra ℤ ι)
    (hp : ∀ w ∈ V,
      MulOpposite.unop (FreeAlgebra.lift ℤ (fun i => MulOpposite.op (T i)) p) w = 0) :
    FreeAlgebra.lift ℤ (cRes V T hT) p = 0 := by
  apply MulOpposite.unop_injective
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [restrict_lift V T hT p v, MulOpposite.unop_zero, LinearMap.zero_apply, Submodule.coe_zero]
  exact hp v v.2

end Transfer

theorem lift_equivariant {ι A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (T : ι → A →+ A) (S : ι → B →+ B) (h : ∀ i a, f (T i a) = S i (f a))
    (q : FreeAlgebra ℤ ι) (a : A) :
    f (FreeAlgebra.lift ℤ (fun i => (T i).toIntLinearMap) q a) =
      FreeAlgebra.lift ℤ (fun i => (S i).toIntLinearMap) q (f a) := by
  induction q using FreeAlgebra.induction generalizing a with
  | grade0 r => simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_zsmul]
  | grade1 i => simp only [FreeAlgebra.lift_ι_apply, AddMonoidHom.coe_toIntLinearMap, h]
  | mul x y hx hy => simp only [map_mul, Module.End.mul_apply, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem lift_mem {ι A : Type*} [AddCommGroup A] (H : AddSubgroup A) (T : ι → A →+ A)
    (hT : ∀ i, ∀ a ∈ H, T i a ∈ H) (q : FreeAlgebra ℤ ι) {a : A} (ha : a ∈ H) :
    FreeAlgebra.lift ℤ (fun i => (T i).toIntLinearMap) q a ∈ H := by
  induction q using FreeAlgebra.induction generalizing a with
  | grade0 r => simpa only [AlgHom.commutes, Module.algebraMap_end_apply] using H.zsmul_mem ha r
  | grade1 i => simpa only [FreeAlgebra.lift_ι_apply, AddMonoidHom.coe_toIntLinearMap] using hT i a ha
  | mul x y hx hy => simpa only [map_mul, Module.End.mul_apply] using hx (hy ha)
  | add x y hx hy => simpa only [map_add, LinearMap.add_apply] using H.add_mem (hx ha) (hy ha)

section Curve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem isCurveOver_along [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (ψ : F →ₐ[K] F') (hfin : FiniteAlong K ψ) : IsCurveOver K F' := by
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
  have hsep : Algebra.IsSeparable Ky F' := by
    haveI : FiniteDimensional Ky F' := hfd
    infer_instance
  exact AlgebraicCurve.isCurveOver_of_transcendental hy hfd hsep

end Curve

section Hurwitz

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
variable {ι : Type*} {n : ℕ}

theorem hurwitz_lift (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (TD : ι → Divisor ℂ F →+ Divisor ℂ F)
    (hTD0 : ∀ i, ∀ D ∈ Divisor.degZero (K := ℂ) (F := F), TD i D ∈ Divisor.degZero (K := ℂ) (F := F))
    (M : FreeAlgebra ℤ ι → Matrix (Fin n) (Fin n) ℂ)
    (hM0 : ∀ r : ℤ, M (algebraMap ℤ _ r) = (r : ℤ) • (1 : Matrix (Fin n) (Fin n) ℂ))
    (hMadd : ∀ x y, M (x + y) = M x + M y) (hMmul : ∀ x y, M (x * y) = M y * M x)
    (hgen : ∀ i, (∀ u ∈ pathPeriodLattice b,
        Matrix.vecMul u (M (FreeAlgebra.ι ℤ i)) ∈ pathPeriodLattice b) ∧
      ∀ D : Divisor ℂ F, Divisor.degree D = 0 →
        abelJacobiDiv b P₀ (TD i D) -
            Matrix.vecMul (abelJacobiDiv b P₀ D) (M (FreeAlgebra.ι ℤ i)) ∈ pathPeriodLattice b)
    (q : FreeAlgebra ℤ ι) :
    (∀ u ∈ pathPeriodLattice b, Matrix.vecMul u (M q) ∈ pathPeriodLattice b) ∧
      ∀ D : Divisor ℂ F, Divisor.degree D = 0 →
        abelJacobiDiv b P₀ (FreeAlgebra.lift ℤ (fun i => (TD i).toIntLinearMap) q D) -
            Matrix.vecMul (abelJacobiDiv b P₀ D) (M q) ∈ pathPeriodLattice b := by
  classical
  induction q using FreeAlgebra.induction with
  | grade0 r =>
      refine ⟨fun u hu => ?_, fun D _ => ?_⟩
      · rw [hM0, Matrix.vecMul_smul, Matrix.vecMul_one]
        exact Submodule.smul_mem _ r hu
      · rw [hM0, Matrix.vecMul_smul, Matrix.vecMul_one, AlgHom.commutes,
          Module.algebraMap_end_apply, map_zsmul, sub_self]
        exact Submodule.zero_mem _
  | grade1 i =>
      simpa only [FreeAlgebra.lift_ι_apply, AddMonoidHom.coe_toIntLinearMap] using hgen i
  | add x y hx hy =>
      refine ⟨fun u hu => ?_, fun D hD => ?_⟩
      · rw [hMadd, Matrix.vecMul_add]
        exact Submodule.add_mem _ (hx.1 u hu) (hy.1 u hu)
      · have h := Submodule.add_mem _ (hx.2 D hD) (hy.2 D hD)
        rw [hMadd, Matrix.vecMul_add, map_add, LinearMap.add_apply, map_add]
        convert h using 1
        abel
  | mul x y hx hy =>
      refine ⟨fun u hu => ?_, fun D hD => ?_⟩
      · rw [hMmul, ← Matrix.vecMul_vecMul]
        exact hx.1 _ (hy.1 u hu)
      · rw [hMmul, ← Matrix.vecMul_vecMul, map_mul, Module.End.mul_apply]

        set E := FreeAlgebra.lift ℤ (fun i => (TD i).toIntLinearMap) y D with hE
        have hE0 : Divisor.degree E = 0 := by
          have := lift_mem (Divisor.degZero (K := ℂ) (F := F)) TD hTD0 y
            ((Divisor.mem_degZero (K := ℂ) (F := F)).2 hD)
          exact (Divisor.mem_degZero (K := ℂ) (F := F)).1 this
        have h1 := hx.2 E hE0
        have h2 := hx.1 _ (hy.2 D hD)
        have h := Submodule.add_mem _ h1 h2
        convert h using 1
        rw [Matrix.sub_vecMul]
        abel

end Hurwitz

section Pic0

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

theorem mk_eq_zero_iff (D : Divisor.degZero (K := k) (F := L)) :
    Pic0.mk D = 0 ↔ (D : Divisor k L).IsPrincipal := by
  rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]

def mkHom : Divisor.degZero (K := k) (F := L) →+ Pic0 k L :=
  QuotientAddGroup.mk' _

@[scoped simp] theorem mkHom_apply (D : Divisor.degZero (K := k) (F := L)) : mkHom D = Pic0.mk D := rfl

end Pic0

end A1F45C
open scoped _root_.P2MW.S_AlgebraicCurve_Pic0_freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero_complex.A1F45C

open A1F45C in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    {ι : Type*} (F' : ι → Type*) [∀ i, Field (F' i)] [∀ i, Algebra ℂ (F' i)]
    [∀ i, HasPrincipalDivisors ℂ (F' i)]
    (φ ψ : ∀ i, F →ₐ[ℂ] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hψ : ∀ i, (ψ i).toRingHom.IsIntegral)
    (hFI : ∀ i, FundamentalIdentityAlong ℂ (φ i) (hφ i))
    (hfin : ∀ i, FiniteAlong ℂ (ψ i)) (hN : ∀ i, NormFormulaAlong ℂ (ψ i) (hfin i))
    (p : FreeAlgebra ℤ ι)
    (hp : ∀ ω ∈ regularDifferentials ℂ F,
      MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun i => MulOpposite.op (Differential.correspondence (φ i) (ψ i))) p) ω = 0) :
    FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)).toIntLinearMap) p = 0 := by
  classical

  obtain ⟨tX, cX, hman, hcomp, ht2, hconn, hF⟩ :=
    AlgebraicCurve.Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex F hfg
  letI : TopologicalSpace (Place ℂ F) := tX
  letI : ChartedSpace ℂ (Place ℂ F) := cX
  haveI : IsManifold 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) (Place ℂ F) := hman
  haveI : CompactSpace (Place ℂ F) := hcomp
  haveI : T2Space (Place ℂ F) := ht2
  haveI : ConnectedSpace (Place ℂ F) := hconn

  obtain ⟨x, hx, hxfin⟩ := hfg
  haveI : Algebra.EssFiniteType ℂ F :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hxfin
  haveI : HasCanonicalDivisor (K := ℂ) (F := F) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver (K := ℂ) (F := F)
  have hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F := ⟨x, hx, hxfin⟩
  set V : Submodule ℂ (Ω[F⁄ℂ]) := regularDifferentials ℂ F with hV
  haveI : Module.Finite ℂ V :=
    (AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := ℂ) (F := F)).1
  set b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V with hb

  obtain ⟨P₀⟩ : Nonempty (Place ℂ F) := inferInstance

  set TΩ : ι → Module.End ℂ (Ω[F⁄ℂ]) := fun i => Differential.correspondence (φ i) (ψ i) with hTΩ
  have hT : ∀ i, ∀ ω ∈ V, TΩ i ω ∈ V := fun i ω hω => by
    haveI : IsCurveOver ℂ (F' i) := isCurveOver_along hfg (ψ i) (hfin i)
    exact AlgebraicCurve.Differential.correspondence_mem_regularDifferentials ℂ F (F' i) hfg (φ i)
      (ψ i) (hφ i) (hψ i) (hfin i) hω

  set R : FreeAlgebra ℤ ι → Module.End ℂ V := fun q =>
    MulOpposite.unop (FreeAlgebra.lift ℤ (cRes V TΩ hT) q) with hR
  set M : FreeAlgebra ℤ ι → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    fun q => LinearMap.toMatrix b b (R q) with hM
  have hM0 : ∀ r : ℤ, M (algebraMap ℤ _ r) = (r : ℤ) • (1 : Matrix _ _ ℂ) := fun r => by
    simp only [hM, hR]
    rw [AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op,
      Algebra.algebraMap_eq_smul_one, map_zsmul, LinearMap.toMatrix_one]
  have hMadd : ∀ x y, M (x + y) = M x + M y := fun x y => by
    simp only [hM, hR, map_add, MulOpposite.unop_add]
  have hMmul : ∀ x y, M (x * y) = M y * M x := fun x y => by
    simp only [hM, hR, map_mul, MulOpposite.unop_mul, LinearMap.toMatrix_mul]

  set TD : ι → Divisor ℂ F →+ Divisor ℂ F :=
    fun i => Divisor.correspondence (φ i) (ψ i) (hφ i) (hψ i) with hTD
  set TZ : ι → Divisor.degZero (K := ℂ) (F := F) →+ Divisor.degZero (K := ℂ) (F := F) :=
    fun i => Pic0.degZeroCorrespondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) with hTZ
  set TP : ι → Pic0 ℂ F →+ Pic0 ℂ F := fun i =>
    Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i) with hTP
  have hTD0 : ∀ i, ∀ D ∈ Divisor.degZero (K := ℂ) (F := F),
      TD i D ∈ Divisor.degZero (K := ℂ) (F := F) :=
    fun i D hD => Divisor.correspondence_mem_degZero (φ i) (ψ i) (hφ i) (hψ i) (hFI i) hD

  set bΩ : Fin (Module.finrank ℂ V) → Ω[F⁄ℂ] := fun i => (b i : Ω[F⁄ℂ]) with hbΩ
  have hgen : ∀ i, (∀ u ∈ pathPeriodLattice bΩ,
        Matrix.vecMul u (M (FreeAlgebra.ι ℤ i)) ∈ pathPeriodLattice bΩ) ∧
      ∀ D : Divisor ℂ F, Divisor.degree D = 0 →
        abelJacobiDiv bΩ P₀ (TD i D) -
            Matrix.vecMul (abelJacobiDiv bΩ P₀ D) (M (FreeAlgebra.ι ℤ i)) ∈ pathPeriodLattice bΩ := by
    intro i
    have hS : ∀ j, Differential.correspondence (φ i) (ψ i) (b j : Ω[F⁄ℂ]) =
        ∑ k, M (FreeAlgebra.ι ℤ i) k j • (b k : Ω[F⁄ℂ]) := by
      intro j
      have hMi : M (FreeAlgebra.ι ℤ i) = LinearMap.toMatrix b b ((TΩ i).restrict (hT i)) := by
        simp only [hM, hR, FreeAlgebra.lift_ι_apply, cRes, MulOpposite.unop_op]
      have hrepr := b.sum_repr ((TΩ i).restrict (hT i) (b j))
      have hcoe : (((TΩ i).restrict (hT i) (b j) : V) : Ω[F⁄ℂ]) =
          Differential.correspondence (φ i) (ψ i) (b j : Ω[F⁄ℂ]) := rfl
      rw [← hcoe, ← hrepr]
      simp only [hMi, LinearMap.toMatrix_apply, Submodule.coe_sum, Submodule.coe_smul]
    exact AlgebraicCurve.abelJacobiDiv_correspondence_sub_vecMul_mem_pathPeriodLattice F hfg hF
      (F' i) (φ i) (ψ i) (hφ i) (hψ i) (hfin i) b P₀ (M (FreeAlgebra.ι ℤ i)) hS
  have hHur := hurwitz_lift bΩ P₀ TD hTD0 M hM0 hMadd hMmul hgen p

  have hRp : R p = 0 := by
    simp only [hR]
    rw [lift_cRes_eq_zero V TΩ hT p hp, MulOpposite.unop_zero]
  have hMp : M p = 0 := by simp only [hM]; rw [hRp, map_zero]

  apply LinearMap.ext
  intro c
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [LinearMap.zero_apply]
  have h1 : FreeAlgebra.lift ℤ (fun i => (TP i).toIntLinearMap) p (Pic0.mk D) =
      Pic0.mk (FreeAlgebra.lift ℤ (fun i => (TZ i).toIntLinearMap) p D) := by
    have := lift_equivariant (mkHom (k := ℂ) (L := F)) TZ TP (fun i a => rfl) p D
    simpa only [mkHom_apply] using this.symm
  have h2 : ((FreeAlgebra.lift ℤ (fun i => (TZ i).toIntLinearMap) p D :
      Divisor.degZero (K := ℂ) (F := F)) : Divisor ℂ F) =
      FreeAlgebra.lift ℤ (fun i => (TD i).toIntLinearMap) p (D : Divisor ℂ F) :=
    lift_equivariant (Divisor.degZero (K := ℂ) (F := F)).subtype TZ TD (fun i a => rfl) p D
  rw [h1, mk_eq_zero_iff, h2]
  have hdeg0 : Divisor.degree
      (FreeAlgebra.lift ℤ (fun i => (TD i).toIntLinearMap) p (D : Divisor ℂ F)) = 0 := by
    rw [← h2]; exact (FreeAlgebra.lift ℤ (fun i => (TZ i).toIntLinearMap) p D).2
  have hAJ := hHur.2 (D : Divisor ℂ F) D.2
  rw [hMp, Matrix.vecMul_zero, sub_zero] at hAJ
  exact AlgebraicCurve.Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice F hfg hF b P₀ _
    hdeg0 hAJ

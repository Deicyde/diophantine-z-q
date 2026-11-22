/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_zero_of_not_isFinite_endKerStr_of_forall_eulerChar_tensorPow_eq. Apache-2.0.
Modification notice (CloudB3 Worker13, 2026-11-15/16): ported to Lean 4.35.0 / Mathlib v4.35.0
(namespace-wrapped port on origin/cloud-b3/w13-recovery).
Modified for the Z-in-Q kernel (charpoly-port, 2026-11-17): the Worker13 port unwrapped into the
CloudB3W16Torsion conventions (original declaration namespaces; imports relocated to the
CloudB3W16Torsion vendor; the FLT-suffixed renames of CloudB3W16Torsion/NOTICE.md applied; port
shim commands removed). Mathematical statements and proofs retained, subject to Lean 4.35 adaptations
listed in scratch/charpoly-port/log.md.
Full original notices/credits: LICENSE, NOTICE.upstream, ATTRIBUTION.upstream.md in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_of_surjective
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isInvertible_finiteBySections
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_le_forall_exists_notMem_support_zeroSchemeIdeal_tensor_tensorPow
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_degree_lt_of_forall_eulerChar_twist_tensorPow_eq_of_inter_iInter_support_zeroSchemeIdeal_eq_empty
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_lift_tensorSectionsBilin_of_isQuasicoherent
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_zero_of_not_isFinite_endKerStr_of_forall_eulerChar_tensorPow_eq

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace Polynomial AlgebraicGeometry.Polynomial"
open NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

noncomputable section

namespace P2mNonIsog

section Poly

theorem eval_zero_basis_smul {ι : Type*} [DecidableEq ι] (S : Finset ι) (v : ι → ℚ) (m : ℚ) (hm : m ≠ 0) (i : ι) :
    (Lagrange.basis S (fun j => v j * m) i).eval 0 = (Lagrange.basis S v i).eval 0 := by
  rw [Lagrange.basis, Lagrange.basis, eval_prod, eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X, zero_sub]
  rw [← sub_mul, mul_inv, mul_neg, mul_neg]
  congr 1
  field_simp

theorem eval_zero_eq_sum {ι : Type*} [DecidableEq ι] (S : Finset ι) (v : ι → ℚ) (hv : Set.InjOn v S)
    (m : ℚ) (hm : m ≠ 0) (R : ℚ[X]) (hR : R.degree < S.card) :
    R.eval 0 = ∑ j ∈ S, R.eval (v j * m) * (Lagrange.basis S v j).eval 0 := by
  have hinj : Set.InjOn (fun j => v j * m) S := fun a ha b hb h =>
    hv ha hb (mul_right_cancel₀ hm h)
  conv_lhs => rw [Lagrange.eq_interpolate hinj hR]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, eval_zero_basis_smul S v m hm j]

theorem poly_eq_of_forall_succ (p q : ℚ[X]) (h : ∀ m : ℕ, p.eval ((m + 1 : ℕ) : ℚ) = q.eval ((m + 1 : ℕ) : ℚ)) :
    p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := Set.range (fun m : ℕ => ((m + 1 : ℕ) : ℚ))) ?_
    (Set.infinite_range_of_injective fun a b hab => by exact_mod_cast Nat.succ_injective (by exact_mod_cast hab))
  rintro _ ⟨m, rfl⟩
  exact h m

end Poly

section Compare

p2m_open "AlgebraicGeometry.OModulePresheaf~ker~zero"

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem isInvertible_tensorPow (L : V.Modules) (hL : Scheme.Modules.IsInvertible L) (n : ℕ) :
    Scheme.Modules.IsInvertible (L.tensorPowFLT n) := by
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unitFLT V
  | succ n ih => exact ih.tensor hL

variable (M N : V.Modules)

abbrev cmp (U : V.Opens) : Γ(M, U) ⊗[Γ(V, U)] Γ(N, U) →ₗ[Γ(V, U)] Γ(M ⊗ N, U) :=
  TensorProduct.lift (Scheme.Modules.tensorSectionsBilin M N U)

theorem cmp_tmul (U : V.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    cmp M N U (s ⊗ₜ t) = Scheme.Modules.tensorSections s t := by
  simp [cmp]

def resTw {U U' : V.Opens} (h : U ≤ U') :
    Γ(M, U') ⊗[Γ(V, U')] Γ(N, U') →ₛₗ[(V.presheaf.map (homOfLE h).op).hom] Γ(M, U) ⊗[Γ(V, U)] Γ(N, U) :=
  (ofModules π M).tensorResₛₗ (ofModules π N) h

theorem resTw_tmul {U U' : V.Opens} (h : U ≤ U') (x : Γ(M, U')) (y : Γ(N, U')) :
    resTw π M N h (x ⊗ₜ y) = M.presheaf.map (homOfLE h).op x ⊗ₜ N.presheaf.map (homOfLE h).op y := rfl

theorem cmp_resTw {U U' : V.Opens} (h : U ≤ U') (t : Γ(M, U') ⊗[Γ(V, U')] Γ(N, U')) :
    cmp M N U (resTw π M N h t) = (M ⊗ N).presheaf.map (homOfLE h).op (cmp M N U' t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [resTw_tmul, cmp_tmul, cmp_tmul]
    exact (Scheme.Modules.map_homOfLE_tensorSections h x y).symm
  | add a b ha hb => simp only [map_add, ha, hb]

theorem cmp_res {U U' : V.Opens} (h : U ≤ U') (t : ((ofModules π M).twist N).obj U') :
    cmp M N U (((ofModules π M).twist N).res h t) = (M ⊗ N).presheaf.map (homOfLE h).op (cmp M N U' t) :=
  cmp_resTw π M N h t

def cmpHom : AffHom ((ofModules π M).twist N) (ofModules π (M ⊗ N)) where
  app U :=
    { toFun := cmp M N U.1
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r t => map_smul (cmp M N U.1)
        ((Scheme.TwoAffineOpenCover.algebraOfHom π U.1).algebraMap r) t }
  app_smul U a t := map_smul (cmp M N U.1) a t
  naturality h := LinearMap.ext fun t => cmp_res π M N h t

theorem cmpHom_bijective (hM : (ofModules π M).IsQuasicoherent) (hN : (ofModules π N).IsQuasicoherent)
    (U : V.affineOpens) : Function.Bijective ((cmpHom π M N).app U) :=
  Scheme.Modules.bijective_lift_tensorSectionsBilin_of_isQuasicoherent π hM hN U

theorem eulerChar_eq_of_bijective [IsSeparated π] (K : V.OrderedAffineCover) {F G : OModulePresheaf π}
    (φ : AffHom F G) (hφ : ∀ U : V.affineOpens, Function.Bijective (φ.app U)) :
    F.eulerChar K = G.eulerChar K := by
  obtain ⟨⟨e0⟩, hS⟩ := AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective φ hφ K
  have h : ∀ i, F.cechFinrank K i = G.cechFinrank K i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [eulerChar_def, eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem eulerChar_ofModules_tensor_eq [IsSeparated π] (K : V.OrderedAffineCover)
    (hM : (ofModules π M).IsQuasicoherent) (hN : (ofModules π N).IsQuasicoherent) :
    (ofModules π (M ⊗ N)).eulerChar K = ((ofModules π M).twist N).eulerChar K :=
  (eulerChar_eq_of_bijective π K (cmpHom π M N) (cmpHom_bijective π M N hM hN)).symm

variable {M N} in

theorem eulerChar_congr (K : V.OrderedAffineCover) (e : M ≅ N) :
    (ofModules π M).eulerChar K = (ofModules π N).eulerChar K := by
  obtain ⟨⟨e0⟩, hS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso π e K
  have h : ∀ i, (ofModules π M).cechFinrank K i = (ofModules π N).cechFinrank K i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [eulerChar_def, eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

end Compare

section Skel

variable {X Y : Scheme.{u}} (φ : X ⟶ Y)

theorem cls_tensor {C : Type*} [Category C] [MonoidalCategory C] (A B : C) :
    toSkeleton (A ⊗ B) = toSkeleton A * toSkeleton B :=
  Skeleton.toSkeleton_tensorObj A B

theorem cls_unit {C : Type*} [Category C] [MonoidalCategory C] : toSkeleton (𝟙_ C) = (1 : Skeleton C) :=
  Skeleton.one_eq.symm

theorem cls_tensorPow {Z : Scheme.{u}} (N : Z.Modules) (n : ℕ) : toSkeleton (N.tensorPowFLT n) = toSkeleton N ^ n := by
  induction n with
  | zero => rw [Scheme.Modules.tensorPow_zeroFLT, pow_zero, cls_unit]
  | succ n ih => rw [Scheme.Modules.tensorPow_succFLT, cls_tensor, ih, pow_succ]

theorem cls_pullback_tensor (A B : Y.Modules) :
    toSkeleton ((Scheme.Modules.pullback φ).obj (A ⊗ B)) =
      toSkeleton ((Scheme.Modules.pullback φ).obj A) * toSkeleton ((Scheme.Modules.pullback φ).obj B) := by
  rw [← cls_tensor]
  exact toSkeleton_eq_toSkeleton_iff.mpr ⟨Scheme.Modules.pullbackTensorObjIsoFLT φ A B⟩

theorem cls_pullback_tensorPow (A : Y.Modules) (n : ℕ) :
    toSkeleton ((Scheme.Modules.pullback φ).obj (A.tensorPowFLT n)) = toSkeleton ((Scheme.Modules.pullback φ).obj A) ^ n := by
  rw [← cls_tensorPow]
  exact toSkeleton_eq_toSkeleton_iff.mpr (Scheme.Modules.nonempty_pullback_tensorPow_iso φ A n)

theorem nonempty_iso_pow_pullback_tensor (𝓛 𝓗 : Y.Modules) (n m : ℕ) :
    Nonempty (((Scheme.Modules.pullback φ).obj (𝓛 ⊗ 𝓗.tensorPowFLT n)).tensorPowFLT m ≅
      ((Scheme.Modules.pullback φ).obj 𝓛).tensorPowFLT m ⊗ ((Scheme.Modules.pullback φ).obj 𝓗).tensorPowFLT (n * m)) := by
  refine toSkeleton_eq_toSkeleton_iff.mp ?_
  rw [cls_tensorPow, cls_pullback_tensor, cls_pullback_tensorPow, cls_tensor, cls_tensorPow, cls_tensorPow, mul_pow,
    ← pow_mul]

theorem nonempty_iso_tensor_pow_zero {Z : Scheme.{u}} (𝓐 𝓑 : Z.Modules) (m : ℕ) :
    Nonempty (𝓐.tensorPowFLT m ⊗ 𝓑.tensorPowFLT 0 ≅ 𝓐.tensorPowFLT m) :=
  ⟨ρ_ _⟩

theorem nonempty_iso_unit_tensor {Z : Scheme.{u}} (𝓐 : Z.Modules) : Nonempty (𝟙_ Z.Modules ⊗ 𝓐 ≅ 𝓐) :=
  ⟨λ_ _⟩

end Skel

section Geometry

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem isNoetherian [IsProper f] : IsNoetherian A := by
  haveI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f
  exact {}

theorem dim_lt_of_ne_univ [IrreducibleSpace A] (g : ℕ) [SmoothOfRelativeDimension g f]
    (B : Set A) (hB : IsClosed B) (hne : B ≠ Set.univ) : topologicalKrullDim B < g := by
  have h1 : topologicalKrullDim B + 1 ≤ topologicalKrullDim (Set.univ : Set A) :=
    (IrreducibleSpace.isIrreducible_univ A).topologicalKrullDim_add_one_le_of_isClosed_of_ne hB
      (Set.subset_univ B) hne
  have h2 : topologicalKrullDim (Set.univ : Set A) = topologicalKrullDim A :=
    IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ A).isHomeomorph
  have h3 : topologicalKrullDim A ≤ g := SmoothOfRelativeDimension.topologicalKrullDim_le f g
  have h : topologicalKrullDim B + 1 ≤ (g : WithBot ℕ∞) := (h1.trans_eq h2).trans h3
  exact ENat.WithBot.add_one_le_natCast_iff.mp h

private theorem _root_.P2mNonIsog.isClosed_range [IsProper f] (γ : SchemeHomOver f f) : IsClosed (Set.range γ.1.base) := by
  haveI : IsProper γ.1 := by
    have : IsProper (γ.1 ≫ f) := by rw [γ.2]; infer_instance
    exact IsProper.of_comp γ.1 f
  exact γ.1.isClosedMap.isClosed_range

p2m_export "P2mNonIsog" "isClosed_range"
end Geometry

section Sections

variable {X Y : Scheme.{u}} (φ : X ⟶ Y) {M : Y.Modules}

theorem support_zeroSchemeIdeal_pullbackSection (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ Y.Modules ⟶ M) :
    ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSectionFLT φ s)).support : Set X) =
      φ.base ⁻¹' (Scheme.Modules.zeroSchemeIdeal s).support := by
  rw [← Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal φ hM s, Scheme.IdealSheafData.support_comap]
  rfl

theorem univ_inter_iInter_eq_empty (hM : Scheme.Modules.IsInvertible M) {g : ℕ} (s : Fin g → (𝟙_ Y.Modules ⟶ M))
    (hs : Set.range φ.base ∩ ⋂ i, ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set Y) = ∅) :
    (((⊤ : Closeds X) : Set X)) ∩
      ⋂ i, ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSectionFLT φ (s i))).support : Set X) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  have hx' : φ.base x ∈ Set.range φ.base ∩ ⋂ i, ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set Y) := by
    refine ⟨⟨x, rfl⟩, Set.mem_iInter.mpr fun i => ?_⟩
    have := Set.mem_iInter.mp hx.2 i
    rwa [support_zeroSchemeIdeal_pullbackSection φ hM (s i)] at this
  rw [hs] at hx'
  exact hx'

end Sections

section Main

variable {K : Type u} [Field K] [IsAlgClosed K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

p2m_open "AlgebraicGeometry.OModulePresheaf~ker~zero"

theorem locTriv_unit : ∀ x : A, ∃ (U : A.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj (𝟙_ A.Modules) ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :=
  (Scheme.Modules.isInvertible_unitFLT A).1

theorem subsingleton_sections_of_eq_bot (W : A.Opens) (h : W = ⊥) : Subsingleton Γ(A, W) := by
  subst h
  infer_instance

omit [IsAlgClosed K] in

theorem supportedIn_top (G : OModulePresheaf f) : G.SupportedIn ⊤ := by
  intro U hU
  have hU' : (U.1 : Set A) = ∅ := by simpa [Closeds.coe_top, Set.inter_univ] using hU
  have hbot : U.1 = ⊥ := TopologicalSpace.Opens.ext (by simpa using hU')
  haveI : Subsingleton Γ(A, U.1) := subsingleton_sections_of_eq_bot U.1 hbot
  exact Module.subsingleton Γ(A, U.1) _

theorem main (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (γ : SchemeHomOver f f)
    (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
        L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
    (hker : ¬ IsFinite (L.endKerStr γ))
    (p : Polynomial ℚ)
    (hp : ∀ m : ℕ, ((OModulePresheaf.ofModules f
        (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPowFLT m)).eulerChar 𝒦 : ℚ) = p.eval (m : ℚ)) :
    p.coeff g = 0 := by
  classical
  haveI : IsProper f := hA.proper
  haveI : IsIntegral A := AbelianSchemePropertyBundle.isIntegral_of_field hA
  haveI : IsNoetherian A := isNoetherian (f := f)

  set B : Set A := Set.range γ.1.base with hBdef
  have hBcl : IsClosed B := isClosed_range γ
  have hBne : B ≠ Set.univ := by
    intro hB
    haveI : Surjective γ.1 := ⟨Set.range_eq_univ.mp hB⟩
    exact hker (RelativeGroupLaw.isFinite_endKerStr_of_surjective K f L hA γ hγ)
  have hBdim : topologicalKrullDim B < g := dim_lt_of_ne_univ (f := f) g B hBcl hBne

  obtain ⟨𝓗, h𝓗, N, 𝔓, hfin⟩ := AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections K f hA
  haveI : IsFinite 𝔓.toProj := hfin
  obtain ⟨a₀, ha₀⟩ :=
    Scheme.Modules.ProjPresentation.exists_forall_le_forall_exists_notMem_support_zeroSchemeIdeal_tensor_tensorPow
      f 𝔓 𝓛 h𝓛

  set 𝓜 : ℕ → A.Modules := fun n => 𝓛 ⊗ 𝓗.tensorPowFLT n with h𝓜def
  have h𝓜inv : ∀ n, Scheme.Modules.IsInvertible (𝓜 n) := fun n => h𝓛.tensor (isInvertible_tensorPow 𝓗 h𝓗 n)
  set 𝓛' : A.Modules := (Scheme.Modules.pullback γ.1).obj 𝓛 with h𝓛'def
  set 𝓗' : A.Modules := (Scheme.Modules.pullback γ.1).obj 𝓗 with h𝓗'def
  have h𝓛' : Scheme.Modules.IsInvertible 𝓛' := h𝓛.pullback γ.1
  have h𝓗' : Scheme.Modules.IsInvertible 𝓗' := h𝓗.pullback γ.1

  have hdeg : ∀ n : ℕ, a₀ ≤ n → ∃ q : ℚ[X], q.degree < g ∧
      ∀ m : ℕ, ((ofModules f (((Scheme.Modules.pullback γ.1).obj (𝓜 n)).tensorPowFLT m)).eulerChar 𝒦 : ℚ) =
        q.eval (m : ℚ) := by
    intro n hn

    obtain ⟨s, hs⟩ :=
      Scheme.Modules.exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt f
        (fun _ : Fin g => 𝓜 n) (fun _ => h𝓜inv n) (fun _ x => ha₀ n hn x) B hBcl hBdim

    have ht := univ_inter_iInter_eq_empty γ.1 (h𝓜inv n) s hs

    have hMn : ∀ x : A, ∃ (U : A.Opens), x ∈ U ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj
        ((Scheme.Modules.pullback γ.1).obj (𝓜 n)) ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :=
      ((h𝓜inv n).pullback γ.1).1
    have hGc : (ofModules f (𝟙_ A.Modules)).IsCoherent := isCoherent_ofModules_of_locallyTrivial f _ locTriv_unit
    have hGq : (ofModules f (𝟙_ A.Modules)).IsQuasicoherent := isQuasicoherent_ofModules_of_locallyTrivial f _ locTriv_unit
    have hGs : (ofModules f (𝟙_ A.Modules)).SupportedIn ⊤ := supportedIn_top _
    have hdimtop : topologicalKrullDim ((⊤ : Closeds A) : Set A) ≤ g :=
      (Topology.IsInducing.topologicalKrullDim_le (Topology.IsEmbedding.subtypeVal.isInducing)).trans
        (SmoothOfRelativeDimension.topologicalKrullDim_le f g)
    obtain ⟨q, -, hq⟩ := OModulePresheaf.exists_polynomial_forall_eulerChar_twist_tensorPow_eq f 𝒦
      (ofModules f (𝟙_ A.Modules)) hGc hGq ⊤ hGs g hdimtop _ hMn
    have hqdeg : q.degree < g :=
      OModulePresheaf.degree_lt_of_forall_eulerChar_twist_tensorPow_eq_of_inter_iInter_support_zeroSchemeIdeal_eq_empty
        f 𝒦 _ hMn (fun i => Scheme.Modules.pullbackSectionFLT γ.1 (s i)) (ofModules f (𝟙_ A.Modules)) hGc hGq ⊤ hGs
        ht q hq
    refine ⟨q, hqdeg, fun m => ?_⟩

    have hNq : (ofModules f (((Scheme.Modules.pullback γ.1).obj (𝓜 n)).tensorPowFLT m)).IsQuasicoherent :=
      isQuasicoherent_ofModules_of_locallyTrivial f _ (isInvertible_tensorPow _ ((h𝓜inv n).pullback γ.1) m).1
    rw [← hq m, ← eulerChar_ofModules_tensor_eq f (𝟙_ A.Modules) _ 𝒦 hGq hNq]
    exact_mod_cast eulerChar_congr f 𝒦 (λ_ _).symm
  choose! qn hqn_deg hqn using hdeg

  have hR : ∀ m : ℕ, ∃ R : ℚ[X], R.natDegree ≤ g ∧
      ∀ n : ℕ, ((ofModules f (𝓛'.tensorPowFLT m ⊗ 𝓗'.tensorPowFLT n)).eulerChar 𝒦 : ℚ) = R.eval (n : ℚ) := by
    intro m
    have hMm := (isInvertible_tensorPow 𝓛' h𝓛' m).1
    exact OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq f 𝒦 (𝓛'.tensorPowFLT m)
      (isCoherent_ofModules_of_locallyTrivial f _ hMm) (isQuasicoherent_ofModules_of_locallyTrivial f _ hMm)
      ⊤ (supportedIn_top _) g
      ((Topology.IsInducing.topologicalKrullDim_le (Topology.IsEmbedding.subtypeVal.isInducing)).trans
        (SmoothOfRelativeDimension.topologicalKrullDim_le f g))
      𝓗' h𝓗'.1
  choose R hRdeg hRval using hR

  set v : Fin (g + 1) → ℚ := fun j => ((a₀ + j : ℕ) : ℚ) with hvdef
  have hv : Set.InjOn v (Finset.univ : Finset (Fin (g + 1))) := by
    intro a _ b _ hab
    have hab' : ((a₀ + a : ℕ) : ℚ) = ((a₀ + b : ℕ) : ℚ) := hab
    have : (a₀ + a : ℕ) = a₀ + b := by exact_mod_cast hab'
    exact Fin.ext (by omega)
  set lam : Fin (g + 1) → ℚ := fun j => (Lagrange.basis Finset.univ v j).eval 0 with hlamdef

  set P : ℚ[X] := ∑ j : Fin (g + 1), C (lam j) * qn (a₀ + j) with hPdef
  have hPdeg : P.degree < g := by
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe g)).mpr fun j _ => ?_)
    exact (degree_mul_le _ _).trans_lt (lt_of_le_of_lt (add_le_of_nonpos_left degree_C_le)
      (hqn_deg (a₀ + j) (Nat.le_add_right _ _)))

  have hpP : p = P := by
    refine poly_eq_of_forall_succ p P fun m₀ => ?_
    set m : ℕ := m₀ + 1 with hmdef
    have hm : (m : ℚ) ≠ 0 := by positivity

    have h0 : p.eval (m : ℚ) = (R m).eval 0 := by
      rw [← hp m]
      have := hRval m 0
      rw [Nat.cast_zero] at this
      rw [← this]
      have e1 : Nonempty (𝓛'.tensorPowFLT m ⊗ 𝓗'.tensorPowFLT 0 ≅ 𝓛'.tensorPowFLT m) := nonempty_iso_tensor_pow_zero _ _ m
      obtain ⟨e1⟩ := e1
      exact_mod_cast (eulerChar_congr f 𝒦 e1).symm

    have hnode : ∀ j : Fin (g + 1), (R m).eval (v j * m) = (qn (a₀ + j)).eval (m : ℚ) := by
      intro j
      have h1 := hRval m ((a₀ + j) * m)
      have h2 := hqn (a₀ + j) (Nat.le_add_right _ _) m
      have hcast : (((a₀ + j) * m : ℕ) : ℚ) = v j * m := by rw [hvdef]; push_cast; ring
      rw [hcast] at h1
      rw [← h1, ← h2]
      obtain ⟨e⟩ := nonempty_iso_pow_pullback_tensor γ.1 𝓛 𝓗 (a₀ + j) m
      exact_mod_cast (eulerChar_congr f 𝒦 e).symm
    have hRm : (R m).degree < (Finset.univ : Finset (Fin (g + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      by_cases hR0 : R m = 0
      · rw [hR0, degree_zero]; exact WithBot.bot_lt_coe _
      · rw [degree_eq_natDegree hR0]; exact_mod_cast Nat.lt_succ_of_le (hRdeg m)
    rw [h0, eval_zero_eq_sum Finset.univ v hv (m : ℚ) hm (R m) hRm, hPdef, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hnode j, eval_mul, eval_C, mul_comm]

  rw [hpP]
  exact coeff_eq_zero_of_degree_lt (by exact_mod_cast hPdeg)

end Main

end P2mNonIsog

end

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (γ : SchemeHomOver f f)
    (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
        L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
    (hker : ¬ IsFinite (L.endKerStr γ))
    (p : Polynomial ℚ)
    (hp : ∀ m : ℕ, ((OModulePresheaf.ofModules f
        (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPowFLT m)).eulerChar 𝒦 : ℚ) = p.eval (m : ℚ)) :
    p.coeff g = 0 :=
  P2mNonIsog.main L hA g 𝒦 𝓛 h𝓛 γ (fun t x y => hγ t x y) hker p hp

end S_GoodReductionJacobian_RelativeGroupLaw_coeff_eq_zero_of_not_isFinite_endKerStr_of_forall_eulerChar_tensorPow_eq
end P2MW


/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_zpow_iso_tensorPow_of_symmetric
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_of_isFinite_endKerStr
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open NeronModelInfra
open GoodReductionJacobian
open TopologicalSpace Opposite

universe u

namespace P2mDegNIsog

section V1

open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}


section Points

variable (L : RelativeGroupLaw K f)

theorem compT_mul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f)
    (β δ : SchemeHomOver f f) :
    NeronModelInfra.schemeHomOverComp z (L.mul f β δ) =
      L.mul t (NeronModelInfra.schemeHomOverComp z β) (NeronModelInfra.schemeHomOverComp z δ) := by
  have h := L.mul_natural f t z.1 z.2 β δ
  have e : ∀ δ : SchemeHomOver f f, GoodReductionJacobian.schemeHomOverComp z.1 z.2 δ = NeronModelInfra.schemeHomOverComp z δ :=
    fun δ => Subtype.ext rfl
  rw [e, e, e] at h
  exact h

theorem compT_one {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp z (L.one f) = L.one t := by
  have h := L.one_natural f t z.1 z.2
  have e : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (L.one f) =
    NeronModelInfra.schemeHomOverComp z (L.one f) := Subtype.ext rfl
  rw [e] at h
  exact h

theorem pow_eq_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f) (n : ℕ) :
    letI := L.pointGroup t; x ^ n = L.nsmul t n x := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih]; rfl

theorem comp_idPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp x (RelativeGroupLaw.idPoint (f := f)) = x :=
  Subtype.ext (Category.comp_id _)

theorem isHom_nsmul (hc : L.IsCommutative) (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (L.mul t x y) (L.nsmul f n RelativeGroupLaw.idPoint) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (L.nsmul f n RelativeGroupLaw.idPoint))
        (NeronModelInfra.schemeHomOverComp y (L.nsmul f n RelativeGroupLaw.idPoint)) := by
  induction n with
  | zero =>
      change NeronModelInfra.schemeHomOverComp (L.mul t x y) (L.one f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (L.one f))
          (NeronModelInfra.schemeHomOverComp y (L.one f))
      rw [compT_one, compT_one, compT_one, L.one_mul]
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, compT_mul, compT_mul, compT_mul, ih, comp_idPoint, comp_idPoint,
        comp_idPoint]
      letI := L.pointCommGroup hc t
      change (NeronModelInfra.schemeHomOverComp x (L.nsmul f n RelativeGroupLaw.idPoint) *
          NeronModelInfra.schemeHomOverComp y (L.nsmul f n RelativeGroupLaw.idPoint)) * (x * y) =
        (NeronModelInfra.schemeHomOverComp x (L.nsmul f n RelativeGroupLaw.idPoint) * x) *
          (NeronModelInfra.schemeHomOverComp y (L.nsmul f n RelativeGroupLaw.idPoint) * y)
      exact mul_mul_mul_comm _ _ _ _

end Points

theorem isCommMonObj (L : RelativeGroupLaw K f) (hc : L.IsCommutative) :
    letI := L.grpObjOverMk; IsCommMonObj (Over.mk f) :=
  (L.isCommMonObj_grpObjOverMk_iff_mul_comm).mpr (fun t x y => hc t x y)

private theorem _root_.P2mDegNIsog.geometricallyConnected [IsAlgClosed K] (hA : AbelianSchemePropertyBundle K f) :
    GeometricallyConnected f := by
  haveI : IsIntegral A := GoodReductionJacobian.AbelianSchemePropertyBundle.isIntegral_of_field hA
  haveI : IrreducibleSpace A := inferInstance
  haveI : GeometricallyIrreducible f := GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed f
  exact GeometricallyIrreducible.geometricallyConnectedFLT f
-- The private geometrically-connected helper is used by its module-local name.
def unbundleHom (L : RelativeGroupLaw K f) :
    letI := L.grpObjOverMk; letI := L.pointGroup f;
    (Over.mk f ⟶ Over.mk f) →* SchemeHomOver f f :=
  letI := L.grpObjOverMk; letI := L.pointGroup f
  { toFun := overHomToSchemeHomOver
    map_one' := L.overHomToSchemeHomOver_one f
    map_mul' := fun a b => L.overHomToSchemeHomOver_mul f a b }

theorem toOverHom_idPoint : schemeHomOverToOverHom (RelativeGroupLaw.idPoint (f := f)) = 𝟙 (Over.mk f) :=
  Over.OverMorphism.ext (by simp [schemeHomOverToOverHom])

theorem left_one_zpow_natCast (L : RelativeGroupLaw K f) (n : ℕ) :
    letI := L.grpObjOverMk;
    ((𝟙 (Over.mk f)) ^ (n : ℤ)).left = (L.nsmul f n RelativeGroupLaw.idPoint).1 := by
  letI := L.grpObjOverMk; letI := L.pointGroup f
  rw [zpow_natCast]
  have h := map_pow (unbundleHom L) (𝟙 (Over.mk f)) n
  change overHomToSchemeHomOver ((𝟙 (Over.mk f)) ^ n) = (overHomToSchemeHomOver (𝟙 (Over.mk f))) ^ n at h
  rw [← toOverHom_idPoint, overHomToSchemeHomOver_schemeHomOverToOverHom, pow_eq_nsmul L f] at h
  rw [toOverHom_idPoint] at h
  exact congrArg Subtype.val h

theorem left_one_inv (L : RelativeGroupLaw K f) :
    letI := L.grpObjOverMk;
    ((𝟙 (Over.mk f))⁻¹).left = (L.inv f RelativeGroupLaw.idPoint).1 := by
  letI := L.grpObjOverMk
  have h := L.overHomToSchemeHomOver_inv f (𝟙 (Over.mk f))
  rw [← toOverHom_idPoint, overHomToSchemeHomOver_schemeHomOverToOverHom] at h
  rw [toOverHom_idPoint] at h
  exact congrArg Subtype.val h

section Skel

variable {C : Type*} [Category C] [MonoidalCategory C]

theorem cls_tensor (X Y : C) : toSkeleton (X ⊗ Y) = toSkeleton X * toSkeleton Y :=
  Skeleton.toSkeleton_tensorObj X Y

theorem cls_unit : toSkeleton (𝟙_ C) = (1 : Skeleton C) := Skeleton.one_eq.symm

end Skel

theorem cls_tensorPow {Z : Scheme.{u}} (N : Z.Modules) (n : ℕ) :
    toSkeleton (N.tensorPowFLT n) = toSkeleton N ^ n := by
  induction n with
  | zero => rw [Scheme.Modules.tensorPow_zeroFLT, cls_unit, pow_zero]
  | succ n ih => rw [Scheme.Modules.tensorPow_succFLT, cls_tensor, ih, pow_succ]

theorem exists_orderedAffineCover (hf : IsProper f) : Nonempty A.OrderedAffineCover := by
  haveI : QuasiCompact f := inferInstance
  haveI : CompactSpace (Spec (CommRingCat.of K)) := inferInstanceAs (CompactSpace (PrimeSpectrum K))
  haveI : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : A.affineOpens => ((V : A.Opens) : Set A))
    (fun V => (V : A.Opens).isOpen) (by
      intro x _
      have hx : x ∈ ((⊤ : A.Opens) : Set A) := trivial
      rw [← iSup_affineOpens_eq_top A, TopologicalSpace.Opens.coe_iSup] at hx
      exact hx)
  letI : LinearOrder (s : Set A.affineOpens) :=
    LinearOrder.lift' (fun i => Fintype.equivFin (s : Set A.affineOpens) i) (Equiv.injective _)
  refine ⟨⟨(s : Set A.affineOpens), fun i => (i.1 : A.Opens), fun i => i.1.2, ?_⟩⟩
  apply le_antisymm le_top
  intro x _
  have hx := hs (Set.mem_univ x)
  rw [TopologicalSpace.Opens.mem_iSup]
  simp only [Set.mem_iUnion] at hx
  obtain ⟨V, hV, hxV⟩ := hx
  exact ⟨⟨V, hV⟩, hxV⟩

theorem eulerChar_congr {M M' : A.Modules} (e : M ≅ M') (𝒦 : A.OrderedAffineCover) :
    (OModulePresheaf.ofModules f M).eulerChar 𝒦 = (OModulePresheaf.ofModules f M').eulerChar 𝒦 := by
  obtain ⟨⟨e0⟩, hS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso f e 𝒦
  have h : ∀ i, (OModulePresheaf.ofModules f M).cechFinrank 𝒦 i = (OModulePresheaf.ofModules f M').cechFinrank 𝒦 i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [OModulePresheaf.eulerChar_def, OModulePresheaf.eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

section Alg
open Polynomial
open AlgebraicGeometry.Polynomial

def dil (q : ℚ[X]) (c : ℚ) : ℚ[X] := q.sum fun i a => C (a * c ^ i) * X ^ i

theorem dil_eval (q : ℚ[X]) (c m : ℚ) : (dil q c).eval m = q.eval (c * m) := by
  rw [dil, Polynomial.sum, eval_finsetSum, eval_eq_sum, Polynomial.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [eval_mul, eval_C, eval_pow, eval_X, mul_pow]
  ring

theorem dil_coeff (q : ℚ[X]) (c : ℚ) (g : ℕ) : (dil q c).coeff g = c ^ g * q.coeff g := by
  rw [dil, Polynomial.sum, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · ring
  · rw [mem_support_iff, not_not] at h
    rw [h, mul_zero]

end Alg

end V1

namespace Isog

open AlgebraicGeometry.OModulePresheaf

section Chi

variable {R : Type u} [CommRing R]

theorem eulerChar_eq_of_equiv {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (F' : OModulePresheaf π') (K : V.OrderedAffineCover) (K' : V'.OrderedAffineCover)
    (hcard : Fintype.card K.ι = Fintype.card K'.ι)
    (h0 : Nonempty (F.H0 K ≃ₗ[R] F'.H0 K')) (hs : ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] F'.HSucc K' i)) :
    F.eulerChar K = F'.eulerChar K' := by
  have h : ∀ i, F.cechFinrank K i = F'.cechFinrank K' i := by
    intro i
    cases i with
    | zero => obtain ⟨e⟩ := h0; exact e.finrank_eq
    | succ j => obtain ⟨e⟩ := hs j; exact e.finrank_eq
  rw [eulerChar_def, eulerChar_def, hcard]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem eulerChar_ofModules_congr {V : Scheme.{u}} {π π' : V ⟶ Spec (.of R)} (h : π = π') (X : V.Modules)
    (K : V.OrderedAffineCover) : (ofModules π X).eulerChar K = (ofModules π' X).eulerChar K := by
  subst h; rfl

end Chi

section PushUnit

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

theorem preimage_eq_bot (U : V.Opens) (hU : (U : Set V) = ∅) : ι ⁻¹ᵁ U = ⊥ := by
  ext z
  simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hz
  have : ι.base z ∈ (U : Set V) := hz
  rw [hU] at this
  exact this

theorem subsingleton_sections_of_eq_bot (W : Z.Opens) (h : W = ⊥) : Subsingleton Γ(Z, W) := by
  subst h
  infer_instance

theorem supportedIn_top : (pushforwardUnit π ι).SupportedIn ⊤ := fun U hU =>
  subsingleton_sections_of_eq_bot (ι ⁻¹ᵁ U.1)
    (preimage_eq_bot ι U.1 (by simpa [Closeds.coe_top, Set.inter_univ] using hU))

theorem res_rfl (W : Z.Opens) (x : Γ(Z, W)) : Z.presheaf.map (homOfLE (le_refl W)).op x = x := by
  rw [Subsingleton.elim (homOfLE (le_refl W)).op (𝟙 (op W)), Z.presheaf.map_id]; rfl

theorem appLE_rfl_apply (U : V.Opens) (a : Γ(V, U)) : ι.appLE U (ι ⁻¹ᵁ U) le_rfl a = ι.app U a := by
  show Z.presheaf.map (homOfLE (le_refl _)).op (ι.app U a) = _
  exact res_rfl (ι ⁻¹ᵁ U) _

theorem isCoherent [IsFinite ι] : (pushforwardUnit π ι).IsCoherent := by
  intro U
  have hfin : (ι.app U.1).hom.Finite := IsFinite.finite_app ι U.1 U.2
  have heq : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl = ι.app U.1 := by
    ext a; exact appLE_rfl_apply ι U.1 a
  letI : Algebra Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have hfin' : Module.Finite Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Finite := by rw [heq]; exact hfin
    exact this
  exact hfin'

theorem loc_core [IsAffineHom ι] (U : V.affineOpens) (g : Γ(Z, ι ⁻¹ᵁ U.1)) (W' : Z.Opens) (hle : W' ≤ ι ⁻¹ᵁ U.1)
    (hW' : W' = Z.basicOpen g) :
    (∀ x : Γ(Z, W'), ∃ (n : ℕ) (y : Γ(Z, ι ⁻¹ᵁ U.1)),
        Z.presheaf.map (homOfLE hle).op y = Z.presheaf.map (homOfLE hle).op (g ^ n) * x) ∧
      (∀ y : Γ(Z, ι ⁻¹ᵁ U.1), Z.presheaf.map (homOfLE hle).op y = 0 → ∃ n : ℕ, g ^ n * y = 0) := by
  subst hW'
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  haveI : IsLocalization.Away g Γ(Z, Z.basicOpen g) := hW.isLocalization_basicOpen g
  have halg : ∀ y : Γ(Z, ι ⁻¹ᵁ U.1),
      algebraMap Γ(Z, ι ⁻¹ᵁ U.1) Γ(Z, Z.basicOpen g) y = Z.presheaf.map (homOfLE hle).op y := fun y => by
    rw [Subsingleton.elim (homOfLE hle) (homOfLE (Z.basicOpen_le g))]; rfl
  constructor
  · intro x
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g) x
    refine ⟨n, y, ?_⟩
    rw [← halg, ← halg, ← h, mul_comm]
  · intro y hy
    rw [← halg] at hy
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp hy
    exact ⟨n, hn⟩

theorem preimage_basicOpen_eq (U : V.affineOpens) (f : Γ(V, U.1)) :
    ι ⁻¹ᵁ V.basicOpen f = Z.basicOpen (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f) := by
  rw [appLE_rfl_apply]; exact Scheme.preimage_basicOpen ι f

theorem pre_le (U : V.affineOpens) (f : Γ(V, U.1)) : ι ⁻¹ᵁ V.basicOpen f ≤ ι ⁻¹ᵁ U.1 :=
  fun _ hx => V.basicOpen_le f hx

theorem smul_basicOpen (U : V.affineOpens) (f : Γ(V, U.1)) (a : Γ(V, U.1)) (x : Γ(Z, ι ⁻¹ᵁ V.basicOpen f)) :
    ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom a •
        (show (pushforwardUnit π ι).obj (V.basicOpen f) from x)) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from
        Z.presheaf.map (homOfLE (pre_le ι U f)).op (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a) * x) := by
  show ι.appLE (V.basicOpen f) (ι ⁻¹ᵁ V.basicOpen f) le_rfl ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op) a) * x
    = _
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem smul_top (U : V.affineOpens) (a : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (a • (show (pushforwardUnit π ι).obj U.1 from y)) =
      (show (pushforwardUnit π ι).obj U.1 from ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a * y) := rfl

theorem res_eq (U : V.affineOpens) (f : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (pushforwardUnit π ι).res (V.basicOpen_le f) (show (pushforwardUnit π ι).obj U.1 from y) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from Z.presheaf.map (homOfLE (pre_le ι U f)).op y) := by
  show Z.presheaf.map _ y = _
  rw [Subsingleton.elim (homOfLE ((Opens.map ι.base).monotone (V.basicOpen_le f))) (homOfLE (pre_le ι U f))]

theorem isQuasicoherent [IsAffineHom ι] : (pushforwardUnit π ι).IsQuasicoherent := by
  intro U f
  set g : Γ(Z, ι ⁻¹ᵁ U.1) := ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f with hg
  obtain ⟨h1, h2⟩ := loc_core ι U g (ι ⁻¹ᵁ V.basicOpen f) (pre_le ι U f) (preimage_basicOpen_eq ι U f)
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := h1 x
    refine ⟨n, y, ?_⟩
    rw [res_eq, smul_basicOpen]
    show Z.presheaf.map (homOfLE (pre_le ι U f)).op y =
      Z.presheaf.map (homOfLE (pre_le ι U f)).op (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n)) *
        (show Γ(Z, ι ⁻¹ᵁ V.basicOpen f) from x)
    rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
    exact hy
  · intro y hy
    rw [res_eq] at hy
    obtain ⟨n, hn⟩ := h2 y hy
    refine ⟨n, ?_⟩
    rw [smul_top]
    show ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n) * (show Γ(Z, ι ⁻¹ᵁ U.1) from y) = 0
    rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
    exact hn

end PushUnit

section Rank

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

theorem finrank_comp_iso {X Y Y' : Scheme.{u}} (g : X ⟶ Y) [Flat g] [IsFinite g] (e : Y ≅ Y') (z : Y') :
    Scheme.Hom.finrank (g ≫ e.hom) z = Scheme.Hom.finrank g (e.inv.base z) := by
  have sq : IsPullback (𝟙 X) (g ≫ e.hom) g e.inv := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ sq z

theorem rankAtStalk_pushforwardUnit_obj [IsFinite ι] [Flat ι] (U : V.affineOpens) (r : ℕ)
    (hr : ∀ y : V, Scheme.Hom.finrank ι y = r) (𝔭 : PrimeSpectrum Γ(V, U.1)) :
    Module.rankAtStalk (R := Γ(V, U.1)) ((pushforwardUnit π ι).obj U.1) 𝔭 = r := by
  have heq : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl = ι.app U.1 := Scheme.Hom.appLE_eq_app ι
  letI alg : Algebra Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  haveI : Module.Finite Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Finite := by rw [heq]; exact IsFinite.finite_app ι U.1 U.2
    exact this
  haveI : Module.Flat Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) (f := ι) inferInstance U ⟨ι ⁻¹ᵁ U.1, U.2.preimage ι⟩ le_rfl
    exact this
  have key := Scheme.Hom.finrank_SpecMap_algebraMap Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) 𝔭
  have hmap : CommRingCat.ofHom (algebraMap Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1)) = ι.app U.1 := by
    rw [← heq]; rfl
  rw [hmap] at key

  have hU : IsAffineOpen U.1 := U.2
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  have hnat : Spec.map (ι.app U.1) = hW.isoSpec.inv ≫ ((ι ∣_ U.1) ≫ hU.isoSpec.hom) := by
    rw [IsAffineOpen.isoSpec_hom, ← Scheme.Opens.toSpecΓ_naturality, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_toSpecΓ, Category.id_comp]
  have hfr : Scheme.Hom.finrank (Spec.map (ι.app U.1)) 𝔭 = r := by
    rw [hnat, Scheme.Hom.finrank_comp_left_of_isIso, finrank_comp_iso,
      Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict ι U.1).flip]
    exact hr _
  rw [hfr] at key
  exact key.symm

end Rank

section Setup

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem connectedSpace (hA : AbelianSchemePropertyBundle K f) : ConnectedSpace A := by
  have h := hA.connectedFibres (IsLocalRing.closedPoint K)
  have h' : _root_.IsConnected (Set.univ : Set A) := by
    convert h using 1
    exact (Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _).symm
  exact connectedSpace_iff_univ.mpr h'

theorem krullDim_top_le (g : ℕ) [SmoothOfRelativeDimension g f] :
    topologicalKrullDim ((⊤ : Closeds A) : Set A) ≤ g :=
  (Topology.IsInducing.topologicalKrullDim_le (Topology.IsEmbedding.subtypeVal.isInducing)).trans
    (SmoothOfRelativeDimension.topologicalKrullDim_le f g)

theorem exists_chart_prime [IsIntegral A] [Nonempty A] (𝒦 : A.OrderedAffineCover) :
    ∃ (U₀ : A.affineOpens) (𝔭 : PrimeSpectrum Γ(A, U₀.1)), (∃ i, U₀.1 = 𝒦.U i) ∧ 𝔭.asIdeal = ⊥ := by
  obtain ⟨a⟩ := (inferInstance : Nonempty A)
  have ha : a ∈ (⊤ : A.Opens) := trivial
  rw [← 𝒦.iSup_eq_top, Opens.mem_iSup] at ha
  obtain ⟨i, hi⟩ := ha
  haveI : Nonempty (𝒦.U i) := ⟨⟨a, hi⟩⟩
  exact ⟨⟨𝒦.U i, 𝒦.isAffineOpen i⟩, ⟨⊥, Ideal.isPrime_bot⟩, ⟨i, rfl⟩, rfl⟩

end Setup

section Chain

variable {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))

theorem isInvertible_tensorPow {𝓛 : A.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (n : ℕ) :
    Scheme.Modules.IsInvertible (𝓛.tensorPowFLT n) := by
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unitFLT A
  | succ n ih => exact ih.tensor h𝓛

variable [IsSeparated f] (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
  (γ : SchemeHomOver f f) [IsAffineHom γ.1]

include h𝓛 in

theorem eulerChar_twist_eq (m : ℕ) :
    ((pushforwardUnit f γ.1).twist (𝓛.tensorPowFLT m)).eulerChar 𝒦 =
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPowFLT m)).eulerChar 𝒦 := by
  have hN : Scheme.Modules.IsInvertible (𝓛.tensorPowFLT m) := isInvertible_tensorPow h𝓛 m

  have e1 : ((pushforwardUnit f γ.1).twist (𝓛.tensorPowFLT m)).eulerChar 𝒦 =
      (ofModules (γ.1 ≫ f) ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m))).eulerChar (𝒦.comap γ.1) := by
    obtain ⟨h0, hs⟩ := nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit f γ.1 𝒦 (𝓛.tensorPowFLT m) hN.1
    exact (eulerChar_eq_of_equiv (ofModules (γ.1 ≫ f) ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m)))
      ((pushforwardUnit f γ.1).twist (𝓛.tensorPowFLT m)) (𝒦.comap γ.1) 𝒦 rfl h0 hs).symm

  have e2 := eulerChar_ofModules_congr γ.2 ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m)) (𝒦.comap γ.1)

  have hq : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m))).IsQuasicoherent :=
    isQuasicoherent_ofModules_of_locallyTrivial f _ (hN.pullback γ.1).1
  have e3 : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m))).eulerChar (𝒦.comap γ.1) =
      (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m))).eulerChar 𝒦 := by
    obtain ⟨h0, hs⟩ := nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated f
      ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m)) hq (𝒦.comap γ.1) 𝒦
    exact eulerChar_eq_of_equiv (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m)))
      (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m))) (𝒦.comap γ.1) 𝒦 rfl h0 hs

  have e4 : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m))).eulerChar 𝒦 =
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPowFLT m)).eulerChar 𝒦 := by
    obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso γ.1 𝓛 m
    obtain ⟨h0, hs, -⟩ := nonempty_cechEquiv_ofModules_of_iso f e 𝒦
    exact eulerChar_eq_of_equiv (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPowFLT m)))
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPowFLT m)) 𝒦 𝒦 rfl h0 hs
  rw [e1, e2, e3, e4]

end Chain

section ProjIsog

variable (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
  (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
  (g : ℕ) [SmoothOfRelativeDimension g f]
  (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
  (γ : SchemeHomOver f f)
  (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
      L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
  (hfin : IsFinite (L.endKerStr γ))
  (p q : Polynomial ℚ)
  (hp : ∀ m : ℕ, ((OModulePresheaf.ofModules f
      (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPowFLT m)).eulerChar 𝒦 : ℚ) = p.eval (m : ℚ))
  (hq : ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPowFLT m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ))

include hA hγ hfin hp hq h𝓛 in

theorem coeff_eq_endDegree_mul_coeff : p.coeff g = (L.endDegree γ : ℚ) * q.coeff g := by
  classical
  haveI := hA.proper
  haveI := hA.smooth
  haveI : ConnectedSpace A := connectedSpace hA
  haveI : IsIntegral A := AbelianSchemePropertyBundle.isIntegral_of_field hA

  haveI := hfin
  haveI : IsFinite γ.1 := RelativeGroupLaw.isFinite_of_isFinite_endKerStr K f L γ hγ
  haveI : Flat γ.1 := AbelianSchemePropertyBundle.flat_of_isFinite K hA γ
  obtain ⟨-, -, hrank⟩ := RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat K f L γ

  set G : OModulePresheaf f := pushforwardUnit f γ.1 with hG
  have hGc : G.IsCoherent := isCoherent f γ.1
  have hGq : G.IsQuasicoherent := isQuasicoherent f γ.1
  have hGs : G.SupportedIn ⊤ := supportedIn_top f γ.1

  obtain ⟨p', -, hp'⟩ := exists_polynomial_forall_eulerChar_twist_tensorPow_eq f 𝒦 G hGc hGq ⊤ hGs g
    (krullDim_top_le (f := f) g) 𝓛 h𝓛.1

  have hpp : p' = p := by
    refine Polynomial.eq_of_infinite_eval_eq p' p
      ((Set.infinite_range_of_injective Nat.cast_injective).mono ?_)
    rintro _ ⟨m, rfl⟩
    show p'.eval (m : ℚ) = p.eval (m : ℚ)
    rw [← hp' m, ← hp m, hG, eulerChar_twist_eq f 𝒦 𝓛 h𝓛 γ m]

  obtain ⟨U₀, 𝔭, -, h𝔭⟩ := exists_chart_prime (A := A) 𝒦
  have hlead := coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq f 𝒦 𝓛 h𝓛.1 g
    (SmoothOfRelativeDimension.topologicalKrullDim_le f g) q hq G hGc hGq p' hp' U₀ 𝔭 h𝔭
  have hrk : Module.rankAtStalk (R := Γ(A, U₀.1)) (G.obj U₀.1) 𝔭 = L.endDegree γ :=
    rankAtStalk_pushforwardUnit_obj f γ.1 U₀ (L.endDegree γ) (fun y => (hrank y).symm) 𝔭
  rw [← hpp, hlead, hrk]

end ProjIsog

end Isog

section Tail

open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

section EtaleKernel

theorem locallyOfFinitePresentation_of_field (q : A ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType q] : LocallyOfFinitePresentation q := by
  haveI : IsNoetherianRing (Γ(Spec (CommRingCat.of K), ⊤) : CommRingCat.{u}) :=
    isNoetherianRing_of_ringEquiv K
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have h := (HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFiniteType)
    (f := q) A.affineCover).mp inferInstance
  exact HasRingHomProperty.of_source_openCover (P := @LocallyOfFinitePresentation)
    A.affineCover (fun i => RingHom.FinitePresentation.of_finiteType.mp (h i))

theorem etale_endKerStr_nsmul (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    [LocallyOfFiniteType f] (n : ℕ) (hn : (n : K) ≠ 0) :
    Etale (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) := by
  have hunit : IsUnit (n : K) := isUnit_iff_ne_zero.mpr hn
  haveI hfu : FormallyUnramified (L.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
      L (fun t x y => hc t x y) n hunit
  haveI : FormallyUnramified (L.nsmul f n RelativeGroupLaw.idPoint).1 := hfu
  haveI : LocallyOfFiniteType ((L.nsmul f n RelativeGroupLaw.idPoint).1 ≫ f) := by
    rw [(L.nsmul f n RelativeGroupLaw.idPoint).2]; infer_instance
  haveI : LocallyOfFiniteType (L.nsmul f n RelativeGroupLaw.idPoint).1 :=
    locallyOfFiniteType_of_comp _ f
  haveI : FormallyUnramified (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : LocallyOfFiniteType (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : LocallyOfFinitePresentation (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) :=
    locallyOfFinitePresentation_of_field _
  haveI : Flat (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) := inferInstance
  exact Etale.of_formallyUnramified_of_flat _

theorem isFinite_endKerStr_nsmul [IsAlgClosed K] (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) (n : ℕ) (hn : (n : K) ≠ 0) :
    IsFinite (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) := by
  haveI : IsProper f := hA.proper
  haveI : Etale (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) := etale_endKerStr_nsmul L hc n hn
  exact (GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
    K f L (L.nsmul f n RelativeGroupLaw.idPoint)).1

end EtaleKernel

section Main

variable [IsAlgClosed K] (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
  (g : ℕ) [SmoothOfRelativeDimension g f]

include hc hA

theorem main (n : ℕ) (hn : (n : K) ≠ 0) : L.endDegree (L.nsmul f n RelativeGroupLaw.idPoint) = n ^ (2 * g) := by

  obtain ⟨𝒦⟩ := exists_orderedAffineCover (f := f) hA.proper
  obtain ⟨𝓛, h𝓛, hsym, q, hq0, hq⟩ :=
    RelativeGroupLaw.exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq
      K f L hA g 𝒦

  letI := L.grpObjOverMk
  haveI := isCommMonObj L hc
  have hsym' : Nonempty ((Scheme.Modules.pullback ((𝟙 (Over.mk f))⁻¹).left).obj 𝓛 ≅ 𝓛) := by
    rw [left_one_inv L]; exact hsym
  set φ : SchemeHomOver f f := L.nsmul f n RelativeGroupLaw.idPoint with hφ
  have hN : Nonempty ((Scheme.Modules.pullback φ.1).obj 𝓛 ≅ 𝓛.tensorPowFLT (n * n)) := by
    have h := Scheme.Modules.nonempty_pullback_zpow_iso_tensorPow_of_symmetric K f hA.smooth hA.proper
      (_root_.P2mDegNIsog.geometricallyConnected (f := f) hA) 𝓛 h𝓛 hsym' (n : ℤ)
    rw [left_one_zpow_natCast L n, show ((n : ℤ) * (n : ℤ)).toNat = n * n by
      rw [← Nat.cast_mul]; exact Int.toNat_natCast (n * n)] at h
    exact h
  obtain ⟨eN⟩ := hN

  have hcls : ∀ m : ℕ, Nonempty ((((Scheme.Modules.pullback φ.1).obj 𝓛).tensorPowFLT m) ≅ 𝓛.tensorPowFLT (n * n * m)) := by
    intro m
    apply toSkeleton_eq_toSkeleton_iff.mp
    rw [cls_tensorPow, cls_tensorPow, toSkeleton_eq_toSkeleton_iff.mpr ⟨eN⟩, cls_tensorPow, ← pow_mul]

  have hp : ∀ m : ℕ, ((OModulePresheaf.ofModules f
      (((Scheme.Modules.pullback φ.1).obj 𝓛).tensorPowFLT m)).eulerChar 𝒦 : ℚ) =
        (dil q ((n : ℚ) * n)).eval (m : ℚ) := by
    intro m
    obtain ⟨e⟩ := hcls m
    rw [eulerChar_congr (f := f) e 𝒦, hq (n * n * m), dil_eval]
    push_cast
    ring_nf

  have hfinKer : IsFinite (L.endKerStr φ) := isFinite_endKerStr_nsmul L hc hA n hn
  have key := Isog.coeff_eq_endDegree_mul_coeff K f L hA g 𝒦 𝓛 h𝓛
    φ (fun {T} t x y => isHom_nsmul L hc n t x y) hfinKer (dil q ((n : ℚ) * n)) q hp hq
  rw [dil_coeff] at key
  have hq0' : q.coeff g ≠ 0 := ne_of_gt hq0
  have h1 : ((L.endDegree φ : ℕ) : ℚ) = ((n : ℚ) * n) ^ g := mul_right_cancel₀ hq0' key.symm
  have h2 : ((L.endDegree φ : ℕ) : ℚ) = ((n ^ (2 * g) : ℕ) : ℚ) := by
    rw [h1]; push_cast; ring
  exact_mod_cast h2

end Main

end Tail

end P2mDegNIsog

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : (n : K) ≠ 0) :
    L.endDegree (L.nsmul f n RelativeGroupLaw.idPoint) = n ^ (2 * g) :=
  P2mDegNIsog.main L hc hA g n hn

end

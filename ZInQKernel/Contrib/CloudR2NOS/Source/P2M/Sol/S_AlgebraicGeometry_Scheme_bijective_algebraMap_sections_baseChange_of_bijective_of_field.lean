/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field.lean
  Source sha256  : 3a599f8aaf660f6aeb85c68bef87b15eca9dbffdb658473450d6747ca9c1f801
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 7 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T6×1; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field
r2nos_namespace_dual
r2nos_erase_attr "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct"

namespace P2mH0BaseChangeField
r2nos_namespace_dual

def coverOfCompact (X : Scheme.{u}) [CompactSpace X] : X.OrderedAffineCover :=
  let 𝒰 := X.affineCover.finiteSubcover
  { ι := 𝒰.I₀
    instFintype := inferInstance
    instLinearOrder := LinearOrder.lift' (Fintype.equivFin 𝒰.I₀) (Fintype.equivFin 𝒰.I₀).injective
    U := fun i => (𝒰.f i).opensRange
    isAffineOpen := fun i => isAffineOpen_opensRange (𝒰.f i)
    iSup_eq_top := 𝒰.iSup_opensRange }

section H0

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
  (K : V.OrderedAffineCover)

def toCochain :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Γ(M, ⊤) →ₗ[R] (OModulePresheaf.ofModules π M).cochain K 0 :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  LinearMap.pi fun s => (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)

theorem toCochain_apply (x : Γ(M, ⊤)) (s : K.Idx 0) :
    toCochain π M K x s = M.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op x := rfl

theorem toCochain_apply' (x : Γ(M, ⊤)) (s : K.Idx 0) :
    toCochain π M K x s = (OModulePresheaf.ofModules π M).res (le_top : K.inter s ≤ ⊤)
      (show (OModulePresheaf.ofModules π M).obj ⊤ from x) := rfl

theorem d_toCochain (x : Γ(M, ⊤)) :
    (OModulePresheaf.ofModules π M).d K 0 (toCochain π M K x) = 0 := by
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, toCochain_apply',
    OModulePresheaf.res_res]
  exact add_neg_cancel _

theorem toCochain_mem (x : Γ(M, ⊤)) : toCochain π M K x ∈ (OModulePresheaf.ofModules π M).H0 K :=
  d_toCochain π M K x

theorem toCochain_injective : Function.Injective (toCochain π M K) := by
  intro x y hxy
  obtain ⟨z, -, huniq⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K _).mp
    (d_toCochain π M K x)
  exact (huniq x fun s => rfl).trans (huniq y fun s => by rw [hxy]; rfl).symm

theorem exists_toCochain_eq (c : (OModulePresheaf.ofModules π M).cochain K 0)
    (hc : c ∈ (OModulePresheaf.ofModules π M).H0 K) : ∃ x : Γ(M, ⊤), toCochain π M K x = c := by
  obtain ⟨x, hx, -⟩ := (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K c).mp hc
  exact ⟨x, funext fun s => (hx s).symm⟩

def H0Equiv :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    (OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] Γ(M, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  (LinearEquiv.ofBijective (LinearMap.codRestrict ((OModulePresheaf.ofModules π M).H0 K)
      (toCochain π M K) (toCochain_mem π M K))
    ⟨fun x y h => toCochain_injective π M K (congrArg Subtype.val h),
     fun ⟨c, hc⟩ => by
      obtain ⟨x, rfl⟩ := exists_toCochain_eq π M K c hc
      exact ⟨x, rfl⟩⟩).symm

end H0

section Transport

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {M N : V.Modules}

def sectionsEquivOfIso (e : M ≅ N) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π N ⊤
    Γ(M, ⊤) ≃ₗ[R] Γ(N, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π N ⊤
  { toFun := fun x => Scheme.Modules.Hom.app e.hom ⊤ x
    invFun := fun y => Scheme.Modules.Hom.app e.inv ⊤ y
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => by
      show Scheme.Modules.Hom.app e.hom ⊤ ((algebraMap R Γ(V, ⊤) r) • x)
        = (algebraMap R Γ(V, ⊤) r) • Scheme.Modules.Hom.app e.hom ⊤ x
      exact Scheme.Modules.Hom.app_smul _ _ _
    left_inv := fun x => by
      change (Scheme.Modules.Hom.app e.hom ⊤ ≫ Scheme.Modules.Hom.app e.inv ⊤) x = x
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
    right_inv := fun y => by
      change (Scheme.Modules.Hom.app e.inv ⊤ ≫ Scheme.Modules.Hom.app e.hom ⊤) y = y
      rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl }

def unitSectionsEquiv :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (SheafOfModules.unit V.ringCatSheaf) ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
    Γ(SheafOfModules.unit V.ringCatSheaf, ⊤) ≃ₗ[R] Γ(V, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (SheafOfModules.unit V.ringCatSheaf) ⊤
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
  { toFun := fun x => (show Γ(V, ⊤) from x)
    invFun := fun y => (show Γ(SheafOfModules.unit V.ringCatSheaf, ⊤) from y)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end Transport

theorem bijective_algebraMap_of_linearEquiv {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (e : S ≃ₗ[A] A) : Function.Bijective (algebraMap A S) := by
  set u : S := e.symm 1 with hu
  have hgen : ∀ s : S, s = e s • u := fun s => by
    rw [hu, ← LinearEquiv.map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  set b : A := e 1
  set a : A := e (u * u)
  have hba : b * a = 1 := by
    have h1 : u = (b * a) • u := by
      calc u = u * 1 := (mul_one u).symm
        _ = u * (b • u) := by rw [← hgen 1]
        _ = b • (u * u) := by rw [mul_smul_comm]
        _ = b • (a • u) := by rw [← hgen (u * u)]
        _ = (b * a) • u := by rw [mul_smul]
    have h2 : (1 - b * a) • u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    have h3 : (1 - b * a) • e u = 0 := by rw [← LinearEquiv.map_smul, h2, map_zero]
    have h4 : e u = 1 := by rw [hu, LinearEquiv.apply_symm_apply]
    rw [h4, smul_eq_mul, mul_one] at h3
    exact (sub_eq_zero.mp h3).symm
  have hbu : IsUnit b := IsUnit.of_mul_eq_one a hba
  have halg : ∀ r : A, algebraMap A S r = (r * b) • u := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul, ← hgen 1]
  constructor
  · intro r r' h
    rw [halg, halg] at h
    have h' := congrArg e h
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, hu, LinearEquiv.apply_symm_apply, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one] at h'
    exact hbu.mul_left_injective h'
  · intro s
    refine ⟨e s * hbu.unit⁻¹, ?_⟩
    rw [halg, mul_assoc, IsUnit.val_inv_mul, mul_one, ← hgen s]

section Main

w03_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover"

theorem main (k : Type u) [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsSeparated π] [QuasiCompact π]
    (hX : letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
      Function.Bijective (algebraMap k Γ(X, ⊤)))
    (A : Type u) [CommRing A] [Algebra k A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap k A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback π (Scheme.TwoAffineOpenCover.specMap k A), ⊤)) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  let 𝒰 := coverOfCompact X
  let 𝒪 : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let p₁ := Limits.pullback.fst π (specMap k A)
  let p₂ := Limits.pullback.snd π (specMap k A)
  have htriv : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj 𝒪 ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :=
    fun x => ⟨⊤, trivial, ⟨Scheme.Modules.pullbackUnitIso _⟩⟩
  obtain ⟨-, hflat⟩ := OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial π 𝒰 𝒪 htriv A
  obtain ⟨⟨e1⟩, -⟩ := hflat inferInstance
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π 𝒪 ⊤
  letI := Scheme.TwoAffineOpenCover.algebraOfHom p₂ ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p₂ ((Scheme.Modules.pullback p₁).obj 𝒪) ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom p₂
    (SheafOfModules.unit (Limits.pullback π (specMap k A)).ringCatSheaf) ⊤
  let e2 : (OModulePresheaf.ofModules π 𝒪).H0 𝒰 ≃ₗ[k] k :=
    (H0Equiv π 𝒪 𝒰).trans ((unitSectionsEquiv π).trans
      (LinearEquiv.ofBijective (Algebra.linearMap k Γ(X, ⊤)) hX).symm)
  let e3 : A ⊗[k] (OModulePresheaf.ofModules π 𝒪).H0 𝒰 ≃ₗ[A] A :=
    (e2.baseChange k A _ _).trans (AlgebraTensorModule.rid k A A)
  let e4 := (H0Equiv p₂ ((Scheme.Modules.pullback p₁).obj 𝒪) (𝒰.baseChange π A)).trans
    ((sectionsEquivOfIso p₂ (Scheme.Modules.pullbackUnitIso p₁)).trans (unitSectionsEquiv p₂))
  exact bijective_algebraMap_of_linearEquiv (e4.symm.trans (e1.trans e3))

end Main

end P2mH0BaseChangeField

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry _root_.AlgebraicGeometry in
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry" in
theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated π] [QuasiCompact π]
    (hX : letI := Scheme.TwoAffineOpenCover.algebraOfHom π ⊤
      Function.Bijective (algebraMap k Γ(X, ⊤)))
    (A : Type u) [CommRing A] [Algebra k A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap k A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback π (Scheme.TwoAffineOpenCover.specMap k A), ⊤)) :=
  P2mH0BaseChangeField.main k π hX A
end S_AlgebraicGeometry_Scheme_bijective_algebraMap_sections_baseChange_of_bijective_of_field
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT

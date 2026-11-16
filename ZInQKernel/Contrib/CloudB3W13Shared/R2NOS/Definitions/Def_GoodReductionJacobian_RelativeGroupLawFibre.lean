/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_GoodReductionJacobian_RelativeGroupLawFibre.lean
  Retrieved      : 2026-11-14 (git smart-protocol blob, byte-for-byte; sha256 in lane4 port manifest)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-14).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or
omitted unless listed under manual repairs:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / port utilities.
  * file-level `set_option`s inserted after the port namespace, reproducing the source build environment: autoImplicit false (source lakefile.lean leanOptions); maxHeartbeats 4000000 (source lakefile.lean leanOptions); synthInstance.maxHeartbeats 400000 (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.types false (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.instanceSearchTypes false (Lean 4.35 option absent from source Lean 4.33.1; `false` restores 4.33.1 behaviour).
  * `import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Pullbacks
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra"

namespace GoodReductionJacobian
r2nos_namespace_dual
namespace RelativeGroupLaw
r2nos_namespace_dual

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

abbrev baseResidueField (s : (Spec (CommRingCat.of R) : Scheme.{u})) : Type u :=
  (Spec (CommRingCat.of R)).residueField s

abbrev basePointInclusion (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    Spec (CommRingCat.of (baseResidueField s)) ⟶ Spec (CommRingCat.of R) :=
  (Spec (CommRingCat.of R)).fromSpecResidueField s

abbrev fibreScheme (f : A ⟶ Spec (CommRingCat.of R)) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    Scheme.{u} :=
  pullback f (basePointInclusion s)

abbrev fibreStr (f : A ⟶ Spec (CommRingCat.of R)) (s : (Spec (CommRingCat.of R) : Scheme.{u})) :
    fibreScheme f s ⟶ Spec (CommRingCat.of (baseResidueField s)) :=
  pullback.snd f (basePointInclusion s)

variable (s : (Spec (CommRingCat.of R) : Scheme.{u}))

theorem fibreScheme_eq_fiber : fibreScheme f s = f.fiber s := rfl

theorem fibreStr_eq_fiberToSpecResidueField :
    fibreStr f s = f.fiberToSpecResidueField s := rfl

def fibrePointToBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (x : SchemeHomOver t' (fibreStr f s)) : SchemeHomOver (t' ≫ basePointInclusion s) f :=
  ⟨x.1 ≫ pullback.fst f (basePointInclusion s), by
    rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩

def fibrePointOfBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (y : SchemeHomOver (t' ≫ basePointInclusion s) f) : SchemeHomOver t' (fibreStr f s) :=
  ⟨pullback.lift y.1 t' y.2, pullback.lift_snd _ _ _⟩

@[simp]
theorem fibrePointToBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (x : SchemeHomOver t' (fibreStr f s)) :
    (fibrePointToBase s x).1 = x.1 ≫ pullback.fst f (basePointInclusion s) :=
  rfl

@[simp]
theorem fibrePointOfBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (y : SchemeHomOver (t' ≫ basePointInclusion s) f) :
    (fibrePointOfBase s y).1 = pullback.lift y.1 t' y.2 :=
  rfl

@[simp]
theorem fibrePointToBase_ofBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (y : SchemeHomOver (t' ≫ basePointInclusion s) f) :
    fibrePointToBase s (fibrePointOfBase s y) = y :=
  Subtype.ext (pullback.lift_fst _ _ _)

@[simp]
theorem fibrePointOfBase_toBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))}
    (x : SchemeHomOver t' (fibreStr f s)) :
    fibrePointOfBase s (fibrePointToBase s x) = x := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [fibrePointOfBase_coe, pullback.lift_fst, fibrePointToBase_coe]
  · rw [fibrePointOfBase_coe, pullback.lift_snd]
    exact x.2.symm

def fibrePointEquiv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) :
    SchemeHomOver t' (fibreStr f s) ≃ SchemeHomOver (t' ≫ basePointInclusion s) f where
  toFun := fibrePointToBase s
  invFun := fibrePointOfBase s
  left_inv := fibrePointOfBase_toBase s
  right_inv := fibrePointToBase_ofBase s

theorem fibrePointToBase_schemeHomOverComp {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of (baseResidueField s)))
    (t' : T' ⟶ Spec (CommRingCat.of (baseResidueField s))) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t (fibreStr f s)) :
    fibrePointToBase s (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (fibrePointToBase s x) :=
  Subtype.ext (Category.assoc _ _ _)

def fibre (G : RelativeGroupLaw R f) : RelativeGroupLaw (baseResidueField s) (fibreStr f s) where
  mul t' x y := fibrePointOfBase s (G.mul _ (fibrePointToBase s x) (fibrePointToBase s y))
  one t' := fibrePointOfBase s (G.one _)
  inv t' x := fibrePointOfBase s (G.inv _ (fibrePointToBase s x))
  mul_assoc t' x y z := by
    simp only [fibrePointToBase_ofBase, G.mul_assoc]
  one_mul t' x := by
    simp only [fibrePointToBase_ofBase, G.one_mul, fibrePointOfBase_toBase]
  mul_one t' x := by
    simp only [fibrePointToBase_ofBase, G.mul_one, fibrePointOfBase_toBase]
  inv_mul_cancel t' x := by
    simp only [fibrePointToBase_ofBase, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [schemeHomOverComp_coe, fibrePointOfBase_coe, fibrePointOfBase_coe, Category.assoc, pullback.lift_fst,
        pullback.lift_fst]
      have h := congrArg Subtype.val
        (G.mul_natural (t ≫ basePointInclusion s) (t' ≫ basePointInclusion s) ψ
          (by rw [← Category.assoc, hψ]) (fibrePointToBase s x) (fibrePointToBase s y))
      rw [schemeHomOverComp_coe] at h
      rw [h, ← fibrePointToBase_schemeHomOverComp, ← fibrePointToBase_schemeHomOverComp]
    · rw [schemeHomOverComp_coe, fibrePointOfBase_coe, fibrePointOfBase_coe, Category.assoc, pullback.lift_snd,
        pullback.lift_snd]
      exact hψ

@[simp]
theorem fibre_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) (x y : SchemeHomOver t' (fibreStr f s)) :
    (G.fibre s).mul t' x y = fibrePointOfBase s (G.mul _ (fibrePointToBase s x) (fibrePointToBase s y)) :=
  rfl

@[simp]
theorem fibre_one (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) :
    (G.fibre s).one t' = fibrePointOfBase s (G.one _) :=
  rfl

@[simp]
theorem fibre_inv (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) (x : SchemeHomOver t' (fibreStr f s)) :
    (G.fibre s).inv t' x = fibrePointOfBase s (G.inv _ (fibrePointToBase s x)) :=
  rfl

end RelativeGroupLaw
end GoodReductionJacobian

end


end ZInQ.Contrib.CloudW03NeronSurj.FLT

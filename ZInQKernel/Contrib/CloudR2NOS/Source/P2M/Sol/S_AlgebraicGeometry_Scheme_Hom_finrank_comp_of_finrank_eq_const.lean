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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const.lean
  Source sha256  : a86a5e3a3d3c4b95ff82f58e1a5af83a7029cd8456042f7f89da9c8874030f6c
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Artinian.Module
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const.AlgebraicGeometry TensorProduct"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.finrank_comp_left_of_isIso Scheme.Hom Flat.SpecMap_iff IsFinite Scheme.Hom.finrank_pullback_snd isAffine_of_isAffineHom IsAffine Spec Spec.map Scheme Scheme.Hom.finrank_SpecMap_eq_finrank Flat Scheme.Hom.finrank_of_isPullback Spec.preimage IsFinite.SpecMap_iff Scheme.Hom.comp_apply"
namespace FinrankComp
r2nos_namespace_dual
w03_open "AlgebraicGeometry"

theorem finrank_eq_mul_of_rankAtStalk_eq (K B C : Type u) [Field K] [CommRing B] [Algebra K B]
    [CommRing C] [Algebra B C] [Algebra K C] [IsScalarTower K B C]
    [Module.Finite K B] [Module.Finite B C] [Module.Flat B C]
    (m : ℕ) (h : ∀ p : PrimeSpectrum B, Module.rankAtStalk (R := B) C p = m) :
    Module.finrank K C = m * Module.finrank K B := by
  classical
  rcases subsingleton_or_nontrivial B with hB | hB
  · have : Subsingleton C := Module.subsingleton B C
    simp [Module.finrank_zero_of_subsingleton]

  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B
  have hfree : Module.Free B C := by
    refine Module.free_of_flat_of_finrank_eq (R := B) (M := C) m fun P => ?_
    haveI := P.2
    letI := Ideal.Quotient.field P.1

    have e := (TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⧸ P.1) P.1.ResidueField
      P.1.ResidueField C)
    have h1 : Module.finrank P.1.ResidueField (P.1.ResidueField ⊗[B ⧸ P.1] ((B ⧸ P.1) ⊗[B] C)) =
        Module.finrank (B ⧸ P.1) ((B ⧸ P.1) ⊗[B] C) := Module.finrank_baseChange
    rw [← h1, LinearEquiv.finrank_eq e, Ideal.finrank_fiber_eq_rankAtStalk]
    exact h ⟨P.1, inferInstance⟩
  have hrk : Module.finrank B C = m := by
    obtain ⟨p⟩ : Nonempty (PrimeSpectrum B) := inferInstance
    have := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := B) (M := C)) p
    rw [h p] at this
    exact this.symm
  rw [← Module.finrank_mul_finrank K B C, hrk, mul_comm]

theorem finrank_comp_SpecMap {K : Type u} [Field K] {B C : CommRingCat.{u}} (ψ : CommRingCat.of K ⟶ B)
    (φ : B ⟶ C)
    [IsFinite (Spec.map ψ)] [Flat (Spec.map ψ)] [IsFinite (Spec.map φ)] [Flat (Spec.map φ)]
    (m : ℕ) (hf : ∀ y, (Spec.map φ).finrank y = m) (z : Spec (CommRingCat.of K)) :
    (Spec.map φ ≫ Spec.map ψ).finrank z = m * (Spec.map ψ).finrank z := by
  have hψ₁ : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).mp inferInstance
  have hψ₂ : ψ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have hφ₁ : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  have hφ₂ : φ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have hc₁ : (ψ ≫ φ).hom.Finite := hφ₁.comp hψ₁
  have hc₂ : (ψ ≫ φ).hom.Flat := hψ₂.comp hφ₂
  rw [← Spec.map_comp, Scheme.Hom.finrank_SpecMap_eq_finrank hc₁ hc₂,
    Scheme.Hom.finrank_SpecMap_eq_finrank hψ₁ hψ₂]
  simp_rw [Scheme.Hom.finrank_SpecMap_eq_finrank hφ₁ hφ₂] at hf

  letI : Algebra K B := ψ.hom.toAlgebra
  letI : Algebra B C := φ.hom.toAlgebra
  letI : Algebra K C := (ψ ≫ φ).hom.toAlgebra
  haveI : IsScalarTower K B C := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite K B := hψ₁
  haveI : Module.Finite B C := hφ₁
  haveI : Module.Flat B C := hφ₂
  change Module.rankAtStalk (R := K) C z = m * Module.rankAtStalk (R := K) B z
  have hf' : ∀ y : PrimeSpectrum B, Module.rankAtStalk (R := B) C y = m := hf
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq_finrank_of_free]
  exact finrank_eq_mul_of_rankAtStalk_eq K B C m hf'

theorem finrank_comp_right_of_isIso {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Y') [IsIso e]
    [IsFinite f] [Flat f] (y : Y) : (f ≫ e).finrank (e y) = f.finrank y := by
  have sq : IsPullback (𝟙 X) (f ≫ e) f (inv e) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq]
  congr 1
  simp [← Scheme.Hom.comp_apply]

theorem finrank_comp_of_field {X Y : Scheme.{u}} (K : Type u) [Field K] (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of K)) [IsFinite f] [Flat f] [IsFinite g] [Flat g]
    (m : ℕ) (hf : ∀ y, f.finrank y = m) (z : Spec (CommRingCat.of K)) :
    (f ≫ g).finrank z = m * g.finrank z := by
  haveI : IsAffine Y := isAffine_of_isAffineHom g
  haveI : IsAffine X := isAffine_of_isAffineHom f

  let ψ : CommRingCat.of K ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ g)
  let φ : Γ(Y, ⊤) ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom)
  have hg : g = Y.isoSpec.hom ≫ Spec.map ψ := by simp [ψ]
  have hφ : X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom = Spec.map φ := by simp [φ]
  have hfg : f ≫ g = X.isoSpec.hom ≫ (Spec.map φ ≫ Spec.map ψ) := by
    rw [← hφ]; simp [hg]
  haveI : IsFinite (Spec.map ψ) := by
    have : Spec.map ψ = Y.isoSpec.inv ≫ g := by simp [ψ]
    rw [this]; infer_instance
  haveI : Flat (Spec.map ψ) := by
    have : Spec.map ψ = Y.isoSpec.inv ≫ g := by simp [ψ]
    rw [this]; infer_instance
  haveI : IsFinite (Spec.map φ) := by rw [← hφ]; infer_instance
  haveI : Flat (Spec.map φ) := by rw [← hφ]; infer_instance
  have hf' : ∀ y, (Spec.map φ).finrank y = m := by
    intro y
    rw [← hφ, Scheme.Hom.finrank_comp_left_of_isIso]
    obtain ⟨y, rfl⟩ : ∃ y₀ : Y, Y.isoSpec.hom y₀ = y := ⟨Y.isoSpec.inv y, by simp [← Scheme.Hom.comp_apply]⟩
    rw [finrank_comp_right_of_isIso]
    exact hf y
  rw [hfg, hg, Scheme.Hom.finrank_comp_left_of_isIso X.isoSpec.hom,
    Scheme.Hom.finrank_comp_left_of_isIso Y.isoSpec.hom]
  exact finrank_comp_SpecMap ψ φ m hf' z

end AlgebraicGeometry.FinrankComp

open AlgebraicGeometry.FinrankComp in
r2nos_open_dual "AlgebraicGeometry.FinrankComp" in
theorem solution
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [Flat f] [IsFinite g] [Flat g]
    (m : ℕ) (hf : ∀ y : Y, f.finrank y = m) (z : Z) :
    (f ≫ g).finrank z = m * g.finrank z := by

  let i := Z.fromSpecResidueField z
  obtain ⟨pt⟩ : Nonempty (Spec (Z.residueField z)) := inferInstance
  have hz : i pt = z := Z.fromSpecResidueField_apply z pt
  let f' := pullback.snd f (pullback.fst g i)
  let g' := pullback.snd g i
  have hf' : ∀ y, f'.finrank y = m := fun y => by
    rw [Scheme.Hom.finrank_pullback_snd]; exact hf _
  have key := finrank_comp_of_field (Z.residueField z) f' g' m hf' pt
  have e : f' ≫ g' = (pullbackRightPullbackFstIso g i f).hom ≫ pullback.snd (f ≫ g) i := by
    simp [f', g']
  rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_pullback_snd,
    Scheme.Hom.finrank_pullback_snd, hz] at key
  exact key
end S_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT

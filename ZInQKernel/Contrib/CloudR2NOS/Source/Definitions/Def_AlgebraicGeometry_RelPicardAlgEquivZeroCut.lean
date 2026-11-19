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
  Source file    : Definitions/Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut.lean
  Source sha256  : 469a6d2c3368b92185f59c35f9ba4535509990b5d64ff876b45f132bd10bdba7
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

namespace AlgebraicGeometry.RelPicard
r2nos_namespace_dual

open CategoryTheory CategoryTheory.Limits NeronModelInfra
r2nos_open_dual "CategoryTheory CategoryTheory.Limits NeronModelInfra"

universe u

variable {R : Type u} [CommRing R]

noncomputable def fibreAt {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    pullback (pullback.snd c t) s ⟶ Spec (CommRingCat.of k) :=
  pullback.snd _ _

def IsAlgEquivZero {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) (L : A.Modules) : Prop :=
  ∃ (T' : Scheme.{u}) (h : T' ⟶ Spec (CommRingCat.of k)) (_ : LocallyOfFiniteType h) (_ : GeometricallyIntegral h)
    (M : (pullback a h).Modules) (_ : Scheme.Modules.IsInvertible M)
    (t₀ t₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h),
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t₀)).obj M ≅
        SheafOfModules.unit (pullback a (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf) ∧
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd a t₁)).obj M ≅
        (Scheme.Modules.pullback (pullback.fst a (𝟙 (Spec (CommRingCat.of k))))).obj L)

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

def FibrewiseAlgEquivZero {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
    IsAlgEquivZero (fibreAt c t s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj M.L)

theorem IsAlgEquivZero.of_iso {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    {L L' : A.Modules} (e : L ≅ L') (hL : IsAlgEquivZero a L) : IsAlgEquivZero a L' := by
  obtain ⟨T', h, hft, hgi, M, hM, t₀, t₁, e₀, ⟨e₁⟩⟩ := hL
  exact ⟨T', h, hft, hgi, M, hM, t₀, t₁, e₀, ⟨e₁ ≪≫ (Scheme.Modules.pullback _).mapIso e⟩⟩

theorem IsAlgEquivZero.pullback {k : Type u} [Field k] {A A' : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    {a' : A' ⟶ Spec (CommRingCat.of k)} (e : A' ⟶ A) (he : e ≫ a = a') {L : A.Modules}
    (hL : IsAlgEquivZero a L) : IsAlgEquivZero a' ((Scheme.Modules.pullback e).obj L) := by
  obtain ⟨T', h, hft, hgi, M, hM, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hL

  let eT : Limits.pullback a' h ⟶ Limits.pullback a h :=
    pullback.map a' h a h e (𝟙 T') (𝟙 _) (by rw [Category.comp_id, he]) (by simp)
  let e1 : Limits.pullback a' (𝟙 (Spec (CommRingCat.of k))) ⟶ Limits.pullback a (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.map a' (𝟙 _) a (𝟙 _) e (𝟙 _) (𝟙 _) (by rw [Category.comp_id, he]) (by simp)
  have hsq : ∀ tt : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h,
      baseChangeSnd a' tt ≫ eT = e1 ≫ baseChangeSnd a tt := by
    intro tt
    apply pullback.hom_ext <;>
      simp only [eT, e1, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]
  have hfst : e1 ≫ pullback.fst a (𝟙 _) = pullback.fst a' (𝟙 _) ≫ e := by
    simp only [e1, pullback.lift_fst]
  refine ⟨T', h, hft, hgi, (Scheme.Modules.pullback eT).obj M, hM.pullback eT, t₀, t₁, ⟨?_⟩, ⟨?_⟩⟩
  · exact (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (hsq t₀)).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback e1).mapIso e₀ ≪≫
      Scheme.Modules.pullbackUnitIso e1
  · exact (Scheme.Modules.pullbackComp _ _).app M ≪≫
      (Scheme.Modules.pullbackCongr (hsq t₁)).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback e1).mapIso e₁ ≪≫
      (Scheme.Modules.pullbackComp _ _).app L ≪≫
      (Scheme.Modules.pullbackCongr hfst).app L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L).symm

theorem geometricallyIntegral_id_Spec (k : Type u) [Field k] :
    GeometricallyIntegral (𝟙 (Spec (CommRingCat.of k))) := by
  constructor
  intro K _ y Z fst snd hP
  haveI : IsIso snd := hP.isIso_snd_of_isIso
  exact AlgebraicGeometry.IsIntegral.of_isIso (inv snd)

theorem fibrewiseAlgEquivZero_unit {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    FibrewiseAlgEquivZero (RigidifiedLineBundle.unit (c := c) (ε := ε) t) := by
  intro k _ _ s
  refine ⟨Spec (CommRingCat.of k), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec k,
    SheafOfModules.unit (Limits.pullback (fibreAt c t s) (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf,
    Scheme.Modules.isInvertible_unit _, ⟨𝟙 _, Category.comp_id _⟩, ⟨𝟙 _, Category.comp_id _⟩,
    ⟨Scheme.Modules.pullbackUnitIso _⟩, ⟨?_⟩⟩
  exact Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackUnitIso _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (Scheme.Modules.pullbackUnitIso _).symm

theorem FibrewiseAlgEquivZero.congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {M M' : RigidifiedLineBundle c ε t} (h : Nonempty (M.L ≅ M'.L)) (hM : FibrewiseAlgEquivZero M) :
    FibrewiseAlgEquivZero M' := by
  intro k _ _ s
  exact (hM k s).of_iso ((Scheme.Modules.pullback _).mapIso h.some)

theorem FibrewiseAlgEquivZero.pullback {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) {M : RigidifiedLineBundle c ε t}
    (hM : FibrewiseAlgEquivZero M) : FibrewiseAlgEquivZero (M.pullbackAlong ψ) := by
  intro k _ _ s'
  have hψ : pullback.snd c t' ≫ ψ.1 = baseChangeSnd c ψ ≫ pullback.snd c t := by
    simp only [baseChangeSnd, pullback.lift_snd]

  let e : Limits.pullback (pullback.snd c t') s' ⟶ Limits.pullback (pullback.snd c t) (s' ≫ ψ.1) :=
    pullback.map _ _ _ _ (baseChangeSnd c ψ) (𝟙 _) ψ.1 hψ (by simp)
  have he : e ≫ fibreAt c t (s' ≫ ψ.1) = fibreAt c t' s' := by
    simp only [e, fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e ≫ pullback.fst (pullback.snd c t) (s' ≫ ψ.1) =
      pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ := by
    simp only [e, pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hM k (s' ≫ ψ.1)).pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

noncomputable def algEquivZeroCut (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    SubPicCondition c ε where
  P := fun _ M => FibrewiseAlgEquivZero M
  unit_mem := fun t => fibrewiseAlgEquivZero_unit t
  congr := fun _ _ _ h hM => hM.congr h
  pullback_mem := fun _ _ ψ _ hM => hM.pullback ψ

end AlgebraicGeometry.RelPicard

end ZInQ.Contrib.CloudW03NeronSurj.FLT

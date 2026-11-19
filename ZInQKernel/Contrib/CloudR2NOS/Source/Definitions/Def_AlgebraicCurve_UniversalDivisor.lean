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
  Source file    : Definitions/Def_AlgebraicCurve_UniversalDivisor.lean
  Source sha256  : 49ad2fa3e457be29578b79b4a0ab3b5ad8bc126b152a5cb70549c5dbb6d1b9cb
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Properties
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

universe u

namespace AlgebraicCurve
r2nos_namespace_dual

variable {k : Type u} [Field k]

structure RelEffDivisor (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)
    (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k)) where
  I : (pullback c t).IdealSheafData
  isFinite : IsFinite (I.subschemeι ≫ pullback.snd c t)
  flat : Flat (I.subschemeι ≫ pullback.snd c t)
  finrank_eq : ∀ s : T, (I.subschemeι ≫ pullback.snd c t).finrank s = r

@[ext] lemma RelEffDivisor.ext {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {D₁ D₂ : RelEffDivisor C c r T t}
    (h : D₁.I = D₂.I) : D₁ = D₂ := by
  cases D₁; cases D₂; cases h; rfl

noncomputable def mapOnProd {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    {T Csym : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {csym : Csym ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t) :
    pullback c t ⟶ pullback c csym :=
  pullback.map c t c csym (𝟙 C) φ (𝟙 (Spec (CommRingCat.of k))) (by simp)
    (by rw [Category.comp_id, hφ])

@[reassoc (attr := simp)]
lemma mapOnProd_fst {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    {T Csym : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {csym : Csym ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t) :
    mapOnProd c φ hφ ≫ pullback.fst c csym = pullback.fst c t := by
  simp only [mapOnProd, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
lemma mapOnProd_snd {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    {T Csym : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {csym : Csym ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t) :
    mapOnProd c φ hφ ≫ pullback.snd c csym = pullback.snd c t ≫ φ := by
  simp only [mapOnProd, pullback.map, pullback.lift_snd]

lemma isPullback_mapOnProd {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    {T Csym : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {csym : Csym ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t) :
    IsPullback (mapOnProd c φ hφ) (pullback.snd c t) (pullback.snd c csym) φ := by
  subst hφ
  refine IsPullback.of_right (h₁₂ := pullback.fst c csym) (v₁₃ := c) (h₂₂ := csym) ?_
    (mapOnProd_snd c φ rfl) (IsPullback.of_hasPullback c csym)
  simpa using IsPullback.of_hasPullback c (φ ≫ csym)

def PullsBack {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) (D' : RelEffDivisor C c r T t) : Prop :=
  Dcan.I.comap (mapOnProd c φ hφ) = D'.I

section transport

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}

noncomputable def comapSubschemeMap (I : (pullback c csym).IdealSheafData) (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) : (I.comap (mapOnProd c φ hφ)).subscheme ⟶ I.subscheme :=
  (I.comapIso (mapOnProd c φ hφ)).hom ≫ pullback.snd _ _

lemma isPullback_comapSubschemeMap (I : (pullback c csym).IdealSheafData) (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) :
    IsPullback (comapSubschemeMap I φ hφ) (I.comap (mapOnProd c φ hφ)).subschemeι
      I.subschemeι (mapOnProd c φ hφ) := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso (mapOnProd c φ hφ)) ?_ ?_).flip
  · simp [comapSubschemeMap]
  · simp
  · simp [comapSubschemeMap]

lemma isPullback_comap_snd (I : (pullback c csym).IdealSheafData) (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) :
    IsPullback (comapSubschemeMap I φ hφ)
      ((I.comap (mapOnProd c φ hφ)).subschemeι ≫ pullback.snd c t)
      (I.subschemeι ≫ pullback.snd c csym) φ :=
  (isPullback_comapSubschemeMap I φ hφ).paste_vert (isPullback_mapOnProd c φ hφ)

end transport

noncomputable def RelEffDivisor.pullbackAlong {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) : RelEffDivisor C c r T t where
  I := Dcan.I.comap (mapOnProd c φ hφ)
  isFinite :=
    have := Dcan.isFinite
    MorphismProperty.of_isPullback (isPullback_comap_snd Dcan.I φ hφ) ‹_›
  flat :=
    have := Dcan.flat
    MorphismProperty.of_isPullback (isPullback_comap_snd Dcan.I φ hφ) ‹_›
  finrank_eq s := by
    have := Dcan.isFinite
    have := Dcan.flat
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_comap_snd Dcan.I φ hφ) s]
    exact Dcan.finrank_eq (φ s)

theorem pullsBack_pullbackAlong {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {r : ℕ} {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) :
    PullsBack Dcan φ hφ (Dcan.pullbackAlong φ hφ) := rfl

lemma PullsBack.eq_pullbackAlong {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {r : ℕ} {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {Dcan : RelEffDivisor C c r Csym csym}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {φ : T ⟶ Csym}
    {hφ : φ ≫ csym = t} {D' : RelEffDivisor C c r T t} (h : PullsBack Dcan φ hφ D') :
    D' = Dcan.pullbackAlong φ hφ :=
  RelEffDivisor.ext h.symm

lemma PullsBack.isPullback {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {Dcan : RelEffDivisor C c r Csym csym}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {φ : T ⟶ Csym}
    {hφ : φ ≫ csym = t} {D' : RelEffDivisor C c r T t} (h : PullsBack Dcan φ hφ D') :
    ∃ ψ : D'.I.subscheme ⟶ Dcan.I.subscheme,
      IsPullback ψ (D'.I.subschemeι ≫ pullback.snd c t)
        (Dcan.I.subschemeι ≫ pullback.snd c csym) φ := by
  obtain rfl := h.eq_pullbackAlong
  exact ⟨_, isPullback_comap_snd Dcan.I φ hφ⟩

lemma RelEffDivisor.pullbackAlong_comp {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of k)} {r : ℕ}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    (Dcan : RelEffDivisor C c r Csym csym)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (φ : T ⟶ Csym) (hφ : φ ≫ csym = t)
    {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)} (φ' : T' ⟶ T)
    (hφ' : φ' ≫ t = t') :
    (Dcan.pullbackAlong φ hφ).pullbackAlong φ' hφ' =
      Dcan.pullbackAlong (φ' ≫ φ) (by rw [Category.assoc, hφ, hφ']) := by
  refine RelEffDivisor.ext ?_
  change (Dcan.I.comap _).comap _ = Dcan.I.comap _
  rw [← Scheme.IdealSheafData.comap_comp]
  congr 1
  ext <;> simp

structure UnivDivisorPack (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (r : ℕ)
    (Csym : Scheme.{u}) (csym : Csym ⟶ Spec (CommRingCat.of k)) where
  Dcan : RelEffDivisor C c r Csym csym
  exists_pullsBack : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k)) [IsIntegral T]
    [LocallyOfFiniteType t] [QuasiCompact t] (D' : RelEffDivisor C c r T t),
    ∃ (φ : T ⟶ Csym) (hφ : φ ≫ csym = t), PullsBack Dcan φ hφ D'
  eq_of_pullsBack : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of k)) [IsReduced T]
    [LocallyOfFiniteType t] [QuasiCompact t] (D' : RelEffDivisor C c r T t)
    (φ₁ φ₂ : T ⟶ Csym) (hφ₁ : φ₁ ≫ csym = t) (hφ₂ : φ₂ ≫ csym = t),
    PullsBack Dcan φ₁ hφ₁ D' → PullsBack Dcan φ₂ hφ₂ D' → φ₁ = φ₂

end AlgebraicCurve

end ZInQ.Contrib.CloudW03NeronSurj.FLT

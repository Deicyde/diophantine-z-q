/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_GoodReductionJacobian_RelativeGroupLawKernel.lean
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
  * 1 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (Lean closes these implicitly at EOF in the original; no-op).
  * file-level `set_option`s inserted after the port namespace, reproducing the source build environment: autoImplicit false (source lakefile.lean leanOptions); maxHeartbeats 4000000 (source lakefile.lean leanOptions); synthInstance.maxHeartbeats 400000 (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.types false (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.instanceSearchTypes false (Lean 4.35 option absent from source Lean 4.33.1; `false` restores 4.33.1 behaviour).
  * `import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Mathlib.AlgebraicGeometry.Pullbacks
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

def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f :=
  Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n

@[simp]
theorem nsmul_zero (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.nsmul t 0 x = G.one t :=
  rfl

@[simp]
theorem nsmul_succ (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t (n + 1) x = G.mul t (G.nsmul t n x) x :=
  rfl

theorem nsmul_one_apply (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.nsmul t 1 x = x := by
  show G.mul t (G.one t) x = x
  exact G.one_mul t x

theorem nsmul_unit (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.nsmul t n (G.one t) = G.one t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmul_succ, ih, G.mul_one]

theorem nsmul_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.nsmul t n x) = G.nsmul t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero =>
      show schemeHomOverComp ψ hψ (G.one t) = G.one t'
      exact G.one_natural t t' ψ hψ
  | succ n ih =>
      calc schemeHomOverComp ψ hψ (G.nsmul t (n + 1) x)
          = schemeHomOverComp ψ hψ (G.mul t (G.nsmul t n x) x) := rfl
        _ = G.mul t' (schemeHomOverComp ψ hψ (G.nsmul t n x)) (schemeHomOverComp ψ hψ x) :=
            G.mul_natural t t' ψ hψ _ _
        _ = G.mul t' (G.nsmul t' n (schemeHomOverComp ψ hψ x)) (schemeHomOverComp ψ hψ x) := by
            rw [ih]
        _ = G.nsmul t' (n + 1) (schemeHomOverComp ψ hψ x) := rfl

def IsTorsionPoint (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : Prop :=
  G.nsmul t n x = G.one t

theorem isTorsionPoint_def (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t n x ↔ G.nsmul t n x = G.one t :=
  Iff.rfl

def torsionSubset (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) : Set (SchemeHomOver t f) :=
  {x | G.IsTorsionPoint t n x}

@[simp]
theorem mem_torsionSubset (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    x ∈ G.torsionSubset t n ↔ G.IsTorsionPoint t n x :=
  Iff.rfl

theorem isTorsionPoint_unit (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.IsTorsionPoint t n (G.one t) :=
  G.nsmul_unit t n

theorem isTorsionPoint_one_iff (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t 1 x ↔ x = G.one t := by
  show G.nsmul t 1 x = G.one t ↔ x = G.one t
  rw [G.nsmul_one_apply]

theorem isTorsionPoint_schemeHomOverComp (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) {x : SchemeHomOver t f}
    (hx : G.IsTorsionPoint t n x) :
    G.IsTorsionPoint t' n (schemeHomOverComp ψ hψ x) := by
  show G.nsmul t' n (schemeHomOverComp ψ hψ x) = G.one t'
  rw [← G.nsmul_natural t t' ψ hψ n x, hx]
  exact G.one_natural t t' ψ hψ

theorem mapsTo_torsionSubset_schemeHomOverComp (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) :
    Set.MapsTo (schemeHomOverComp ψ hψ) (G.torsionSubset t n) (G.torsionSubset t' n) :=
  fun _ hx => G.isTorsionPoint_schemeHomOverComp t t' ψ hψ n hx

abbrev idPoint : SchemeHomOver f f :=
  ⟨𝟙 A, Category.id_comp f⟩

def schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) : A ⟶ A :=
  (G.nsmul f n idPoint).1

theorem schemeNsmul_over (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeNsmul n ≫ f = f :=
  (G.nsmul f n idPoint).2

abbrev schemeKer (G : RelativeGroupLaw R f) (n : ℕ) : Scheme.{u} :=
  pullback (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev schemeKerStr (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeKer n ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1

end RelativeGroupLaw

end GoodReductionJacobian

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT

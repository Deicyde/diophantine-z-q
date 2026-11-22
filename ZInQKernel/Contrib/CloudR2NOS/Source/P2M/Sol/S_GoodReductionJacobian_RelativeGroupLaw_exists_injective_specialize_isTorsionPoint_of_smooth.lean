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
  Source file    : P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_smooth.lean
  Source sha256  : fb779c9996fff980dc9fe5835b668fd5f38de4597902a8f6aa31c7f714241a63
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option linter.unusedSectionVars false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_isTorsionPoint_of_comp_eq
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_smooth
r2nos_namespace_dual

set_option autoImplicit false

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_smooth.GoodReductionJacobian"
open scoped TensorProduct nonZeroDivisors
r2nos_open_scoped_dual "TensorProduct nonZeroDivisors"

universe u

namespace GoodReductionJacobian
r2nos_namespace_dual
w03_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.nsmul_succ RelativeGroupLaw.eq_of_isTorsionPoint_of_comp_eq"
namespace RelativeGroupLaw
r2nos_namespace_dual
w03_export "GoodReductionJacobian.RelativeGroupLaw" "one_natural mul_one one mul_natural inv one_mul mul nsmul nsmul_succ IsTorsionPoint isTorsionPoint_schemeHomOverComp baseChangePointToBase baseChangePointEquiv baseChangePointToBase_mul baseChangePointToBase_one genericFibre fibre eq_of_isTorsionPoint_of_comp_eq"
namespace TorsionSpecialization
r2nos_namespace_dual
w03_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section GenericFibreOfBase

variable (R : Type u) [CommRing R] [IsDomain R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (R' : Type u) [CommRing R'] [Algebra R R']
  (L : Type u) [Field L] [Algebra R' L] [Algebra K L] [Algebra R L]
  [IsScalarTower R R' L] [IsScalarTower R K L]
  [IsLocalization (Algebra.algebraMapSubmonoid R' R⁰) L]

local notation "P" => R' ⊗[R] K
local notation "tR'" => Spec.map (CommRingCat.ofHom (algebraMap R R'))
local notation "ιK" => Spec.map (CommRingCat.ofHom (algebraMap R K))

noncomputable def β : P →ₐ[R] L :=
  Algebra.TensorProduct.lift ((Algebra.ofId R' L).restrictScalars R) ((Algebra.ofId K L).restrictScalars R)
    (fun _ _ => Commute.all _ _)

theorem β_tmul (r' : R') (k : K) : β R K R' L (r' ⊗ₜ k) = algebraMap R' L r' * algebraMap K L k :=
  Algebra.TensorProduct.lift_tmul _ _ _ r' k

theorem β_comp_includeLeft :
    (β R K R' L).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap R' L := by
  ext r'
  change β R K R' L (r' ⊗ₜ 1) = _
  rw [β_tmul, map_one, _root_.mul_one]

theorem β_comp_includeRight :
    (β R K R' L).toRingHom.comp
      ((Algebra.TensorProduct.includeRight : K →ₐ[R] P) : K →+* P) = algebraMap K L := by
  ext k
  change β R K R' L (1 ⊗ₜ k) = _
  rw [β_tmul, map_one, _root_.one_mul]

theorem isUnit_includeLeft (m : Algebra.algebraMapSubmonoid R' R⁰) :
    IsUnit (Algebra.TensorProduct.includeLeftRingHom (R := R) (B := K) (m : R')) := by
  obtain ⟨_, ⟨r, hr, rfl⟩⟩ := m
  change IsUnit ((algebraMap R R' r) ⊗ₜ[R] (1 : K))
  have h : (algebraMap R R' r) ⊗ₜ[R] (1 : K) = (1 : R') ⊗ₜ[R] (algebraMap R K r) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [h]
  have hu : IsUnit (algebraMap R K r) := by
    refine isUnit_iff_ne_zero.mpr ?_
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr
  exact hu.map (Algebra.TensorProduct.includeRight : K →ₐ[R] P)

noncomputable def α : L →+* P :=
  IsLocalization.lift (M := Algebra.algebraMapSubmonoid R' R⁰)
    (g := (Algebra.TensorProduct.includeLeftRingHom : R' →+* P)) (isUnit_includeLeft R K R')

theorem α_algebraMap (r' : R') : α R K R' L (algebraMap R' L r') = r' ⊗ₜ 1 :=
  IsLocalization.lift_eq _ r'

theorem β_comp_α : (β R K R' L).toRingHom.comp (α R K R' L) = RingHom.id L := by
  apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid R' R⁰)
  ext r'
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [α_algebraMap]
  change β R K R' L (r' ⊗ₜ 1) = _
  rw [β_tmul, map_one, _root_.mul_one]

theorem α_comp_algebraMap :
    (α R K R' L).comp (algebraMap K L) =
      ((Algebra.TensorProduct.includeRight : K →ₐ[R] P) : K →+* P) := by
  apply IsLocalization.ringHom_ext R⁰ (S := K)
  ext r
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' L, α_algebraMap]
  change (algebraMap R R' r) ⊗ₜ[R] (1 : K) = (1 : R') ⊗ₜ[R] (algebraMap R K r)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

noncomputable def e : pullback tR' ιK ⟶ Spec (CommRingCat.of L) :=
  (pullbackSpecIso R R' K).hom ≫ Spec.map (CommRingCat.ofHom (α R K R' L))

noncomputable def j : Spec (CommRingCat.of L) ⟶ pullback tR' ιK :=
  Spec.map (CommRingCat.ofHom (β R K R' L).toRingHom) ≫ (pullbackSpecIso R R' K).inv

theorem j_e : j R K R' L ≫ e R K R' L = 𝟙 _ := by
  rw [j, e, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    β_comp_α, CommRingCat.ofHom_id]
  exact Spec.map_id _

theorem j_fst : j R K R' L ≫ pullback.fst tR' ιK = Spec.map (CommRingCat.ofHom (algebraMap R' L)) := by
  rw [j, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    β_comp_includeLeft]

theorem e_snd : e R K R' L ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = pullback.snd tR' ιK := by
  rw [e, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, α_comp_algebraMap,
    pullbackSpecIso_hom_snd]

end GenericFibreOfBase

section Restrict

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}

theorem baseChangePointToBase_genericFibreRestrict {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t g) :
    baseChangePointToBase (specGenericFibreInclusion R K) (genericFibreRestrict R K g t a) =
      GoodReductionJacobian.schemeHomOverComp (pullback.fst t (specGenericFibreInclusion R K))
        pullback.condition a :=
  Subtype.ext (genericFibreRestrict_coe_comp_fst g t a)

theorem genericFibreRestrict_mul (LB : RelativeGroupLaw R g) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a b : SchemeHomOver t g) :
    genericFibreRestrict R K g t (LB.mul t a b) =
      (LB.genericFibre K).mul (pullback.snd t (specGenericFibreInclusion R K))
        (genericFibreRestrict R K g t a) (genericFibreRestrict R K g t b) := by
  apply (baseChangePointEquiv (specGenericFibreInclusion R K) (f := g) _).injective
  change baseChangePointToBase _ _ = baseChangePointToBase _ _
  rw [baseChangePointToBase_mul, baseChangePointToBase_genericFibreRestrict,
    baseChangePointToBase_genericFibreRestrict, baseChangePointToBase_genericFibreRestrict,
    LB.mul_natural]

theorem genericFibreRestrict_one (LB : RelativeGroupLaw R g) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    genericFibreRestrict R K g t (LB.one t) =
      (LB.genericFibre K).one (pullback.snd t (specGenericFibreInclusion R K)) := by
  apply (baseChangePointEquiv (specGenericFibreInclusion R K) (f := g) _).injective
  change baseChangePointToBase _ _ = baseChangePointToBase _ _
  rw [baseChangePointToBase_one, baseChangePointToBase_genericFibreRestrict, LB.one_natural]

theorem genericFibreRestrict_nsmul (LB : RelativeGroupLaw R g) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (a : SchemeHomOver t g) :
    genericFibreRestrict R K g t (LB.nsmul t n a) =
      (LB.genericFibre K).nsmul (pullback.snd t (specGenericFibreInclusion R K)) n
        (genericFibreRestrict R K g t a) := by
  induction n with
  | zero => exact genericFibreRestrict_one K LB t
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, genericFibreRestrict_mul, ih]

theorem isTorsionPoint_of_genericFibreRestrict (LB : RelativeGroupLaw R g) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (hinj : Function.Injective (genericFibreRestrict R K g t))
    (n : ℕ) (a : SchemeHomOver t g)
    (ha : (LB.genericFibre K).IsTorsionPoint (pullback.snd t (specGenericFibreInclusion R K)) n
      (genericFibreRestrict R K g t a)) :
    LB.IsTorsionPoint t n a := by
  apply hinj
  change genericFibreRestrict R K g t (LB.nsmul t n a) = genericFibreRestrict R K g t (LB.one t)
  rw [genericFibreRestrict_nsmul, genericFibreRestrict_one]
  exact ha

end Restrict

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}

theorem preconnectedSpace_spec (S : Type u) [CommRing S] [IsDomain S] :
    PreconnectedSpace (Spec (CommRingCat.of S) : Scheme.{u}) := by
  haveI : IrreducibleSpace (PrimeSpectrum S) := inferInstance
  haveI : IrreducibleSpace (Spec (CommRingCat.of S) : Scheme.{u}) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum S))
  infer_instance

theorem nonempty_spec (S : Type u) [CommRing S] [Nontrivial S] :
    Nonempty (Spec (CommRingCat.of S) : Scheme.{u}) :=
  inferInstanceAs (Nonempty (PrimeSpectrum S))

theorem main (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (n : ℕ) (hn : IsUnit (n : R))
    (R' : Type u) [CommRing R'] [IsDomain R'] [Algebra R R']
    (hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (L : Type u) [Field L] [Algebra R' L] [Algebra K L] [Algebra R L]
    [IsScalarTower R R' L] [IsScalarTower R K L]
    [IsLocalization (Algebra.algebraMapSubmonoid R' R⁰) L]
    (k' : Type u) [Field k'] [Algebra R k'] (ψ : R' →ₐ[R] k') :
    ∃ r : {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
              (pullback.snd g (specGenericFibreInclusion R K)) //
            (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z}
          → {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
            LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y},
      Function.Injective r ∧
      ∀ z, ∃ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g,
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R R'))) n x ∧
        Spec.map (CommRingCat.ofHom (algebraMap R' L)) ≫ x.1 =
          z.1.1 ≫ pullback.fst g (specGenericFibreInclusion R K) ∧
        (r z).1.1 = Spec.map (CommRingCat.ofHom (ψ : R' →+* k')) ≫ x.1 := by

  let ι := specGenericFibreInclusion R K
  have hι : ι = Spec.map (CommRingCat.ofHom (algebraMap R K)) := rfl
  let T : Scheme.{u} := Spec (CommRingCat.of R')
  let t : T ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R R'))
  let sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K L))
  let ee : pullback t ι ⟶ Spec (CommRingCat.of L) := e R K R' L
  let jj : Spec (CommRingCat.of L) ⟶ pullback t ι := j R K R' L
  have hje : jj ≫ ee = 𝟙 _ := j_e R K R' L
  have hjfst : jj ≫ pullback.fst t ι = Spec.map (CommRingCat.ofHom (algebraMap R' L)) :=
    j_fst R K R' L
  have hesnd : ee ≫ sL = pullback.snd t ι := e_snd R K R' L

  have hbij := hN.neronMapping T t hsm

  let p : Spec (CommRingCat.of k') ⟶ T := Spec.map (CommRingCat.ofHom (ψ : R' →+* k'))
  have hp : p ≫ t = Spec.map (CommRingCat.ofHom (algebraMap R k')) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap

  have ext : ∀ z : {z : SchemeHomOver sL (pullback.snd g ι) //
      (LB.genericFibre K).IsTorsionPoint sL n z},
      ∃ x : SchemeHomOver t g, LB.IsTorsionPoint t n x ∧
        genericFibreRestrict R K g t x = GoodReductionJacobian.schemeHomOverComp ee hesnd z.1 := by
    intro z
    obtain ⟨x, hx⟩ := hbij.2 (GoodReductionJacobian.schemeHomOverComp ee hesnd z.1)
    refine ⟨x, ?_, hx⟩
    apply isTorsionPoint_of_genericFibreRestrict K LB t hbij.1 n x
    rw [hx]
    exact (LB.genericFibre K).isTorsionPoint_schemeHomOverComp sL _ ee hesnd n z.2
  choose xOf hxTors hxRes using ext

  have hxi : ∀ z, Spec.map (CommRingCat.ofHom (algebraMap R' L)) ≫ (xOf z).1 =
      z.1.1 ≫ pullback.fst g ι := by
    intro z
    have h := congrArg Subtype.val (hxRes z)

    have h' := genericFibreRestrict_coe_comp_fst (K := K) g t (xOf z)
    rw [h] at h'

    rw [← hjfst, Category.assoc, ← h', GoodReductionJacobian.schemeHomOverComp_coe]
    simp only [Category.assoc]
    rw [← Category.assoc, hje, Category.id_comp]

  let r : {z : SchemeHomOver sL (pullback.snd g ι) // (LB.genericFibre K).IsTorsionPoint sL n z} →
      {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y} :=
    fun z => ⟨GoodReductionJacobian.schemeHomOverComp p hp (xOf z),
      LB.isTorsionPoint_schemeHomOverComp t _ p hp n (hxTors z)⟩
  refine ⟨r, ?_, fun z => ⟨xOf z, hxTors z, hxi z, rfl⟩⟩

  intro z₁ z₂ h
  have h1 : p ≫ (xOf z₁).1 = p ≫ (xOf z₂).1 :=
    congrArg (fun w : {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y} => w.1.1) h
  haveI : IsSeparated g := hN.separated
  haveI : LocallyOfFiniteType g := hN.locallyOfFiniteType
  haveI : PreconnectedSpace T := preconnectedSpace_spec R'
  haveI : Nonempty (Spec (CommRingCat.of k') : Scheme.{u}) := nonempty_spec k'
  have hx12 : xOf z₁ = xOf z₂ :=
    GoodReductionJacobian.RelativeGroupLaw.eq_of_isTorsionPoint_of_comp_eq LB hcomm n hn t
      (xOf z₁) (xOf z₂) (hxTors z₁) (hxTors z₂) p h1
  apply Subtype.ext
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [← hxi z₁, ← hxi z₂, hx12]
  · rw [z₁.1.2, z₂.1.2]

end Main

end GoodReductionJacobian.RelativeGroupLaw.TorsionSpecialization

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (n : ℕ) (hn : IsUnit (n : R))
    (R' : Type u) [CommRing R'] [IsDomain R'] [Algebra R R']
    (hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (L : Type u) [Field L] [Algebra R' L] [Algebra K L] [Algebra R L]
    [IsScalarTower R R' L] [IsScalarTower R K L]
    [IsLocalization (Algebra.algebraMapSubmonoid R' R⁰) L]
    (k' : Type u) [Field k'] [Algebra R k'] (ψ : R' →ₐ[R] k') :
    ∃ r : {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
              (pullback.snd g (specGenericFibreInclusion R K)) //
            (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z}
          → {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
            LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y},
      Function.Injective r ∧
      ∀ z, ∃ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g,
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R R'))) n x ∧
        Spec.map (CommRingCat.ofHom (algebraMap R' L)) ≫ x.1 =
          z.1.1 ≫ pullback.fst g (specGenericFibreInclusion R K) ∧
        (r z).1.1 = Spec.map (CommRingCat.ofHom (ψ : R' →+* k')) ≫ x.1 :=
  GoodReductionJacobian.RelativeGroupLaw.TorsionSpecialization.main K LB hcomm hN n hn R' hsm L k' ψ
end S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_smooth
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT

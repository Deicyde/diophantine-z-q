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
  Source file    : Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean
  Source sha256  : 0dc870b7f0be4e97313d3333986ba5e61f6916ab6f7e16ab5058bb9eb2f1f1fe
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 8 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 6 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 1 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: R9×1; rule citations in the batch ledger.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Ring.Subring.Pointwise
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Bezout
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing
r2nos_open_dual "IsDedekindDomain WithZero IsLocalRing"

namespace AlgebraicCurve
r2nos_namespace_dual

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

structure Place where

  toValuationSubring : ValuationSubring F

  algebraMap_mem' : ∀ a : K, algebraMap K F a ∈ toValuationSubring

  ne_top' : toValuationSubring ≠ ⊤

  isPrincipalIdealRing' : IsPrincipalIdealRing toValuationSubring

theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.ValuationSubring.not_isField_of_ne_top {A : ValuationSubring F} (hA : A ≠ ⊤) :
    ¬IsField A := by
  intro hf
  apply hA
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  by_cases hx : x ∈ A
  · exact hx
  ·

    exfalso
    have hx0 : x ≠ 0 := fun h => hx (h ▸ A.zero_mem)
    have hxi : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
    have hxi0 : (⟨x⁻¹, hxi⟩ : A) ≠ 0 := by
      simp only [ne_eq, Subtype.ext_iff]
      exact inv_ne_zero hx0
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel hxi0
    have hb' : x⁻¹ * (b : F) = 1 := by
      have h := congrArg (Subtype.val) hb
      simpa using h
    have hbx : (b : F) = x := by
      field_simp at hb'
      exact hb'
    exact hx (hbx ▸ b.2)

namespace Place
r2nos_namespace_dual

variable {K F}

theorem toValuationSubring_injective :
    Function.Injective (toValuationSubring (K := K) (F := F)) := by
  rintro ⟨a, _, _, _⟩ ⟨b, _, _, _⟩ (rfl : a = b)
  rfl

@[ext]
theorem ext {v w : Place K F} (h : v.toValuationSubring = w.toValuationSubring) : v = w :=
  toValuationSubring_injective h

variable (v : Place K F)

instance : IsPrincipalIdealRing v.toValuationSubring := v.isPrincipalIdealRing'

instance : IsDiscreteValuationRing v.toValuationSubring where
  not_a_field' := by
    rw [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact ValuationSubring.not_isField_of_ne_top F v.ne_top'

instance : Algebra K v.toValuationSubring :=
  ((algebraMap K F).codRestrict v.toValuationSubring.toSubring v.algebraMap_mem').toAlgebra

@[simp]
theorem coe_algebraMap (a : K) :
    (algebraMap K v.toValuationSubring a : F) = algebraMap K F a := rfl

instance : IsScalarTower K v.toValuationSubring F :=
  IsScalarTower.of_algebraMap_eq fun a => (v.coe_algebraMap a).symm

abbrev ResidueField : Type _ := IsLocalRing.ResidueField v.toValuationSubring

def deg : ℕ := Module.finrank K v.ResidueField

class FiniteResidue : Prop where
  finite : Module.Finite K v.ResidueField

def heightOneSpectrum : HeightOneSpectrum v.toValuationSubring :=
  IsDiscreteValuationRing.maximalIdeal _

@[simp]
theorem heightOneSpectrum_asIdeal :
    v.heightOneSpectrum.asIdeal = IsLocalRing.maximalIdeal v.toValuationSubring := rfl

def adicValuation : Valuation F ℤᵐ⁰ := v.heightOneSpectrum.valuation F

theorem adicValuation_ne_zero {f : F} (hf : f ≠ 0) : v.adicValuation f ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr hf

theorem adicValuation_coe (a : v.toValuationSubring) :
    v.adicValuation (a : F) = v.heightOneSpectrum.intValuation a := by
  simpa [adicValuation] using v.heightOneSpectrum.valuation_of_algebraMap (K := F) a

theorem adicValuation_coe_eq_one_iff (a : v.toValuationSubring) :
    v.adicValuation (a : F) = 1 ↔ IsUnit a := by
  rw [v.adicValuation_coe, HeightOneSpectrum.intValuation_eq_one_iff, heightOneSpectrum_asIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

theorem adicValuation_coe_irreducible {π : v.toValuationSubring} (hπ : Irreducible π) :
    v.adicValuation (π : F) = exp (-1 : ℤ) := by
  rw [v.adicValuation_coe]
  exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero
    (by rw [heightOneSpectrum_asIdeal, hπ.maximalIdeal_eq])

def ord (f : F) : ℤ := -(WithZero.log (v.adicValuation f))

@[simp]
theorem ord_zero : v.ord (0 : F) = 0 := by simp [ord]

@[simp]
theorem ord_one : v.ord (1 : F) = 0 := by simp [ord]

theorem ord_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    v.ord (f * g) = v.ord f + v.ord g := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul (v.adicValuation_ne_zero hf) (v.adicValuation_ne_zero hg)]
  ring

theorem ord_inv (f : F) : v.ord f⁻¹ = -v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · simp only [ord, map_inv₀, WithZero.log_inv, neg_neg]

theorem ord_coe_unit (u : v.toValuationSubringˣ) :
    v.ord ((u : v.toValuationSubring) : F) = 0 := by
  simp [ord, (v.adicValuation_coe_eq_one_iff _).mpr u.isUnit]

theorem ord_coe_irreducible {π : v.toValuationSubring} (hπ : Irreducible π) :
    v.ord (π : F) = 1 := by
  simp [ord, v.adicValuation_coe_irreducible hπ]

theorem ord_zpow (f : F) (n : ℤ) : v.ord (f ^ n) = n * v.ord f := by
  simp only [ord, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

theorem ord_unit_smul_zpow (u : v.toValuationSubringˣ) {π : v.toValuationSubring}
    (hπ : Irreducible π) (n : ℤ) :
    v.ord (((u : v.toValuationSubring) : F) * ((π : F) ^ n)) = n := by
  have hπF : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hu : ((u : v.toValuationSubring) : F) ≠ 0 := by
    simp [ne_eq, ZeroMemClass.coe_eq_zero]
  rw [v.ord_mul hu (zpow_ne_zero n hπF), v.ord_coe_unit u, zero_add,
    v.ord_zpow _ _, v.ord_coe_irreducible hπ, mul_one]

theorem exists_unit_mul_zpow {f : F} (hf : f ≠ 0) {π : v.toValuationSubring}
    (hπ : Irreducible π) :
    ∃ u : v.toValuationSubringˣ,
      f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (v.ord f)) := by
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := F) hπ hf
  rw [Units.smul_def, Algebra.smul_def] at hu
  have hcoe : algebraMap v.toValuationSubring F (u : v.toValuationSubring)
      = ((u : v.toValuationSubring) : F) := rfl
  have hcoe' : algebraMap v.toValuationSubring F π = (π : F) := rfl
  rw [hcoe, hcoe'] at hu
  have hn : v.ord f = n := by rw [hu]; exact v.ord_unit_smul_zpow u hπ n
  exact ⟨u, by rw [hn, hu]⟩

end Place

abbrev Divisor : Type _ := Place K F →₀ ℤ

namespace Divisor
r2nos_namespace_dual

variable {K F}

def degree : Divisor K F →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (v.deg : ℤ)

@[simp]
theorem degree_single (v : Place K F) (n : ℤ) :
    degree (Finsupp.single v n) = n * v.deg := by
  simp [degree]

def degZero : AddSubgroup (Divisor K F) := degree.ker

theorem mem_degZero {D : Divisor K F} : D ∈ degZero (K := K) (F := F) ↔ degree D = 0 :=
  Iff.rfl

def IsPrincipal (D : Divisor K F) : Prop := ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, D v = v.ord f

def principal : AddSubgroup (Divisor K F) where
  carrier := {D | IsPrincipal D}
  zero_mem' := ⟨1, one_ne_zero, fun v => by simp⟩
  add_mem' := by
    rintro D E ⟨f, hf, hD⟩ ⟨g, hg, hE⟩
    exact ⟨f * g, mul_ne_zero hf hg, fun v => by
      rw [Finsupp.add_apply, hD v, hE v, v.ord_mul hf hg]⟩
  neg_mem' := by
    rintro D ⟨f, hf, hD⟩
    exact ⟨f⁻¹, inv_ne_zero hf, fun v => by
      rw [Finsupp.neg_apply, hD v, v.ord_inv]⟩

theorem mem_principal {D : Divisor K F} :
    D ∈ principal (K := K) (F := F) ↔ IsPrincipal D := Iff.rfl

end Divisor

class HasPrincipalDivisors : Prop where
  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F,
    (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0

abbrev Pic : Type _ := Divisor K F ⧸ Divisor.principal (K := K) (F := F)

abbrev Pic0 : Type _ :=
  Divisor.degZero (K := K) (F := F) ⧸
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))

namespace Pic0
r2nos_namespace_dual

variable {K F}

def mk (D : Divisor.degZero (K := K) (F := F)) : Pic0 K F := QuotientAddGroup.mk D

theorem mk_surjective : Function.Surjective (mk (K := K) (F := F)) :=
  QuotientAddGroup.mk_surjective

@[simp]
theorem mk_add (D E : Divisor.degZero (K := K) (F := F)) : mk (D + E) = mk D + mk E := rfl

@[simp]
theorem mk_zero : mk (0 : Divisor.degZero (K := K) (F := F)) = 0 := rfl

variable (K F) in

def torsion (n : ℕ) : AddSubgroup (Pic0 K F) :=
  (Submodule.torsionBy ℤ (Pic0 K F) (n : ℤ)).toAddSubgroup

theorem mem_torsion {n : ℕ} {x : Pic0 K F} : x ∈ torsion K F n ↔ (n : ℤ) • x = 0 :=
  Submodule.mem_torsionBy_iff _ _

end Pic0

def AbelJacobiCard (p : ℕ) (g : ℕ) : Prop :=
  ∀ n : ℕ, Nat.card (Pic0.torsion K F (p ^ n)) = p ^ (2 * g * n)

namespace Place
r2nos_namespace_dual

open scoped Pointwise
r2nos_open_scoped_dual "Pointwise"

variable {K F}
variable (σ : F ≃ₐ[K] F)

def smulRingEquiv (A : ValuationSubring F) : A ≃+* (σ • A : ValuationSubring F) where
  toFun x := ⟨σ x, by
    simpa [AlgEquiv.smul_def] using
      ValuationSubring.smul_mem_pointwise_smul σ (x : F) A x.2⟩
  invFun y := ⟨σ.symm y, by
    have := (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem (g := σ)
      (S := A) (x := (y : F))).mp y.2
    simpa [AlgEquiv.smul_def, AlgEquiv.aut_inv] using this⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem coe_smulRingEquiv_apply (A : ValuationSubring F) (x : A) :
    ((smulRingEquiv σ A x : (σ • A : ValuationSubring F)) : F) = σ x := rfl

theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.ValuationSubring.pointwise_smul_top :
    σ • (⊤ : ValuationSubring F) = ⊤ := by
  ext x
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact ⟨fun _ => ValuationSubring.mem_top x, fun _ => ValuationSubring.mem_top _⟩

instance : SMul (F ≃ₐ[K] F) (Place K F) where
  smul σ v :=
    { toValuationSubring := σ • v.toValuationSubring
      algebraMap_mem' := fun a => by
        have h := ValuationSubring.smul_mem_pointwise_smul σ (algebraMap K F a)
          v.toValuationSubring (v.algebraMap_mem' a)
        rwa [AlgEquiv.smul_def, σ.commutes] at h
      ne_top' := fun h => v.ne_top' <| by
        have := congrArg (σ⁻¹ • ·) h
        simpa [ValuationSubring.pointwise_smul_top] using this
      isPrincipalIdealRing' :=
        IsPrincipalIdealRing.of_surjective
          (smulRingEquiv σ v.toValuationSubring : _ ≃+* _)
          (smulRingEquiv σ v.toValuationSubring).surjective }

variable (v : Place K F)

@[simp]
theorem smul_toValuationSubring : (σ • v).toValuationSubring = σ • v.toValuationSubring := rfl

instance : MulAction (F ≃ₐ[K] F) (Place K F) where
  one_smul v := by
    ext1
    rw [smul_toValuationSubring, one_smul]
  mul_smul σ τ v := by
    ext1
    simp only [smul_toValuationSubring]
    rw [mul_smul]

theorem ord_smul (f : F) : (σ • v).ord (σ f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ

  set n := v.ord f with hn

  set e := smulRingEquiv σ v.toValuationSubring with he
  have hπ' : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hu' : IsUnit (e (u : v.toValuationSubring)) := u.isUnit.map e
  have hcoeu : ((hu'.unit : (σ • v).toValuationSubring) : F)
      = σ ((u : v.toValuationSubring) : F) := by
    rw [IsUnit.unit_spec]
    rfl
  have hcoeπ : ((e π : (σ • v).toValuationSubring) : F) = σ (π : F) := rfl
  have key : σ f = ((hu'.unit : (σ • v).toValuationSubring) : F)
      * (((e π : (σ • v).toValuationSubring) : F) ^ n) := by
    rw [hcoeu, hcoeπ, hu, map_mul, map_zpow₀]
  rw [key, (σ • v).ord_unit_smul_zpow hu'.unit hπ' n]

def smulResidueAlgEquiv : v.ResidueField ≃ₐ[K] (σ • v).ResidueField :=
  AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv
      (smulRingEquiv σ v.toValuationSubring)) <| fun a => by
    have h3 : (smulRingEquiv σ v.toValuationSubring) (algebraMap K v.toValuationSubring a)
        = algebraMap K (σ • v).toValuationSubring a := by
      ext
      rw [coe_smulRingEquiv_apply, coe_algebraMap, σ.commutes]
      rfl
    show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    exact congrArg _ h3

@[simp]
theorem deg_smul : (σ • v).deg = v.deg :=
  ((smulResidueAlgEquiv σ v).toLinearEquiv.finrank_eq).symm

end Place

namespace Divisor
r2nos_namespace_dual

open scoped Pointwise
r2nos_open_scoped_dual "Pointwise"

variable {K F}

instance : DistribMulAction (F ≃ₐ[K] F) (Divisor K F) := Finsupp.comapDistribMulAction

theorem smul_def (σ : F ≃ₐ[K] F) (D : Divisor K F) :
    σ • D = Finsupp.mapDomain (σ • ·) D := rfl

@[simp]
theorem smul_single (σ : F ≃ₐ[K] F) (v : Place K F) (n : ℤ) :
    σ • Finsupp.single v n = Finsupp.single (σ • v) n := by
  rw [smul_def, Finsupp.mapDomain_single]

theorem smul_apply_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) (v : Place K F) :
    (σ • D) (σ • v) = D v := by
  rw [smul_def]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective σ) D v

theorem smul_apply (σ : F ≃ₐ[K] F) (D : Divisor K F) (w : Place K F) :
    (σ • D) w = D (σ⁻¹ • w) := by
  have : (σ • D) (σ • (σ⁻¹ • w)) = D (σ⁻¹ • w) := smul_apply_smul σ D (σ⁻¹ • w)
  rwa [smul_inv_smul] at this

@[simp]
theorem degree_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) : degree (σ • D) = degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
      rw [smul_add, map_add, map_add, ih, smul_single, degree_single, degree_single,
        Place.deg_smul]

theorem smul_mem_degZero (σ : F ≃ₐ[K] F) {D : Divisor K F}
    (hD : D ∈ degZero (K := K) (F := F)) : σ • D ∈ degZero (K := K) (F := F) := by
  rwa [mem_degZero, degree_smul]

theorem smul_mem_principal (σ : F ≃ₐ[K] F) {D : Divisor K F}
    (hD : D ∈ principal (K := K) (F := F)) : σ • D ∈ principal (K := K) (F := F) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨σ f, by simpa using hf, fun w => ?_⟩
  rw [smul_apply, hD (σ⁻¹ • w)]
  have h := Place.ord_smul σ (σ⁻¹ • w) f
  rw [smul_inv_smul] at h
  exact h.symm

end Divisor

namespace Pic0
r2nos_namespace_dual

open scoped Pointwise
r2nos_open_scoped_dual "Pointwise"

variable {K F}

def degZeroSMulHom (σ : F ≃ₐ[K] F) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((DistribSMul.toAddMonoidHom (Divisor K F) σ).domRestrict
    (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.smul_mem_degZero σ D.2)

@[simp]
theorem coe_degZeroSMulHom (σ : F ≃ₐ[K] F) (D : Divisor.degZero (K := K) (F := F)) :
    (degZeroSMulHom σ D : Divisor K F) = σ • (D : Divisor K F) := rfl

instance : SMul (F ≃ₐ[K] F) (Pic0 K F) where
  smul σ := QuotientAddGroup.map _ _ (degZeroSMulHom σ) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.smul_mem_principal σ hD)

theorem smul_mk (σ : F ≃ₐ[K] F) (D : Divisor.degZero (K := K) (F := F)) :
    σ • (mk D) = mk (degZeroSMulHom σ D) := rfl

instance : DistribMulAction (F ≃ₐ[K] F) (Pic0 K F) where
  one_smul x := by
    obtain ⟨D, rfl⟩ := mk_surjective x
    rw [smul_mk]
    exact congrArg mk (Subtype.ext (by rw [coe_degZeroSMulHom, one_smul]))
  mul_smul σ τ x := by
    obtain ⟨D, rfl⟩ := mk_surjective x
    rw [smul_mk, smul_mk, smul_mk]
    exact congrArg mk (Subtype.ext (by simp only [coe_degZeroSMulHom]; rw [mul_smul]))
  smul_zero σ := by
    show σ • mk 0 = mk 0
    rw [smul_mk]
    exact congrArg mk (map_zero _)
  smul_add σ x y := by
    obtain ⟨D, rfl⟩ := mk_surjective x
    obtain ⟨E, rfl⟩ := mk_surjective y
    show σ • mk (D + E) = mk (degZeroSMulHom σ D) + mk (degZeroSMulHom σ E)
    rw [smul_mk]
    exact congrArg mk (map_add _ _ _)

end Pic0

namespace Place
r2nos_namespace_dual

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

open IsDedekindDomain.HeightOneSpectrum in
r2nos_open_dual "IsDedekindDomain.HeightOneSpectrum" in

theorem isPrincipalIdealRing_valuationSubring (w : HeightOneSpectrum R) :
    IsPrincipalIdealRing ((w.valuation F).valuationSubring) := by
  rw [show (w.valuation F).valuationSubring = valuationSubringAtPrime F w from
    (valuationSubringAtPrime_eq_valuationSubring (K := F) w).symm]

  infer_instance

open IsDedekindDomain.HeightOneSpectrum in
r2nos_open_dual "IsDedekindDomain.HeightOneSpectrum" in

def ofHeightOneSpectrum [Algebra K R] [IsScalarTower K R F] (w : HeightOneSpectrum R) :
    Place K F where
  toValuationSubring := (w.valuation F).valuationSubring
  algebraMap_mem' := fun a => by
    rw [Valuation.mem_valuationSubring_iff, IsScalarTower.algebraMap_apply K R F]
    exact w.valuation_le_one (algebraMap K R a)
  ne_top' := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' := isPrincipalIdealRing_valuationSubring w

@[simp]
theorem ofHeightOneSpectrum_toValuationSubring [Algebra K R] [IsScalarTower K R F]
    (w : HeightOneSpectrum R) :
    (ofHeightOneSpectrum (K := K) w).toValuationSubring = (w.valuation F).valuationSubring :=
  rfl

end Place

end AlgebraicCurve
end

end ZInQ.Contrib.CloudW03NeronSurj.FLT

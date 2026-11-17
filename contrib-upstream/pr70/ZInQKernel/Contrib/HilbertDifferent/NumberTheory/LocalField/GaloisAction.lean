/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/LocalField/GaloisAction.lean
Original SHA-256: 7499acaddb94238f7edb105c38b8e06fdc0f876815a3d82e42db47206a025d8d
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/NumberTheory/LocalField/GaloisAction.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.Algebra.Ring.Action.Invariant
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.IsGaloisGroup.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.FiniteExtension.Basic
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.IntegerRing
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.Valuation.ValuativeRel.Extension
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open ValuativeRel

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

variable [Module.Finite K L]

/- The ring of integers is stable under every automorphism of a finite extension of a
nonarchimedean local field. -/
instance integerRingIsInvariantSubring : IsInvariantSubring (L ≃ₐ[K] L) 𝒪[L] where
  smul_mem σ x hx := by
    rw [Valuation.mem_integer_iff] at hx ⊢
    simpa only [AlgEquiv.smul_def, σ.valuation_eq] using hx

end TauCeti

namespace AlgEquiv

open TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/- Coercing the action on the integer ring to `L` recovers the field automorphism. -/
@[simp]
theorem coe_smul_integerRing (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    ((σ • x : 𝒪[L]) : L) = σ (x : L) :=
  (rfl)

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/- The integer-ring equivalence agrees with the canonical automorphism action. -/
@[simp]
theorem integerRingEquiv_apply (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    σ.integerRingEquiv x = σ • x :=
  Subtype.ext (by rw [coe_integerRingEquiv_apply, coe_smul_integerRing])

end AlgEquiv

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

/- Automorphisms act on the ring of integers by `𝒪[K]`-algebra automorphisms: the action commutes
with the scalars from the ring of integers of the base field. -/
instance integerRingSMulCommClass : SMulCommClass (L ≃ₐ[K] L) 𝒪[K] 𝒪[L] :=
  ⟨fun σ x y ↦ by
    simpa only [AlgEquiv.integerRingEquiv_apply] using map_smul σ.integerRingEquiv x y⟩

/- The residue-field action of extension automorphisms fixes the base residue field. -/
instance integerRingFaithfulSMul : FaithfulSMul (L ≃ₐ[K] L) 𝒪[L] where
  eq_of_smul_eq_smul {σ τ} h := AlgEquiv.ext fun y ↦ by
    obtain ⟨a, ha, hay⟩ := exists_algebraMap_mul_mem_integerRing K L y
    have hσ : ((σ • ⟨_, hay⟩ : 𝒪[L]) : L) = ((τ • ⟨_, hay⟩ : 𝒪[L]) : L) := by rw [h]
    have ha' : algebraMap K L (a : K) ≠ 0 :=
      (map_ne_zero _).2 (Subtype.coe_ne_coe.2 ha)
    rw [AlgEquiv.coe_smul_integerRing, AlgEquiv.coe_smul_integerRing, map_mul, map_mul,
      AlgEquiv.commutes, AlgEquiv.commutes] at hσ
    exact mul_left_cancel₀ ha' hσ

end TauCeti

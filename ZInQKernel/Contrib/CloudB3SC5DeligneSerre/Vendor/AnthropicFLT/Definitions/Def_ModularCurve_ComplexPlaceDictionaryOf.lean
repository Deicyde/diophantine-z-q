/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf (git blob 50664e5eddc294a5e2d4d7bb076b57ef0f19777d, sha256 dd65ac866f371bb1704409250c5931dbd797dfda5686af0a8f3557797a58a5c4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve

def realizeOf (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) (τ : ℍ) : ℂ := by
  classical
  exact
    if H : ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    then (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ
    else 0

theorem realizeOf_def (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) (τ : ℍ) :
    realizeOf Γ x τ = by
      classical
      exact
        if H : ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
            (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
              x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
                ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
        then (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ
        else 0 :=
  rfl

theorem realizeOf_of_not (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) (τ : ℍ)
    (h : ¬ ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    realizeOf Γ x τ = 0 := by
  classical
  rw [realizeOf_def]
  exact dif_neg h

structure ComplexPlaceDictionaryOf (Γ : Subgroup SL(2, ℤ))
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) where

  pt : ℍ → AlgebraicCurve.Place ℂ (laurentBaseChange ℂ F₀)

  ramification : ℍ → ℕ

  ramification_pos : ∀ τ : ℍ, 0 < ramification τ

  pt_smul : ∀ (γ : Γ) (τ : ℍ), pt ((γ : SL(2, ℤ)) • τ) = pt τ

  mem_pt_iff : ∀ (τ : ℍ) (x : laurentBaseChange ℂ F₀),
    x ∈ (pt τ).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
        (fun z : ℍ => ‖realizeOf Γ (x : LaurentSeries ℂ) z‖)

  meromorphicOrderAt_realizeOf : ∀ (τ : ℍ) (x : laurentBaseChange ℂ F₀), x ≠ 0 →
    meromorphicOrderAt (fun z : ℂ => realizeOf Γ (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) =
      (((ramification τ : ℤ) * (pt τ).ord x : ℤ) : WithTop ℤ)

namespace ComplexPlaceDictionaryOf

variable {Γ : Subgroup SL(2, ℤ)} {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

theorem pt_smul_of_mem (D : ComplexPlaceDictionaryOf Γ F₀) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    D.pt (γ • τ) = D.pt τ :=
  D.pt_smul ⟨γ, hγ⟩ τ

theorem ramification_ne_zero (D : ComplexPlaceDictionaryOf Γ F₀) (τ : ℍ) : D.ramification τ ≠ 0 :=
  (D.ramification_pos τ).ne'

end ComplexPlaceDictionaryOf

theorem realizeOf_gamma0 (N : ℕ) (x : LaurentSeries ℂ) (τ : ℍ) :
    realizeOf (CongruenceSubgroup.Gamma0 N) x τ = realize N x τ :=
  rfl

def ComplexPlaceDictionaryOf.ofGamma0 {N : ℕ} [NeZero N] (D : ComplexPlaceDictionary N) :
    ComplexPlaceDictionaryOf (CongruenceSubgroup.Gamma0 N) (modularFunctionFieldFull N) where
  pt := D.pt
  ramification := D.ramification
  ramification_pos := D.ramification_pos
  pt_smul := D.pt_smul
  mem_pt_iff := D.mem_pt_iff
  meromorphicOrderAt_realizeOf := D.meromorphicOrderAt_realize

def ComplexPlaceDictionaryOf.toGamma0 {N : ℕ} [NeZero N]
    (D : ComplexPlaceDictionaryOf (CongruenceSubgroup.Gamma0 N) (modularFunctionFieldFull N)) :
    ComplexPlaceDictionary N where
  pt := D.pt
  ramification := D.ramification
  ramification_pos := D.ramification_pos
  pt_smul := D.pt_smul
  mem_pt_iff := D.mem_pt_iff
  meromorphicOrderAt_realize := D.meromorphicOrderAt_realizeOf

@[simp]
theorem ComplexPlaceDictionaryOf.pt_ofGamma0 {N : ℕ} [NeZero N] (D : ComplexPlaceDictionary N) :
    (ComplexPlaceDictionaryOf.ofGamma0 D).pt = D.pt :=
  rfl

@[simp]
theorem ComplexPlaceDictionaryOf.pt_toGamma0 {N : ℕ} [NeZero N]
    (D : ComplexPlaceDictionaryOf (CongruenceSubgroup.Gamma0 N) (modularFunctionFieldFull N)) :
    D.toGamma0.pt = D.pt :=
  rfl

end ModularCurve

end

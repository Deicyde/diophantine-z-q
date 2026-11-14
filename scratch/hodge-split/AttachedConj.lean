import ZInQKernel.Contrib.G9.I4Layer
import ZInQKernel.HDecomp.ModCurves.C9
import ZInQKernel.HDecomp.Textbook.C10Closed
import ZInQKernel.Contrib.Chebotarev.FrobeniusDense

/-!
# hodge-split, companion file: `AttachedConj` proved from the kernel's T18 and T19

Task hodge-split, 2026-11-14. Separate from `HodgeSplit.lean` because importing `ZInQKernel.HDecomp`
puts a second `PkgI4` namespace (the root one) in scope, which makes the opened names of
`HodgeSplit.lean` ambiguous; scratch files cannot import each other. `IsConj` and `AttachedConj`
below are textual copies of the definitions in `HodgeSplit.lean` §10 with the names
`ZInQ.Contrib.G9.PkgI4.*` written out (the same constants `HodgeSplit.lean` resolves through
`open ZInQ.Contrib.G9`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ZInQ.Contrib.HodgeSplit

open Module

noncomputable section

/-- `r` and `ρ'` are conjugate by a fixed matrix (g12-det's `G0Galois.IsConj`, verbatim). -/
def IsConj {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r ρ' : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) : Prop :=
  ∃ P : GL (Fin n) (PadicAlgCl ℓ), ∀ σ, r.toHom σ = P * ρ'.toHom σ * P⁻¹

/-- **GLUE (Chebotarev density with Brauer–Nesbitt).** Copy of `HodgeSplit.lean`'s `AttachedConj`. -/
def AttachedConj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ρ ρ' : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ 2) (S : Finset ℕ),
    ρ.IsSemisimple → ρ'.IsSemisimple →
    (∀ p : ℕ, p.Prime → p ∉ S → ρ.UnramifiedAt p ∧ ρ'.UnramifiedAt p ∧
      ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ),
        ZInQ.Contrib.G9.PkgI4.LiesOver v p →
        ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p → (ρ.mat σ).trace = (ρ'.mat σ).trace) →
    IsConj ρ ρ'

/-! ## §13. Glue proved: `AttachedConj` (Chebotarev with Brauer–Nesbitt)

From the kernel's proved leaves T18 (`ZInQ.Contrib.frobeniusDense`, through Tau Ceti's Chebotarev)
and T19 (`TSkolemKW.C10.brauerNesbittChar0'`), via `C9Rhof.iso_of_arithFrob`
(`ZInQKernel/HDecomp/ModCurves/C9.lean`). The bridge: pkg-I4's matrix-valued `GaloisRep` as a
Mathlib `Representation` on `ℚ̄_ℓ²`; its `IsSemisimple` (invariant complements) as
`IsSemisimpleModule` over the group algebra (Mathlib's `Representation.mapSubmodule`). -/

section AttachedConjSec


variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- pkg-I4's `GaloisRep` as a Mathlib `Representation` on `ℚ̄_ℓⁿ`. -/
def galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) :
    Representation (PadicAlgCl ℓ) ZInQ.Contrib.G9.PkgI4.GQ (Fin n → PadicAlgCl ℓ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) ≃ₐ[PadicAlgCl ℓ] _).toMonoidHom.comp
    ((Units.coeHom _).comp ρ.toHom)

theorem galRepRep_apply {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    galRepRep ρ σ = Matrix.toLin' (ρ.mat σ) := rfl

theorem toMatrix_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (galRepRep ρ σ) = ρ.mat σ := by
  rw [LinearMap.toMatrix_eq_toMatrix', galRepRep_apply, LinearMap.toMatrix'_toLin']

theorem trace_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    LinearMap.trace (PadicAlgCl ℓ) _ (galRepRep ρ σ) = (ρ.mat σ).trace := by
  rw [LinearMap.trace_eq_matrix_trace (PadicAlgCl ℓ) (Pi.basisFun (PadicAlgCl ℓ) (Fin n)),
    toMatrix_galRepRep]

theorem continuous_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) :
    Continuous fun g => LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (galRepRep ρ g) := by
  simp only [toMatrix_galRepRep]
  exact Units.continuous_val.comp ρ.continuous_toHom

theorem mem_invtSubmodule_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n)
    (W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ)) :
    W ∈ (galRepRep ρ).invtSubmodule ↔ ∀ σ, W.map (Matrix.toLin' (ρ.mat σ)) ≤ W := by
  rw [Representation.mem_invtSubmodule]
  refine forall_congr' fun σ => ?_
  rw [Module.End.mem_invtSubmodule, Submodule.map_le_iff_le_comap, galRepRep_apply]

theorem isSemisimpleModule_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (h : ZInQ.Contrib.G9.PkgI4.GaloisRep.IsSemisimple ρ) :
    IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) ZInQ.Contrib.G9.PkgI4.GQ) (galRepRep ρ).asModule := by
  rw [isSemisimpleModule_iff, ← (galRepRep ρ).mapSubmodule.complementedLattice_iff]
  refine ⟨fun a => ?_⟩
  obtain ⟨W, hW⟩ := a
  obtain ⟨W', hc, hW'⟩ := h W ((mem_invtSubmodule_galRepRep ρ W).mp hW)
  refine ⟨⟨W', (mem_invtSubmodule_galRepRep ρ W').mpr hW'⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    exact Subtype.ext hc.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subtype.ext hc.sup_eq_top

/-- `C9Rhof.FrobeniusDense` from the kernel's proved T18 (same body, other namespace). -/
theorem frobeniusDense_C9 : C9Rhof.FrobeniusDense := by
  intro U hU σ S
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := ZInQ.Contrib.frobeniusDense U hU σ S
  exact ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩

/-- **`AttachedConj`, proved** (from T18, T19 in the kernel). -/
theorem attachedConj_proof : AttachedConj := by
  intro ℓ _ ρ ρ' S hss hss' hS
  have htr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (τ : ZInQ.Contrib.G9.PkgI4.GQ),
      ZInQ.Contrib.G9.PkgI4.LiesOver v p → ZInQ.Contrib.G9.PkgI4.IsArithFrob τ v p →
      LinearMap.trace (PadicAlgCl ℓ) _ (galRepRep ρ τ) =
        LinearMap.trace (PadicAlgCl ℓ) _ (galRepRep ρ' τ) := by
    intro p hp hpS v τ hv hτ
    rw [trace_galRepRep, trace_galRepRep]
    exact (hS p hp hpS).2.2 v τ hv hτ
  obtain ⟨e⟩ := C9Rhof.iso_of_arithFrob TSkolemKW.C10.brauerNesbittChar0' frobeniusDense_C9 S
    (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (Pi.basisFun (PadicAlgCl ℓ) (Fin 2))
    (galRepRep ρ) (galRepRep ρ') (continuous_galRepRep ρ) (continuous_galRepRep ρ')
    (isSemisimpleModule_galRepRep ρ hss) (isSemisimpleModule_galRepRep ρ' hss') htr
  let L : (Fin 2 → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) :=
    ((galRepRep ρ).asModuleEquiv.symm.trans (e.restrictScalars (PadicAlgCl ℓ))).trans
      (galRepRep ρ').asModuleEquiv
  have hL : ∀ σ v, L (galRepRep ρ σ v) = galRepRep ρ' σ (L v) := by
    intro σ v
    simp only [L, LinearEquiv.trans_apply, Representation.asModuleEquiv_symm_map_rho,
      LinearEquiv.restrictScalars_apply, LinearEquiv.map_smul,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
  let M := LinearMap.toMatrix' L.toLinearMap
  let M' := LinearMap.toMatrix' L.symm.toLinearMap
  have h1 : M' * M = 1 := by
    simp only [M, M', ← LinearMap.toMatrix'_comp]
    rw [show (L.symm.toLinearMap ∘ₗ L.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => L.symm_apply_apply v, LinearMap.toMatrix'_id]
  have h2 : M * M' = 1 := by
    simp only [M, M', ← LinearMap.toMatrix'_comp]
    rw [show (L.toLinearMap ∘ₗ L.symm.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => L.apply_symm_apply v, LinearMap.toMatrix'_id]
  have hcomm : ∀ σ, M * ρ.mat σ = ρ'.mat σ * M := by
    intro σ
    have : L.toLinearMap ∘ₗ galRepRep ρ σ = galRepRep ρ' σ ∘ₗ L.toLinearMap :=
      LinearMap.ext fun v => hL σ v
    have h' := congrArg LinearMap.toMatrix' this
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, galRepRep_apply, galRepRep_apply,
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin'] at h'
    exact h'
  refine ⟨⟨M', M, h1, h2⟩, fun σ => Units.ext ?_⟩
  change ρ.mat σ = M' * ρ'.mat σ * M
  rw [mul_assoc, ← hcomm σ, ← mul_assoc, h1, one_mul]

end AttachedConjSec

end

end ZInQ.Contrib.HodgeSplit

#print axioms ZInQ.Contrib.HodgeSplit.attachedConj_proof

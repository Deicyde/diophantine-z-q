import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Topology of the integral trace module

Appendix F, tex 9655–9668. For the finite complete coefficient field above two,
its coefficient DVR is compact (with its valuation topology and finite residue field).
No relation between reduction of individual coordinates and the abstract quotient is used.
-/

namespace ZInQ.Manuscript.RC.TraceLimits

open scoped Valued

/-- The compactness hypothesis holds for a complete coefficient DVR with finite
residue field, equipped with its rank-one valuation topology (tex 9649–9665). -/
theorem coefficientDVR_compact (K Γ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ]
    [Valued K Γ] [(Valued.v : Valuation K Γ).RankOne]
    [CompleteSpace 𝒪[K]] [IsDiscreteValuationRing 𝒪[K]] [Finite 𝓀[K]] :
    CompactSpace 𝒪[K] :=
  Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2
    ⟨inferInstance, inferInstance, inferInstance⟩

variable {O V : Type*} [CommRing O] [AddCommGroup V] [Module O V]

/-- The reduction submodule, embedded in the characteristic-zero space. -/
abbrev residual (Λ : Submodule O V) (m : Ideal O) : Submodule O V :=
  (m • (⊤ : Submodule O Λ)).map Λ.subtype

/-- Reduction of a finite module over a finite residue ring has finitely many values. -/
theorem residual_quotient_finite (Λ : Submodule O V) (hΛ : Λ.FG)
    (m : Ideal O) [Finite (O ⧸ m)] :
    Finite (Λ ⧸ (m • (⊤ : Submodule O Λ))) := by
  have : Module.Finite O Λ := Module.Finite.of_fg hΛ
  exact Submodule.finite_quotient_smul m (Module.Finite.fg_top (R := O) (M := Λ))

/-- Finitely many integral coordinates detecting vectors of the lattice make the
lattice finite over the coefficient DVR (tex 9663–9665). -/
theorem lattice_fg_of_integral_coordinates [IsNoetherianRing O] {J : Type*} [Finite J]
    (Λ : Submodule O V) (coordinates : Λ →ₗ[O] (J → O))
    (hinj : Function.Injective coordinates) : Λ.FG := by
  let e : Λ ≃ₗ[O] LinearMap.range coordinates := LinearEquiv.ofInjective coordinates hinj
  have : IsNoetherian O Λ := isNoetherian_of_linearEquiv e.symm
  exact Module.Finite.iff_fg.mp (inferInstance : Module.Finite O Λ)

variable [TopologicalSpace O] [CompactSpace O]
variable [TopologicalSpace V] [T2Space V] [IsTopologicalAddGroup V] [ContinuousSMul O V]

/-- A finite module over the compact coefficient ring is closed (tex 9663–9665). -/
theorem lattice_closed (Λ : Submodule O V) (hΛ : Λ.FG) : IsClosed (Λ : Set V) :=
  (Λ.isCompact_of_fg hΛ).isClosed

/-- The reduction submodule is closed, by Noetherianity of the coefficient DVR. -/
theorem residual_closed [IsNoetherianRing O] (Λ : Submodule O V) (hΛ : Λ.FG) (m : Ideal O) :
    IsClosed (residual Λ m : Set V) := by
  rw [residual, Submodule.map_smul'', Submodule.map_subtype_top]
  have : IsNoetherian O Λ := isNoetherian_of_fg_of_noetherian Λ hΛ
  exact lattice_closed _ (Submodule.FG.of_le_of_isNoetherian Submodule.smul_le_right)

/-- The reduction kernel is open in the lattice, using its finite index and closedness. -/
theorem residual_isOpen [IsNoetherianRing O] (Λ : Submodule O V) (hΛ : Λ.FG)
    (m : Ideal O) [Finite (O ⧸ m)] :
    IsOpen ((m • (⊤ : Submodule O Λ) : Submodule O Λ) : Set Λ) := by
  let N : Submodule O Λ := m • ⊤
  have hN : IsClosed (N : Set Λ) := by
    have h := (residual_closed Λ hΛ m).preimage (continuous_subtype_val : Continuous (Λ.subtype : Λ → V))
    convert h using 1
    ext v
    change v ∈ N ↔ ∃ w ∈ N, (w : V) = (v : V)
    exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨w, hw, e⟩ => Subtype.ext e ▸ hw⟩
  have : Finite (Λ ⧸ N.toAddSubgroup) := residual_quotient_finite Λ hΛ m
  have : N.toAddSubgroup.FiniteIndex := N.toAddSubgroup.finiteIndex_of_finite_quotient
  exact N.toAddSubgroup.isOpen_of_isClosed_of_finiteIndex hN

#print axioms coefficientDVR_compact
#print axioms lattice_fg_of_integral_coordinates
#print axioms lattice_closed
#print axioms residual_closed
#print axioms residual_quotient_finite
#print axioms residual_isOpen

end ZInQ.Manuscript.RC.TraceLimits

import ZInQKernel.Contrib.Chebotarev.Exists
import ZInQKernel.Contrib.Chebotarev.FrobeniusDenseOfExists
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Frobenius tests in the Krull topology

Tex 9666–9668. Convert the tree's finite restriction formulation of
Frobenius density to topological density.
-/

namespace ZInQ.Manuscript.RC.TraceLimits

open ZInQ.Contrib.ChebFD.C10

/-- Genuine arithmetic Frobenius elements outside any fixed finite set are dense. -/
theorem dense_arithmeticFrobenius (avoid : Finset ℕ) :
    Dense {g : GQ | ∃ q, q.Prime ∧ q ∉ avoid ∧ IsFrobAt g q} := by
  intro g
  refine mem_closure_iff_nhds.mpr fun W hW => ?_
  have hW' : (fun k : GQ => g * k) ⁻¹' W ∈ nhds (1 : GQ) :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨E, hE, hEW⟩ :=
    (krullTopology_mem_nhds_one_iff ℚ Qbar _).mp hW'
  obtain ⟨h, q, hq, hqavoid, hf, hEq⟩ :=
    frobDense ZInQ.Contrib.chebotarevExists avoid E hE g
  have hfix : g⁻¹ * h ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [AlgEquiv.mul_apply, hEq x hx, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have hw := hEW hfix
  exact ⟨h, by simpa only [Set.mem_preimage, mul_inv_cancel_left] using hw,
    q, hq, hqavoid, hf⟩

/-- For a continuous function on a compact group, the set of simultaneous right
periods modulo an open additive subgroup is open (on-the-spot, provenance (c)). -/
theorem isOpen_rightPeriods {G A : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] [CompactSpace G] [AddGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] (f : G → A) (hf : Continuous f)
    (P : AddSubgroup A) (hP : IsOpen (P : Set A)) :
    IsOpen {n : G | ∀ g : G, f (g * n) - f g ∈ P} := by
  let D : G × G → A := fun x => f (x.1 * x.2) - f x.1
  have hD : Continuous D :=
    (hf.comp (continuous_fst.mul continuous_snd)).sub (hf.comp continuous_fst)
  have hc : IsClosed (Prod.snd '' (D ⁻¹' (P : Set A)ᶜ)) :=
    isClosedMap_snd_of_compactSpace _ (hP.isClosed_compl.preimage hD)
  convert hc.isOpen_compl using 1
  ext n
  simp [D]

#print axioms dense_arithmeticFrobenius
#print axioms isOpen_rightPeriods

end ZInQ.Manuscript.RC.TraceLimits

import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Models
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Passage from a finite reduction on an integral lattice to a compactly supported
locally constant function on the ambient trace-zero space (tex 8563–8566;
the topology bookkeeping is provenance (c)). -/

namespace ZInQ.Manuscript.RC.LocalWeights

open Matrix Function Set Topology
open scoped Topology

theorem locallyConstant_of_factors {X Y Z : Type*} [TopologicalSpace X]
    {g : X → Y} {f : X → Z} (hg : IsLocallyConstant g)
    (h : ∀ x y, g x = g y → f x = f y) : IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq f).mpr
  intro x
  exact (hg.eventually_eq x).mono fun y he => h _ _ he

theorem compactOpen_support {X O : Type*} [TopologicalSpace X] [CompactSpace X]
    [Zero O] {f : X → O} (hf : IsLocallyConstant f) :
    IsCompact (support f) ∧ IsOpen (support f) := by
  have he : support f = (f ⁻¹' {0})ᶜ := rfl
  rw [he]
  exact ⟨(hf.isOpen_fiber 0).isClosed_compl.isCompact, (hf.isClosed_fiber 0).isOpen_compl⟩

/-- Extend a weight on a compact open lattice by zero. -/
noncomputable def extendWeight {X A O : Type*} [Zero O] (i : A → X) (f : A → O) : X → O :=
  Function.extend i f (fun _ => 0)

theorem extendWeight_spec {X A O : Type*} [Zero O] (i : A → X) (f : A → O)
    (hi : Function.Injective i) :
    (∀ a, extendWeight i f (i a) = f a) ∧
      (∀ x ∉ Set.range i, extendWeight i f x = 0) := by
  exact ⟨fun a => hi.extend_apply _ _ _, fun x hx => Function.extend_apply' _ _ _ hx⟩

theorem extendWeight_compactOpen {X A O : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace A] [CompactSpace A] [Zero O] {i : A → X} {f : A → O}
    (hi : IsOpenEmbedding i) (hf : IsLocallyConstant f) :
    IsLocallyConstant (extendWeight i f) ∧ IsCompact (support (extendWeight i f)) ∧
    IsOpen (support (extendWeight i f)) := by
  classical
  have hs := extendWeight_spec i f hi.injective
  have heq (o : O) : extendWeight i f ⁻¹' {o} = i '' (f ⁻¹' {o}) ∪
      if o = 0 then (range i)ᶜ else ∅ := by
    classical
    ext x
    by_cases hx : x ∈ range i
    · obtain ⟨a, rfl⟩ := hx
      have hz : i a ∈ i '' (f ⁻¹' {o}) ↔ f a = o := by
        simp only [mem_image, mem_preimage, mem_singleton_iff]
        exact ⟨fun ⟨b, hb, hba⟩ => hi.injective hba ▸ hb, fun h => ⟨a, h, rfl⟩⟩
      have hri : i a ∈ range i := mem_range_self a
      simp only [mem_preimage, mem_singleton_iff, hs.1, mem_union, hz]
      by_cases ho : o = 0 <;> simp [ho, hri]
    · have hh : x ∉ i '' (f ⁻¹' {o}) := fun ⟨a, _, ha⟩ => hx ⟨a, ha⟩
      simp only [mem_preimage, mem_singleton_iff, hs.2 x hx, mem_union, hh, false_or]
      by_cases ho : o = 0
      · subst o
        simp [hx]
      · simp [ho, Ne.symm ho]
  have hl : IsLocallyConstant (extendWeight i f) := by
    classical
    refine IsLocallyConstant.iff_isOpen_fiber.mpr fun o => ?_
    rw [heq]
    refine (hi.isOpenMap _ (hf.isOpen_fiber o)).union ?_
    split
    · exact (isCompact_range hi.continuous).isClosed.isOpen_compl
    · exact isOpen_empty
  have him : support (extendWeight i f) = i '' support f := by
    ext x
    constructor
    · intro hx
      by_cases h : x ∈ range i
      · obtain ⟨a, rfl⟩ := h
        exact ⟨a, by simpa [mem_support, hs.1] using hx, rfl⟩
      · exact False.elim (hx (hs.2 x h))
    · rintro ⟨a, ha, rfl⟩
      simpa [mem_support, hs.1] using ha
  exact ⟨hl, him ▸ (compactOpen_support hf).1.image hi.continuous,
    (hl.isClosed_fiber 0).isOpen_compl⟩

instance mat_compactSpace {A : Type*} [TopologicalSpace A] [CompactSpace A] :
    CompactSpace (Mat A) :=
  inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → A))

variable (p : ℕ) [Fact p.Prime]

/-- The integral trace-zero matrices are a compact open lattice in the rational
trace-zero space. This is the support at the good primes. -/
theorem goodWeight_compactOpen {O : Type*} [Zero O] [One O] [Nontrivial O]
    (h : (1 : O) ≠ 0) :
    IsLocallyConstant (goodWeight p : TraceZero ℚ_[p] → O) ∧
      IsCompact (support (goodWeight p : TraceZero ℚ_[p] → O)) ∧
      IsOpen (support (goodWeight p : TraceZero ℚ_[p] → O)) := by
  let i : Mat ℤ_[p] → Mat ℚ_[p] := fun x => x.map (PadicInt.Coe.ringHom (p := p))
  have hi : IsOpenEmbedding i := (PadicInt.isOpenEmbedding_coe (p := p)).matrix_map
  have hr : {x : TraceZero ℚ_[p] | ∀ j k, x.val j k ∈ PadicInt.subring p} =
      Subtype.val ⁻¹' Set.range i := by
    ext x
    constructor
    · intro hx
      exact ⟨fun j k => ⟨x.val j k, hx j k⟩, rfl⟩
    · rintro ⟨a, e⟩ j k
      rw [← e]
      exact (a j k).property
  have hc : IsClopen {x : TraceZero ℚ_[p] | ∀ j k, x.val j k ∈ PadicInt.subring p} := by
    rw [hr]
    exact ⟨(isCompact_range hi.continuous).isClosed.preimage continuous_subtype_val,
      hi.isOpen_range.preimage continuous_subtype_val⟩
  classical
  let S : Set (TraceZero ℚ_[p]) := {x | ∀ j k, x.val j k ∈ PadicInt.subring p}
  have hf (x : TraceZero ℚ_[p]) : goodWeight p x = if x ∈ S then (1 : O) else 0 := rfl
  have hs : support (goodWeight p : TraceZero ℚ_[p] → O) = S := by
    ext x
    rw [mem_support, hf]
    by_cases hmem : x ∈ S
    · rw [ite_eq_left hmem]
      exact iff_of_true h hmem
    · rw [ite_eq_right hmem]
      exact iff_of_false (not_not_intro rfl) hmem
  refine ⟨?_, ?_, hs ▸ hc.2⟩
  · let f := LocallyConstant.const (TraceZero ℚ_[p]) (1 : O)
    have he : (goodWeight p : TraceZero ℚ_[p] → O) = ⇑(f.indicator hc) := by
      funext x
      rw [LocallyConstant.indicator_apply_eq_if, hf, show f x = (1 : O) from rfl]
      by_cases hx : x ∈ S
      · rw [ite_eq_left hx, ite_eq_left hx]
      · rw [ite_eq_right hx, ite_eq_right hx]
    rw [he]
    exact (f.indicator hc).isLocallyConstant
  · rw [hs]
    change IsCompact {x : TraceZero ℚ_[p] | ∀ j k, x.val j k ∈ PadicInt.subring p}
    rw [hr]
    have ht : Continuous (fun x : Mat ℚ_[p] => x.trace) := by
      simp only [Matrix.trace_fin_two]
      exact (continuous_apply_apply 0 0).add (continuous_apply_apply 1 1)
    exact (isClosed_singleton.preimage ht).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_range hi.continuous)

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights
#print axioms locallyConstant_of_factors
#print axioms compactOpen_support
#print axioms extendWeight_spec
#print axioms extendWeight_compactOpen
#print axioms goodWeight_compactOpen

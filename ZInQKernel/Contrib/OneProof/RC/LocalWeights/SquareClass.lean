import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Product
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Compact

/-! Additional fixed norm squareclass tests, tex 8564–8566. The norm map
and its conjugation and scaling laws are explicit inputs to the adapter. -/

namespace ZInQ.Manuscript.RC.LocalWeights

variable {X G V A O : Type*} [Monoid G] [Monoid V] [Monoid A] [CommRing O]

/-- An indicator on norm squareclasses preserves both local transformation
rules. The allowed set is invariant under multiplication by squares of
integral units, including the inverse of each such square. -/
noncomputable def LocalRule.withSquareClass (W : LocalRule (O := O) X G V)
    (q : X → A) (unit : V → Aˣ) (Q : Set A)
    (hconj : ∀ u x, q (W.conj u x) = q x)
    (hscale : ∀ v x, q (W.scale v x) = (unit v).val ^ 2 * q x)
    (hQ : ∀ v a, (unit v).val ^ 2 * a ∈ Q ↔ a ∈ Q) :
    LocalRule (O := O) X G V := by
  classical
  refine { W with weight := fun x => if q x ∈ Q then W.weight x else 0
                  weight_conj := ?_
                  weight_scale := ?_ }
  · intro u x
    rw [hconj]
    by_cases hx : q x ∈ Q <;> simp only [hx, ite_true, ite_false, W.weight_conj, mul_zero]
  · intro v x
    rw [hscale, hQ]
    by_cases hx : q x ∈ Q <;> simp only [hx, ite_true, ite_false, W.weight_scale, mul_zero]

omit [Monoid A] in
/-- A locally constant characteristic test preserves compact open support. -/
theorem squareClass_compactOpen [TopologicalSpace X]
    (f : X → O) (q : X → A) (Q : Set A) [DecidablePred (· ∈ Q)]
    (hf : IsLocallyConstant f) (hc : IsCompact (Function.support f))
    (hQ : IsLocallyConstant (fun x => decide (q x ∈ Q))) :
    IsLocallyConstant (fun x => if q x ∈ Q then f x else 0) ∧
    IsCompact (Function.support (fun x => if q x ∈ Q then f x else 0)) ∧
    IsOpen (Function.support (fun x => if q x ∈ Q then f x else 0)) := by
  let g : X → O := fun x => if q x ∈ Q then f x else 0
  have hg : IsLocallyConstant g := by
    apply (IsLocallyConstant.iff_eventually_eq g).mpr
    intro x
    exact ((hf.eventually_eq x).and (hQ.eventually_eq x)).mono (fun y ⟨hf', hQ'⟩ => by
      have hh : q y ∈ Q ↔ q x ∈ Q := by simpa using hQ'
      simp only [g, hf', hh])
  have hgset : Function.support g = (g ⁻¹' {0})ᶜ := rfl
  have hsub : Function.support g ⊆ Function.support f := by
    intro x hx
    change g x ≠ 0 at hx
    change f x ≠ 0
    by_cases h : q x ∈ Q
    · simpa only [g, ite_eq_left h] using hx
    · exact False.elim (hx (ite_eq_right h))
  refine ⟨hg, hc.of_isClosed_subset ?_ hsub, ?_⟩
  · rw [hgset]
    exact (hg.isOpen_fiber 0).isClosed_compl
  · rw [hgset]
    exact (hg.isClosed_fiber 0).isOpen_compl

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights
#print axioms LocalRule.withSquareClass
#print axioms squareClass_compactOpen

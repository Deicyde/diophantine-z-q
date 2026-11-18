import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Compact

/-! Transport of the rules through zero extension, used for tex 8496 and 8571–8577.
The transport lemma is provenance (c). -/

namespace ZInQ.Manuscript.RC.LocalWeights

theorem extendWeight_transform {X A O : Type*} [MulZeroClass O]
    (i : A → X) (hi : Function.Injective i) (f : A → O) (c : O)
    (g : X → X) (v : A → A) (g' : X → X) (v' : A → A)
    (hg : Function.LeftInverse g' g)
    (h : ∀ a, g (i a) = i (v a)) (h' : ∀ a, g' (i a) = i (v' a))
    (hf : ∀ a, f (v a) = c * f a) (x : X) :
    extendWeight i f (g x) = c * extendWeight i f x := by
  have hs := extendWeight_spec i f hi
  by_cases hx : x ∈ Set.range i
  · obtain ⟨a, rfl⟩ := hx
    rw [h, hs.1, hs.1, hf]
  · have hn : g x ∉ Set.range i := by
      rintro ⟨a, ha⟩
      have he := (h' a).symm.trans (congrArg g' ha)
      exact hx ⟨v' a, he.trans (hg x)⟩
    rw [hs.2 _ hn, hs.2 _ hx, mul_zero]

end ZInQ.Manuscript.RC.LocalWeights

#print axioms ZInQ.Manuscript.RC.LocalWeights.extendWeight_transform

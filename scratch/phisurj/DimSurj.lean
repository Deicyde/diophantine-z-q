import ZInQKernel.Contrib.OneProof.MumfordKLFinite
import ZInQKernel.Contrib.AbVarBC.Mul
import ZInQKernel.Contrib.AbVarBC.Dim

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj

namespace PhiSurj

/-- **Dimension count.** A locally quasi-finite closed morphism `f : X → Y` of schemes, with `Y`
irreducible and `dim Y ≤ dim X = a < ∞`, is surjective: otherwise images of irreducible closed subsets of
`X` (strictly increasing, since fibres are discrete) followed by `Y` give a chain of length `a + 1` in `Y`. -/
theorem surjective_of_dim_le {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f]
    (hc : IsClosedMap f.base) [IrreducibleSpace Y] [Nonempty X] (a : ℕ)
    (hX : topologicalKrullDim X = a) (hY : topologicalKrullDim Y ≤ a) :
    Function.Surjective f.base := by
  by_contra hns
  have hrange : Set.range f.base ≠ Set.univ := fun h => hns (Set.range_eq_univ.mp h)
  let F : IrreducibleCloseds X → IrreducibleCloseds Y := fun Z =>
    ⟨f.base '' Z, Z.isIrreducible.image _ f.base.hom.continuous.continuousOn, hc _ Z.isClosed⟩
  have hF : StrictMono F := by
    intro Z W hZW
    have hsub : (Z : Set X) ⊆ W := hZW.le
    refine lt_of_le_of_ne (Set.image_mono hsub) ?_
    intro heq
    have heq' : f.base '' (Z : Set X) = f.base '' W := congrArg (fun T : IrreducibleCloseds Y => (T : Set Y)) heq
    obtain ⟨z₀, hz₀⟩ := QuasiSober.sober Z.isIrreducible Z.isClosed
    obtain ⟨w₀, hw₀⟩ := QuasiSober.sober W.isIrreducible W.isClosed
    have hz₀W : z₀ ∈ (W : Set X) := hsub hz₀.mem
    have hw₀z₀ : w₀ ⤳ z₀ := hw₀.specializes hz₀W
    have hne : w₀ ≠ z₀ := by
      intro h
      subst h
      apply (ne_of_lt hZW)
      apply SetLike.coe_injective
      exact (isGenericPoint_def.mp hz₀).symm.trans (isGenericPoint_def.mp hw₀)
    have h1 := ZInQ.Contrib.AbVarBC.MulRigidity.ne_of_specializes_of_lqf f hw₀z₀ hne
    obtain ⟨z, hz, hfz⟩ : f.base w₀ ∈ f.base '' (Z : Set X) := by rw [heq']; exact ⟨w₀, hw₀.mem, rfl⟩
    have h2 : z₀ ⤳ z := hz₀.specializes hz
    have h3 : f.base z₀ ⤳ f.base w₀ := hfz ▸ h2.map f.base.hom.continuous
    have h4 : f.base w₀ ⤳ f.base z₀ := hw₀z₀.map f.base.hom.continuous
    exact h1 (h4.antisymm h3).eq
  let top : IrreducibleCloseds Y := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  let G : WithTop (IrreducibleCloseds X) → IrreducibleCloseds Y := fun t => t.elim top F
  have hG : StrictMono G := by
    intro s t hst
    cases t with
    | top =>
      cases s with
      | top => exact absurd hst (lt_irrefl _)
      | coe Z =>
        change F Z < top
        refine lt_of_le_of_ne (fun _ _ => trivial) ?_
        intro h
        apply hrange
        apply Set.eq_univ_of_univ_subset
        intro y _
        have : y ∈ (F Z : Set Y) := by rw [h]; trivial
        obtain ⟨x, -, rfl⟩ := this
        exact ⟨x, rfl⟩
    | coe W =>
      cases s with
      | top => exact absurd hst (not_lt_of_ge le_top)
      | coe Z => exact hF (WithTop.coe_lt_coe.mp hst)
  have hle := Order.krullDim_le_of_strictMono G hG
  have : Nonempty (IrreducibleCloseds X) := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  rw [Order.krullDim_WithTop] at hle
  change topologicalKrullDim X + 1 ≤ topologicalKrullDim Y at hle
  rw [hX] at hle
  have := hle.trans hY
  have h' : ((a + 1 : ℕ) : WithBot ℕ∞) ≤ (a : WithBot ℕ∞) := by exact_mod_cast this
  have h'' : a + 1 ≤ a := by exact_mod_cast h'
  omega

end PhiSurj

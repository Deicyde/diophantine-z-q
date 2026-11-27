import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Read preconnected fibers on the original base from its geometrically connected restriction

This is the receiving implication for Stacks, Lemma 37.28.4 (Tag 055G): it keeps the
given morphism and the very open subscheme supplied by the geometric connectedness theorem.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.IsogenyDegree

universe u

/-- A geometrically connected restriction gives preconnected point fibers of the
original morphism at every point of that open. -/
theorem preconnected_fiber_on_open {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    [GeometricallyConnected (f ∣_ U)] (s : S) (hs : s ∈ U) :
    _root_.IsPreconnected (f ⁻¹' {s}) := by
  have hs' : s ∈ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  obtain ⟨t, rfl⟩ := hs'
  let i := (f ⁻¹ᵁ U).ι
  let q := f ∣_ U
  have hP : IsPullback i q f U.ι := (isPullback_morphismRestrict f U).flip
  have heq : i '' (q ⁻¹' {t}) = f ⁻¹' {U.ι t} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change q y = t at hy
      change (i ≫ f) y = U.ι t
      rw [hP.w, Scheme.Hom.comp_apply, hy]
    · intro hx
      change f x = U.ι t at hx
      obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x t hx
      refine ⟨hP.isoPullback.inv z, ?_, ?_⟩
      · change (hP.isoPullback.inv ≫ q) z = t
        rw [hP.isoPullback_inv_snd, hz₂]
      · change (hP.isoPullback.inv ≫ i) z = x
        rw [hP.isoPullback_inv_fst, hz₁]
  rw [← heq]
  exact (q.isConnected_preimage_singleton t).isPreconnected.image _ i.continuous.continuousOn

#print axioms preconnected_fiber_on_open

end ZInQ.Contrib.IsogenyDegree

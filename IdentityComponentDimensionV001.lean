import NeronRelativeDimensionV001

/-!
# Generic dimension equals the dimension of every open piece of a fibre

For a smooth group scheme `N` over a valuation ring `O ⊆ K` with generic fibre `A`, any map
`φ : O → k` to a field and any nonempty open subscheme `U` of `N ×_O k` (for instance the
identity component of the geometric special fibre), `dim A = dim U`: both equal the single
relative dimension of `N`. Consequently `dim A = a + t` follows from the dimension of the
semi-abelian extension `dim U = a + t` alone, or (previous file) from smoothness of relative
dimension `t` of its quotient map.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace NeronRelativeDimension

variable {K : Type} [Field K] {O : ValuationSubring K} {A : PkgI3.AbVar K}

/-- **`dim A = dim U`** for any nonempty open subscheme `U` of any fibre of the smooth group model,
together with the common relative dimension. -/
theorem dim_generic_eq_dim_open (hV1 : SmoothGroupRelDimLocal) (hV3 : SmoothRelDimKrullDim)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom]
    (e : (Over.pullback (jO O)).obj N ≅ A.X)
    {k : Type} [Field k] (φ : O →+* k)
    (U : Over (Spec (CommRingCat.of k))) [Nonempty U.left]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj N)
    [IsOpenImmersion inc.left] :
    topologicalKrullDim A.X.left = topologicalKrullDim U.left ∧
      ∃ d : ℕ, SmoothOfRelativeDimension d N.hom ∧
        topologicalKrullDim A.X.left = (d : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := hV1 O N
  have hA : SmoothOfRelativeDimension d A.X.hom := generic_relDim N d e
  have hG := fibre_relDim N d φ
  have hU : SmoothOfRelativeDimension d U.hom := open_relDim inc d
  have neA : Nonempty A.X.left := nonempty_of_grp A.X
  have dA := hV3 K A.X.left A.X.hom d
  have dU := hV3 k U.left U.hom d
  exact ⟨dA.trans dU.symm, d, hd, dA⟩

/-- **`dim A = a + t` from the dimension of the semi-abelian extension**: if the open subgroup
`U` of the fibre has `dim U = a + t`, then `dim A = a + t`. -/
theorem dim_eq_add_of_extension_dim (hV1 : SmoothGroupRelDimLocal) (hV3 : SmoothRelDimKrullDim)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom]
    (e : (Over.pullback (jO O)).obj N ≅ A.X)
    {k : Type} [Field k] (φ : O →+* k)
    (U : Over (Spec (CommRingCat.of k))) [GrpObj U]
    (inc : U ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj N)
    [IsOpenImmersion inc.left] (a t : ℕ)
    (hext : topologicalKrullDim U.left = ((a + t : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim A.X.left = ((a + t : ℕ) : WithBot ℕ∞) := by
  have : Nonempty U.left := nonempty_of_grp U
  exact (dim_generic_eq_dim_open hV1 hV3 N e φ U inc).1.trans hext

end NeronRelativeDimension

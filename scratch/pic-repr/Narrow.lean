import ZInQKernel.OneProof.H.TailZ24
import ZInQKernel.OneProof.H.LF2SmoothDim
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Representability

/-! pic-repr §2: the narrowed form proved — abelian varieties of dimension 1 (elliptic curves)
over a separably closed field, from the vendored Jacobian-Challenge theorem
`AlgebraicGeometry.exists_representableBy_picardFunctor` (curve Hilbert scheme chart + group criterion). -/

open CategoryTheory AlgebraicGeometry LF2.InfraSmoothDim

namespace PicRepr

/-- A smooth irreducible `K`-scheme of dimension `n` is smooth of relative dimension `n`
(every standard smooth chart has relative dimension `n`: it contains a closed point, whose local
ring has the chart's relative dimension, and that is `dim X`). -/
theorem smoothOfRelativeDimension_of_dim {K : Type*} [Field K] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [IrreducibleSpace X] (n : ℕ)
    (hn : topologicalKrullDim X = n) : SmoothOfRelativeDimension n f := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth f x
  let _ := (f.appLE U V e).hom.toAlgebra
  have h' : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of K), U) Γ(X, V) := h
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h'.out
  obtain ⟨y, hyV, hy⟩ := nonempty_inter_closedPoints (Z := (V : Set X)) ⟨x, hxV⟩
    V.2.isLocallyClosed
  have h1 := (stalk_dim_of_chart f hU hV e P.dimension
    (P.isStandardSmoothOfRelativeDimension rfl) y hyV hy).1
  have h2 := (topologicalKrullDim_eq_of_smooth f y hy).1
  rw [hn, h1] at h2
  have hPn : P.dimension = n := by exact_mod_cast h2.symm
  exact ⟨U, hU, V, hV, hxV, e, P.isStandardSmoothOfRelativeDimension hPn⟩

/-- `PicRepresentableAbVar` for abelian varieties smooth of relative dimension 1 over a separably
closed field. -/
theorem picRepresentable_relDimOne_sepClosed (K : Type) [Field K] [IsSepClosed K]
    (A : PkgI3.AbVar K) [SmoothOfRelativeDimension 1 A.X.hom] :
    ∃ P : Over (Spec (CommRingCat.of K)), Nonempty ((picardFunctor A.X.hom).obj.RepresentableBy P) :=
  exists_representableBy_picardFunctor A.X.hom

/-- **Narrowed form, proved.** `PicRepresentableAbVar` for every abelian variety of dimension 1
over a separably closed field. -/
theorem picRepresentable_dimOne_sepClosed (K : Type) [Field K] [IsSepClosed K]
    (A : PkgI3.AbVar K) (hA : A.dim = 1) :
    ∃ P : Over (Spec (CommRingCat.of K)), Nonempty ((picardFunctor A.X.hom).obj.RepresentableBy P) := by
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  have : SmoothOfRelativeDimension 1 A.X.hom :=
    smoothOfRelativeDimension_of_dim A.X.hom 1 (by exact_mod_cast hA)
  exact picRepresentable_relDimOne_sepClosed K A

end PicRepr

#print axioms PicRepr.picRepresentable_dimOne_sepClosed

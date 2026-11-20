import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Density
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.PointReading

/-! Generic fibre of (O.7), tex 8487–8489 and 9101–9113.
The density passage and interface are on the spot (c). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Classical MatrixGroups TauCeti.ExactDivisor
open AlgebraicGeometry CategoryTheory UpperHalfPlane WeierstrassCurve ModularCurve
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.AtkinPin

namespace ZInQ.Manuscript.RC.AtkinRational

/-- A comparison on the fixed projective Weierstrass model: the difference
of the two morphisms' field readings is itself read by a morphism. This
property mentions neither the Atkin–Lehner action nor the parametrization. -/
def RepresentsDifference (N : ℕ) [NeZero N] (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∀ (u v : (X0Branch.model N).X ⟶ Proj E.toProjective.grading)
    (_ : u ≫ projectiveOverQ E = (X0Branch.model N).overQ)
    (_ : v ≫ projectiveOverQ E = (X0Branch.model N).overQ) (e : ℤ),
    ∃ D : (X0Branch.model N).X ⟶ Proj E.toProjective.grading,
      D ≫ projectiveOverQ E = (X0Branch.model N).overQ ∧
      ∀ (F : Type) [Field F] [Algebra ℚ F] (x : FieldPoint (X0Branch.model N).overQ F),
        projectiveValue (x.val ≫ D) =
          projectiveValue (x.val ≫ u) - e • projectiveValue (x.val ≫ v)

set_option maxHeartbeats 600000 in
/-- On the interior, the signed difference is constant by the complex chart
identity and faithful reading on the projective elliptic curve. The interior
contains a dominant point, so reducedness of the source and separatedness of
the target give equality of morphisms with the descended rational constant
map. Evaluate there at the rational cusp and then extend fields. -/
theorem based_of_representedDifference {N Q : ℕ} [NeZero N] {hQ : Q ∥ N}
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (W : RationalAtkin (X0Branch.model N) hQ)
    (π : (X0Branch.model N).X ⟶ Proj E.toProjective.grading)
    (hπ : π ≫ projectiveOverQ E = (X0Branch.model N).overQ)
    (b : FieldPoint (X0Branch.model N).overQ ℚ) (hb : projectiveValue (b.comp π hπ).val = 0)
    (e : ℤ)
    (hchart : ∀ base τ : ℍ,
      let P := fun t : ℍ => projectiveValue (((X0Branch.model N).complexPoint t).comp π hπ).val
      P (atkinGL hQ • τ) = e • P τ + (P (atkinGL hQ • base) - e • P base))
    (D : (X0Branch.model N).X ⟶ Proj E.toProjective.grading)
    (hD : D ≫ projectiveOverQ E = (X0Branch.model N).overQ)
    (hread : ∀ (F : Type) [Field F] [Algebra ℚ F]
      (x : FieldPoint (X0Branch.model N).overQ F),
      projectiveValue (x.val ≫ D) =
        projectiveValue (((x.comp W.hom W.overQ).comp π hπ).val) -
          e • projectiveValue (x.comp π hπ).val) :
    BasedAtkinOnPoints (X0Branch.model N) W π hπ b e := by
  let X := X0Branch.model N
  let P := fun t : ℍ => projectiveValue ((X.complexPoint t).comp π hπ).val
  have ht (τ : ℍ) : projectiveValue ((X.complexPoint τ).val ≫ D) =
      P (atkinGL hQ • τ) - e • P τ := by
    rw [hread ℂ (X.complexPoint τ), W.chart]
  have hc (τ : ℍ) : X0Model.complexPoint N τ ≫ D =
      X0Model.complexPoint N default ≫ D := by
    apply projectiveValue_injective_of_origin E (b.comp π hπ).val hb
    change projectiveValue ((X.complexPoint τ).val ≫ D) =
      projectiveValue ((X.complexPoint default).val ≫ D)
    rw [ht, ht default]
    have h := hchart default τ
    change P (atkinGL hQ • τ) = _ at h
    rw [h]
    change e • P τ + (P (atkinGL hQ • default) - e • P default) - e • P τ = _
    abel
  have hd := eq_constant_of_chart (projectiveOverQ E) D hD b.val _ hc
  intro F _ _ x
  let a := b.map (Algebra.ofId ℚ F)
  have ha : x.val ≫ D = a.val ≫ D := by
    conv_lhs => rw [hd]
    change x.val ≫ X.overQ ≫ b.val ≫ D =
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ F)) ≫ b.val) ≫ D
    rw [← Category.assoc, x.property, Category.assoc]
  have hh := (hread F x).symm.trans ((congrArg (projectiveValue (E := E)) ha).trans (hread F a))
  dsimp only
  rw [zsmul_sub]
  have hh' := congrArg (fun z => z + (e • projectiveValue (x.comp π hπ).val -
    projectiveValue (((a.comp W.hom W.overQ).comp π hπ).val))) hh
  convert hh' using 1 <;> abel


end ZInQ.Manuscript.RC.AtkinRational

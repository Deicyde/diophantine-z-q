import ZInQKernel.Contrib.CloudR2Poincare.L6.CubeTheorem

/-!
# Native square from the actual cube class

The universal cube is established on the actual triple product before being
pulled back to any test scheme. In particular, this argument never imposes
reducedness or Noetherian hypotheses on the original square's parameter.
-/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L6

/-- The class-valued cube relation on arbitrary test schemes, obtained only
by pullback of the proved actual cube-class equality on J cubed. -/
theorem nativeCubeRelation
    (k : Type u) [Field k] [CharZero k] (J : PkgI3.AbVar k)
    (P : Over (Spec (.of k))) (f g h : P ⟶ J.X) (L : J.X.left.Pic) :
    Scheme.Pic.map (f * g * h).left L * Scheme.Pic.map f.left L *
        Scheme.Pic.map g.left L * Scheme.Pic.map h.left L =
      Scheme.Pic.map (f * g).left L * Scheme.Pic.map (f * h).left L *
        Scheme.Pic.map (g * h).left L :=
  nativeCubeRelation_of_class_eq_one J.X L (nativeCubeClass_eq_one J L) P f g h

/-- Exact unchanged native theorem of the square. No cube, square,
Picard-invariance, numerical-rank or supplied-model premise remains. -/
theorem NativeTheoremOfTheSquare_proof : L2.NativeTheoremOfTheSquare.{u} :=
  nativeSquare_of_cubeRelation nativeCubeRelation

end ZInQ.Contrib.CloudR2Poincare.L6

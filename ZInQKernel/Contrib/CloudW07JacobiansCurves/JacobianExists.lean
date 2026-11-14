import ZInQKernel.HDecomp.ModCurves.Defs
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Albanese
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.FieldDescent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.Rigidity
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.AbelianVariety.Albanese.UniversalProperty

/-!
# cloud-w07: frontier row H-36, `LeafModCurves.JacobianExists ℚ`, proved

The fixed statement (`ZInQKernel/HDecomp/ModCurves/Defs.lean`, fork `main` at `cba8157f`) asks,
for every smooth proper geometrically connected curve `X` over `K` (`LeafModCurves.IsCurve`) with
a `K`-point `P₀`, for an abelian variety `J : PkgI3.AbVar K` and a morphism `aj : X ⟶ J.X` with
the Albanese property `LeafModCurves.IsJacobian X P₀ J aj`: `P₀ ≫ aj = η`, and every pointed
`K`-morphism `f : X ⟶ A.X` to an abelian variety factors as `aj ≫ φ` through a unique group-scheme
homomorphism `φ : J.X ⟶ A.X`.

It is proved for every field `K` (`jacobianExists_of_field`), by the vendored library of
`frenzymath/Jacobian-Challenge` (commit `c4254cce`, Apache-2.0, by Axel Delaval, Jie Xu and
Shitan Xu; see `LICENSE`, `NOTICE` and `README.md` in this directory):

* `AlgebraicGeometry.exists_abelianVariety_picardDegreeZero`: the degree-zero Picard sheaf of a
  smooth proper geometrically integral curve over any field is represented by an abelian variety
  (a smooth proper geometrically irreducible commutative group scheme) with the tensor group law;
* `AlgebraicGeometry.Curve.isAlbanese_abelJacobiMap`: the Abel–Jacobi map into it has the
  Albanese universal property (Milne, *Jacobian varieties*, Prop. 6.1), any genus and any field;
* `AlgebraicGeometry.IsAlbanese.existsUnique_schemeMap`: the factorization is unique even among
  all `K`-morphisms;
* `AlgebraicGeometry.isMonHom_of_isProper_of_geometricallyIntegral`: a pointed morphism out of a
  proper geometrically integral group scheme is a homomorphism (rigidity).

The only translation needed: the source's curves are geometrically *irreducible*, the
statement's are geometrically *connected*; a smooth geometrically connected morphism is
geometrically integral (`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`, vendored Tau
Ceti, already in the kernel). The abelian varieties of both sides are the same group schemes:
`PkgI3.AbVar` asks for `GrpObj`, proper, smooth, geometrically integral; the source's
`AbelianVariety` for a commutative group object, smooth, proper, geometrically irreducible, and
smooth + geometrically irreducible is geometrically integral
(`AlgebraicGeometry.Smooth.geometricallyIntegral`, vendored), while commutativity is Mathlib's
`isCommMonObj_of_isProper_of_geometricallyIntegral`.
No `sorry`, no `axiom`, no extra hypothesis; the statement is the fixed `def`, unchanged.
-/

noncomputable section

namespace ZInQ.Contrib.CloudW07JacobiansCurves

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

/-- **Jacobians exist over every field** (Weil 1948; Milne, *Jacobian varieties*, Thm 1.1 with
Prop. 6.1): `LeafModCurves.JacobianExists K` for every field `K`. -/
theorem jacobianExists_of_field (K : Type) [Field K] : LeafModCurves.JacobianExists K := by
  intro X hX P₀
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  have : GeometricallyIrreducible X.hom := inferInstance
  let : X.left.Over (Spec (.of K)) := ⟨X.hom⟩
  have : SmoothOfRelativeDimension 1 (X.left ↘ Spec (.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  have : IsProper (X.left ↘ Spec (.of K)) := inferInstanceAs (IsProper X.hom)
  have : GeometricallyIntegral (X.left ↘ Spec (.of K)) :=
    inferInstanceAs (GeometricallyIntegral X.hom)
  obtain ⟨variety, representation, tensorCompatible, -⟩ :=
    exists_abelianVariety_picardDegreeZero (baseField := K) X.left
  let aj : X ⟶ variety.group.X :=
    Curve.abelJacobiMap ⟨X⟩ P₀.left (by simp) representation
  have alb : IsAlbanese P₀ variety aj :=
    Curve.isAlbanese_abelJacobiMap ⟨X⟩ P₀ variety representation tensorCompatible
  have : GeometricallyIntegral variety.group.X.hom :=
    Smooth.geometricallyIntegral variety.group.X.hom
  let J : PkgI3.AbVar K :=
    { X := variety.group.X
      grp := variety.group.grp
      proper := variety.proper
      smooth := variety.smooth
      geomInt := inferInstance }
  refine ⟨J, aj, ⟨alb.1, ?_⟩⟩
  intro A f hf
  obtain ⟨g, hg, huniq⟩ := alb.existsUnique_schemeMap f hf
  have pointed : η[variety.group.X] ≫ g = η[A.X] := by
    rw [← alb.1, Category.assoc, ← hg, hf]
  have : IsMonHom g := isMonHom_of_isProper_of_geometricallyIntegral g pointed
  exact ⟨g, ⟨inferInstance, hg.symm⟩, fun φ hφ => huniq φ hφ.2.symm⟩

/-- **Frontier row H-36 (`t33`), proved:** `LeafModCurves.JacobianExists ℚ`. -/
theorem JacobianExists_proof : LeafModCurves.JacobianExists ℚ :=
  jacobianExists_of_field ℚ

end ZInQ.Contrib.CloudW07JacobiansCurves

import ZInQKernel.HDecomp.ModCurves.Defs
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.CuspOrbits

/-! Evaluation of the Albanese factor on field-valued cusp classes.
Tex 1785–1787 and 2937–2942; on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj PkgI3
open scoped MatrixGroups

namespace ZInQ.Manuscript.RC.J0Cusps

variable {K : Type} [Field K]

/-- The unique group-scheme morphism whose composite with Abel–Jacobi is
the given based morphism. -/
def factor {X : Over (Spec (.of K))} {b : 𝟙_ (Over (Spec (.of K))) ⟶ X} {J A : AbVar K}
    {aj : X ⟶ J.X} (hJ : LeafModCurves.IsJacobian X b J aj)
    (π : X ⟶ A.X) (hπ : b ≫ π = η[A.X]) : J.X ⟶ A.X :=
  (hJ.univ A π hπ).exists.choose

theorem factor_isMonHom {X : Over (Spec (.of K))} {b : 𝟙_ (Over (Spec (.of K))) ⟶ X} {J A : AbVar K}
    {aj : X ⟶ J.X} (hJ : LeafModCurves.IsJacobian X b J aj)
    (π : X ⟶ A.X) (hπ : b ≫ π = η[A.X]) : IsMonHom (factor hJ π hπ) :=
  (hJ.univ A π hπ).exists.choose_spec.1

theorem abelJacobi_comp_factor {X : Over (Spec (.of K))} {b : 𝟙_ (Over (Spec (.of K))) ⟶ X} {J A : AbVar K}
    {aj : X ⟶ J.X} (hJ : LeafModCurves.IsJacobian X b J aj)
    (π : X ⟶ A.X) (hπ : b ≫ π = η[A.X]) : aj ≫ factor hJ π hπ = π :=
  (hJ.univ A π hπ).exists.choose_spec.2

/-- An independently given group-scheme map also gives a based morphism from
the curve, by composition with Abel–Jacobi. -/
theorem abelJacobi_comp_isBased {X : Over (Spec (.of K))}
    {b : 𝟙_ (Over (Spec (.of K))) ⟶ X} {J A : AbVar K} {aj : X ⟶ J.X}
    (hJ : LeafModCurves.IsJacobian X b J aj) (g : J.X ⟶ A.X) [IsMonHom g] :
    b ≫ (aj ≫ g) = η[A.X] := by
  rw [← Category.assoc, hJ.base, IsMonHom.one_hom]

variable {L : Type} [Field L] [Algebra K L]

/-- Evaluate the based Abel–Jacobi map on a field-valued point of the curve.
For the represented Abel–Jacobi map this is the class of the point minus the base point. -/
def pointClass {X : Over (Spec (.of K))} {J : AbVar K}
    (aj : X ⟶ J.X) (p : AbVar.ptObj (K := K) L ⟶ X) : Additive (J.Pt L) :=
  Additive.ofMul (p ≫ aj)

/-- The homomorphism on points followed by the chosen additive uniformization. -/
def torusHom {J A : AbVar K} {T : Type*} [AddCommGroup T]
    (g : J.X ⟶ A.X) [IsMonHom g] (u : Additive (A.Pt L) →+ T) : Additive (J.Pt L) →+ T :=
  u.comp ((IsMonHom.monoidHom g (AbVar.ptObj (K := K) L)).toAdditive)

/-- Evaluation of the composite in tex 1786 at a field-valued point. -/
theorem torusHom_pointClass {X : Over (Spec (.of K))} {J A : AbVar K}
    {T : Type*} [AddCommGroup T] {aj : X ⟶ J.X}
    {π : X ⟶ A.X} (g : J.X ⟶ A.X) [IsMonHom g] (hg : aj ≫ g = π)
    (u : Additive (A.Pt L) →+ T) (p : AbVar.ptObj (K := K) L ⟶ X) :
    torusHom g u (pointClass aj p) = u (Additive.ofMul (p ≫ π)) := by
  change u (Additive.ofMul ((p ≫ aj) ≫ g)) = _
  rw [Category.assoc, hg]

/-- Compose the map on cusp orbits with Abel–Jacobi. The result can be
used over an algebraic closure even for cusps whose residue field is not rational. -/
def classOfCusp (N : ℕ) {X : Over (Spec (.of K))} {J : AbVar K}
    (aj : X ⟶ J.X)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) →
      (AbVar.ptObj (K := K) L ⟶ X)) :
    CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) → Additive (J.Pt L) :=
  fun r => pointClass aj (c r)

/-- A representative in the Elkik API first maps to its cusp orbit. -/
def cuspClass (N : ℕ) [NeZero N] {X : Over (Spec (.of K))} {J : AbVar K}
    (aj : X ⟶ J.X)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) →
      (AbVar.ptObj (K := K) L ⟶ X)) (r : OnePoint ℚ) : Additive (J.Pt L) :=
  classOfCusp N aj c (ElkikPrint.cuspOrbit N r)

/-- On the support of the quadratic sum, evaluating the Abel–Jacobi factor
needs only the image of the cusp represented by zero. -/
theorem torusHom_cuspClass_of_jacobi_ne_zero (N a m : ℕ) [NeZero N] [NeZero m]
    (hmN : m.Coprime N) (hχ : jacobiSym (a : ℤ) m ≠ 0)
    {X : Over (Spec (.of K))} {J A : AbVar K}
    {T : Type*} [AddCommGroup T] {aj : X ⟶ J.X}
    {π : X ⟶ A.X} (g : J.X ⟶ A.X) [IsMonHom g] (hg : aj ≫ g = π)
    (u : Additive (A.Pt L) →+ T)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) →
      (AbVar.ptObj (K := K) L ⟶ X)) :
    torusHom g u (cuspClass N aj c (((a : ℚ) / m : ℚ) : OnePoint ℚ)) =
      u (Additive.ofMul (c (ElkikPrint.cuspOrbit N ((0 : ℚ) : OnePoint ℚ)) ≫ π)) := by
  unfold cuspClass
  rw [cuspOrbit_eq_zero_of_jacobi_ne_zero N a m hmN hχ]
  exact torusHom_pointClass g hg u _


end ZInQ.Manuscript.RC.J0Cusps

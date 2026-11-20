import ZInQKernel.Contrib.OneProof.RC.GoodReduction.Integral
import ZInQKernel.Contrib.OneProof.RC.AtkinSign.Geometry

/-! Specialization of the affine transformation and cancellation on
degree-zero classes (tex 8487–8489, on-the-spot glue (c)). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.Obj CategoryTheory.MonObj
open FreeAbelianGroup (of)

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.GoodReduction

open PMGeometry (DivZero center)

variable {X : PMAdelic.CoarseFibre} {J P : Type} [AddCommGroup J] [AddCommGroup P]

/-- The affine constant cancels exactly on the divisor in
`SpecialFibreAtSigns.atkin_quotient`. Use the same based evaluation at
the two moved points, including the moved cusp. -/
theorem atkinQuotient_of_affine (infinity : X.Point)
    (d : DivZero X.Point →+ J) (q : J →+ P) (p : ℕ) (ε : ℤ)
    (v : X.Point → P) (t : P) (hzero : v infinity = 0)
    (hval : ∀ x, q (d (center infinity (of x))) = v x)
    {x : X.Point}
    (hx : v (X.W p x) = ε • v x + t)
    (hinf : v (X.W p infinity) = ε • v infinity + t) :
    q (d (center infinity (of (X.W p x) - of (X.W p infinity)))) =
      ε • q (d (center infinity (of x))) := by
  simp only [map_sub, hval, hx, hinf, hzero, smul_zero, zero_add, add_sub_cancel_right]

set_option synthInstance.maxHeartbeats 250000 in
/-- For a level operator identified with an integral endomorphism,
carry the generic signed transformation to the residue point group.
The constant section can be the image of the moved integral cusp.
The point readings identify the based PM value and the group law on
the reduced elliptic points. -/
theorem atkinQuotient_of_integralRelation
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {M E : Over (Spec (.of R))} [Smooth M.hom] [GrpObj E]
    (hN : CToPrinted.IsNeronModelOver R K E)
    (f : M ⟶ E) (W : M ⟶ M) (u : 𝟙_ (Over (Spec (.of R))) ⟶ E) (ε : ℤ)
    (hgen : (generic R K).map W ≫ (generic R K).map f =
      ((generic R K).map f) ^ ε * (generic R K).map (toUnit M ≫ u))
    {T : Scheme.{0}} (k : T ⟶ Spec (.of R)) {U : Over T}
    (point : X.Point → (U ⟶ (Over.pullback k).obj M))
    (read : (U ⟶ (Over.pullback k).obj E) →* Multiplicative P)
    (infinity : X.Point) (d : DivZero X.Point →+ J) (q : J →+ P) (p : ℕ)
    (hW : ∀ x, point (X.W p x) = point x ≫ (Over.pullback k).map W)
    (hval : ∀ x, q (d (center infinity (of x))) =
      (read (point x ≫ (Over.pullback k).map f)).toAdd)
    (x : X.Point) :
    q (d (center infinity (of (X.W p x) - of (X.W p infinity)))) =
      ε • q (d (center infinity (of x))) := by
  let F := Over.pullback k
  let _ : GrpObj (F.obj E) := Functor.grpObjObj (F := F)
  let v := fun x => (read (point x ≫ F.map f)).toAdd
  let t := (read (point infinity ≫ F.map (toUnit M ≫ u))).toAdd
  have hcst (z : X.Point) :
      point z ≫ F.map (toUnit M ≫ u) = point infinity ≫ F.map (toUnit M ≫ u) := by
    have hT : IsTerminal (F.obj (𝟙_ (Over (Spec (.of R))))) :=
      IsTerminal.isTerminalObj F _ isTerminalTensorUnit
    simp only [Functor.map_comp, ← Category.assoc]
    rw [hT.hom_ext (point z ≫ F.map (toUnit M)) (point infinity ≫ F.map (toUnit M))]
  have hrel := integralAffine_baseChange hN f W (toUnit M ≫ u) ε hgen k
  have hv (z : X.Point) : v (X.W p z) = ε • v z + t := by
    change (read (point (X.W p z) ≫ F.map f)).toAdd = ε • v z + t
    rw [hW, Category.assoc, hrel, MonObj.comp_mul, GrpObj.comp_zpow,
      hcst, map_mul read, map_zpow read]
    rfl
  apply atkinQuotient_of_affine infinity d q p ε v t _ hval (hv x) (hv infinity)
  have hc : center infinity (of infinity) = 0 := by
    apply Subtype.ext
    change of infinity - FreeAbelianGroup.lift (fun _ : X.Point => (1 : ℤ)) (of infinity) •
      of infinity = 0
    simp
  change (read (point infinity ≫ F.map f)).toAdd = 0
  rw [← hval infinity, hc, map_zero, map_zero]


end ZInQ.Manuscript.RC.GoodReduction

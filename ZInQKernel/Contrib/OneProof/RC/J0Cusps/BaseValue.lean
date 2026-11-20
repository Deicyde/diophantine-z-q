import ZInQKernel.Contrib.OneProof.RC.J0Cusps.CuspComparison

/-! The basedness equation from specialization at infinity (tex 1785–1787,
2836–2838). On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter ModularCurve MonObj MonoidalCategory PkgI3 UpperHalfPlane
open scoped Topology

namespace ZInQ.Manuscript.RC.J0Cusps

/-- The analytic normalization at infinity gives the algebraic basedness
equation once the target uniformization is faithful. -/
theorem cusp_at_infinity_maps_to_unit (N : ℕ) [NeZero N] {A : AbVar ℚ}
    (π : source N ⟶ A.X)
    {T : Type*} [AddCommGroup T] [TopologicalSpace T] [T2Space T]
    (u : Additive (A.Pt ℂ) →+ T) (hu : Function.Injective u)
    (U : Point ℂ (complexBaseChange.obj A.X) → T)
    (hU : Continuous U) (hUeval : ∀ p : A.Pt ℂ, U (complexLift p) = u (Additive.ofMul p))
    (an : ℍ → T)
    (hchart : ∀ τ : ℍ, U (complexLift (interior N τ ≫ π)) = an τ)
    (hlim : Tendsto an atImInfty (𝓝 0)) :
    X0Model.cusp N ≫ π.left = (η[A.X]).left := by
  let i := Spec.map (CommRingCat.ofHom (Rat.castHom ℂ))
  let p := branchComplex N (Rat.castHom ℂ) (modularFunctionField N).subtype
  have hv := value_eq_of_chart_limit π (interior N) p U hU
    (tendsto_infinity N) (Eventually.of_forall hchart) hlim
  rw [hUeval] at hv
  have hp : p ≫ π = (1 : A.Pt ℂ) :=
    Additive.ofMul.injective (hu (hv.trans (map_zero u).symm))
  let toRat : AbVar.ptObj (K := ℚ) ℂ ⟶ 𝟙_ (Over (Spec (.of ℚ))) :=
    Over.homMk i (maps_to_rat_unique _ _)
  have hOne : (1 : A.Pt ℂ) = toRat ≫ η[A.X] :=
    MonObj.comp_one toRat |>.symm
  have hleft := congrArg (fun P : A.Pt ℂ => P.left) (hp.trans hOne)
  have he : i ≫ (X0Model.cusp N ≫ π.left) = i ≫ (η[A.X]).left := by
    rw [← Category.assoc]
    exact hleft
  have hi : IsDominant i := ⟨by
    intro y
    let z := IsLocalRing.closedPoint ℂ
    rw [Subsingleton.elim y (i z)]
    exact subset_closure (Set.mem_range_self z)⟩
  have hred : IsReduced (Spec (.of ℚ)) := inferInstance
  exact @ext_of_isDominant_of_isSeparated _ _ _ _ hred _ _ A.X.hom inferInstance
    (maps_to_rat_unique _ _) i hi he


end ZInQ.Manuscript.RC.J0Cusps

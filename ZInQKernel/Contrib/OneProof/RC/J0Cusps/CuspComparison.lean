import ZInQKernel.Contrib.OneProof.RC.J0Cusps.CuspAssignment

/-! Specializing the comparison to the actual source cusps, with a given
Abel–Jacobi factorization. On the spot (c), tex 1785–1787 and 2937–2943. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter MonObj PkgI3 UpperHalfPlane
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

namespace ZInQ.Manuscript.RC.J0Cusps

private def scalarSpec : AbVar.ptObj (K := ℚ) ℂ ⟶ AbVar.ptObj (K := ℚ) Qbar :=
  Over.homMk (Spec.map (CommRingCat.ofHom qbarToComplex)) (maps_to_rat_unique _ _)

/-- Extend the coordinates of Jacobian points along the specified embedding. -/
def extendJacobian (J : AbVar ℚ) : Additive (J.Pt Qbar) →+ Additive (J.Pt ℂ) :=
  MonoidHom.toAdditive (show J.Pt Qbar →* J.Pt ℂ from
    { toFun := fun P => scalarSpec ≫ P
      map_one' := MonObj.comp_one _
      map_mul' := fun _ _ => MonObj.comp_mul _ _ _ })

private theorem extendJacobian_class (N : ℕ) [NeZero N] {J : AbVar ℚ}
    (aj : source N ⟶ J.X) (r : OnePoint ℚ) :
    extendJacobian J (cuspClass N aj (algebraicCusp N) r) =
      cuspClass N aj (extendPoint ∘ algebraicCusp N) r := by
  change Additive.ofMul (scalarSpec ≫ (algebraicCusp N (ElkikPrint.cuspOrbit N r) ≫ aj)) =
    Additive.ofMul (extendPoint (algebraicCusp N (ElkikPrint.cuspOrbit N r)) ≫ aj)
  rw [← Category.assoc]
  rfl

/-- Source specialization at every rational cusp label transfers the
analytic limit to the image of its actual geometric cusp class. -/
theorem cusp_comparison_of_factor
    (N : ℕ) [NeZero N]
    {J A : AbVar ℚ} {aj : source N ⟶ J.X} (π : source N ⟶ A.X)
    (g : J.X ⟶ A.X) [IsMonHom g] (hg : aj ≫ g = π)
    {T : Type*} [AddCommGroup T] [TopologicalSpace T] [T2Space T]
    (u : Additive (A.Pt ℂ) →+ T) (U : Point ℂ (complexBaseChange.obj A.X) → T)
    (hU : Continuous U) (hUeval : ∀ p : A.Pt ℂ, U (complexLift p) = u (Additive.ofMul p))
    (an : ℍ → T) (lim : ℚ → T)
    (hchart : ∀ τ : ℍ, U (complexLift (interior N τ ≫ π)) = an τ)
    (hlim : ∀ (r : ℚ) (σ : SL(2, ℤ)), mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ) = r →
      Tendsto (fun τ : ℍ => an (σ • τ)) atImInfty (𝓝 (lim r))) :
    ∃ φ : Additive (J.Pt Qbar) →+ T,
      ∀ r : ℚ, φ (cuspClass N aj (algebraicCusp N) r) = lim r := by
  refine ⟨(torusHom g u).comp (extendJacobian J), fun r => ?_⟩
  rw [AddMonoidHom.comp_apply, extendJacobian_class]
  let p := extendPoint (algebraicCusp N (ElkikPrint.cuspOrbit N (r : OnePoint ℚ)))
  change torusHom g u (pointClass aj p) = lim r
  rw [torusHom_pointClass g hg, ← hUeval]
  obtain ⟨σ, hσ⟩ := (r : OnePoint ℚ).exists_mem_SL2 ℤ
  have hs := algebraicCusp_limit N σ
  rw [orbitOfSL_eq, hσ] at hs
  exact value_eq_of_chart_limit π (fun τ : ℍ => interior N (σ • τ))
    p U hU hs (Eventually.of_forall fun τ => hchart (σ • τ)) (hlim r σ hσ)


end ZInQ.Manuscript.RC.J0Cusps

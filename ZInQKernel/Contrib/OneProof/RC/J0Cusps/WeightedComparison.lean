import ZInQKernel.Contrib.OneProof.RC.J0Cusps.BaseValue
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ModelJacobian

/-! The remaining comparison on the target, after identifying the source
cusps. On the spot (c), tex 1785–1787 and 2937–2943. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter MonObj PkgI3 UpperHalfPlane
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

namespace ZInQ.Manuscript.RC.J0Cusps

/-- The class of a cusp minus infinity in the geometric Jacobian. -/
def algebraicCuspClass (N : ℕ) [NeZero N] (r : OnePoint ℚ) : Additive ((J0 N).Pt Qbar) :=
  cuspClass N (aj0 N) (algebraicCusp N) r

theorem algebraicCuspClass_factors (N : ℕ) [NeZero N] (r : OnePoint ℚ) :
    algebraicCuspClass N r =
      classOfCusp N (aj0 N) (algebraicCusp N) (ElkikPrint.cuspOrbit N r) := rfl

/-- The specialization of the Albanese construction to the actual (J_0(N)). -/
def modularFactor (N : ℕ) [NeZero N] {A : AbVar ℚ}
    (π : source N ⟶ A.X) (hb : infinity N ≫ π = η[A.X]) :
    (J0 N).X ⟶ A.X :=
  factor (isJacobian_aj0 N) π hb

theorem modularFactor_isMonHom (N : ℕ) [NeZero N] {A : AbVar ℚ}
    (π : source N ⟶ A.X) (hb : infinity N ≫ π = η[A.X]) :
    IsMonHom (modularFactor N π hb) :=
  factor_isMonHom (isJacobian_aj0 N) π hb

theorem aj0_comp_modularFactor (N : ℕ) [NeZero N] {A : AbVar ℚ}
    (π : source N ⟶ A.X) (hb : infinity N ≫ π = η[A.X]) :
    aj0 N ≫ modularFactor N π hb = π :=
  abelJacobi_comp_factor (isJacobian_aj0 N) π hb

/-- Source specialization at every rational cusp label transfers the
analytic limit to the image of its actual geometric cusp class. -/
theorem cusp_comparison
    (N : ℕ) [NeZero N]
    {A : AbVar ℚ} (π : source N ⟶ A.X) (hb : infinity N ≫ π = η[A.X])
    {T : Type*} [AddCommGroup T] [TopologicalSpace T] [T2Space T]
    (u : Additive (A.Pt ℂ) →+ T) (U : Point ℂ (complexBaseChange.obj A.X) → T)
    (hU : Continuous U) (hUeval : ∀ p : A.Pt ℂ, U (complexLift p) = u (Additive.ofMul p))
    (an : ℍ → T) (lim : ℚ → T)
    (hchart : ∀ τ : ℍ, U (complexLift (interior N τ ≫ π)) = an τ)
    (hlim : ∀ (r : ℚ) (σ : SL(2, ℤ)), mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ) = r →
      Tendsto (fun τ : ℍ => an (σ • τ)) atImInfty (𝓝 (lim r))) :
    ∃ φ : Additive ((J0 N).Pt Qbar) →+ T,
      ∀ r : ℚ, φ (algebraicCuspClass N r) = lim r := by
  letI := modularFactor_isMonHom N π hb
  exact cusp_comparison_of_factor N π (modularFactor N π hb) (aj0_comp_modularFactor N π hb)
    u U hU hUeval an lim hchart hlim

/-- The resulting comparison in the form consumed by the quadratic sum. -/
theorem weighted_comparison
    (N m : ℕ) [NeZero N]
    {A : AbVar ℚ} (π : source N ⟶ A.X) (hb : infinity N ≫ π = η[A.X])
    {T : Type*} [AddCommGroup T] [TopologicalSpace T] [T2Space T]
    (u : Additive (A.Pt ℂ) →+ T) (U : Point ℂ (complexBaseChange.obj A.X) → T)
    (hU : Continuous U) (hUeval : ∀ p : A.Pt ℂ, U (complexLift p) = u (Additive.ofMul p))
    (an : ℍ → T) (lim : ℚ → T)
    (hchart : ∀ τ : ℍ, U (complexLift (interior N τ ≫ π)) = an τ)
    (hlim : ∀ (r : ℚ) (σ : SL(2, ℤ)), mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ) = r →
      Tendsto (fun τ : ℍ => an (σ • τ)) atImInfty (𝓝 (lim r))) :
    ∃ φ : Additive ((J0 N).Pt Qbar) →+ T,
      ∀ a < m, jacobiSym (a : ℤ) m ≠ 0 →
        φ (algebraicCuspClass N (((a : ℚ) / m : ℚ) : OnePoint ℚ)) = lim ((a : ℚ) / m) := by
  obtain ⟨φ, hφ⟩ := cusp_comparison N π hb u U hU hUeval an lim hchart hlim
  exact ⟨φ, fun a _ _ => hφ ((a : ℚ) / m)⟩

/-- At a compatible faithful uniformization, the analytic normalization supplies
the basedness required by the weighted comparison. -/
theorem weighted_comparison_from_limits
    (N m : ℕ) [NeZero N]
    {A : AbVar ℚ} (π : source N ⟶ A.X)
    {T : Type*} [AddCommGroup T] [TopologicalSpace T] [T2Space T]
    (u : Additive (A.Pt ℂ) →+ T) (hu : Function.Injective u)
    (U : Point ℂ (complexBaseChange.obj A.X) → T)
    (hU : Continuous U) (hUeval : ∀ p : A.Pt ℂ, U (complexLift p) = u (Additive.ofMul p))
    (an : ℍ → T) (lim : ℚ → T)
    (hchart : ∀ τ : ℍ, U (complexLift (interior N τ ≫ π)) = an τ)
    (hzero : Tendsto an atImInfty (𝓝 0))
    (hlim : ∀ (r : ℚ) (σ : SL(2, ℤ)), mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ) = r →
      Tendsto (fun τ : ℍ => an (σ • τ)) atImInfty (𝓝 (lim r))) :
    ∃ φ : Additive ((J0 N).Pt Qbar) →+ T,
      ∀ a < m, jacobiSym (a : ℤ) m ≠ 0 →
        φ (algebraicCuspClass N (((a : ℚ) / m : ℚ) : OnePoint ℚ)) = lim ((a : ℚ) / m) := by
  have hb : infinity N ≫ π = η[A.X] :=
    Over.OverMorphism.ext (cusp_at_infinity_maps_to_unit N π u hu U hU hUeval an hchart hzero)
  exact weighted_comparison N m π hb u U hU hUeval an lim hchart hlim


end ZInQ.Manuscript.RC.J0Cusps

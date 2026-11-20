import ZInQKernel.Contrib.OneProof.RC.J0Cusps.Factor
import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Definitions.AlgebraicGeometry.ComplexPoint.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-! The remaining chart comparison takes place on the source curve.
Continuity on complex points transports it through the rational map.
Tex 1785–1787, 1825–1828, 2937–2942; on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonObj PkgI3 Filter UpperHalfPlane
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

namespace ZInQ.Manuscript.RC.J0Cusps

/-- The scalar extension used to give rational-scheme points the complex topology. -/
abbrev complexBaseChange :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))

/-- The lift of a complex point over the rationals to the base changed scheme. -/
def complexLift {X : Over (Spec (.of ℚ))} (p : AbVar.ptObj (K := ℚ) ℂ ⟶ X) :
    Point ℂ (complexBaseChange.obj X) :=
  Over.homMk (pullback.lift p.left (𝟙 _) (by simpa [AbVar.ptObj] using Over.w p))
    (pullback.lift_snd _ _ _)

theorem complexLift_comp {X Y : Over (Spec (.of ℚ))}
    (p : AbVar.ptObj (K := ℚ) ℂ ⟶ X) (π : X ⟶ Y) :
    complexLift (p ≫ π) = Point.map (complexBaseChange.map π) (complexLift p) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;>
    simp [complexLift, Point.map, Over.pullback_map_left, Category.assoc] <;> rfl

/-- A limit on the source, together with the interior comparison and continuity
of the uniformization on the target, determines the value at the source point. -/
theorem value_eq_of_chart_limit {X Y : Over (Spec (.of ℚ))} (π : X ⟶ Y)
    {Index T : Type*} [TopologicalSpace T] [T2Space T] {F : Filter Index} [F.NeBot]
    (x : Index → (AbVar.ptObj (K := ℚ) ℂ ⟶ X))
    (c : AbVar.ptObj (K := ℚ) ℂ ⟶ X)
    (u : Point ℂ (complexBaseChange.obj Y) → T) (hu : Continuous u)
    {an : Index → T} {v : T}
    (hsource : Tendsto (fun t => complexLift (x t)) F (𝓝 (complexLift c)))
    (hchart : (fun t => u (complexLift (x t ≫ π))) =ᶠ[F] an)
    (hlimit : Tendsto an F (𝓝 v)) :
    u (complexLift (c ≫ π)) = v := by
  have hmap := (Point.continuous_map (complexBaseChange.map π)).continuousAt.tendsto.comp hsource
  have ht := hu.continuousAt.tendsto.comp hmap
  simpa only [Function.comp_apply, ← complexLift_comp] using
    tendsto_nhds_unique (ht.congr' (by
      filter_upwards [hchart] with t heq
      simpa only [Function.comp_apply, ← complexLift_comp] using heq)) hlimit

/-- Any two analytic cusp limits in the orbit of zero agree, once the interior
function descends through the level action. This applies to the scaled symbols. -/
theorem cuspLimit_eq_zero_of_jacobi_ne_zero {T : Type*} [TopologicalSpace T] [T2Space T]
    (N a m : ℕ) [NeZero m] (hmN : m.Coprime N) (hχ : jacobiSym (a : ℤ) m ≠ 0)
    (an : ℍ → T) (lim : ℚ → T)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, an (g • τ) = an τ)
    (hlim : ∀ (r : ℚ) (σ : SL(2, ℤ)), mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ) = r →
      Tendsto (fun τ : ℍ => an (σ • τ)) atImInfty (𝓝 (lim r))) :
    lim 0 = lim ((a : ℚ) / m) := by
  have ham : a.Coprime m := by
    by_contra ha
    apply hχ
    exact jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa [Nat.Coprime, Int.gcd_eq_natAbs] using ha)
  obtain ⟨g, hg, hgz⟩ := exists_gamma0_smul_zero N a m (NeZero.ne m) ham hmN
  have hS : mapGL ℚ ModularGroup.S • (OnePoint.infty : OnePoint ℚ) = (0 : ℚ) := by
    rw [OnePoint.smul_infty_eq_ite]
    change (if (1 : ℚ) = 0 then OnePoint.infty else ((0 / 1 : ℚ) : OnePoint ℚ)) = _
    simp
  have hgS : mapGL ℚ (g * ModularGroup.S) • (OnePoint.infty : OnePoint ℚ) = (((a : ℚ) / m : ℚ) : OnePoint ℚ) := by
    rw [map_mul, mul_smul, hS, hgz]
  apply tendsto_nhds_unique ?_ (hlim _ _ hgS)
  exact (hlim 0 ModularGroup.S hS).congr (fun τ => by simp only [mul_smul, hinv g hg])

/-- The exact comparison on the support of the quadratic sum follows from
one source limit, at the cusp represented by zero. The target continuity
and chart equality are the ones for the chosen interior parametrization. -/
theorem cuspComparison_of_zero_chart_limit
    {X : Over (Spec (.of ℚ))} {J A : AbVar ℚ} {aj : X ⟶ J.X} {π : X ⟶ A.X}
    (g : J.X ⟶ A.X) [IsMonHom g] (hg : aj ≫ g = π)
    {T : Type*} [AddCommGroup T] [TopologicalSpace T] [T2Space T]
    (u : Additive (A.Pt ℂ) →+ T) (U : Point ℂ (complexBaseChange.obj A.X) → T)
    (hU : Continuous U) (hUeval : ∀ p : A.Pt ℂ, U (complexLift p) = u (Additive.ofMul p))
    (N m : ℕ) [NeZero N] [NeZero m] (hmN : m.Coprime N)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) →
      (AbVar.ptObj (K := ℚ) ℂ ⟶ X))
    (x : ℍ → (AbVar.ptObj (K := ℚ) ℂ ⟶ X)) (an : ℍ → T) (lim : ℚ → T)
    (hsource : Tendsto (fun τ : ℍ => complexLift (x (ModularGroup.S • τ))) atImInfty
      (𝓝 (complexLift (c (ElkikPrint.cuspOrbit N ((0 : ℚ) : OnePoint ℚ))))))
    (hchart : ∀ τ : ℍ, U (complexLift (x τ ≫ π)) = an τ)
    (hinv : ∀ δ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, an (δ • τ) = an τ)
    (hlim : ∀ (r : ℚ) (σ : SL(2, ℤ)), mapGL ℚ σ • (OnePoint.infty : OnePoint ℚ) = r →
      Tendsto (fun τ : ℍ => an (σ • τ)) atImInfty (𝓝 (lim r))) :
    ∀ a < m, jacobiSym (a : ℤ) m ≠ 0 →
      torusHom g u (cuspClass N aj c (((a : ℚ) / m : ℚ) : OnePoint ℚ)) = lim ((a : ℚ) / m) := by
  have hS : mapGL ℚ ModularGroup.S • (OnePoint.infty : OnePoint ℚ) = (0 : ℚ) := by
    rw [OnePoint.smul_infty_eq_ite]
    change (if (1 : ℚ) = 0 then OnePoint.infty else ((0 / 1 : ℚ) : OnePoint ℚ)) = _
    simp
  have hzero := value_eq_of_chart_limit π (fun τ : ℍ => x (ModularGroup.S • τ))
    _ U hU hsource (Filter.Eventually.of_forall fun τ => hchart (ModularGroup.S • τ))
    (hlim 0 ModularGroup.S hS)
  intro a _ hχ
  rw [torusHom_cuspClass_of_jacobi_ne_zero N a m hmN hχ g hg u c, ← hUeval, hzero]
  exact cuspLimit_eq_zero_of_jacobi_ne_zero N a m hmN hχ an lim hinv hlim


end ZInQ.Manuscript.RC.J0Cusps

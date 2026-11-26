import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Core
import ZInQKernel.Contrib.OneProof.RC.X0Model2.ChartReparam
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-! Weight-two invariance of the native value under `Γ₀(N)` (K6).

The analytic point map is constant on `Γ₀(N)` orbits, so the chain rule for the
manifold derivative together with the derivative `(cτ + d)⁻²` of the Möbius action
gives `f_ω(γ • τ) = (cτ + d)² f_ω(τ)`. The differentiability of the point map (K4)
is taken as an explicit hypothesis. The result is packaged as a slash-invariant
form of weight two for `Γ₀(N)` viewed inside `GL(2, ℝ)`. -/

noncomputable section

open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter
open scoped Manifold MatrixGroups ModularForm Topology

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

variable (N : ℕ) [NeZero N]

/-- The statement K4: the analytic point map is holomorphic. -/
def ArcPointMDifferentiable : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) (arcPoint N)

/-- The analytic point map is constant on `Γ₀(N)` orbits. -/
theorem arcPoint_smul (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    arcPoint N (γ • τ) = arcPoint N τ := by
  unfold arcPoint
  congr 1
  apply Over.OverMorphism.ext
  exact X0Model2.complexPoint_smul N γ hγ τ

/-- The inclusion of the upper half plane has the identity as manifold derivative. -/
theorem mfderiv_coe_upperHalfPlane (τ : ℍ) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℍ → ℂ) τ = ContinuousLinearMap.id ℂ ℂ := by
  rw [(mdifferentiable_coe τ).mfderiv]
  have hev : writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) τ ((↑) : ℍ → ℂ) =ᶠ[𝓝 (extChartAt 𝓘(ℂ) τ τ)] id := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℂ)) τ] with z hz
    exact (extChartAt 𝓘(ℂ) τ).right_inv hz
  rw [ModelWithCorners.range_eq_univ, fderivWithin_univ, hev.fderiv_eq, fderiv_id]
  rfl

/-- The manifold derivative of the Möbius action of `g ∈ GL(2, ℝ)` with positive
determinant at `τ`, applied to `1`, is `det g / (cτ + d)²`. -/
theorem mfderiv_smul_one {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun σ : ℍ => g • σ) τ (1 : ℂ) =
      ((g.val.det : ℂ) / denom g τ ^ 2 : ℂ) := by
  let h : ℂ → ℂ := fun z ↦ ↑(g • ofComplex z)
  have hh : HasDerivAt h (g.val.det / denom g τ ^ 2) τ := (hasStrictDerivAt_smul hg τ).hasDerivAt
  have hcomp : ((↑) : ℍ → ℂ) ∘ (fun σ : ℍ => g • σ) = h ∘ ((↑) : ℍ → ℂ) := by
    funext σ
    simp [h, ofComplex_apply]
  have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun σ : ℍ => g • σ) τ := mdifferentiable_smul hg τ
  have h1 := mfderiv_comp τ (mdifferentiable_coe (g • τ)) hmd
  have hhm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) h (τ : ℂ) :=
    hh.differentiableAt.mdifferentiableAt
  have h2 := mfderiv_comp τ hhm (mdifferentiable_coe τ)
  rw [← hcomp, h1, mfderiv_coe_upperHalfPlane, mfderiv_coe_upperHalfPlane,
    mfderiv_eq_fderiv] at h2
  have h3 := congrArg (fun L => L (1 : ℂ)) h2
  refine Eq.trans h3 ?_
  show fderiv ℂ h (τ : ℂ) (1 : ℂ) = _
  rw [hh.hasFDerivAt.fderiv]
  exact one_smul ℂ _

/-- The manifold derivative of the Möbius action of `γ ∈ SL(2, ℤ)` at `τ`, applied
to `1`, is `(cτ + d)⁻²`. -/
theorem mfderiv_sl_smul_one (γ : SL(2, ℤ)) (τ : ℍ) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun σ : ℍ => γ • σ) τ (1 : ℂ) = (denom γ τ ^ 2)⁻¹ := by
  have hdet : (γ : GL (Fin 2) ℝ).val.det = 1 :=
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).2
  have key := mfderiv_smul_one (g := (γ : GL (Fin 2) ℝ)) (by rw [hdet]; exact one_pos) τ
  rw [hdet, Complex.ofReal_one, one_div] at key
  exact key

/-- Transport of the holomorphic covector along an equality of points, through the
identification of the tangent spaces. -/
theorem covectorOfSection_cast (ω : Γ((curveC N).hom.relativeDifferentials, ⊤))
    {p q : ComplexPoint (curveC N)} (h : p = q) (v : TangentSpace 𝓘(ℂ, Fin 1 → ℂ) p) :
    ComplexPoint.covectorOfSection ω q (tangentSpaceCast 𝓘(ℂ, Fin 1 → ℂ) p q v) =
      ComplexPoint.covectorOfSection ω p v := by
  subst h
  rfl

/-- Transport of the manifold derivative along an equality of maps, through the
identification of the tangent spaces. -/
theorem mfderiv_cast {G H : ℍ → ComplexPoint (curveC N)} (h : G = H) (x : ℍ) (v : ℂ) :
    tangentSpaceCast 𝓘(ℂ, Fin 1 → ℂ) (G x) (H x) (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) G x v) =
      mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) H x v := by
  subst h
  rfl

/-- Weight-two transformation of the covector pairing for any map that is constant on
the orbits of `γ ∈ SL(2, ℤ)` and differentiable at `γ • τ`. -/
theorem covector_weight_two (ω : Γ((curveC N).hom.relativeDifferentials, ⊤))
    (F : ℍ → ComplexPoint (curveC N)) (γ : SL(2, ℤ)) (hF : ∀ σ : ℍ, F (γ • σ) = F σ)
    (τ : ℍ) (hd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) F (γ • τ)) :
    ComplexPoint.covectorOfSection ω (F (γ • τ))
        (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) F (γ • τ) (1 : ℂ)) =
      denom γ τ ^ 2 *
        ComplexPoint.covectorOfSection ω (F τ) (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) F τ (1 : ℂ)) := by
  have hfun : F ∘ (fun σ : ℍ => γ • σ) = F := funext hF
  have hdet : (γ : GL (Fin 2) ℝ).val.det = 1 :=
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ).2
  have hφ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun σ : ℍ => γ • σ) τ :=
    mdifferentiable_smul (g := (γ : GL (Fin 2) ℝ))
      (by change 0 < ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det; rw [hdet]; exact one_pos) τ
  have hchain := mfderiv_comp τ hd hφ
  have hA : mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) F τ (1 : ℂ) =
      tangentSpaceCast 𝓘(ℂ, Fin 1 → ℂ) ((F ∘ fun σ : ℍ => γ • σ) τ) (F τ)
        ((denom γ τ ^ 2)⁻¹ • mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) F (γ • τ) (1 : ℂ)) := by
    refine (mfderiv_cast N hfun τ (1 : ℂ)).symm.trans ?_
    congr 1
    rw [hchain]
    show mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) F (γ • τ)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun σ : ℍ => γ • σ) τ (1 : ℂ)) = _
    rw [mfderiv_sl_smul_one]
    calc mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) F (γ • τ) ((denom γ τ ^ 2)⁻¹ : ℂ) =
        mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) F (γ • τ) ((denom γ τ ^ 2)⁻¹ • (1 : ℂ)) := by
          rw [smul_eq_mul, mul_one]
      _ = _ := (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) F (γ • τ)).map_smul _ (1 : ℂ)
  have hne : denom γ τ ^ 2 ≠ 0 := pow_ne_zero _ (denom_ne_zero _ τ)
  rw [hA, ContinuousLinearEquiv.map_smul, ContinuousLinearMap.map_smul,
    covectorOfSection_cast N ω (p := (F ∘ fun σ : ℍ => γ • σ) τ) (hF τ), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  rfl

/-- K6 in terms of the automorphy factor: given K4, for `γ ∈ Γ₀(N)`,
`f_ω(γ • τ) = j(γ, τ)² f_ω(τ)`. -/
theorem nativeValue_smul_denom (hK4 : ArcPointMDifferentiable N)
    (ω : Γ((curveC N).hom.relativeDifferentials, ⊤))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    nativeValue N ω (γ • τ) = denom γ τ ^ 2 * nativeValue N ω τ :=
  covector_weight_two N ω (arcPoint N) γ (arcPoint_smul N γ hγ) τ (hK4 (γ • τ))

/-- K6, slash form: given K4, `f_ω ∣[2] γ = f_ω` for `γ ∈ Γ₀(N)`. -/
theorem nativeValue_slash_SL (hK4 : ArcPointMDifferentiable N)
    (ω : Γ((curveC N).hom.relativeDifferentials, ⊤))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    nativeValue N ω ∣[(2 : ℤ)] γ = nativeValue N ω := by
  funext τ
  rw [ModularForm.SL_slash_apply, nativeValue_smul_denom N hK4 ω γ hγ τ]
  have hne : denom γ τ ^ 2 ≠ 0 := pow_ne_zero _ (denom_ne_zero _ τ)
  rw [zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, mul_comm,
    ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- K6: given K4, for `γ = [[a, b], [c, d]] ∈ Γ₀(N)`,
`f_ω(γ • τ) = (cτ + d)² f_ω(τ)`. -/
theorem nativeValue_smul_gamma0 (hK4 : ArcPointMDifferentiable N)
    (ω : Γ((curveC N).hom.relativeDifferentials, ⊤))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    nativeValue N ω (γ • τ) = ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ 2 * nativeValue N ω τ := by
  have h := (ModularForm.slash_action_eq'_iff (2 : ℤ) (nativeValue N ω) γ τ).mp
    (congrFun (nativeValue_slash_SL N hK4 ω γ hγ) τ)
  rw [h, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]

/-- K6, slash form for `Γ₀(N)` viewed inside `GL(2, ℝ)`. -/
theorem nativeValue_slash (hK4 : ArcPointMDifferentiable N)
    (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) :
    ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)),
      nativeValue N ω ∣[(2 : ℤ)] γ = nativeValue N ω := by
  intro γ hγ
  obtain ⟨γ', hγ', rfl⟩ := Subgroup.mem_map.mp hγ
  exact nativeValue_slash_SL N hK4 ω γ' hγ'

/-- Given K4, the native value of a global differential as a slash-invariant form of
weight two for `Γ₀(N)`. -/
def nativeSlashInvariantForm (hK4 : ArcPointMDifferentiable N)
    (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) :
    SlashInvariantForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := nativeValue N ω
  slash_action_eq' := nativeValue_slash N hK4 ω

@[simp]
theorem nativeSlashInvariantForm_apply (hK4 : ArcPointMDifferentiable N)
    (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) (τ : ℍ) :
    nativeSlashInvariantForm N hK4 ω τ = nativeValue N ω τ :=
  rfl

end ZInQ.Manuscript.RC.CuspFormDifferentials

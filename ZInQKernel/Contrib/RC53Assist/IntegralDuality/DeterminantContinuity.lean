import ZInQKernel.Contrib.OneProof.RC.FibreDuality.DetPairing

/-!
# Continuity of the determinant form on the actual Tate module

The source Tate module has the inverse-limit topology of its genuine finite
levels. Scalar multiplication by a fixed two-adic integer is continuous by
projection to those levels. The determinant form is jointly continuous because
its two basis coordinates are continuous, and multiplication and subtraction
are continuous on the two-adic integers.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.FibreDuality

attribute [local instance] levTop

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K}

/-- Multiplication by a fixed scalar is continuous on the actual inverse limit. -/
theorem continuous_const_smul_tate (a : ℤ_[2]) :
    Continuous fun x : TateS K S W => a • x := by
  refine continuous_induced_rng.mpr (continuous_pi fun n => ?_)
  have hc : Continuous fun x : Lev K S W n => resN n a • x :=
    continuous_of_discreteTopology
  exact hc.comp (continuous_projLev n)

/-- The scalar-continuity instance used by continuous integral cochains. -/
instance tate_continuousConstSMul : ContinuousConstSMul ℤ_[2] (TateS K S W) :=
  ⟨continuous_const_smul_tate⟩

/-- The source determinant form is jointly continuous for the inverse-limit topology. -/
theorem continuous_detT [W.IsElliptic] [HasFullTwoTorsion K S W] :
    Continuous fun p : TateS K S W × TateS K S W => detT p.1 p.2 := by
  have h0 := continuous_coord (K := K) (S := S) (W := W) 0
  have h1 := continuous_coord (K := K) (S := S) (W := W) 1
  exact ((h0.comp continuous_fst).mul (h1.comp continuous_snd)).sub
    ((h1.comp continuous_fst).mul (h0.comp continuous_snd))

/-- The determinant adjoint is bijective on the actual finite-free Tate module. -/
theorem detT_bijective [W.IsElliptic] [HasFullTwoTorsion K S W] :
    Function.Bijective (detT (K := K) (S := S) (W := W)) := by
  let b : Module.Basis (Fin 2) ℤ_[2] (TateS K S W) :=
    tateBasis (K := K) (S := S) (W := W)
  constructor
  · intro x y h
    have h0 := LinearMap.congr_fun h (b 0)
    have h1 := LinearMap.congr_fun h (b 1)
    simp [b, detT_apply, Module.Basis.repr_self] at h0 h1
    apply b.repr.injective
    apply Finsupp.ext
    intro i
    fin_cases i
    · exact h1
    · exact h0
  · intro f
    refine ⟨f (b 1) • b 0 - f (b 0) • b 1, ?_⟩
    apply b.ext
    intro i
    fin_cases i <;> simp [b, map_sub, LinearMap.map_smul₂, detT_basis,
      detT_basis_swap, detT_self, smul_eq_mul]

end ZInQ.Contrib.RC53Assist.IntegralDuality

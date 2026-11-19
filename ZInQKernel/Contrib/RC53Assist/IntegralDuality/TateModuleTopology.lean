import ZInQKernel.Contrib.RC53Assist.IntegralDuality.DeterminantContinuity
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.PadicLimit
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The actual Tate module has the two-adic module topology

Projection to the genuine finite torsion levels proves joint continuity of
scalar multiplication. The specified Tate basis then gives a continuous
linear equivalence with a finite product of two-adic integers. Transport of
the module topology supplies the precise topology hypothesis of integral
Galois duality; no arithmetic duality is used.
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.LambdaCoef

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K}

attribute [local instance] levTop

/-- Joint scalar continuity follows from the actual finite coefficient projections. -/
theorem tate_jointScalarContinuous :
    Continuous fun p : ℤ_[2] × TateS K S W => p.1 • p.2 := by
  refine continuous_induced_rng.mpr (continuous_pi fun n => ?_)
  let f : ZMod (2 ^ n) × Lev K S W n → Lev K S W n :=
    fun p => p.1.val • p.2
  have hf : Continuous f := continuous_of_discreteTopology
  exact hf.comp
    (((PadicLimit.continuous_toZModPow (p := 2) n).comp continuous_fst).prodMk
      ((continuous_projLev n).comp continuous_snd))

/-- The inherited Tate topology makes its two-adic scalar action jointly continuous. -/
instance tate_jointContinuousSMul : ContinuousSMul ℤ_[2] (TateS K S W) :=
  ⟨tate_jointScalarContinuous⟩

/-- The specified Tate basis is a continuous coordinate identification in both directions. -/
def tateCoordinates [W.IsElliptic] [HasFullTwoTorsion K S W] :
    TateS K S W ≃L[ℤ_[2]] (Fin 2 → ℤ_[2]) where
  toLinearEquiv := (tateBasis (K := K) (S := S) (W := W)).equivFun
  continuous_toFun := continuous_pi fun i => continuous_coord i
  continuous_invFun := by
    let b : Module.Basis (Fin 2) ℤ_[2] (TateS K S W) := tateBasis
    change Continuous fun x : Fin 2 → ℤ_[2] => b.equivFun.symm x
    have h : (fun x : Fin 2 → ℤ_[2] => b.equivFun.symm x) =
        (fun x => ∑ i : Fin 2, x i • b i) := by
      funext x
      exact b.equivFun_symm_apply x
    rw [h]
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

/-- The actual inverse-limit topology is the module topology of the two-adic lattice. -/
theorem tate_isModuleTopology [W.IsElliptic] [HasFullTwoTorsion K S W] :
    IsModuleTopology ℤ_[2] (TateS K S W) :=
  IsModuleTopology.iso (tateCoordinates (K := K) (S := S) (W := W)).symm

end ZInQ.Contrib.RC53Assist.IntegralDuality

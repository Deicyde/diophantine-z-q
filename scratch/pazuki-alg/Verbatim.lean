import ZInQKernel.Contrib.OneProof.PazukiCor13Upper

/-! pazuki-alg: verbatim copy of `PazukiDict.AnalyticPPAlgebraic` (ZInQKernel/Contrib/OneProof/PazukiCor13Upper.lean,
as at 37b70108) checked `rfl` against the original. -/

noncomputable section
namespace PazukiAlgVerbatim
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj
open ZInQ.LeafPush2 (CPts IsSiegel IsPeriodMatrix Char2 thetaConst pazukiC2)
open AvSplit.HomLatticeAN3 (bcC ptE)
open BPAnalytic (Torus proj)
open PazukiDict (IsSymmPrincipal IsThetaPeriodMatrix)

def AnalyticPPAlgebraic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ)) (φ : Torus Λ ≃+ Additive (CPts (bcC A σ) (RingHom.id ℂ))),
    BPAnalytic.Uniformization.IsUniformization (bcC A σ) Λ φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → ∀ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ),
      (∀ w, w ∈ Λ ↔ ∃ m n : Fin 2 → ℤ, T w = Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ)) →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (σ' : K' →+* ℂ)
      (hσ : σ'.comp (algebraMap K K') = σ) (L : (A.baseChange K').X.left.Pic),
      IsSymmPrincipal (A.baseChange K') L ∧ IsThetaPeriodMatrix A σ σ' hσ L Λ φ Ω

example : AnalyticPPAlgebraic = PazukiDict.AnalyticPPAlgebraic := rfl

end PazukiAlgVerbatim

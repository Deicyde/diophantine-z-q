import ZInQKernel.Contrib.OneProof.ShimuraMainCM

/-! hcm-weierstrass: verbatim copy of the target statement `ZInQ.Contrib.HCMDict.ShimuraThm54` and its clause form
`IsAnalyticUnif` (ZInQKernel/Contrib/OneProof/ShimuraMainCM.lean, base 27657ffb), checked equal by `rfl`. -/

noncomputable section
open Complex
namespace HCMWCopy
open WeierstrassCurve.Affine (Point)
open ZInQ.Contrib.HCMDict (conjPt)

def IsAnalyticUnif (W : WeierstrassCurve ℂ) (Λ : Set ℂ) (ξ : ℂ → W.toAffine.Point) : Prop :=
  (∀ z w, ξ (z + w) = ξ z + ξ w) ∧ Function.Surjective ξ ∧ (∀ z, ξ z = 0 ↔ z ∈ Λ) ∧
    ∀ z₀, ξ z₀ ≠ 0 → ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ∃ X Y : ℂ → ℂ,
      DifferentiableOn ℂ X U ∧ DifferentiableOn ℂ Y U ∧
      ∀ z ∈ U, ∃ h : W.toAffine.Nonsingular (X z) (Y z), ξ z = .some (X z) (Y z) h

section Printed
open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise T5Glue

def ShimuraThm54 : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ) →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)), ArtinCond m e σ s →
  ∀ (𝔞 : Set (QNeg m)), (∃ L : PeriodPair, (L.lattice : Set ℂ) = kappa m '' 𝔞) →
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic], E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
  ∀ ξ : ℂ → E.toAffine.Point, IsAnalyticUnif E (kappa m '' 𝔞) ξ →
    ∃ ξ' : ℂ → (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticUnif (E.map (σ : ℂ →+* ℂ)) (kappa m '' sInvLat m s 𝔞) ξ' ∧
      ∀ u v : QNeg m,
        finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞 →
        conjPt (σ : ℂ →+* ℂ) (ξ (kappa m u)) = ξ' (kappa m v)

example : ShimuraThm54 = ZInQ.Contrib.HCMDict.ShimuraThm54 := rfl
example : @IsAnalyticUnif = @ZInQ.Contrib.HCMDict.IsAnalyticUnif := rfl
end Printed
end HCMWCopy

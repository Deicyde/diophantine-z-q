import ZInQKernel.Contrib.OneProof.RingClassLattice

/-! hx-used: verbatim copies of the target `T5Glue.X0ModuliGalois`
(ZInQKernel/Contrib/OneProof/RingClassLattice.lean:673 at base 43513d87) and of the statement it feeds,
`Shimura.ShimuraReciprocityModFn` (ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean:76), checked by `rfl`.
Dependencies (`IsRatModFn`, `IsConjModel`, `pp`, `modCoord`, `ιC`, `Qbar`, `HeegnerForm`, ...) are the kernel's. -/

noncomputable section

namespace HXCopy

set_option autoImplicit false
set_option maxRecDepth 20000

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura T5Glue

def X0ModuliGalois : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (g : UpperHalfPlane → ℂ), IsRatModFn N g →
    ∀ (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ),
      (∀ i < N, ∃ a : Qbar, ιC a = modCoord N τ i) →
      IsConjModel (σ : ℂ →+* ℂ) (pp τ) (pp τ') μ →
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((pp τ).weierstrassP (1 / N)) = μ ^ 2 * (pp τ').weierstrassP (k / N) ∧
        σ ((pp τ).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp τ').derivWeierstrassP (k / N)) →
      σ (g τ) = g τ'


def ShimuraReciprocityModFn : Prop :=
  ∀ (N : ℕ) (g : UpperHalfPlane → ℂ), IsRatModFn N g →
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
      (∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J) x)) →
    ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
      idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
      idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
      ∃ a a' : Qbar, ιC a = g Q.tauH ∧ ιC a' = g Q'.tauH ∧ ρ a = a'



example : X0ModuliGalois = T5Glue.X0ModuliGalois := rfl
example : ShimuraReciprocityModFn = ZInQ.Contrib.TYZGenus.Shimura.ShimuraReciprocityModFn := rfl

end HXCopy

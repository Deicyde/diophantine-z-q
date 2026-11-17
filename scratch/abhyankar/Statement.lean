import ZInQKernel.Contrib.OneProof.Abhyankar

/-! Verbatim copy of `SGRDirect.NVLocal.TameBranchNormal`
(ZInQKernel/Contrib/OneProof/SGRDirectNVLocal.lean, line 627, wip/nv-local 2e4ff83d), renamed
`TameBranchNormalCopy`, checked equal to the original and proved. -/

open IsLocalRing

noncomputable section

namespace AbhyankarScratch

def TameBranchNormalCopy : Prop :=
  ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsGalois K L] (m : Ideal R) [m.IsMaximal],
    IsRegularLocalRing (Localization.AtPrime m) → ringKrullDim (Localization.AtPrime m) = 2 →
    ∀ f g : R, m = Ideal.span {f, g} → (Ideal.span {f}).IsPrime →
    ∀ p : ℕ, p.Prime → (p : R) ∈ m → Module.finrank K L < p →
    (∀ P : Ideal R, P.IsPrime → P.height = 1 → P ≤ m → f ∉ P → g ∉ P →
      ∀ P' : Ideal (integralClosure R L), P'.IsPrime → P'.under R = P →
        P'.ramificationIdx R = 1) →
    ∀ 𝔓 : Ideal (integralClosure R L), 𝔓.IsMaximal → 𝔓.under R = m →
    ∀ Q : Ideal (integralClosure R L), Q.IsPrime → Q.under R = Ideal.span {f} → Q ≤ 𝔓 →
      (∀ Q' : Ideal (integralClosure R L), Q'.IsPrime → Q'.under R = Ideal.span {f} → Q' ≤ 𝔓 →
        Q' = Q) ∧
      (∀ (F : Type) [CommRing F] [Algebra (integralClosure R L ⧸ Q) F]
          [IsFractionRing (integralClosure R L ⧸ Q) F] (z : F),
        IsIntegral (integralClosure R L ⧸ Q) z →
        ∃ a s : integralClosure R L, s ∉ 𝔓 ∧
          algebraMap _ F (Ideal.Quotient.mk Q s) * z = algebraMap _ F (Ideal.Quotient.mk Q a))

example : TameBranchNormalCopy = SGRDirect.NVLocal.TameBranchNormal := rfl

theorem tameBranchNormalCopy : TameBranchNormalCopy := Abhyankar.tameBranchNormal

end AbhyankarScratch

#print axioms AbhyankarScratch.tameBranchNormalCopy

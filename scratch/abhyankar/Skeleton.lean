import ZInQKernel.Contrib.OneProof.SGRDirectNVLocal

open IsLocalRing HDec

noncomputable section

namespace Abhyankar

/-- The conclusion of `TameBranchNormal` for a ring `S`, a maximal ideal `𝔓`, a prime `Q ≤ 𝔓` over `𝔮`. -/
def BranchConcl {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (𝔮 : Ideal A) (𝔓 Q : Ideal S) : Prop :=
  (∀ Q' : Ideal S, Q'.IsPrime → Q'.under A = 𝔮 → Q' ≤ 𝔓 → Q' = Q) ∧
  (∀ (F : Type) [CommRing F] [Algebra (S ⧸ Q) F] [IsFractionRing (S ⧸ Q) F] (z : F),
    IsIntegral (S ⧸ Q) z →
    ∃ a s : S, s ∉ 𝔓 ∧ algebraMap _ F (Ideal.Quotient.mk Q s) * z = algebraMap _ F (Ideal.Quotient.mk Q a))

def TBNLocal : Prop :=
  ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsRegularLocalRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L], ringKrullDim A = 2 →
    ∀ f g : A, maximalIdeal A = Ideal.span {f, g} → (Ideal.span {f}).IsPrime →
    ∀ p : ℕ, p.Prime → (p : A) ∈ maximalIdeal A → Module.finrank K L < p →
    (∀ P : Ideal A, P.IsPrime → P.height = 1 → f ∉ P → g ∉ P →
      ∀ P' : Ideal (integralClosure A L), P'.IsPrime → P'.under A = P →
        P'.ramificationIdx A = 1) →
    ∀ 𝔓 : Ideal (integralClosure A L), 𝔓.IsMaximal →
    ∀ Q : Ideal (integralClosure A L), Q.IsPrime → Q.under A = Ideal.span {f} → Q ≤ 𝔓 →
      BranchConcl (Ideal.span {f}) 𝔓 Q

theorem tameBranchNormal_of_local (h : TBNLocal) : SGRDirect.NVLocal.TameBranchNormal := by
  sorry

def KummerBase : Prop :=
  ∀ (A Ω : Type) [CommRing A] [IsDomain A] [IsRegularLocalRing A] [Field Ω] [Algebra A Ω],
    Function.Injective (algebraMap A Ω) → ringKrullDim A = 2 →
    ∀ f g : A, maximalIdeal A = Ideal.span {f, g} →
    ∀ a b : ℕ, 0 < a → 0 < b → ∀ t u : Ω, t ^ a = algebraMap A Ω f → u ^ b = algebraMap A Ω g →
      IsRegularLocalRing (Algebra.adjoin A {t, u}) ∧ ringKrullDim (Algebra.adjoin A {t, u}) = 2 ∧
      (Ideal.span {(⟨t, Algebra.subset_adjoin (by simp)⟩ : Algebra.adjoin A {t, u}),
        ⟨u, Algebra.subset_adjoin (by simp)⟩}).IsMaximal

def KummerUnram : Prop :=
  ∀ (A K L Ω : Type) [CommRing A] [IsDomain A] [IsRegularLocalRing A] [Field K] [Field L] [Field Ω]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra L Ω] [Algebra K Ω] [Algebra A Ω]
    [IsScalarTower A K Ω] [IsScalarTower K L Ω] [FiniteDimensional L Ω], ringKrullDim A = 2 →
    ∀ f g : A, maximalIdeal A = Ideal.span {f, g} → (Ideal.span {f}).IsPrime →
    ∀ p : ℕ, p.Prime → (p : A) ∈ maximalIdeal A → Module.finrank K L < p →
    (∀ P : Ideal A, P.IsPrime → P.height = 1 → f ∉ P → g ∉ P →
      ∀ P' : Ideal (integralClosure A L), P'.IsPrime → P'.under A = P →
        P'.ramificationIdx A = 1) →
    ∀ t u : Ω, t ^ Module.finrank K L = algebraMap A Ω f → u ^ Module.finrank K L = algebraMap A Ω g →
    IntermediateField.adjoin L {t, u} = ⊤ →
      Module.Finite (Algebra.adjoin A {t, u}) (integralClosure (Algebra.adjoin A {t, u}) Ω) ∧
      ∀ Q : Ideal (integralClosure (Algebra.adjoin A {t, u}) Ω), [Q.IsPrime] → Q.height = 1 →
        Algebra.IsUnramifiedAt (Algebra.adjoin A {t, u}) Q

def EtaleBranch : Prop :=
  ∀ (B S' : Type) [CommRing B] [IsDomain B] [IsRegularLocalRing B] [CommRing S'] [IsDomain S']
    [Algebra B S'], ringKrullDim B = 2 → ∀ t u : B, maximalIdeal B = Ideal.span {t, u} → t ≠ 0 →
    Algebra.Etale B S' → Module.Finite B S' → Function.Injective (algebraMap B S') →
    ∀ 𝔓' : Ideal S', 𝔓'.IsMaximal →
    ∀ Q' : Ideal S', Q'.IsPrime → algebraMap B S' t ∈ Q' → Q' ≤ 𝔓' → Q' ≠ 𝔓' →
      (∀ Q'' : Ideal S', Q''.IsPrime → algebraMap B S' t ∈ Q'' → Q'' ≤ 𝔓' → Q'' ≠ 𝔓' → Q'' = Q') ∧
      (∀ (F : Type) [CommRing F] [Algebra (S' ⧸ Q') F] [IsFractionRing (S' ⧸ Q') F] (z : F),
        IsIntegral (S' ⧸ Q') z →
        ∃ a s : S', s ∉ 𝔓' ∧
          algebraMap _ F (Ideal.Quotient.mk Q' s) * z = algebraMap _ F (Ideal.Quotient.mk Q' a))

def BranchDescent : Prop :=
  ∀ (A K L Ω : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L] [Field Ω]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Algebra L Ω] [Algebra K Ω] [Algebra A Ω]
    [IsScalarTower A K Ω] [IsScalarTower K L Ω] [FiniteDimensional L Ω] [Algebra.IsSeparable L Ω]
    (A'' : Subalgebra A Ω), Algebra.IsIntegral A A'' → IsNoetherianRing (integralClosure A'' Ω) →
    ∀ 𝔮 : Ideal A, 𝔮.IsPrime →
    (∀ 𝔓' : Ideal (integralClosure A'' Ω), 𝔓'.IsMaximal →
      ∀ Q' : Ideal (integralClosure A'' Ω), Q'.IsPrime → Q'.under A = 𝔮 → Q' ≤ 𝔓' →
        BranchConcl 𝔮 𝔓' Q') →
    ∀ 𝔓 : Ideal (integralClosure A L), 𝔓.IsMaximal →
    ∀ Q : Ideal (integralClosure A L), Q.IsPrime → Q.under A = 𝔮 → Q ≤ 𝔓 →
      ((Module.finrank L Ω : ℕ) : integralClosure A L) ∉ 𝔓 → BranchConcl 𝔮 𝔓 Q

end Abhyankar

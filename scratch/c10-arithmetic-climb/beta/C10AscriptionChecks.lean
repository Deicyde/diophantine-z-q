import C10AscriptionCandidate

/-!
Independent guard for the source ascription.

The decisive evidence is (3): the SAME proof term `ClimbC10Ascription.originalC10WithFieldBeta`
is accepted at a type written out here in full, mentioning the real `GlueC10Link.rL`,
`MatrixUnits2`, `FrobSquares`, `IsFrobAt` and the original conclusion, without naming the
Expected definition anywhere.
-/

open GlueDescent GlueC10 PkgI3 GlueC10Link ClimbFieldAdapterExpected ClimbFieldAdapter
open ClimbC10Ascription

set_option linter.unusedVariables false

-- (1) by-name ascriptions against the frozen Expected
example : ClimbC10AscriptionExpected.OriginalC10WithFieldBeta := originalC10WithFieldBeta
example : ClimbC10AscriptionExpected.SlotsAreAdapterTheorems := slotsAreAdapterTheorems

-- (2) W2 written out
example : ∀ (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ),
    (∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) → ε₀ 1 1 = 1 →
    (∀ g h, betaField β₀ g * betaField β₀ h = epsField ε₀ g h * betaField β₀ (g * h)) ∧
    (∀ g, betaField β₀ g ≠ 0) ∧ betaField β₀ 1 = 1 := slotsAreAdapterTheorems

-- (3) W1 written out in full, over the REAL Link objects, without naming the Expected def
example : ∀ (hC : ChebotarevExists) (hBN : BrauerNesbittChar0) (hM : CharPolyIndepOfEll)
    (S : Finset ℕ) (h3S : 3 ∈ S) (h5S : 5 ∈ S)
    (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ)
    (hco : ∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) (hε1 : ε₀ 1 1 = 1)
    (c : GQ → GQ → GlueC10.Qbar) (a : GQ → GlueC10.Qbar)
    (ha : ∀ g h, a g * a h * c g h = epsField ε₀ g h * a (g * h))
    (ha1 : a 1 = 1) (af : ℕ → GlueC10.Qbar)
    (k₅ V₅ W₅ : Type) [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : GlueC10.Qbar →+* k₅)
    (T₅ : GQ → Module.End k₅ V₅) (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h))
    (hT₅1 : T₅ 1 = 1) (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    (r₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ u₅.W
        (rL c (epsField ε₀) a (betaField β₀) ha (fieldCochain β₀ ε₀ hco) (fieldNonzero β₀)
          ha1 (fieldNormalizedAtOne β₀ ε₀ hco hε1) ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) =
        LinearMap.trace k₅ W₅ (r₅ g))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ W₅ (r₅ g) = ι₅ (af p))
    (k₃ V₃ W₃ ιI κ : Type) [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃] [TopologicalSpace k₃]
    [IsTopologicalRing k₃] [T2Space k₃] [AddCommGroup V₃] [Module k₃ V₃]
    [FiniteDimensional k₃ V₃] [AddCommGroup W₃] [Module k₃ W₃] [FiniteDimensional k₃ W₃]
    [Fintype ιI] [DecidableEq ιI] [Fintype κ] [DecidableEq κ] (ι₃ : GlueC10.Qbar →+* k₃)
    (T₃ : GQ → Module.End k₃ V₃) (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h))
    (hT₃1 : T₃ 1 = 1) (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (bV : Module.Basis ιI k₃ u₃.W) (bW : Module.Basis κ k₃ W₃) (r₃ : Representation k₃ GQ W₃)
    (hrc : Continuous fun g =>
      LinearMap.toMatrix bV bV
        (rL c (epsField ε₀) a (betaField β₀) ha (fieldCochain β₀ ε₀ hco) (fieldNonzero β₀)
          ha1 (fieldNormalizedAtOne β₀ ε₀ hco hε1) ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (r₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k₃ GQ)
      (rL c (epsField ε₀) a (betaField β₀) ha (fieldCochain β₀ ε₀ hco) (fieldNonzero β₀)
        ha1 (fieldNormalizedAtOne β₀ ε₀ hco hε1) ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k₃ GQ) r₃.asModule)
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₃ W₃ (r₃ g) = ι₃ (af p))
    (hSq : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      ∃ (L : Type) (_ : Field L) (k : Type) (_ : Field k), CharP k p ∧
        ∃ (A Aσ : AbVar L) (mu : AbVar.Hom Aσ A) (Ab Ab' : AbVar k) (F : AbVar.Hom Ab Ab')
          (mub : AbVar.Hom Ab' Ab) (N : ℕ), N ≠ 0 ∧
          FrobSquares 3 mu F mub (T₃ g) N ∧ FrobSquares 5 mu F mub (T₅ g) N),
    Nonempty
      ((rL c (epsField ε₀) a (betaField β₀) ha (fieldCochain β₀ ε₀ hco) (fieldNonzero β₀)
          ha1 (fieldNormalizedAtOne β₀ ε₀ hco hε1) ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule
        ≃ₗ[MonoidAlgebra k₃ GQ] r₃.asModule) :=
  originalC10WithFieldBeta

-- (4) the real theorem is what was applied: its own type still elaborates here
#check @GlueC10Link.c10_of_squares

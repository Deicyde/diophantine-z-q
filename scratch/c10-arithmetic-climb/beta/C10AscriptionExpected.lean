import ZInQKernel.HDecomp.C10.Link
import FieldAdapterCandidate

/-!
# EXPECTED WRAPPER — source ascription against the ACTUAL #62 `c10_of_squares`

**DEFINITIONS ONLY. No proofs, no candidate.** Submitted for the independent freeze before
any proof bytes, as with every earlier lane.

This replaces the hand-copied binder shapes of `FieldAdapterBinderShape.lean` (`6badddb0…`,
retained unchanged) with a statement that mentions the REAL theorem's objects: the module
`ZInQKernel.HDecomp.C10.Link` is imported from the parent's read-only replay prefix
`/tmp/issue37-consolidation-a23f44c9/scaled/semisimplicity/independent-review/replay/lp2`,
whose `Link.olean` was compiled from the exact frozen #62 source (`0c72f9e5…`).

Shape: every premise of `GlueC10Link.c10_of_squares` is reproduced **unaltered** and
universally quantified, with exactly three changes and no others:

* `C` is instantiated by the literal `GlueC10.Qbar` (an ASCRIPTION; the consumer's `C` is not
  thereby selected, and no global tuple is chosen);
* `β` and `ε` are instantiated by the field specializations `betaField β₀`, `epsField ε₀` of
  GIVEN units-valued data;
* the three β-side slots `hβ`, `hβ0`, `hβ1` are filled by the already-compiled adapter
  theorems — `hβ1` only via `ε₀ 1 1 = 1`, which is an explicit premise here.

Everything else — `hC`, `hBN`, `hM`, `S`, `h3S`, `h5S`, `c`, `a`, `ha`, `ha1`, `af`, the
`ℓ = 5` block, the `ℓ = 3` block, `bV`, `bW`, `ρ₃`, `hrc`, `hρc`, `hr`, `hρ`, `hρ₃`, `hSq` —
is passed through exactly, with no placeholder and no weakening. The conclusion is the
original conclusion.

**This is conditional.** It does NOT prove C10: every arithmetic premise above is still a
hypothesis, and no `μ`, degree, Tate, `Ψ`, `E`, `T`, `α`, `χ` or `af` datum is constructed
anywhere in this lane.
-/

noncomputable section

open GlueDescent GlueC10 PkgI3 GlueC10Link ClimbFieldAdapterExpected

namespace ClimbC10AscriptionExpected

-- a `Prop` telescope never references its own binder names; keep the names, silence the linter
set_option linter.unusedVariables false

/-- **W1 — the original `c10_of_squares`, with only the three β-side slots filled.**
The premise names are kept for readability; the unused-variable linter is silenced for this
statement because a `Prop` telescope never references its own binder names. -/
def OriginalC10WithFieldBeta : Prop :=
  ∀ (hC : ChebotarevExists) (hBN : BrauerNesbittChar0) (hM : CharPolyIndepOfEll)
    (S : Finset ℕ) (h3S : 3 ∈ S) (h5S : 5 ∈ S)
    -- the GIVEN units-valued datum and its explicit normalization
    (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ)
    (hco : ∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) (hε1 : ε₀ 1 1 = 1)
    -- the remaining scalar data, unaltered
    (c : GQ → GQ → GlueC10.Qbar) (a : GQ → GlueC10.Qbar)
    (ha : ∀ g h, a g * a h * c g h = epsField ε₀ g h * a (g * h))
    (ha1 : a 1 = 1) (af : ℕ → GlueC10.Qbar)
    -- ℓ = 5, unaltered
    (k₅ V₅ W₅ : Type) [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : GlueC10.Qbar →+* k₅)
    (T₅ : GQ → Module.End k₅ V₅) (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h))
    (hT₅1 : T₅ 1 = 1) (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    (r₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ u₅.W
        (rL c (epsField ε₀) a (betaField β₀) ha
          (ClimbFieldAdapter.fieldCochain β₀ ε₀ hco)
          (ClimbFieldAdapter.fieldNonzero β₀) ha1
          (ClimbFieldAdapter.fieldNormalizedAtOne β₀ ε₀ hco hε1)
          ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) =
        LinearMap.trace k₅ W₅ (r₅ g))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ W₅ (r₅ g) = ι₅ (af p))
    -- ℓ = 3, unaltered
    (k₃ V₃ W₃ ιI κ : Type) [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃] [TopologicalSpace k₃]
    [IsTopologicalRing k₃] [T2Space k₃] [AddCommGroup V₃] [Module k₃ V₃]
    [FiniteDimensional k₃ V₃] [AddCommGroup W₃] [Module k₃ W₃] [FiniteDimensional k₃ W₃]
    [Fintype ιI] [DecidableEq ιI] [Fintype κ] [DecidableEq κ] (ι₃ : GlueC10.Qbar →+* k₃)
    (T₃ : GQ → Module.End k₃ V₃) (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h))
    (hT₃1 : T₃ 1 = 1) (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (bV : Module.Basis ιI k₃ u₃.W) (bW : Module.Basis κ k₃ W₃) (r₃ : Representation k₃ GQ W₃)
    (hrc : Continuous fun g =>
      LinearMap.toMatrix bV bV
        (rL c (epsField ε₀) a (betaField β₀) ha
          (ClimbFieldAdapter.fieldCochain β₀ ε₀ hco)
          (ClimbFieldAdapter.fieldNonzero β₀) ha1
          (ClimbFieldAdapter.fieldNormalizedAtOne β₀ ε₀ hco hε1)
          ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (r₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k₃ GQ)
      (rL c (epsField ε₀) a (betaField β₀) ha
        (ClimbFieldAdapter.fieldCochain β₀ ε₀ hco)
        (ClimbFieldAdapter.fieldNonzero β₀) ha1
        (ClimbFieldAdapter.fieldNormalizedAtOne β₀ ε₀ hco hε1)
        ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k₃ GQ) r₃.asModule)
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₃ W₃ (r₃ g) = ι₃ (af p))
    (hSq : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      ∃ (L : Type) (_ : Field L) (k : Type) (_ : Field k), CharP k p ∧
        ∃ (A Aσ : AbVar L) (mu : AbVar.Hom Aσ A) (Ab Ab' : AbVar k) (F : AbVar.Hom Ab Ab')
          (mub : AbVar.Hom Ab' Ab) (N : ℕ), N ≠ 0 ∧
          FrobSquares 3 mu F mub (T₃ g) N ∧ FrobSquares 5 mu F mub (T₅ g) N),
    Nonempty
      ((rL c (epsField ε₀) a (betaField β₀) ha
          (ClimbFieldAdapter.fieldCochain β₀ ε₀ hco)
          (ClimbFieldAdapter.fieldNonzero β₀) ha1
          (ClimbFieldAdapter.fieldNormalizedAtOne β₀ ε₀ hco hε1)
          ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule ≃ₗ[MonoidAlgebra k₃ GQ] r₃.asModule)

/-- **W2 — the slot-filling is exactly the adapter's, not a re-derivation.** States that the
three filled slots are the adapter theorems applied to the GIVEN units datum. -/
def SlotsAreAdapterTheorems : Prop :=
  ∀ (β₀ : GQ → GlueC10.Qbarˣ) (ε₀ : GQ → GQ → GlueC10.Qbarˣ)
    (hco : ∀ g h, β₀ g * β₀ h = ε₀ g h * β₀ (g * h)) (hε1 : ε₀ 1 1 = 1),
    (∀ g h, betaField β₀ g * betaField β₀ h = epsField ε₀ g h * betaField β₀ (g * h)) ∧
    (∀ g, betaField β₀ g ≠ 0) ∧ betaField β₀ 1 = 1

end ClimbC10AscriptionExpected

/-! ## Elaboration checks — definitions only -/

#check @ClimbC10AscriptionExpected.OriginalC10WithFieldBeta
#check @ClimbC10AscriptionExpected.SlotsAreAdapterTheorems
#check @GlueC10Link.c10_of_squares

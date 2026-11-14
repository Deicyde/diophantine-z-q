import C10AscriptionExpected

/-!
# Candidate: source ascription against the ACTUAL `GlueC10Link.c10_of_squares`

PRIVATE CANDIDATE. Proves `ClimbC10AscriptionExpected.OriginalC10WithFieldBeta` (W1) and
`SlotsAreAdapterTheorems` (W2) against the FROZEN Expected
(`C10AscriptionExpected.lean`, sha256
241d35a499ef8e086c6761168504df625d96f7ea2280fcf01fa4b205683961d3), which is imported as
compiled and NOT edited.

W1 is discharged by APPLYING the real theorem `GlueC10Link.c10_of_squares` to its full
telescope of actual objects — no hand-copied restatement — with `C := GlueC10.Qbar` and the
three β-side slots filled by the already-compiled adapter theorems. Every other premise is
passed straight through from the caller.

**Conditional, and not a C10 proof.** `hC`, `hBN`, `hM`, the Frobenius squares `hSq`,
continuity `hrc`/`hρc`, semisimplicity `hr`/`hρ`, the modular traces `h₅`/`hρ₅`/`hρ₃` and all
remaining data stay hypotheses of the statement. Nothing is constructed here: no B2, no global
abelian-variety datum, no Tate module, no degrees, no preimages, no LC/continuity, no
arithmetic input. `C := GlueC10.Qbar` is an ascription; the consumer's `C` is not selected.
-/

noncomputable section

open GlueDescent GlueC10 PkgI3 GlueC10Link ClimbFieldAdapterExpected ClimbFieldAdapter

namespace ClimbC10Ascription

theorem slotsAreAdapterTheorems : ClimbC10AscriptionExpected.SlotsAreAdapterTheorems :=
  fun β₀ ε₀ hco hε1 =>
    ⟨fieldCochain β₀ ε₀ hco, fieldNonzero β₀, fieldNormalizedAtOne β₀ ε₀ hco hε1⟩

theorem originalC10WithFieldBeta : ClimbC10AscriptionExpected.OriginalC10WithFieldBeta := by
  intro hC hBN hM S h3S h5S β₀ ε₀ hco hε1 c a ha ha1 af
  intro k₅ V₅ W₅ i1 i2 i3 i4 i5 i6 i7 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ r₅ h₅ hρ₅
  intro k₃ V₃ W₃ ιI κ j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 j16
  intro ι₃ T₃ hT₃ hT₃1 u₃ hu₃ bV bW r₃ hrc hρc hr hρ hρ₃ hSq
  exact GlueC10Link.c10_of_squares hC hBN hM S h3S h5S GlueC10.Qbar c (epsField ε₀) a
    (betaField β₀) ha (fieldCochain β₀ ε₀ hco) (fieldNonzero β₀) ha1
    (fieldNormalizedAtOne β₀ ε₀ hco hε1) af
    k₅ V₅ W₅ ι₅ T₅ hT₅ hT₅1 u₅ hu₅ r₅ h₅ hρ₅
    k₃ V₃ W₃ ιI κ ι₃ T₃ hT₃ hT₃1 u₃ hu₃ bV bW r₃ hrc hρc hr hρ hρ₃ hSq

end ClimbC10Ascription

/-! ## Reports -/

#print axioms ClimbC10Ascription.slotsAreAdapterTheorems
#print axioms ClimbC10Ascription.originalC10WithFieldBeta

#check @ClimbC10Ascription.slotsAreAdapterTheorems
#check @ClimbC10Ascription.originalC10WithFieldBeta

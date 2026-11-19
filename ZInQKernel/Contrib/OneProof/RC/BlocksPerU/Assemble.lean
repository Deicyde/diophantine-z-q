import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Descent
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Sieve

/-! The conditional per-pool realization with the analytic and arithmetic
inputs at their source levels. -/

noncomputable section

namespace ZInQ.Manuscript.RC.BlocksPerU

open ThetaCoeff O12Formwise AddressGenuine PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {I J K O L : Type} [Fintype I] [Field K] [TopologicalSpace K]
  [CommRing O] [IsDomain O] [CharZero O] [Algebra O K] [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {avoid : Finset ℕ} {frob : ℕ → GalQ}
variable {M W R : ℕ} {S : AppF.ThetaStage (Odd.StageRing O M)} {δ : ℤ} {adm : ℕ → Prop}
variable {P : Window T.Good S W} {E : Lift S}
variable {N : ℕ} [NeZero N]

/-- The four consumer inputs are obtained together from the weighted old
theta law, its moving and unary laws, the ordinary theta law, a complex
constituent span, and attachments at the intrinsic source levels. -/
theorem realize_of_stage (Dₗ : LevelSetup P avoid N) (D : Divisions E δ W R adm)
    (η : (ZMod N)ˣ →* Oˣ) (η_eval : ∀ u, (η u : O) = E.η (representative u))
    (η_order : ∀ u, ∃ e : ℕ, (η u : O) ^ (2 ^ e : ℕ) = 1)
    (hodd : let C := diamondCharacters Dₗ.common_four η η_eval η_order
            (C.η C.minusOne : O) * ((C.symbol (-1) C.minusOne : ℤ) : O) ^ E.parity.val = -1)
    (κ : K →+* ℂ) (X : Inventory I J K T N) (hspan : SpansOverComplex X κ)
    (hOld : OldStageLaw κ Dₗ (diamondCharacters Dₗ.common_four η η_eval η_order))
    (hSieve : MovingSieveLaw κ Dₗ (diamondCharacters Dₗ.common_four η η_eval η_order))
    (hθ : OrdinaryThetaLaw)
    (hUnary : UnaryStageLaw κ Dₗ (diamondCharacters Dₗ.common_four η η_eval η_order))
    (H : ∀ s : J, SourceAttachment (X.sourceLevel s) frob (X.source s))
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q) :
    ∃ (A : Basis I K (ZMod N)ˣ (Test T avoid)) (C : DiamondCharacters O (ZMod N)ˣ E.η)
      (V : Blocks (P := P) A E D C) (ρ₀ : Attachment A frob)
      (levels : BlockLevels V), AtLevel levels ρ₀ :=
  realize Dₗ D η η_eval η_order hodd κ X (spansAt_of_complex X κ hspan)
    (blockModularity_of_stage κ Dₗ D _ hOld hSieve hθ hUnary) H hfrob

#print axioms realize_of_stage

end ZInQ.Manuscript.RC.BlocksPerU

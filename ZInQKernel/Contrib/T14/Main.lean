import ZInQKernel.Contrib.BrauerT14T15.Main
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Index

/-!
# Leaf T14 (T14a′ and T14b′, cochain forms) proved outright

Task t1415-tc reduced the Brauer–Hasse–Noether leaves T14a′ (`PkgI6.BrauerHasse2C`) and T14b′
(`PkgI6.BrauerReciprocity2C`) to the single Prop
`ZInQ.Contrib.BrauerT14T15.KummerIndexBound`, the Kummer case of the second fundamental inequality
of global class field theory: `[C_F : N_{L/F} C_L] ≤ p` for a Galois extension `L/F` of number
fields of prime degree `p` with `μ_p ⊂ F` (Milne, *Class Field Theory*, VII §6; locator
UNVERIFIED).

Tau Ceti (commit 97a5b235, module `Global.Kummer.Index`, backported by task kw-new) proves this
statement as `TauCeti.ClassFieldTheory.index_range_ideleClassNormMap_le_of_finrank_prime`, about
the same objects: Mathlib's idele class group and Tau Ceti's norm map
`GlobalNumberFields.ideleClassNormMap`. So `KummerIndexBound` holds, and T14a′, T14b′ (and T15′,
proved by t1415-tc) follow through `leaves_of_kummerIndexBound`.
-/

namespace ZInQ.Contrib.T14

open PkgI6 ZInQ.Contrib.BrauerT14T15

/-- **The Kummer case of the second fundamental inequality** (the hypothesis of t1415-tc's
reduction), from Tau Ceti's `index_range_ideleClassNormMap_le_of_finrank_prime`. -/
theorem kummerIndexBound : KummerIndexBound :=
  fun F L _ _ _ _ _ _ p _ _ hfin =>
    TauCeti.ClassFieldTheory.index_range_ideleClassNormMap_le_of_finrank_prime F L p hfin

/-- **Leaf T14a′** (the Hasse principle for `Br(ℚ)[2]`, cochain form). -/
theorem brauerHasse2C : BrauerHasse2C :=
  (leaves_of_kummerIndexBound kummerIndexBound).1

/-- **Leaf T14b′** (Hilbert reciprocity / the sum formula for `Br(ℚ)[2]`, cochain form). -/
theorem brauerReciprocity2C : BrauerReciprocity2C :=
  (leaves_of_kummerIndexBound kummerIndexBound).2.1

/-- T14a′, T14b′ and T15′ together, with no hypothesis. -/
theorem leaves_T14_T15 : BrauerHasse2C ∧ BrauerReciprocity2C ∧ LocalH2CardC :=
  leaves_of_kummerIndexBound kummerIndexBound

/-- The kernel's Brauer step of B2 (`PkgI6.cob_of_same_finite_support`) with all three leaves
discharged. -/
theorem cob_of_same_finite_support'
    (ε₁ ε₂ : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2)
    (c₁ : IsCocycle2 ε₁) (c₂ : IsCocycle2 ε₂)
    (hsame : ∀ (p : ℕ) [Fact p.Prime],
      IsCoboundary2 (resC ℚ_[p] ε₁) ↔ IsCoboundary2 (resC ℚ_[p] ε₂)) :
    IsCoboundary2 (ε₁ - ε₂) :=
  cob_of_same_finite_support_of_kummerIndexBound kummerIndexBound ε₁ ε₂ c₁ c₂ hsame

end ZInQ.Contrib.T14

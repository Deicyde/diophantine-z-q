import ZInQKernel.Contrib.BrauerT14T15.T15
import ZInQKernel.Contrib.BrauerT14T15.GlobalT14

/-!
# Leaves T14 and T15 (cochain forms) from Tau Ceti: summary

* **T15** (`PkgI6.LocalH2CardC`): proved outright, `ZInQ.Contrib.BrauerT14T15.localH2CardC`.
* **T14a′** (`PkgI6.BrauerHasse2C`) and **T14b′** (`PkgI6.BrauerReciprocity2C`): proved from
  Tau Ceti's Brauer-group statements for `ℚ` (`brauerHasse2C_of_injective`,
  `brauerReciprocity2C_of_sum`), and hence from the single Prop `KummerIndexBound`, the Kummer case
  of the second inequality of global class field theory, which is the hypothesis under which the
  vendored Tau Ceti proves the Hasse principle and the sum formula.

So the three textbook leaves T14a′, T14b′, T15′ of the H decomposition reduce to the one
literature statement `KummerIndexBound` (`leaves_of_kummerIndexBound`).
-/

namespace ZInQ.Contrib.BrauerT14T15

open PkgI6

/-- **T14a′, T14b′ and T15′ from the Kummer case of the second inequality.** -/
theorem leaves_of_kummerIndexBound (h : KummerIndexBound) :
    BrauerHasse2C ∧ BrauerReciprocity2C ∧ LocalH2CardC :=
  ⟨brauerHasse2C_of_kummerIndexBound h, brauerReciprocity2C_of_kummerIndexBound h, localH2CardC⟩

/-- The consumer of the three leaves in the kernel (`PkgI6.cob_of_same_finite_support`, the Brauer
step of B2), with the leaves discharged from `KummerIndexBound`. -/
theorem cob_of_same_finite_support_of_kummerIndexBound (h : KummerIndexBound)
    (ε₁ ε₂ : Field.absoluteGaloisGroup ℚ → Field.absoluteGaloisGroup ℚ → ZMod 2)
    (c₁ : IsCocycle2 ε₁) (c₂ : IsCocycle2 ε₂)
    (hsame : ∀ (p : ℕ) [Fact p.Prime],
      IsCoboundary2 (resC ℚ_[p] ε₁) ↔ IsCoboundary2 (resC ℚ_[p] ε₂)) :
    IsCoboundary2 (ε₁ - ε₂) :=
  cob_of_same_finite_support (brauerHasse2C_of_kummerIndexBound h)
    (brauerReciprocity2C_of_kummerIndexBound h) localH2CardC ε₁ ε₂ c₁ c₂ hsame

end ZInQ.Contrib.BrauerT14T15

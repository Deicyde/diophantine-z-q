import ZInQKernel.Contrib.OneProof.FowlerUnique
import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.FromOesterlePrinted

/-! # Fowler's Proposition 2·7 from Oesterlé's effective class-number bound

`FowlerProp27PrintCanonical` follows from `OesterleTheorem1Printed`, the printed form of
Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki
1983/84, Exposé 631, Astérisque 121–122 (1985), Theorem 1, p. 310, with the constant
`C = 7000`, which §5.1, p. 321, takes from the unread reference [Ce]. Oesterlé's statement
is the stronger one: this file records the implication and does not replace the Fowler
hypothesis. The conductor product, the unit-index bounds and the genus divisibility used in
Fowler's argument are proved in `FowlerDiscriminantBound`. -/

namespace HDec.CMBranch.FowlerBridges

open FowlerArithmetic TauCeti.GlobalNumberFields

/-- Fowler, Proposition 2·7, p. 615, in the canonical discriminant form, from the printed
Oesterlé estimate for imaginary quadratic fields. No other input is used. -/
theorem fowlerProp27PrintCanonical_of_oesterlePrinted (h : OesterleTheorem1Printed.{0}) :
    FowlerProp27PrintCanonical := by
  apply fowlerProp27Print_iff_canonical.mp
  intro Δ _ _ K _ _ _ hk O hO n hn hClass
  have hcard : properClassNumber O = Nat.card (Pic O) :=
    Nat.card_congr (properIdealClassesEquivClassGroup O hk)
  exact hO ▸ fowler_bound_of_oesterle_printed h O hk n hn (hcard ▸ hClass)

end HDec.CMBranch.FowlerBridges

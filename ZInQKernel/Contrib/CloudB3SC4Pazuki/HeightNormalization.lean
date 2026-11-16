import ZInQKernel.OneProof.H.TailY
import Mathlib.NumberTheory.Height.NumberField

/-!
# Coordinate count and height normalization for the Pazuki source reading

Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012),
pp. 25 and 30–31, uses all `r^(2*g)` constants with both characteristics in
`{0, 1/r, ..., (r-1)/r}^g`. At `g = r = 2` this is the repository's `Char2`.
His height is Euclidean at the infinite places, with the usual local
multiplicities, and uses the maximum at the finite places.

These theorems only check those two aspects of the existing definitions.
They do not prove `ZInQ.HeightSplit.PazukiCor13Upper`, do not assume a
comparison theorem, and supply no new hypothesis to the single proof.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3SC4Pazuki

open NumberField

/-- Both binary characteristics are present: there are sixteen coordinates,
not the four second-order theta constants for the square of a principal bundle. -/
theorem theta_characteristics_card : Fintype.card ZInQ.LeafPush2.Char2 = 16 := by
  norm_num [ZInQ.LeafPush2.Char2, Fintype.card_prod, Fintype.card_fun]

/-- The actual multiplicative Euclidean height has the usual infinite-place
multiplicities. This is a definitional normalization check, not a height bound. -/
theorem mulHeightL2_eq_places {F : Type*} [Field F] [NumberField F]
    {Idx : Type*} [Fintype Idx] (z : Idx → F) (hz : z ≠ 0) :
    ZInQ.HeightSplit.mulHeightL2 z =
      (∏ v : InfinitePlace F, (Real.sqrt (∑ i, v (z i) ^ 2)) ^ v.mult) *
        ∏ᶠ v : FinitePlace F, ⨆ i, v (z i) := by
  simp only [ZInQ.HeightSplit.mulHeightL2, hz, ite_false]
  exact congrArg₂ (fun (a b : ℝ) => a * b)
    (NumberField.prod_archAbsVal_eq (K := F) (fun v => Real.sqrt (∑ i, v (z i) ^ 2)))
    (NumberField.prod_nonarchAbsVal_eq (K := F) (fun v => ⨆ i, v (z i)))

/-- Dividing by the number-field degree gives the absolute logarithmic
Euclidean height printed in Pazuki's definition of the theta height. -/
theorem absLogHeightL2_eq_places {F : Type*} [Field F] [NumberField F]
    {Idx : Type*} [Fintype Idx] (z : Idx → F) (hz : z ≠ 0) :
    ZInQ.HeightSplit.absLogHeightL2 z =
      Real.log ((∏ v : InfinitePlace F, (Real.sqrt (∑ i, v (z i) ^ 2)) ^ v.mult) *
        ∏ᶠ v : FinitePlace F, ⨆ i, v (z i)) / Module.finrank ℚ F := by
  rw [ZInQ.HeightSplit.absLogHeightL2, mulHeightL2_eq_places z hz]

end ZInQ.Contrib.CloudB3SC4Pazuki

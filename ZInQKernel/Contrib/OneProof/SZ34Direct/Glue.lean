import ZInQKernel.Contrib.OneProof.SZ34Direct.Statement
import ZInQKernel.Contrib.OneProof.SZ34Direct.NeronExistence

/-!
# The glue: `SilverbergZarhinThm34Given` and the open hypothesis are equivalent

* `silverbergZarhinThm34_of_given`: the row with the Néron model given proves the open hypothesis
  `SZRaynaud.SilverbergZarhinThm34`. At an extension `V` of `O` to the finite Galois extension `E`,
  `V` is a discrete valuation ring (`SZRaynaud.isDiscreteValuationRing_of_finite_separable`), a
  Néron model exists (`SZ34Direct.exists_neron_groupModelO`, proved), and the row makes it
  semistable.
* `given_of_silverbergZarhinThm34`: conversely, the open hypothesis gives the row, because
  semistability passes between Néron models
  (`SZRaynaud.isSemistableResT_of_hasSemistableReductionSZ`, through the canonical isomorphism of
  Néron models).

So the replacement is neither stronger nor weaker than the hypothesis it replaces
(`silverbergZarhinThm34Given_iff`), and the open count does not change: one statement replaces
one, and Néron-model existence is a Lean theorem.
-/

noncomputable section

namespace SZ34Direct

/-- **The open hypothesis from the row with the Néron model given** (existence of the Néron model
is proved in Lean). -/
theorem silverbergZarhinThm34_of_given (h : SilverbergZarhinThm34Given) :
    SZRaynaud.SilverbergZarhinThm34 := by
  intro K _ O _ A
  obtain ⟨E, hfin, hgal, hs⟩ := h K O A
  refine ⟨E, hfin, hgal, fun V hV => ?_⟩
  have : IsDiscreteValuationRing V :=
    SZRaynaud.isDiscreteValuationRing_of_finite_separable O V hV
  obtain ⟨𝒩, h𝒩⟩ := exists_neron_groupModelO V (A.baseChange E)
  exact ⟨𝒩, h𝒩, hs V hV 𝒩 h𝒩⟩

/-- **The row with the Néron model given from the open hypothesis** (uniqueness of Néron models). -/
theorem given_of_silverbergZarhinThm34 (h : SZRaynaud.SilverbergZarhinThm34) :
    SilverbergZarhinThm34Given := by
  intro K _ O _ A
  obtain ⟨E, hfin, hgal, hs⟩ := h K O A
  exact ⟨E, hfin, hgal, fun V hV 𝒩 h𝒩 =>
    SZRaynaud.isSemistableResT_of_hasSemistableReductionSZ 𝒩 h𝒩 (hs V hV)⟩

/-- The two statements are equivalent. -/
theorem silverbergZarhinThm34Given_iff :
    SilverbergZarhinThm34Given ↔ SZRaynaud.SilverbergZarhinThm34 :=
  ⟨silverbergZarhinThm34_of_given, given_of_silverbergZarhinThm34⟩

end SZ34Direct

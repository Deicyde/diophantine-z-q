import ZInQKernel.Contrib.OneProof.SZThm35.Thm35
import ZInQKernel.Contrib.OneProof.NeronDVR.RelativeSquare
import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsDVRReduction

/-!
# Silverberg–Zarhin, Theorem 3.4, as printed: semistable reduction of the Néron model, which is presupposed

The row `silverbergZarhinThm34` (`SZRaynaud.SilverbergZarhinThm34`) states Grothendieck's semistable reduction theorem
through `SZRaynaud.HasSemistableReductionSZ`, which is existential: it asserts that a Néron model exists over each
prolongation of the valuation, and that it has semistable reduction. Silverberg–Zarhin's notion of semistable reduction
(Def. 3.1, p. 405) is a property of the Néron model, whose existence the print presupposes (§3, pp. 404–405). The human
readings of 2026-11-26 (CheyLoveday) rated the row a consequence for exactly this reason and noted that a restatement
taking the Néron model as given would be a direct instance.

* `SilverbergZarhinThm34Printed`: that restatement. Every Néron model over every prolongation has semistable reduction,
  the reading of "the Néron model" used by `SZRaynaud.SilverbergZarhinThm35` (Néron models are unique up to unique
  isomorphism: `SZRaynaud.isIso_neronModelComparison_of_neron`).
* `silverbergZarhinThm34Printed_of_row`: the row implies the leaf (semistability passes between Néron models,
  `SZRaynaud.isSemistableResT_of_hasSemistableReductionSZ`), so the leaf is not stronger than the row.
* `silverbergZarhinThm34_of_printed`: the leaf implies the row, with Néron-model existence over each prolongation, which
  is a discrete valuation ring (`SZRaynaud.isDiscreteValuationRing_of_finite_separable`): BLR §1.4 Thm 3, proved in the
  tree (`NeronDVR.neronSchemeExtensionDedekind_proof`, specialized by
  `ZInQ.FaltingsRestate.neronSchemeModelExistsDVR_of_dedekind`).
* `silverbergZarhinThm34_iff_printed`: the two are equivalent.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace ZInQ.OneProof.SZ34Printed

/-- **Silverberg–Zarhin, *Semistable reduction and torsion subgroups of abelian varieties*, Ann. Inst. Fourier 45
(1995), 403–420, Theorem 3.4, pp. 405–406** (printed form; proof in the print: "See Proposition 3.6 of [7]", SGA 7 I,
Exp. IX, Th. 3.6):

* Theorem 3.4, pp. 405–406: "(Semistable reduction theorem-Grothendieck). — Suppose X is an abelian variety over a
  field F and v is a discrete valuation on F. Then there is a finite Galois extension L of F such that X has
  semistable reduction at the extensions of v to L."
* Definition 3.1, p. 405: "If X is an abelian variety over a field F, and v is a discrete valuation on F, then X has
  […] (ii) semistable reduction at v if X_v^0 is an extension of an abelian variety by an affine torus".
* §3, pp. 404–405: "Suppose X is an abelian variety over a field F, and v is a discrete valuation on F with residue
  field k and valuation ring R. The Néron model 𝒳 of X at v is a smooth separated model of X over R such that for every
  smooth scheme 𝒴 over R and morphism f : 𝒴 ⊗_R F → X over F there is a unique morphism f_R : 𝒴 → 𝒳 over R which
  extends f. The generic fiber of 𝒳 can be canonically identified with X, and 𝒳 is a commutative group scheme over R
  whose group structure extends that of X. Let X_v = 𝒳 ⊗_R k and let X_v^0 denote the identity component of the
  special fiber X_v."

Lean form: `F = K` with the discrete valuation ring `O`; `L = E` a finite Galois extension of `K` inside the fixed
algebraic closure; "the extensions of v to L" are the valuation subrings `V` of `E` lying over `O`; "X has semistable
reduction at w" is read for the Néron model 𝒳 of `A_E` over `V`, presupposed by the print, as: every Néron model
(`ReductSplit.GroupModelO` with `IsNeronModel`: smooth, separated, quasi-compact, with the Néron mapping
property for smooth schemes) has special fibre whose identity component is an extension of an abelian variety
by a torus over the residue field (`DictModels.RaynaudOr.IsSemistableResT`; Def. 3.1(ii)). Reading steps: the
embedding of `L` into a fixed algebraic closure is a choice; "the Néron model" is read as "every Néron model". -/
def SilverbergZarhinThm34Printed : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K),
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧ IsGalois K E ∧
      ∀ V : ValuationSubring E, V.comap (algebraMap K E) = O →
        ∀ 𝒩 : ReductSplit.GroupModelO (A.baseChange E) V, 𝒩.IsNeronModel →
          DictModels.RaynaudOr.IsSemistableResT 𝒩

/-- The row implies the printed leaf: semistability over the residue field passes to every Néron model. So the leaf is
not stronger than the row. -/
theorem silverbergZarhinThm34Printed_of_row (h : SZRaynaud.SilverbergZarhinThm34) :
    SilverbergZarhinThm34Printed := by
  intro K _ O _ A
  obtain ⟨E, hfin, hgal, hs⟩ := h K O A
  exact ⟨E, hfin, hgal, fun V hV 𝒩 h𝒩 =>
    SZRaynaud.isSemistableResT_of_hasSemistableReductionSZ 𝒩 h𝒩 (hs V hV)⟩

/-- Néron models exist over every discrete valuation ring, for every abelian variety over its fraction field. -/
def NeronGroupModelsExist : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O] (A : PkgI3.AbVar K),
    ∃ 𝒩 : ReductSplit.GroupModelO A O, 𝒩.IsNeronModel

/-- The printed leaf implies the row, given Néron models over the prolongations (each a discrete valuation ring). -/
theorem silverbergZarhinThm34_of_printed_of_exists (h : SilverbergZarhinThm34Printed)
    (hN : NeronGroupModelsExist) : SZRaynaud.SilverbergZarhinThm34 := by
  intro K _ O _ A
  obtain ⟨E, hfin, hgal, hs⟩ := h K O A
  refine ⟨E, hfin, hgal, fun V hV => ?_⟩
  have : IsDiscreteValuationRing V := SZRaynaud.isDiscreteValuationRing_of_finite_separable O V hV
  obtain ⟨𝒩, h𝒩⟩ := hN E V (A.baseChange E)
  exact ⟨𝒩, h𝒩, hs V hV 𝒩 h𝒩⟩

/-- **Néron models exist over every discrete valuation ring** (BLR §1.4 Thm 3 over an affine Dedekind scheme,
proved as `NeronDVR.neronSchemeExtensionDedekind_proof`, specialized to a discrete valuation ring by
`ZInQ.FaltingsRestate.neronSchemeModelExistsDVR_of_dedekind`, with its group structure from
`ReductSplit.exists_neron_groupModel`). -/
theorem neronGroupModelsExist : NeronGroupModelsExist := fun _ _ O _ A =>
  ReductSplit.exists_neron_groupModel
    (ZInQ.FaltingsRestate.neronSchemeModelExistsDVR_of_dedekind NeronDVR.neronSchemeExtensionDedekind_proof) O A

/-- **The printed leaf implies the row**: Néron models exist over the prolongations. -/
theorem silverbergZarhinThm34_of_printed (h : SilverbergZarhinThm34Printed) : SZRaynaud.SilverbergZarhinThm34 :=
  silverbergZarhinThm34_of_printed_of_exists h neronGroupModelsExist

/-- **The row is equivalent to the printed leaf.** -/
theorem silverbergZarhinThm34_iff_printed :
    SZRaynaud.SilverbergZarhinThm34 ↔ SilverbergZarhinThm34Printed :=
  ⟨silverbergZarhinThm34Printed_of_row, silverbergZarhinThm34_of_printed⟩

end ZInQ.OneProof.SZ34Printed

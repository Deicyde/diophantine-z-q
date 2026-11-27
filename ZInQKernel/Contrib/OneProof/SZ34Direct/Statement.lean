import ZInQKernel.Contrib.OneProof.SZThm35.Thm35

/-!
# Silverberg–Zarhin, Theorem 3.4, with the Néron model given

The open hypothesis `SZRaynaud.SilverbergZarhinThm34` concludes `HasSemistableReductionSZ`, which
asserts that a Néron model exists. Silverberg and Zarhin presuppose that model: their notion of
semistable reduction (Def. 3.1 (ii), p. 405) is a property of *the* Néron model. This file states
Theorem 3.4 with the Néron model taken as given: for every Néron model of `A_E` at every extension
of the valuation, the identity component of the special fibre is an extension of an abelian
variety by a torus.

Source, read on the page images of the journal text (Annales de l'Institut Fourier, as digitized
by Numdam, journal pagination):

* p. 404–405, §3: "Suppose X is an abelian variety over a field F, and v is a discrete valuation
  on F with residue field k and valuation ring R. The Néron model 𝒳 of X at v is a smooth separated
  model of X over R such that for every smooth scheme 𝒴 over R and morphism f : 𝒴 ⊗_R F → X over F
  there is a unique morphism f_R : 𝒴 → 𝒳 over R which extends f. The generic fiber of 𝒳 can be
  canonically identified with X, and 𝒳 is a commutative group scheme over R whose group structure
  extends that of X. Let X_v = 𝒳 ⊗_R k and let X_v^0 denote the identity component of the special
  fiber X_v."
* p. 405, Def. 3.1 (ii): X has "semistable reduction at v if X_v^0 is an extension of an abelian
  variety by an affine torus".
* pp. 405–406, Theorem 3.4 (Semistable reduction theorem, Grothendieck): "Suppose X is an abelian
  variety over a field F and v is a discrete valuation on F. Then there is a finite Galois
  extension L of F such that X has semistable reduction at the extensions of v to L." Proof: "See
  Proposition 3.6 of [7]" (SGA 7 I, Exp. IX).

Dictionary:

* `F`, `v`, `R`: a field `K` with a valuation subring `O` that is a discrete valuation ring.
* `L`: an intermediate field `E` of `K ⊆ K̄`, finite and Galois over `K` (every finite extension
  embeds in `K̄`).
* the extensions of `v` to `L`: valuation subrings `V` of `E` with `V ∩ K = O`.
* the Néron model of `X_L` at `V`: a group model `𝒩 : ReductSplit.GroupModelO (A.baseChange E) V`
  (smooth, separated, quasi-compact, with a group law whose generic fibre is identified with
  `A_E` as a group scheme) with the Néron mapping property `𝒩.IsNeronModel` (unique extension of
  morphisms from generic fibres of smooth `V`-schemes). The Néron model is unique up to unique
  isomorphism, so "the" Néron model reads as "every" Néron model; restricting to quasi-compact
  group models only weakens the statement.
* semistable reduction: `DictModels.RaynaudOr.IsSemistableResT 𝒩`, the identity component of the
  special fibre over the residue field `k` is an extension of an abelian variety by a torus (not
  necessarily split), the same reading as the row `SZRaynaud.SilverbergZarhinThm35` (Thm. 3.5).
-/

noncomputable section

namespace SZ34Direct

/-- **Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Theorem 3.4, pp. 405–406, with the Néron
model given** (Néron model as defined on pp. 404–405; semistable reduction as in Def. 3.1 (ii),
p. 405; read on the journal page images). For an abelian variety `A` over a field `K` with a
discrete valuation ring `O`, there is a finite Galois extension `E ⊆ K̄` of `K` such that, at every
extension `V` of `O` to `E`, every Néron model of `A_E` over `V` has semistable reduction in
Silverberg–Zarhin's sense. Unlike `SZRaynaud.SilverbergZarhinThm34`, the existence of the Néron
model is not part of the statement. -/
def SilverbergZarhinThm34Given : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K),
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧ IsGalois K E ∧
      ∀ V : ValuationSubring E, V.comap (algebraMap K E) = O →
        ∀ 𝒩 : ReductSplit.GroupModelO (A.baseChange E) V, 𝒩.IsNeronModel →
          DictModels.RaynaudOr.IsSemistableResT 𝒩

end SZ34Direct

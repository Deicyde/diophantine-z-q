# SZ34Direct: Silverberg–Zarhin Theorem 3.4 with the Néron model given

Target: the open hypothesis `silverbergZarhinThm34` (`SZRaynaud.SilverbergZarhinThm34`), rated GLUE
on 2026-11-26 because its conclusion `HasSemistableReductionSZ` asserts that a Néron model exists,
which Silverberg and Zarhin presuppose.

## The split

* the row: Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Thm 3.4, pp. 405–406, with the Néron
  model given, `SZ34Direct.SilverbergZarhinThm34Given` (`Statement.lean`), printed form;
* Néron-model existence over every discrete valuation ring: proved in Lean,
  `SZ34Direct.neronSchemeModelExistsDVR_proof` and `SZ34Direct.exists_neron_groupModelO`
  (`NeronExistence.lean`, repackaging the tree's `NeronDVR` proof); no printed row is needed;
* the glue to the open hypothesis: `SZ34Direct.silverbergZarhinThm34_of_given` (`Glue.lean`);
* the converse: `SZ34Direct.given_of_silverbergZarhinThm34`, so the row is equivalent to the
  hypothesis (`SZ34Direct.silverbergZarhinThm34Given_iff`);
* the headline: `SZ34Direct.frozenTarget_sz34Given` (`FoldCheck.lean`), `frozenTarget`'s body over
  the research bundle with the field replaced.

Count change: 0 (one statement replaces one; existence is a Lean theorem).

## The print

Read on the page images of the journal text (Annales de l'Institut Fourier 45, no. 2 (1995),
403–420, as digitized by Numdam, journal pagination; doi:10.5802/aif.1459):

* pp. 404–405, §3, the Néron model: "a smooth separated model of X over R such that for every
  smooth scheme 𝒴 over R and morphism f : 𝒴 ⊗_R F → X over F there is a unique morphism
  f_R : 𝒴 → 𝒳 over R which extends f. The generic fiber of 𝒳 can be canonically identified with
  X, and 𝒳 is a commutative group scheme over R whose group structure extends that of X."
* p. 405, Def. 3.1 (ii): "semistable reduction at v if X_v^0 is an extension of an abelian variety
  by an affine torus", with X_v = 𝒳 ⊗_R k and X_v^0 its identity component.
* pp. 405–406, Theorem 3.4: "Suppose X is an abelian variety over a field F and v is a discrete
  valuation on F. Then there is a finite Galois extension L of F such that X has semistable
  reduction at the extensions of v to L." Proof: "See Proposition 3.6 of [7]."

## Departures from the print

* "the Néron model" is read as "every Néron model" (unique up to unique isomorphism; the converse
  `given_of_silverbergZarhinThm34` uses that uniqueness in Lean).
* Néron models are `ReductSplit.GroupModelO` with `IsNeronModel`: they also carry quasi-compactness
  and the group law with its generic identification as group schemes (the print's "group structure
  extends that of X"). Quantifying over fewer models only weakens the statement.
* Semistability is `DictModels.RaynaudOr.IsSemistableResT`, the reading already used for
  Theorem 3.5 (`SZRaynaud.SilverbergZarhinThm35`): an open connected subgroup of the special fibre
  over `k`, faithfully flat onto an abelian variety, with kernel a torus in the functor of points
  over `k̄`.

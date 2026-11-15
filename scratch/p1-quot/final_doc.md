/-!
# p1-quot: the glue field `quotientP1Coordinate` reduced to printed leaves

`HDec.MCRGlue.QuotientP1Coordinate` (`ZInQKernel/OneProof/H/TailW.lean`; bundle field
`HDec.HSyn.OpenGlue7.quotientP1Coordinate`): for the smooth model `𝒴` at `p > 324` and a triple with R1fp, R1hecke,
R2fp, a finite `q : 𝒴 → 𝒵` over `ℤ_(p)` and `ρ' : 𝒵 ≅ P¹_{ℤ_(p)}` (by charts) with the fibre relation `CoordFibres`
for `ρ' ∘ q` (the tame quotient `𝒴/Γ' = P¹`, SGA 1 Exp. V).

Main theorem (no `sorry`, standard axioms):

```
HDec.MCRQuot.quotientP1Coordinate_of_printed
    (hAF : ProperCurveAF) (hQE : FiniteQuotientExists) (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1)
    (hFix : TameFixedPointsDisjoint) (hCyc : TameInertiaCyclic)      -- mcr-glue's leaves L1-L6 (TailW)
    (hT : PkgI2.TorsionStructure.{0})                                -- T5 (the chain: from mumfordTorsionAlgClosed)
    (hYI : PropTSGlue.HeckeIrreducible)                              -- the chain: from deligneComponentsY3PrintedAb
    (hO : CMStabObj) :                                               -- glue on CM objects (mcr-quot (C1b-obj))
    MCRGlue.QuotientP1Coordinate
```

It is `MCRGlue.quotientP1Coordinate_of_leaves` (TailW) with mcr-glue's glue A, B, C discharged by mcr-quot's proofs
(helpers `QuotientP1/MCRQuotA.lean`, `QuotientP1/MCRQuotB.lean`), with mcr-quot's foundational glue `P1SchemeQ`
proved here (`QuotientP1/P1Scheme.lean`), `CurveBijIso` from curve-split (`_root_.CurveSplit.curveBijIso`,
`TailR`), and `ModelYIrreducible` taken in the chain's form `HeckeIrreducible` (the same body, `rfl`). gap-triage's
finding that Lemma NV (`CoverModelOfHeckeN`) is not needed is used: `hCov` entered mcr-quot only for
`ModelYIrreducible`. docs/research/p1-quot.md.
-/

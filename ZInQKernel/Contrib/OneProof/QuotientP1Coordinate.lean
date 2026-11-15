import ZInQKernel.Contrib.OneProof.QuotientP1.FixedDisjoint
import ZInQKernel.Contrib.OneProof.QuotientP1.P1Scheme
import ZInQKernel.OneProof.H.TailR

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


namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# p1-quot: `QuotientP1Coordinate` from printed leaves and `CMStabObj`

`P1SchemeQ` is proved (`QuotientP1Proof.p1SchemeQ_body`, `QuotientP1/P1Scheme.lean`); L5 is proved from
Edixhoven's theorem (`tameFixedPointsDisjoint_of_edixhoven`, `QuotientP1/FixedDisjoint.lean`); `CurveBijIso` is
curve-split's theorem; `ModelYIrreducible` is the chain's `PropTSGlue.HeckeIrreducible` (same body, `rfl`).
════════════════════════════════════════════════════════════════════════════════════════════ -/

namespace MCRQuot

open MCRGlue ModelGlue LeafQM LeafQM.AV

/-- **(B-P¹) `P1SchemeQ`, proved** (the relative projective line of the vendored CloudW07 library). -/
theorem p1SchemeQ : P1SchemeQ := _root_.QuotientP1Proof.p1SchemeQ_body

/-- `ModelYIrreducible` is the chain's `HeckeIrreducible`. -/
theorem modelYIrreducible_iff : ModelYIrreducible = PropTSGlue.HeckeIrreducible := rfl

/-- **`QuotientP1Coordinate` from mcr-glue's leaves L1-L6, T5, `CurveBijIso`, `HeckeIrreducible` and
`CMStabObj`.** -/
theorem quotientP1Coordinate_of_leaves' (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hFix : TameFixedPointsDisjoint)
    (hCyc : TameInertiaCyclic) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
    (hYI : PropTSGlue.HeckeIrreducible) (hO : CMStabObj) : MCRGlue.QuotientP1Coordinate :=
  have hfix : FibreAutFixFinite := fibreAutFixFinite_of' hC hYI
  have gA : FibreAutTame := fibreAutTame_of' hT hfix
  MCRGlue.quotientP1Coordinate_of_leaves hAF hQE hTS hP1 hFix hCyc gA
    (genericQuotientP1_of'' gA hT hTS hC p1SchemeQ)
    (MCRGlue.coordinateNormalization_of (cMSectionsDisjoint_of'' gA hfix (cMStabInvolution_of hC hYI hO))
      (coordinateFromSections_of'' gA hT))

/-- **`QuotientP1Coordinate` from the leaves L1-L4, L6, Edixhoven's fixed-point theorem, T5, `HeckeIrreducible`
and the glue `CMStabObj`** (L5 from Edixhoven; `CurveBijIso` is curve-split's `_root_.CurveSplit.curveBijIso`). -/
theorem quotientP1Coordinate_of_printed (hAF : ProperCurveAF) (hQE : FiniteQuotientExists)
    (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1) (hE : EdixhovenFixedSmooth)
    (hCyc : TameInertiaCyclic) (hT : PkgI2.TorsionStructure.{0})
    (hYI : PropTSGlue.HeckeIrreducible) (hO : CMStabObj) : MCRGlue.QuotientP1Coordinate :=
  quotientP1Coordinate_of_leaves' hAF hQE hTS hP1 (tameFixedPointsDisjoint_of_edixhoven hE) hCyc hT
    _root_.CurveSplit.curveBijIso hYI hO

end MCRQuot

end HDec

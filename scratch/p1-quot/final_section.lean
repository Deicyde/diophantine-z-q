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

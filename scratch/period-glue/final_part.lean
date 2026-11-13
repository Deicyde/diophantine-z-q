
/-! ## End to end: fibre-qm-period's `FibreQMPeriod` with period-glue's pieces (proved) -/

namespace HSyn.G0Split.FibreQM.PeriodGlue

open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMapH

/-- **`FibreQMPeriod` from leaves and the remaining glue (proved).** period-map's
`fibreQMPeriod_periodMap` with `BaseChangeClassUnique`, `S8Nonzero` proved, `T11aRiemannEnd`
derived from `T11aRiemannHom`, `SphereFactorAffine` proved, and `PiTwistC`, `QMTwistLattice`,
`S8WeightExact` replaced by their pieces.
* Leaves: `R1R2fp`, `PkgI1.QMHauptmodul`, T35 (`UniformizationExistsT35`), `T11aRiemannHom`,
  `QMClassNumberOne`, `R1bFamily`, `CMDescends` (candidate), `PkgI1.ThetaModularity`,
  `GammaStarGen` (candidate), `ValenceBoundGammaStar` (candidate), and
  `GlueDescent.LeafSkolemNoether` (proved in the kernel: `TSkolemKW.leafSkolemNoether`).
* Glue: `Pin.MobiusGlue` (proved by mobius-glue), `TwistOrbitFinite`, `FibreTransferC`,
  `CPtsTransport`. -/
theorem fibreQMPeriod_periodGlue (h : R1R2fp) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hHom : T11aRiemannHom)
    (hCN : QMClassNumberOne) (hR : R1bFamily (ownY h) (ownΦ h) (ownπ h))
    (hTO : TwistOrbitFinite (ownY h) (ownΦ h)) (hFT : FibreTransferC (ownY h) (ownπ h))
    (hSN : GlueDescent.LeafSkolemNoether) (hD : CMDescends)
    (hTM : PkgI1.ThetaModularity) (hG : GammaStarGen)
    (hV : PeriodMap.ValenceBoundGammaStar) (hCP : CPtsTransport) : ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_periodMap h hM hH hE (t11aRiemannEnd_of_hom hHom) hCN hR
    baseChangeClassUnique_proof
    (piTwistC_of _ _ _ (own_spec h).1 (own_spec h).2.2 hTO hFT)
    (qmTwistLattice_of' hHom hSN) hD s8Nonzero_proof
    sphereFactorAffine_proof (s8WeightExact_of hTM hG) hV hCP

end HSyn.G0Split.FibreQM.PeriodGlue

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.baseChangeClassUnique_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.qmTwistLattice_of'
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.piTwistC_of
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.s8Nonzero_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.s8WeightExact_of
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.sphereFactorAffine_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.fibreQMPeriod_periodGlue

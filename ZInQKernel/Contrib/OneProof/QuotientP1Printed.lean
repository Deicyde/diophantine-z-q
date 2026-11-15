import ZInQKernel.Contrib.OneProof.QuotientP1.FromFields
import ZInQKernel.Contrib.OneProof.QuotientP1.Lichtenbaum
import ZInQKernel.Contrib.OneProof.CMStab
import ZInQKernel.Contrib.OneProof.QuotientP1.QuotProper

/-!
# p1-quot2: `quotientP1Coordinate` without mcr-glue's leaf L1 and without the glue `CMStabObjWeak`

`HDec.MCRGlue.QuotientP1Coordinate` (`ZInQKernel/OneProof/H/TailW.lean`; bundle field
`HDec.HSyn.OpenGlue7.quotientP1Coordinate`). p1-quot (`QuotientP1Coordinate.lean`) reduced it to mcr-glue's leaves
L1-L4, Edixhoven's tame fixed-point theorem, T5, `HeckeIrreducible` and the glue `CMStabObjWeak`. Here:

* L1 (`ProperCurveAF`, a composite) is replaced by the printed leaf `QuotientP1Proof.LichtenbaumProjective`
  (Lichtenbaum 1968 Thm 2.8 / Liu Thm 8.3.16 for `S = Spec R`, `R` a DVR): the model `𝒴` is integral
  (`isIntegral_model`), flat, regular (vendored FLT) and of dimension 2 (`QuotientP1Proof.topologicalKrullDim_eq_two`),
  hence projective, and finite sets in a projective `ℤ_(p)`-scheme lie in an affine open (EGA II 4.5.4, proved in
  `QuotientP1/Lichtenbaum.lean`).
* `CMStabObjWeak` is proved from cm-stab's `GapGlue.cmStabObj_of` (`CMStab.lean`), whose inputs are the textbook
  fields `uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed`.

Main theorems (no `sorry`, standard axioms):

```
HDec.MCRQuot.quotientP1Coordinate_of_printed2
    (hL : QuotientP1Proof.LichtenbaumProjective) (hQE : FiniteQuotientExists) (hTS : TameQuotientSmooth)
    (hP1 : SmoothModelOfP1) (hE : EdixhovenFixedSmooth2) (hT : PkgI2.TorsionStructure.{0})
    (hYI : PropTSGlue.HeckeIrreducible) (hO : CMStabObjWeak) : MCRGlue.QuotientP1Coordinate
HDec.MCRQuot.quotientP1Coordinate_of_fields2
    (hL : QuotientP1Proof.LichtenbaumProjective) (hQE : FiniteQuotientExists) (hTS : TameQuotientSmooth)
    (hP1 : SmoothModelOfP1) (hE : EdixhovenFixedSmooth2)
    (hMT : AvSplit.MumfordTorsionAlgClosed) (hRC : LeafQM.AV.R1UnivRigid.MumfordRigidityCore)
    (hD : ShimuraGlue.DeligneComponentsY3PrintedAb)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism) :
    MCRGlue.QuotientP1Coordinate
```
docs/research/p1-quot2.md. -/

namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-- **`CMStabObjWeak` from the textbook fields** `uniformizationLeafAll`, `gagaMorphism`,
`mumfordTorsionAlgClosed` (cm-stab's `GapGlue.cmStabObj_of`, with T5 from `mumfordTorsionAlgClosed`). -/
theorem cMStabObjWeak_of_fields (hU : _root_.BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : _root_.ZInQ.HomLattice.GAGAMorphism) (hMT : _root_.AvSplit.MumfordTorsionAlgClosed) :
    CMStabObjWeak :=
  cMStabObjWeak_of (_root_.GapGlue.cmStabObj_of hU hG hMT (_root_.AvSplit.torsionStructure_of_mumford hMT))

/-- **`QuotientP1Coordinate` from Lichtenbaum's theorem, mcr-glue's leaves L2-L4, Edixhoven's tame fixed-point
theorem, T5, `HeckeIrreducible` and `CMStabObjWeak`.** p1-quot's `quotientP1Coordinate_of_printed` with L1 replaced:
the finite sets of points of the integral model `𝒴` lie in affine opens by `exists_affine_of_lichtenbaum`. -/
theorem quotientP1Coordinate_of_printed2 (hL : _root_.QuotientP1Proof.LichtenbaumProjective)
    (hQE : FiniteQuotientExists) (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1)
    (hE : EdixhovenFixedSmooth2) (hT : PkgI2.TorsionStructure.{0}) (hYI : PropTSGlue.HeckeIrreducible)
    (hO : CMStabObjWeak) : MCRGlue.QuotientP1Coordinate := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  have hC : CurveBijIso := _root_.CurveSplit.curveBijIso
  have hfix : FibreAutFixFinite := fibreAutFixFinite_of' hC hYI
  have gA : FibreAutTame := fibreAutTame_of' hT hfix
  obtain ⟨hfin, hnd⟩ := gA p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  have hover := fibreAut_over 𝒴 𝒜
  haveI : IsIntegral 𝒴.left := isIntegral_model hC hYI hM h1 hh h2
  haveI : IsDiscreteValuationRing (Zloc p) := zloc_isDVR p
  haveI : IsProper 𝒴.hom := hM.1
  haveI : SmoothOfRelativeDimension 1 𝒴.hom := hM.2.1
  have hAF : ∀ s : Finset 𝒴.left, ∃ W : 𝒴.left.Opens, IsAffineOpen W ∧ ∀ x ∈ s, x ∈ W :=
    fun s => _root_.QuotientP1Proof.exists_affine_of_lichtenbaum hL 𝒴.hom s
  obtain ⟨𝒵, q, hq, hqf⟩ := hQE p 𝒴 hM.1 hAF (fibreAut 𝒴 𝒜) hfin hover
  obtain ⟨hZp, hZs⟩ := hTS p 𝒴 𝒵 q hM.1 hM.2.1 _ hfin hnd hover hq hqf
  obtain ⟨σ₀, hσ₀⟩ := genericQuotientP1_of'' gA hT hTS hC p1SchemeQ p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
    𝒵 q hq hqf
  obtain ⟨ρ'₀, hρ'₀⟩ := hP1 p 𝒵 hZp hZs σ₀ hσ₀
  obtain ⟨ρ', hρ', hCF⟩ := coordinateFromSections_of'' gA hT p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf
    hZp hZs (cMSectionsDisjoint'_of hE gA hfix gQuotientPointOrbits (cMStabNontrivial_of hO)
      qbarPointsConjugate p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf) ρ'₀ hρ'₀
  exact ⟨𝒵, q, ρ', hqf, hρ', hCF⟩

/-- **`QuotientP1Coordinate` from Lichtenbaum's theorem, mcr-glue's leaves L2-L4, Edixhoven's theorem and the
chain's fields** (T5 from `mumfordTorsionAlgClosed`; `HeckeIrreducible` from `deligneComponentsY3PrintedAb` and
`mumfordRigidityCore`, as in p1-quot's `quotientP1Coordinate_of_fields`; `CMStabObjWeak` from
`uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed`). -/
theorem quotientP1Coordinate_of_fields2 (hL : _root_.QuotientP1Proof.LichtenbaumProjective)
    (hQE : FiniteQuotientExists) (hTS : TameQuotientSmooth) (hP1 : SmoothModelOfP1)
    (hE : EdixhovenFixedSmooth2) (hMT : _root_.AvSplit.MumfordTorsionAlgClosed)
    (hRC : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidityCore)
    (hD : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb)
    (hU : _root_.BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : _root_.ZInQ.HomLattice.GAGAMorphism) : MCRGlue.QuotientP1Coordinate :=
  quotientP1Coordinate_of_printed2 hL hQE hTS hP1 hE
    (_root_.AvSplit.torsionStructure_of_mumford hMT)
    (TSHecke.heckeIrreducible_of_connected (_root_.ShimuraSplit.y3Connected_of_deligne
      (_root_.ShimuraGlue.deligneComponentsY3_of_printed
        ((_root_.LeafQM.AV.R1UnivRigid.deligneComponentsY3Printed_iff_ab
          (_root_.LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core hRC)).mpr hD))))
    (cMStabObjWeak_of_fields hU hG hMT)

/-- **`QuotientP1Coordinate` with L3 replaced by its smoothness half** (`TameQuotientSmoothRelDim`; properness
of the quotient proved in `QuotientP1/QuotProper.lean`). Inputs: Lichtenbaum's theorem, L2, the smoothness half
of L3, L4, Edixhoven's theorem and the chain's fields. -/
theorem quotientP1Coordinate_of_fields3 (hL : _root_.QuotientP1Proof.LichtenbaumProjective)
    (hQE : FiniteQuotientExists) (hTS : TameQuotientSmoothRelDim) (hP1 : SmoothModelOfP1)
    (hE : EdixhovenFixedSmooth2) (hMT : _root_.AvSplit.MumfordTorsionAlgClosed)
    (hRC : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidityCore)
    (hD : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb)
    (hU : _root_.BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : _root_.ZInQ.HomLattice.GAGAMorphism) : MCRGlue.QuotientP1Coordinate :=
  quotientP1Coordinate_of_fields2 hL hQE (tameQuotientSmooth_of_relDim hTS) hP1 hE hMT hRC hD hU hG

end MCRQuot

end HDec

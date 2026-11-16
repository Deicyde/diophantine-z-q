import ZInQKernel.OneProof.H.TailZ35
import ZInQKernel.Contrib.OneProof.SGRDirectElkies

/-!
# sgr-fold: `shimuraIntegralModelRep` and `quotientP1Coordinate` bypassed (route NV of sgr-direct)

The two fields fed one consumer, `HDec.HeckeRestNV.HeckeVertWitness` (leaf-fold4's glue, filled in TailO's
`glue4_of_open6`). sgr-fold fills it instead by `SGRDirect.heckeVertWitness_of_nvSqrtAny` (sgr-direct), whose inputs
are the generation-6 fields `r1r2`, `t5`, `qmAutCard`, T35 (Serre's rigidity), `alFixedPoints`, and two Props carried
down in the glue bundles `OpenGlue6`/`OpenGlue7`:

* `SGRDirect.NVLocalInertia` (h-b1 §3 Lemma NV step 3; GLUE, the new top field `OpenGlue8.nvLocalInertia`);
* `SGRDirect.HeckeSqrtBranchAny`, proved here at the top (`heckeSqrtBranchAny_of_open29`) from the research field
  `elkiesX6StarPrinted` by sgr-direct's `SGRDirect.heckeSqrtBranchAny_of_elkies`, with `R1R2fp` read off the top
  bundles through the existing conversions down to generation 14 (`x6Rows_of_open14`, as `sixContactMin_of_open17`
  does) and T5 from `mumfordTorsionAlgClosed` (`AvSplit.torsionStructure_of_mumford`).

`openGlue7_of_nvLocalInertia` is the glue conversion of the fold (`OneProof/H/TailZ36.lean`).
-/

namespace HDec

namespace HSyn

namespace SGRFold

/-- The top bundles converted down to generation 14 (research), as the stack `sixContactMin_of_open29` …
`sixContactMin_of_open18` does. -/
theorem research14_of_open29 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) : OpenResearchLeaves14 :=
  openResearchLeaves14_of_OpenResearchLeaves15 <| openResearchLeaves15_of_OpenResearchLeaves16 <|
    openResearchLeaves16_of_OpenResearchLeaves17 <| openResearchLeaves17_of_OpenResearchLeaves18 <|
    openResearchLeaves18_of_OpenResearchLeaves19 <| openResearchLeaves19_of_OpenResearchLeaves20
      (openResearchLeaves20_of_OpenResearchLeaves21 (openResearchLeaves21_of_OpenResearchLeaves22 r t) t) t

/-- The top added-leaves bundle converted down to generation 12, as the stack does. -/
theorem added12_of_open29 (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17) : OpenAddedLeaves12 :=
  addedLeaves12_of_open13 <| openAddedLeaves13_of_OpenAddedLeaves14 <|
    openAddedLeaves14_of_OpenAddedLeaves15
      (openAddedLeaves15_of_OpenAddedLeaves16 (openAddedLeaves16_of_OpenAddedLeaves17 l))
      (openTextbookLeaves10_of_OpenTextbookLeaves11 t)

/-- **`HeckeSqrtBranchAny` from the top bundles**: sgr-direct's `heckeSqrtBranchAny_of_elkies` with Elkies' printed
model (`elkiesX6StarPrinted`), `R1R2fp` (generation 14's `x6Rows_of_open14`) and T5. -/
theorem heckeSqrtBranchAny_of_open29 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11)
    (l : OpenAddedLeaves17) : SGRDirect.HeckeSqrtBranchAny :=
  SGRDirect.heckeSqrtBranchAny_of_elkies
    (LeafAdopt.R1R2fp_of_rep (x6Rows_of_open14 (research14_of_open29 r t)
      (openTextbookLeaves10_of_OpenTextbookLeaves11 t) (added12_of_open29 t l)).1)
    (_root_.AvSplit.torsionStructure_of_mumford t.mumfordTorsionAlgClosed) r.elkiesX6StarPrinted

/-- **The glue bundle of generation 7 from `NVLocalInertia` and the top bundles** (sgr-fold). -/
theorem openGlue7_of_nvLocalInertia (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17)
    (hL : SGRDirect.NVLocalInertia) : OpenGlue7 where
  nvLocalInertia := hL
  heckeSqrtBranchAny := heckeSqrtBranchAny_of_open29 r t l

end SGRFold

end HSyn

end HDec

#print axioms HDec.HSyn.SGRFold.heckeSqrtBranchAny_of_open29
#print axioms HDec.HSyn.SGRFold.openGlue7_of_nvLocalInertia

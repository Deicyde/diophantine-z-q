import ZInQKernel.OneProof.H.TailZ38
import ZInQKernel.Contrib.OneProof.SGRFold

/-! # OneProof H, sgr-fold (leaf-fold30): `sixContactMin_of_open33` (hand fold, r6-nf style)

Fields removed (bypassed at their single consumer `HeckeRestNV.HeckeVertWitness`, which TailO's `glue4_of_open6` now
fills by sgr-direct's route NV, `SGRDirect.heckeVertWitness_of_nvSqrtAny`; pruned from every generation by PruneScan):
`shimuraIntegralModelRep` (`OpenAddedLeaves17`) and `quotientP1Coordinate` (`OpenGlue7`).
Fields added (new glue): `nvLocalInertia` (`SGRDirect.NVLocalInertia`, h-b1 §3 Lemma NV step 3).
`HeckeSqrtBranchAny` is proved from `elkiesX6StarPrinted` (`SGRFold.heckeSqrtBranchAny_of_open29`), which generation 22
gets from leaf-fold26's discharge. docs/research/sgr-fold.md. -/

namespace HDec

namespace HSyn

/-- **The glue still open** (sgr-fold): `NVLocalInertia` only (replaces `OpenGlue7`'s `quotientP1Coordinate`). -/
structure OpenGlue8 : Prop where
  /-- sgr-direct, GLUE (h-b1 §3 Lemma NV step 3; consequence of Abhyankar's lemma and Zariski–Nagata purity): for
  `E/ℚ(X)` finite Galois of degree `< p` with branch data in `S ∪ {∞}`, `S` `p`-integral and distinct mod `p`, and
  `b ∈ S` whose residue fields are unramified at `p`, every vertical inertia element at `p` has a conjugate in an
  inertia group over `X − b`. -/
  nvLocalInertia : SGRDirect.NVLocalInertia

/-- `OpenGlue7` from `OpenGlue8`: `HeckeSqrtBranchAny` by the contribution (Elkies' printed model, through
generation 22 of the research bundle). -/
theorem openGlue7_of_OpenGlue8 (r : OpenResearchLeaves25) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17)
    (g : OpenGlue8) : OpenGlue7 where
  nvLocalInertia := g.nvLocalInertia
  heckeSqrtBranchAny := SGRFold.heckeSqrtBranchAny_of_open29
    (openResearchLeaves22_of_OpenResearchLeaves23
      (openResearchLeaves23_of_OpenResearchLeaves24 (openResearchLeaves24_of_OpenResearchLeaves25 r) t)) t l

/-- **G0 with only the open leaves and the open glue** (sgr-fold, leaf-fold30). -/
theorem sixContactMin_of_open33 (r : OpenResearchLeaves25) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17)
    (g : OpenGlue8) : ZInQ.SixContactMin :=
  sixContactMin_of_open32 r t l (openGlue7_of_OpenGlue8 r t l g)

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open33

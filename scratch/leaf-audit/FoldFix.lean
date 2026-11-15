import ZInQKernel.OneProof.H.TailZ41

/-! leaf-audit: corrected theta-fold top. `linYangEx29All` (false) replaced by the existential `LinYangEx29`;
`hθ` no longer needs `QMHauptmodul`. Same bundles otherwise (by-hand fold: in TailZ41, field
`linYangEx29 : G0Split.ThetaPt.LinYangPrinted.LinYangEx29` instead of `linYangEx29All`). -/

namespace HDec.HSyn

theorem sixContactMin_of_open29_fixed (r : OpenResearchLeaves21) (t : OpenTextbookLeaves11)
    (l : OpenAddedLeaves17) (g : OpenGlue7)
    (hI : G0Split.ThetaPt.LinYangPrinted.IgusaThetaExpressions)
    (hL : G0Split.ThetaPt.LinYangPrinted.LinYangEx29) : ZInQ.SixContactMin :=
  sixContactMin_of_open28 r t l g
    (fun _ => G0Split.ThetaPt.IgusaAlgFinal.thetaRatiosAtQM_of_printed hI hL)

end HDec.HSyn

#print axioms HDec.HSyn.sixContactMin_of_open29_fixed

import ZInQKernel.Contrib.OneProof.Y3X6.Top

/-! # y3-x6: the fold with the moduli row over `Y₃` (no `X₆` field)

Task y3-x6 (2026-11-17). Report: `docs/research/y3-x6.md`; log: `scratch/y3-x6/log.md`.

On cm-branch2's route (`HDec.HSyn.sixContactMin_of_open73_cm`, the manuscript's CM branch in place of NoCM), the
two `X₆` fields of the research bundle, `x6CoarseModuliIdeal` (the coarse moduli scheme `X₆ = X₀(6,1)` and the
Atkin–Lehner group) and `elkiesX6StarEveryIdeal` (Elkies' coordinate on `X₆/W`), were read only to build

* the moduli row's `X₆` witness `(X, Ψ, fY, π₆)` with `X6Props`, `R2X6PropsIff`, `X6Surj` (through
  `gonzalezRotgerX6Ab` and `babaGranathRationalAb`), whose readers need only R2 on `Y₃`, `π` onto `P¹(ℚ̄)` and the
  converse CM clauses: all three are clauses of y3-p1j's leaf `Y3P1j.Y3ToP1j` (the manuscript's map `Y₃ → P¹_j`,
  diophantine_zq.tex L420-440), so the row is restated over `Y₃` (`Y3X6.R1R2fpY3`, `Y3X6/Row.lean`) and every
  generation of the chain is copied with that row (`Y3X6/Copy*.lean`, generated);
* the `X₆` conic model (row H-43, read by nothing on the CM-branch route; carried as `True`);
* sgr-direct's `HeckeSqrtBranchAny` (a square root of `c(27X + 16)` in the Galois closure of `Y₃ → P¹`), which on
  the `Y₃` route is the open glue field `heckeSqrtBranchAny` (docs/research/y3-x6.md §4: the manuscript's tame
  local equation L517-526 is a local statement at `p > 324` and does not give a global square root).

`HDec.HSyn.sixContactMin_of_open74_y3x6 (r : OpenResearchLeaves55Y3) (t : OpenTextbookLeaves18)
(l : OpenAddedLeaves27) : ZInQ.SixContactMin` (`Y3X6/Top.lean`) is the resulting top theorem;
`OpenResearchLeaves55Y3` = `OpenResearchLeaves54CM` − `x6CoarseModuliIdeal` − `elkiesX6StarEveryIdeal` + `y3ToP1j` +
`heckeSqrtBranchAny`. -/

namespace HDec.HSyn

/-- **`ZInQ.SixContactMin` without `X₆`** (y3-x6): cm-branch2's top (`sixContactMin_of_open73_cm`) with the two `X₆`
fields of `OpenResearchLeaves54CM` replaced by y3-p1j's leaf `Y3P1j.Y3ToP1j` and the glue
`SGRDirect.HeckeSqrtBranchAny`. -/
theorem sixContactMin_y3x6 (r : OpenResearchLeaves55Y3) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves27) : ZInQ.SixContactMin :=
  sixContactMin_of_open74_y3x6 r t l

end HDec.HSyn

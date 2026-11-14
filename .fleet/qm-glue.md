# qm-glue (2026-11-14): result

**Verdict.** (b) `GammaStarFromO1` is PROVED (Mathlib only, no leaf); hence rows H-87 and H-88 are theorems from
published-form leaves only. (a) `ThetaQuotientValue24` is reduced exactly to a closed numeric statement at an
explicit period matrix and is equivalent to the published value `IgusaCMValue24` (Lin–Yang (2),(14) at the
Baba–Granath CM value −16/27); an exact Lean computation of −16/27 was not achieved (needs CM theory). (d) the
coarse-witness comparison is reduced to one named glue `CoarseFactor` (+ `CurveBijIso`, proved by curve-split);
the moduli rows' universal glue Props follow from existential published statements. (c) no further Lean
reduction of `ThetaFourthRatiosAlgebraic` over the present definitions (composite leaf candidate).

**Compiles (all VERIFIED, axioms [propext, Classical.choice, Quot.sound]):**
- `scratch/qm-glue/GammaStar.lean` (import Mathlib): `HDec.LeafQCheck.QMglue.gammaStarFromO1_proof :
  QMSplitVB.GammaStarFromO1` (and Haupt.lean's copy). Cover of Γ* by 4 cosets of ℚ^×Γ¹ (closure induction,
  16-entry table), distinct cosets, Γ* cocompact Fuchsian, lexicographic fundamental domain, area via Mathlib's
  `IsFundamentalDomain.measure_eq` for the Möbius group of Γ¹: vol = (2π/3)/4 = π/6.
- `scratch/qm-glue/ThetaValue24.lean` (import Mathlib): fixed point τ₂₄ = i(√6+√3); Ω(τ₂₄) =
  [[(−4+3√−6)/14, (−1−√−6)/7], [(−1−√−6)/7, (−4+3√−6)/7]]; `thetaQuotientValue24_iff`; leaf ⇔ glue.
- `scratch/qm-glue/HauptGlue.lean` (over leaf-fold4's chain, `chk.sh`): `valenceFormulaGammaStar_of_leaves` (H-87),
  `qmHauptmodulBase3_of_leaves` (H-88: r4 + ValenceFormulaCocompactEq + ShimizuCovolumeO1 + IgusaCMValue24).
- `scratch/qm-glue/ModuliCompare.lean` (chain): `coarseCompare_of`, `coarseX6OfFine_of`, `hauptmodulOfX6_of`,
  `residueOfX6_of`, `hauptmodulUniqueX6S_of` (from the kernel's MobiusGlue, = T5 by image-plane),
  `conicOfWitness_of'`, `connectedOfFine_of_canonical`, rows `r1r2fpRep_of_canonical` (H-1),
  `x6ConicModel_of_canonical'` (H-43).

**Remains:** `CoarseFactor` (descent of the forgetful map along the finite Y₃ → X₆; AG of curves);
`ThetaFourthRatiosAlgebraic` (needs a polarization object on PkgI3.AbVar to split); the exact value −16/27.
Note: qm-split's chain copy ~/qms-olean is gone; `chk.sh` uses leaf-fold6's compiled chain copied to ~/qmg-olean.
Report: docs/research/qm-glue.md; log: scratch/qm-glue/log.md.

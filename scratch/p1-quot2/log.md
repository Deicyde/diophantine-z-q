# p1-quot2 results log

Base: wip/p1-quot2 = f30ece89 (p1-quot); merged origin/wip/cm-stab (6242b2f9, leaf-fold22 + cm-stab) as 0e783b9b (clean).
Build tree: copy of ~/dzq-wt/yu-prune-base/.lake/build (c2ad4181) + lean/.lake/build; then `lake build` of the merged tree.

## Findings
- VERIFIED (read): cm-stab's `GapGlue.cmStabObj_of : UniformizationLeafAll → GAGAMorphism → MumfordTorsionAlgClosed →
  ObjBridge.TorsionStructure → GapGlue.CMStabObj` (ZInQKernel/Contrib/OneProof/CMStab.lean L1170, branch origin/wip/cm-stab,
  axioms recorded by cm-stab in scratch/cm-stab/axioms.txt: standard). All three inputs are textbook fields of
  OpenTextbookLeaves11 (TailZ32: mumfordTorsionAlgClosed, uniformizationLeafAll, gagaMorphism).
- VERIFIED (read): vendored FLT theorem `ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing`
  (smooth over a DVR ⇒ regular stalks).
- VERIFIED (read): vendored Jacobian-Challenge `ProjectiveSpectrum.exists_homogeneous_notMem_of_finset` (graded prime avoidance) and
  `exists_isAffineOpen_superset_of_isClosedImmersion` (EGA II 4.5.4 over a field; the proof uses only that the base is affine).
- VERIFIED (read): Mathlib `Smooth.of_smooth_fiberToSpecResidueField` (EGA IV 17.5.1 direction flat + lfp + smooth fibres ⇒ smooth);
  Mathlib `ringKrullDim_stalk_eq_coheight`; Contrib/Dim `topologicalKrullDim_eq_of_smoothOfRelativeDimension`.
- VERIFIED (read): chain textbook field `regularSmoothPerfect` (Stacks 00TV) and curve-split's `normalCurveSmoothQ_of_regularSmooth` (TailR).

## Compile log

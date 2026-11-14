# leaf-fold5 (2026-11-14)

**Result (VERIFIED).** `HDec.HSyn.sixContactMin_of_open5 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves5)
(l : OpenAddedLeaves5) (g : OpenGlue5) : ZInQ.SixContactMin` (the kernel's own `SixContactMin`) compiles with no
`sorry` and only `[propext, Classical.choice, Quot.sound]`. It has 70 hypotheses: 26 research + 21 textbook +
21 added leaves + 2 glue Props (55 LEAF / 13 LEAF? / 2 GLUE). leaf-fold4 had 66 (58 / 7 / 1).

- (a) leaf-fold4's last glue Prop `HeckeVertWitness` is now a theorem: vert-witness + model-glue, with smooth-fibre's
  `SmoothFibreReduced` as the kernel theorem. Its inputs are the new leaf candidates `ShimuraGoodReduction` (needs a
  human check: level 3 at 3 | D) and `CurveBijIso`, the existing fields `r1r2` and `t5`, and the smaller glue Prop
  `ModelCoordinateResidue` (the tame quotient 𝒴/Γ' ≅ P¹ over ℤ_(p); not proved).
- (b) Each of these is now a theorem from weaker published statements, or from fields already present:
  - T3 and T41 (neron-c);
  - T6 and T7, and T8 = PoincareComplement + glue `SimpleImageIsogeny` (av-b1);
  - T9, Serre's lemma, and T11(b) from its existence half (av-b2);
  - T34 and T38 (curves-g; T38's rational-point clause is proved).
- (c) 33 of the 70 fields are now the kernel's own constants (leaf-fold4: 5). The 10 av-b1/curves-g/neron-c kernel
  leaves and the av-b1 glue Prop are used directly. 17 copied fields are restated over the kernel's Props, each with
  a proved transport (part e40).

**Compiles.** The olean chain: leaf-fold4's sources unchanged, then TailL, TailM, TailN. Check5 confirms the kernel
conclusion and no `sorryAx` in the dependency closure. The flat file `scratch/leaf-fold5/Leaves5.lean` (121 783 lines)
exits 0 in 1570 s with 349 standard axiom reports. `py/verbatim_check.py` prints ALL OK: the folded statements are
their sources' text.

**Remains.**
- Two glue Props: `ModelCoordinateResidue` and `SimpleImageIsogeny`. Keeping T8 as a leaf instead gives 69 Props
  with 1 glue.
- 13 LEAF? fields, listed in docs/research/leaf-fold5.md §3.
- 37 fields are still chain copies. Their Props involve copied QML3/QMPair, Faltings heights over the copied
  GroupModel, or the scratch-only QM, period, Hecke, p-adic and Galois layers (report §5).

Report: docs/research/leaf-fold5.md. Lean: scratch/leaf-fold5/ (BUILD.md, log.md).

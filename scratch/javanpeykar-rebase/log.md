# javanpeykar-rebase log

- 2026-11-16 15:02 start. Merged origin/main (e41a7169), origin/wip/integrate-w82 (5e235a40, not on main), height-fix 49e6d97d (no conflicts).
- Build tree: copied ~/dzq-wt/height-fix/.lake/build and lean/.lake/build (copy, not symlink).
- Consumers of ConstantFieldExtensionUnramifiedFull (grep, VERIFIED): only JavanpeykarFix.isBelyiFunction_baseChange_full,
  used by belyiBaseChange_of_full at L = AlgebraicClosure K (an infinite algebraic extension). So the consumer needs
  an infinite K'/K; plan: prove the algebraic case from the finite case in Lean (directed union of finite subextensions).
- 15:14 build1 (PrintedStableHeight, JavanpeykarFix): OK, 12777 jobs. VERIFIED.
- Finite.lean (Stichtenoth finite leaf, full_of_finite): compiles clean. VERIFIED.
- ZInQKernel/Contrib/OneProof/JavanpeykarRebase.lean: `lake build +Main +Discharges +JavanpeykarRebase` OK (14114 jobs). VERIFIED.
- #discharges (scratch/javanpeykar-rebase/Discharges-output.txt): javanpeykarBound by
  JavanpeykarRebase.javanpeykarBound_of_printed_rebase, still assumes [JavanpeykarRebase.JavanpeykarPrintedMap,
  JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite, UniformizationLeafAll, MumfordTorsionAlgClosed,
  ZInQ.HeightFix.SemiAbelianDescendsPerfect]; standard axioms. full_of_finite, finite_of_full,
  javanpeykarPrintedMap_of_fix: standard axioms. VERIFIED.
- Base change found: uniformizationLeafAll is no longer a textbook field (proved, `_root_.uniformizationLeafAll_proof`,
  folded at TailZ44). Added `javanpeykarBound_of_printed_rebase_final` (fills it); spec uses it. height-fix's spec
  still reads {t}.uniformizationLeafAll and fails on this base; the combined spec replaces it by the proof.
- #discharges re-run: _final still assumes [JavanpeykarPrintedMap, ConstantFieldExtensionUnramifiedFinite,
  MumfordTorsionAlgClosed, SemiAbelianDescendsPerfect]; standard axioms. VERIFIED.
- Autofold dry runs (kinds.tsv of this base, strict LEAF/GLUE on N):
  * autofold.json (PrintedMap kind consequence, flag pending reading; Stichtenoth published; semiAbelianDescendsPerfect
    project glue): 16/21 on 37 -> 17/22 on 39 (needs --allow-rise). Generated module compiles, sixContactMin_of_open39
    standard axioms (FoldDryRun-compile.txt). VERIFIED.
  * autofold-with-height-fix.json (height-fix's two discharges + this one, glue added once): 16/21 -> 19/20 on 39;
    height-fix's spec alone: 16/21 -> 18/20 on 38. Marginal effect of javanpeykarBound: GLUE 0, LEAF +1. Generated
    module compiles, standard axioms (FoldDryRunHF-compile.txt). VERIFIED.
  * If a reading clears PrintedMap (kind published): standalone 16/21 -> 18/21; combined 16/21 -> 20/19, i.e. GLUE -1
    for javanpeykarBound relative to height-fix alone. VERIFIED (dry run only, /tmp specs, not kept).

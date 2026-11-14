# op-dedupe (fleet summary)

**What builds.** `lake build +ZInQKernel.OneProof.Main` succeeds; `#print axioms ZInQ.OneProof.frozenTarget` gives
`[propext, Classical.choice, Quot.sound]`. The H chain (`ZInQKernel/OneProof/H/`) now uses the kernel's
declarations: it imports `Contrib/HeightBC/{StalkPullback,LocalStructure,StalkTensor,CotangentBC}` (LF2Stalks and
LF3Cot are now only imports) and `Contrib/FrobChain/TateBridge`. `scripts/one_proof/gen.sh` no longer reproduces
the H modules; `scratch/one-proof/redo.sh` regenerates them from the leaf-fold4 copies (byte for byte).

**Counts.** 7306 -> 4355 declarations (2951 removed). Of the 3311 map rows: 2941 removed, 365 KEPT, 5 were text
inside comments. Every removed copy was checked at the constant level first (FaithCheck: type/value equal to the
kernel's after renaming, syntactically or by `isDefEq`, as a fixpoint): 3164 faithful, 93 differ. 29 of the 66
bundle fields are now kernel Props (e.g. `PkgI2.RaynaudCriterion`, `PkgI3.FaltingsTate`,
`ZInQ.DefFaltings.R21_Bost`).

**KEPT (365, reasons in scratch/one-proof/kept.txt).** 294 G9 layer (`ZInQ.Contrib.G9.*`: the kernel's G9 is over
its own `ZInQ.Contrib.G9.PkgI4` copy); 22 TateBridge35 and 13 G7/TateBridge (H's `G7Data` differs); 14 `E1Sub.bc*`;
7 leaf-push2 leaves (`ZInQ.LeafPush2.R03/R18/R22*`, over H's leaf-push2 copies); 7 `AbVarBC.abVarBaseChange*`;
3 `GlueOutputs` (hardened `PazukiOutput`); 4 def-faltings EC/example lemmas.

**Discharge.** No field of the four bundles and none of the 9 TYZ/GZ hypotheses is proved anywhere in ZInQKernel/
(Lean search, `scratch/one-proof/search_proofs.tsv`); all OPEN, so there is no `frozenTarget_v2`.

**What remains.** Identify the G9 layer with PkgI4 (294 copies); the leaf-push2, G7Data/TateBridge35 and E1Sub
variants are different statements from the kernel's, which is a decision about statements, not a dedupe. Report:
docs/research/op-dedupe.md; log: scratch/one-proof/log-dedupe.md.

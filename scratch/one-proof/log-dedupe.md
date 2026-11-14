# op-dedupe results log

## Step 1: baseline (2026-11-13 22:55 PST)
- `lake build +ZInQKernel.OneProof.Main`: success, 6m59s wall (11801 jobs; rebuilt part of the tree).
- Main.lean `#print axioms`: `'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]`.

## Step 2a: LF2Stalks, LF3Cot (root namespace) -> HeightBC imports
- Tool: `scratch/one-proof/del_decls.py` (deletes the map's declarations of one module, with attached docstrings and
  `@[..]`/`open .. in` lines; adds the kernel module imports).
- LF2Stalks: 43 of 43 declarations deleted; imports `Contrib.HeightBC.StalkPullback`, `Contrib.HeightBC.LocalStructure`.
- LF3Cot: 6 of 6 declarations deleted; imports `Contrib.HeightBC.StalkTensor`, `Contrib.HeightBC.CotangentBC`.
- `lake build +ZInQKernel.OneProof.Main`: success (5m09s), no edits needed.

## Step 2b: LPrefix, first attempts (all 1746 rows at once)
- Name resolution: inside `namespace HDec.A`, an unqualified `x` never resolves to the kernel's `A.x`, and `open N`
  opens `HDec.N` when it exists. Unknown-identifier errors (e.g. `J2` in `HDec.PkgI1`, autoImplicit turned it into a
  variable). Fix: `scratch/one-proof/add_opens.py` adds explicit-list `open _root_.Q (names)` lines (tag
  `-- op-dedupe`) after each `namespace` and `open` line inside HDec, aliasing exactly the deleted names.
- Map rows inside comments (`class field theory;` etc., 4 in LPrefix): `del_decls.py` skips them (they had opened an
  unterminated comment that silently swallowed 2/3 of the file).
- `include ... in` / multi-line `omit ... in` / `@[..]` lines: attached to the following declaration, not to the
  preceding extent (otherwise `end Kernel` etc. was swallowed).
- Semantic divergence found: `HDec.GlueAssembly.PazukiOutput` (hardened `+3`) differs from the kernel's (`log π`)
  under the same name; `HDec.ZInQ.LeafPush2.stableFaltingsHeight` (leaf-push2's copy, kernel has none) differs from
  the kernel's resolution `ZInQ.DefFaltings.stableFaltingsHeight`. Same text can mean different constants, so the
  text map is not enough. Added a constant-level check (`scratch/one-proof/FaithCheck.body.lean`): with the original
  H chain compiled to /tmp/opd_orig (lean --root, LEAN_PATH overlay), a mapped copy is FAITHFUL when its type (value
  for defs, constructor types for inductives) equals the kernel's after renaming faithful `HDec.m` to `m` (greatest
  fixpoint). DIVERGENT copies are KEPT.
- `ZInQ.DefFaltings.AbVar`: the H copy is a structure; the kernel has the alias
  `abbrev ZInQ.DefFaltings.AbVar K := PkgI3.AbVar K` (Contrib/HeightBC/G0StableBC.lean). The copy (with its
  `baseChange`, `dim`, `ZInQ.H5Neron.AbVar.zero`) is replaced by an import of G0StableBC (fixes/LPrefix.py).

## Faithfulness check (constant level), 2026-11-14 ~01:00
- Original chain (a2de2112 sources) compiled to /tmp/opd_orig with `lean --root=/tmp/opd_root -o ...` (LEAN_PATH
  overlay: /tmp/opd_orig/ZInQKernel/* symlinks to the build dir except OneProof/H). Times: LPrefix 510s, TailC 151s,
  others < 90s.
- Checker `scratch/one-proof/FaithCheck.body.lean` (imports `FaithCheck.imports.txt`: TailK + the map's kernel
  modules except HeightBC.{StalkPullback,...} and FrobChain.{TateBridge and its 6 importers}: TateBridge clashes
  with LF2UnramConj's root `G0ModField.numberField_of_fd`). Comparison: syntactic, else `isDefEq` (400M heartbeats),
  after renaming faithful `HDec.m` -> `m` in constants and in `Expr.proj` structure names, plus the manual
  identification `HDec.ZInQ.DefFaltings.AbVar` -> kernel alias (fields, `baseChange`, `dim`, `H5Neron.AbVar.zero`
  -> `PkgI3.AbVar.*`). Fixpoint in 5 rounds.
- Result (`scratch/one-proof/faith.tsv`): 2905 of 3262 HDec-namespace map rows FAITHFUL; 25 rows are not
  declarations (map rows inside comments etc.); 275 "no kernel constant" (FrobChain modules excluded from the check,
  pending); 57 genuinely divergent (type/value/ctor): the `ZInQ.Contrib.G9` copies (kernel uses its own
  `ZInQ.Contrib.G9.PkgI4` layer), leaf-push2's copies (`HDec.ZInQ.LeafPush2.stableFaltingsHeight`, `IsCurve`, ...),
  `GlueAssembly.PazukiOutput` (+3 vs log π) and everything depending on them.
- `scratch/one-proof/kept.txt` = all DIVERGENT names (332) with the reason; `del_decls.py` skips them.

## LPrefix done
- `redo.sh LPrefix a2de2112 LPrefix.lean`: 1714 declarations deleted (21830 lines), 28 KEPT, 4 comment rows skipped,
  65 kernel module imports + `Contrib.HeightBC.G0StableBC` (alias), 259 `-- op-dedupe` open lines.
- Manual fixes (`fixes/LPrefix.py`): dot notation `ρ.HasHTWeightsAtSelf` on the kernel's `PkgI4.GaloisRep` written
  as `GaloisRep.HasHTWeightsAtSelf (ρ := ρ)` (3 places); DefFaltings.AbVar copy -> kernel alias; 12 `#hdec_same`
  lines whose HDec constant is gone replaced by comments.
- `lake build ZInQKernel.OneProof.H.LPrefix`: success, 0 errors (~3 min).

## TailA-TailE (2026-11-14 early morning)
- TailA: first pass 235 deleted; 2 dot-notation errors (`r.HasHTWeightsAtSelf`) -> generic `fixes/_common.py`
  (`PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r)`, the HDec predicate on the kernel's `PkgI4.GaloisRep`).
- TailB: 129 deleted, 7 dot-notation fixes (common), builds.
- TailC: errors in the `ZInQ.Contrib.G9` block: kernel's G9 is stated over its own layer `ZInQ.Contrib.G9.PkgI4`,
  the H copy over `PkgI4`; the checker accepts many by `isDefEq` but proofs `rw` syntactically. All 294
  `ZInQ.Contrib.G9.*` copies KEPT (manual entry in kept.txt). `QML3.goodReduction` ambiguous (KEPT HDec version vs
  kernel through the `QML3` alias): `fixes/TailC.py` names `LeafQM.AV.QML3.goodReduction`. `open _root_.HDec.PkgI4`
  lines now get kernel aliases too (add_opens).
- TailD: no rows; add_opens only (7 alias lines).
- TailE: import clash `G0ModField.numberField_of_fd` (LF2UnramConj, root namespace) vs Contrib/FrobChain/TateBridge
  (brought in through the new kernel imports). LF2UnramConj: its copy replaced by `import
  ZInQKernel.Contrib.FrobChain.TateBridge` (same statement, `IF = IntermediateField ℚ Qbar`). Explicit
  `_root_.HDec.Y` references to removed copies redirected to `_root_.Y` (common fix, 19 lines).
- Faithfulness check rerun with the FrobChain modules (now importable): 3144 of 3262 FAITHFUL, 93 divergent,
  25 non-declarations. kept.txt = 93 divergent + 272 G9 (365 names). TailA/TailC regenerated with the smaller KEPT
  set: TailA 291 deleted, TailC 316 deleted. LPrefix..TailE rebuild: success (5m49s).

## TailF-TailK, Main (2026-11-14 ~00:40)
- TailF: 45 deleted, builds (45s). TailG: 32 deleted, builds. TailH: 197 deleted; `attribute [instance] AbVar.grp ...`
  (re-attributing the removed DefFaltings.AbVar copy's fields) dropped in `fixes/TailH.py`; builds.
- TailI, TailJ, TailK: no rows; add_opens only (TailJ 31 alias lines).
- `lake build +ZInQKernel.OneProof.Main`: success (11864 jobs);
  `'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- Declaration counts per module: `scratch/one-proof/counts.md` (7306 -> 4355, 2951 removed).

## Step 3: hypotheses
- `scratch/one-proof/PrintFields.lean` prints the 66 fields of the four bundles with their types; run on the original
  chain (/tmp/opd_orig) and on the new one: `fields_before.tsv`, `fields_after.tsv`. Same 66 fields in the same
  order; 29 field types changed from `HDec.X` to the kernel's `X` (each a FAITHFUL copy, i.e. defeq after renaming),
  37 unchanged (H-only definitions or KEPT copies). frozenTarget's 9 TYZ/GZ hypotheses are kernel names already
  (unchanged).

## Step 4: discharge search
- `scratch/one-proof/SearchProofs.lean` (imports Main + the 78 kernel modules that mention a field/hypothesis Prop
  name): for each bundle field and each frozenTarget hypothesis, every non-HDec theorem whose type is the Prop
  (syntactic or `isDefEq`, same head constant). Result `search_proofs.tsv`: no theorem found for any of the 66 fields
  or the 9 TYZ/GZ hypotheses (grep cross-check: only `X1Belyi.TorsionStructure` is proved, not `PkgI2.TorsionStructure`;
  `GenusPointLeafCM` appears in no theorem statement). No `frozenTarget_v2` added (nothing to supply).
- Correction (00:55): 20 map rows had names with a bogus prefix "`ZInQ.Contrib.AbVarBC`.." (a comment line
  "namespace `ZInQ.Contrib.AbVarBC`." read as a namespace, in H and kernel alike); `String.toName` failed on them so
  the checker had not compared them. Rerun with the prefix stripped (`faith_mapped.txt`): all 20 FAITHFUL; the
  divergent set is unchanged (93). Final: 3164 FAITHFUL, 93 divergent, 5 non-declarations (rows in comments).
- Row accounting: 3311 = 2941 removed (2892 HDec + 49 root) + 365 KEPT + 5 in comments.

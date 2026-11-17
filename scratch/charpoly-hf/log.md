# charpoly-hf results log

## Setup (2026-11-16 18:30 PST)
- Base wip/leaf-fold33b 968b59ef8; origin/main c1e4ed1b8 already an ancestor (merge: "Already up to date").
- Build: reflink copy of ~/dzq-wt/leaf-fold33b/.lake/build and lean/.lake/build (that tree is at 4da8d4f32 =
  base + hP23 fold; H chain identical).
- Copied charpoly-charp's sources (origin/wip/charpoly-charp 512080e4) into scratch/charpoly-hf/cc/ for reference.

## Reading findings (VERIFIED by reading)
- charpoly-charp's only char-p input: `exists_minpoly_endE (hH : PkgI3.HomFreeFinite) (hT : TateModuleFree) Ab α`
  (CommonTraceHomFree.lean), applied at FrobTraceLink's `Ab : AbVar k`, `CharP k p`, for ℓ = 3, 5 and
  E = PadicAlgCl ℓ. It uses `hH k Ab Ab` (End free finite + ℤ_ℓ ⊗ End ↪ End T_ℓ) and `hT` (basis of T_ℓ).
- FrobTraceLink (TailC L8674) is existential in (k, Ab, α): no property of α beyond FrobCompare at 3, 5 is available.
- Blueprint names `HDec.HSyn.OpenTextbookLeaves13.charPolyIndepOfEllAlgClosed`
  (blueprint/roadmap/height-decomposition/abelian-varieties/characteristic-polynomial.md L6).

## Lean (VERIFIED, Lean 4.35.0 / Mathlib v4.35.0, axioms propext, Classical.choice, Quot.sound: axioms_out.txt)
- scratch/charpoly-hf/MinpolyCharP.lean (imports TailC) = ZInQKernel/Contrib/OneProof/MinpolyIndepCharP.lean:
  `CharpolyHF.MinpolyIndepOfEllCharP` (def), `minpoly_baseChange_iff`, `exists_minpoly_endE_charP`,
  `HDec.G14Trace.common_trace_of_minpolyCharP`, `g14TraceCompat_of_link_minpolyCharP`,
  `HDec.HSyn.G0AssembleMod.linkedTateData_of_local_minpolyCharP (hM) (hT : TateModuleFree) : LinkedTateLocal → LinkedTateData`.
  Pitfall: `Fintype.linearIndependent_iff.mp h` timed out (whnf) for vectors in `Module.End E (E ⊗[K] W)`;
  explicit `(R := E) (v := …)` fixed it.
- scratch/charpoly-hf/Consequence.lean = ZInQKernel/Contrib/OneProof/MinpolyIndepCharPThm3.lean:
  `HomFreeFiniteAlgClosedCharP` (Mumford §19 Thm 3 printed form, k alg. closed of char p) and
  `minpolyIndepOfEllCharP_of_homFree (hH) (hT) : MinpolyIndepOfEllCharP`.
- Copied verbatim from wip/charpoly-charp: ZInQKernel/Contrib/OneProof/CharPolyLattice.lean (degpoly-proof),
  R16PrintedC.lean (`R16Split.r16_of_printedC`, T7 only at ℚ). All four modules build (lake build, 11765 jobs).

## Taint of the T7 field on the base route (scratch/charpoly-hf/Taint.lean -> taint_out.txt), VERIFIED
- frozenTarget closure 270,833 constants; seeds `*.t7`, `*.charPolyIndepOfEllAlgClosed`; 65 tainted.
- Carriers on the route: OpenTextbookLeaves2HF, 3HF, 4HF, 6HF–14HF (homfree reroute copies) and OpenTextbookLeaves15 (TailZ48).
- Every tainted constant is in Contrib/OneProof/HomFreeFiniteAlgClosedReroute.lean (61), TailZ48 (3), Main (frozenTarget).
  Direct readers: gluePieces_of_open4_hf (t.t7), textbookLeaves4_of_open6_hf (t7 := t7_of_algClosed5 …),
  openResearchLeaves21_of_OpenResearchLeaves22_hf (R16: r16_of_printed … t.charPolyIndepOfEllAlgClosed).
  The original OTL13 (named by the blueprint) is not on the route.

## Fold (swap), VERIFIED in a copy tree (~/chf-foldtree: reflink copy of this worktree without .git; outside the repo)
- `python3 scratch/charpoly-hf/fold_edit.py --tree ~/chf-foldtree` (asserts every match): edits
  Contrib/OneProof/HomFreeFiniteAlgClosedReroute.lean and OneProof/H/TailZ48.lean; diff = scratch/charpoly-hf/fold.patch
  (268 lines; `git apply --check` OK on this branch).
- Field `charPolyIndepOfEllAlgClosed` (Mumford §19 Thm 4) replaced by `homFreeFiniteAlgClosedCharP`
  (`CharpolyHF.HomFreeFiniteAlgClosedCharP`, Mumford §19 Thm 3, k alg. closed of char p). Count-neutral.
- `lake build ZInQKernel.OneProof.Main` there: Build completed successfully (14192 jobs).
- FoldCheck.lean there (foldcheck_out.txt): OTL15 has no charPolyIndepOfEllAlgClosed, has homFreeFiniteAlgClosedCharP;
  blueprint target OTL13.charPolyIndepOfEllAlgClosed still exists; closure 270,888 constants, none of
  AVB1.CharPolyIndepOfEllAlgClosed, PkgI3.CharPolyIndepOfEll, AVB1.HomFreeFiniteAlgClosed, PkgI3.HomFreeFinite,
  HomFreeFiniteAlgClosedNoEmb, sorryAx, OTL13.charPolyIndepOfEllAlgClosed, t7_of_algClosed5, no constant named
  *CharPolyIndepOfEll*; frozenTarget axioms [propext, Classical.choice, Quot.sound].
- Docs there: `lake env lean scripts/one_proof/OpenStatements.lean` (40 open hypotheses); kinds.tsv row renamed
  (source "Mumford 19 Thm 3 (specialization: k algebraically closed of characteristic p > 0)"); claims.tsv row of the old
  field dropped; `render_open.py` -> "33 H hypotheses, strictest 13/20, 7 others"; `render_open.py --check` ok;
  frontier-crosswalk regenerated (H-71 loses its field) and `--check` ok (run in the worktree with the folded
  open-statements.json, then restored). Diff = scratch/charpoly-hf/fold-docs.patch (applies).
- #discharges on this branch (unfolded; Discharges.lean -> discharges_out.txt): 40 open hypotheses, 9222 theorems,
  49 discharge lines; the new modules discharge no field directly (expected: a reroute); the copied CharPolyLattice
  gives degpoly-proof's count-neutral `charPolyIndepOfEllAlgClosed_of_noEmb`; no sorry.
- Not run: autoform (not installed on this host); the DumpCompact hash guard.
- Hash guard (DumpCompact.lean, extended to the reroute module; hashes_0_base.txt, hashes_1_fold.txt, hashdiff.txt):
  14501 -> 14501 constants; only before 10 (the projections `OTL6HF..14HF.charPolyIndepOfEllAlgClosed`,
  `OTL15.charPolyIndepOfEllAlgClosed`), only after 10 (the `homFreeFiniteAlgClosedCharP` projections); changed 86:
  the 14 carrier structures' constructor families (mk, _flat_ctor, rec, casesOn, recOn) and t7 / field projections,
  and the values of gluePieces_of_open4_hf, textbookLeaves4_of_open6_hf, openResearchLeaves21_of_OpenResearchLeaves22_hf,
  the pass-through conversions textbookLeaves6..9_of_open7..10_hf, openTextbookLeaves10..13_of_..._hf,
  openTextbookLeaves14HF_of_OpenTextbookLeaves15. frozenTarget and sixContactMin_of_open41: hashes unchanged
  (constants referenced by name).
- Blueprint targets (BlueprintNames.lean, bp_names.txt = 2531 `lean:` names): 117 not in Main's environment in
  both trees, outputs identical (bpnames_base.txt = bpnames_fold.txt): the fold deletes no blueprint target.
- Composition with fold33-combine (origin/wip/fold33-combine 0e516baa, not yet in leaf-fold33b), VERIFIED:
  reflink copy ~/chf-combinetree of ~/dzq-wt/fold33-combine (without .git) + the four new Contrib modules +
  `fold_edit.py` (renames the field also in its TailZ49 / OpenTextbookLeaves16): `lake build ZInQKernel.OneProof.Main`
  OK (14178 jobs), frozenTarget standard axioms; FoldCheck (foldcheck_combine_out.txt): closure 270,455, no banned
  constant. Text-level dry run of fold_edit.py on that branch's files: OK.

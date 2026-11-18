# fold-cm: replaying the CM-branch package fold on a later head

Jack's ruling (to "Should [the CM-branch package] fold now?"): "Fold now at +4 (Recommended)".

autofold.py's `discharges` format cannot express this fold (the removed fields are unread on the new route, not proved),
so the fold is a chain of generators (`scratch/fold-cm/gen/`), each idempotent (rerun on this tree: identical output) and
each asserting the text it edits. The proof file `ZInQKernel/Contrib/OneProof/CMBranchUC8.lean` (the CM branch on
fold-c8's base bundles) is separate from the fold. Every step was run once here; every generated module compiled on the
first or second try. Run from the repository root, one Lean process at a time.

## 0. Merges (skip if the head has them)

    git merge 664e00417     # origin/wip/cm-fold-rebase (cm-branch, cm-branch2, cox-lattice, cm-fold-rebase); all files added
    git merge 9a2bbbe3f     # origin/wip/y3-x6b (y3-p1j, y3-x6, y3-x6b); all files added

Hygiene (commits 500a44fd4 and the component-2 WIP commit here): rename `scratch/cm-branch/CMBranchMain.lean`,
`scratch/cm-branch2/gen/top2_header.lean`, `scratch/cm-fold-rebase/MainDryRun.lean`, `scratch/y3-x6b/MainDryRun.lean` to
`.lean.txt`; remove the host paths in `scratch/cm-branch/gen/mk_localize.py` and `scratch/cm-branch2/gen/gen_open73.py`.

## 1. Component 1 (cm-fold-rebase)

    lake build ZInQKernel.Contrib.OneProof.CMBranchUC8 ZInQKernel.Contrib.OneProof.CMBranch2
    python3 scratch/fold-cm/gen/mk_top_live.py ZInQKernel/OneProof/H/TailZ<k>.lean sixContactMin_of_open<N> ZInQKernel/OneProof/H/CMTopLive.lean
    lake build ZInQKernel.OneProof.H.CMTopLive
    lake env lean scratch/fold-cm/DirtyCM.lean > scratch/fold-cm/dirty-cm.tsv      # ~9 min; root = the `_cm` top
    python3 scratch/fold-cm/gen/gen_r5live.py && lake build ZInQKernel.OneProof.H.CMR5
    python3 scratch/fold-cm/gen/gen_open81.py && lake build ZInQKernel.OneProof.H.TailZ88
    python3 scratch/fold-cm/gen/fold_main1.py
    lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
    bash scratch/fold-cm/run_checks.sh 1 hashes_fold0.txt     # after a base DumpCompact into /tmp/fcm/hashes_fold0.txt

Head-dependent points (edit if the head moved):
* `mk_top_live.py` walks from the head's top through every TailZ (k >= 87, not fold-cm's) and `C8Chain.lean` down to
  `sixContactMin_of_open4_hf_pz_eb_u_c8`; a research-only autofold top above open80 is picked up automatically. A head
  whose chain base is not fold-c8's `_u_c8` base needs a new `CMBranchUC8.lean`.
* `DirtyCM.lean`: the `root` name (`HDec.HSyn.sixContactMin_of_open<N>_cm`).
* `gen_open81.py`: `TOPK, TOPN, TOPR` (head TailZ, top, research bundle) and the chain of bundles that carry
  `gonzalezRotgerThm512X6RCF` (61 -> 60 -> 59 -> 54SFU -> GR9 36EBCFSFU -> 35EBCFSFU); an autofold that added research
  generations above 61 carries the field too: copy those generations the same way (one more `drop_field` block each).
* `fold_main1.py`: the Main.lean patterns (import TailZ87, binder OpenResearchLeaves61, call open80).

## 2. Component 2 (y3-x6b), after component 1

    lake build ZInQKernel.Contrib.OneProof.Y3X6.Row
    python3 scratch/fold-cm/gen/gen_y3live.py && lake build ZInQKernel.OneProof.H.Y3Copy6
    python3 scratch/fold-cm/gen/gen_top_y3.py && lake build ZInQKernel.OneProof.H.TailZ89
    python3 scratch/fold-cm/gen/fold_main2.py
    lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
    bash scratch/fold-cm/run_checks.sh 2 hashes_fold1.txt
    lake env lean scratch/fold-cm/ClosureX6.lean > scratch/fold-cm/closure-x6.txt   # the integrator's closure scan

`gen_y3live.py` imports y3-x6b's `scratch/y3-x6b/gen/gen_y3b.py` (DELETE, REPLACE, PATCH, field rule) and replaces its
bost-gr9 entries by the live chain's (`..._sf_u_c8`, `..._sf_u`); the copies are suffixed `_y3c` because y3-x6b's own
`_y3` names exist in `Contrib/OneProof/Y3X6/Copy*.lean`. `gen_top_y3.py`: constants `K, N, R` (component 1's top).

## 3. Expected outcome

render_open: 33 H hypotheses, strict 5/28, strictest 5/28 (base 5/24 on 29). Hash guard: only `frozenTarget` changes.

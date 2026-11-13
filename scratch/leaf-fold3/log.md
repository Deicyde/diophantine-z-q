# leaf-fold3 results log

## 11:44 start (fresh; no earlier log)
- Base 88dc9bd4. Merged origin/wip/kummer-comp (423d6b7c) and origin/wip/hecke-rest (e27601d8): both have reports.
- Copied leaf-fold2's build (parts/, scripts, root-module sources) into scratch/leaf-fold3/.
- mk_prefix.py: issue #2 items (2) kernel's strengthened `fibre_conjugates_isomorphic` (ZInQKernel/HDecomp/QM/Leaves.lean:500,
  with its proof; the weak one had no user), (5) second `#print axioms HSyn.sixContactMin_of_leaves` dropped, (8) QM "Lemma P"
  -> "Lemma QP" (25 occurrences; `lemmaP_lattice` keeps its Lean name, which lives in rv-qm-polar and the kernel, with a note).
- mk_g7bound.py: g0-assemble3's G7Data fix (`[L:ℚ] ≤ D` as last clause) in parts 75, z85, z86; diff against g0-assemble3's
  parts = HDec header/open lines only.
- mk_lf3.py: new parts partsF/c10 (Burnside), c20 (cpts-transport), c40 (kf-glue d20 lines 1-15, 431-end), c50 (twist-descent),
  c60 (hodge-bc2), c70 (linked-tate c10-c15), c75 (lt-goodred 99d); c30 (hom-unify) and d90 (fold) hand-written;
  root module LF3Cot (infra-stalks CotangentBaseChange lines 523-end).
- lake build of the kernel modules needed (Contrib T14 T28 RLeaf HeightBC HodgeBC2 Mobius Dim TwistDescent FrobPieces HomUnify
  AbVarBC, HDecomp QM.Pin etc.) started 11:47.

## 12:01-12:38 olean chain, VERIFIED compiled
- LPrefix 558 s, TailA 66 s, TailB 98 s, TailC 171 s, TailD 9 s, LF2Stalks/UnifRoot/SmoothDim/UnramConj/LF3Cot 6-12 s each,
  TailE 57 s (with `import ZInQKernel.Contrib.Mobius.Main` in place of the scratch module LF2ImagePlane): all 0 errors.
- TailF: first run failed at import: `ZInQKernel.Contrib.RLeaf.T40` (via TateCuspMuN/TateCuspTorsion) imports Tau Ceti's
  `Backport.Algebra.Group.Units.Basic`, which clashes (`Units.val_mul_zpow_natCast_mul`) with
  `ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic` already in the chain (T14 etc.). T40 import dropped; field t40 kept.
- TailF second run: 2 errors, twist-descent's PartGDM (`GaloisDescentMor` not defined in g0-assemble3's kf-glue port);
  PartGDM omitted (unused). Third run: TailF 41 s, 0 errors.
- TailG (Prop. TS): 101 errors at first (orphan `attribute … in` before dropped duplicates; duplicates of chain declarations;
  typeclass timeouts in kummer-comp's core; ts-kummer's current file has a forward reference). Fixed in mk_propts.py:
  drop the `… in` modifiers with a dropped declaration, dedup against the chain, `synthInstance.maxHeartbeats 400000`,
  KummerComp.lean in place of KummerTS.lean, one rewrite `rw [bcPt` → `rw [LeafAdopt… LeafQM.AV.bcPt`; chunker fixes
  (one-line `@[simp] lemma`, attributes after docstrings). TailG 69 s, 0 errors.
- TailH (lt-local route): 7 errors, then 3 (text-identity dedup across namespaces dropped `ZInQ.NeronLG` lemmas and an
  anonymous instance of another namespace); fixed by keying anonymous instances by namespace + text and no text dedup
  in mk_ltlocal.py. TailH 283 s, 0 errors.
- TailI (d90_fold3.lean) 29 s, 0 errors. All 16 `#print axioms` lines read `[propext, Classical.choice, Quot.sound]`,
  including `HDec.HSyn.sixContactMin_of_open3`, `gluePieces_of_open3`, `propTSAll_of_pieces3`, `linkedTateLocal_of_leaves3`.
- olean/Check3.lean: `example : (∀ r t l g, _root_.ZInQ.SixContactMin) := HDec.HSyn.sixContactMin_of_open3` compiles, so the
  conclusion is the kernel's own `ZInQ.SixContactMin`.
- Counts: 26 + 20 + 16 + 6 = 68 (leaf-fold2: 26 + 18 + 13 + 9 = 66); glue 9 → 6, SPECULATIVE glue 2 → 0.
- 12:40 olean/chain_log*.txt (compile logs with host paths) were committed by mistake in 0-2 commits before this; untracked and gitignored since.

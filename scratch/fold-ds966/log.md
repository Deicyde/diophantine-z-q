# fold-ds966 log

Base: wip/leaf-fold33b cdbee71f (TailZ73, `sixContactMin_of_open66`; render_open: 38 open, H strict 4/29 on 33).

## Fold 1: dsThm966Printed (fork PR #48, origin/cloud-b3s/c5-deligne-serre bc93461d)

1. Branch content (VERIFIED, git): merge base with the fold head is 5c7d9ba7 (main), so the branch's own changes are
   `git diff 5c7d9ba7 bc93461d`: 4281 files, all added, all under ZInQKernel/Contrib/: 7 proof files
   (OneProof/DSThm966PrintedProof.lean, CloudB3SC5DeligneSerre/{BridgeLemmas,PrintedBridge}.lean,
   CloudB3SC5FiniteImage/ContinuousFiniteImage.lean, CloudB3SC5ChebotarevBridge/ClassWeighted.lean,
   CloudB3SC5NewformReduction/{Basic,G9}.lean) and 4274 vendored files under
   CloudB3SC5DeligneSerre/Vendor/AnthropicFLT/ (4269 .lean, LICENSE, NOTICE, NOTICE.upstream,
   ATTRIBUTION.upstream.md, SOURCE_MANIFEST.json). The 1360 in-tree modules the closure uses are unchanged between
   5c7d9ba7 and cdbee71f.
2. Pruning (VERIFIED, scratch/fold-ds966/closure.py over the import lines of the branch): the import closure of
   ZInQKernel.Contrib.OneProof.DSThm966PrintedProof has 5633 project modules, among them all 4269 vendored .lean
   modules of the new copy (and 148 of CloudB3W16Torsion's, some of CloudB2X0Transitive's). Pruning removes 0 files:
   the copy is already exactly the closure (the branch had pruned it, and commit 416f2bf5 re-pointed 124 modules to
   CloudB3W16Torsion's copy).
3. Re-pointing (VERIFIED, scratch/fold-ds966/dupscan.py): none of the 4269 upstream module names of the new copy
   occurs in any vendored copy already in the tree (CloudB3W16Torsion, CloudB2X0Transitive, CloudW02Connectedness,
   CharPolyPort; 2203 AnthropicFLT modules), so there is no textually identical module to re-point to: the copy is
   kept whole.
4. Build tree: .lake/build copied (cp --reflink) from ~/dzq-wt/leaf-fold33b at the same commit cdbee71f (Main and
   Discharges built there; 6249 of the 6284 Contrib modules had oleans).
5. CONTRIB-BUILD before the fold (VERIFIED, scratch/fold-ds966/contrib_build.sh = `lake build` of every
   `git ls-files 'ZInQKernel/Contrib/*.lean'` module by name, 6284 modules, under /usr/bin/time -v; cgroup
   memory.current sampled every 2 s, includes page cache; LEAN_NUM_THREADS=8; host load ~30):
   - before1 (fills the 405 modules missing from the copied tree, replays the rest; 16296 jobs): wall 14:12.75,
     user 4254 s, sys 762 s, max RSS of one process 14,753,284 kB (14.1 GiB), cgroup peak 26.0 GB; success.
   - before2 (no-op rerun, fully warm): wall 0:15.73, max RSS 1,059,712 kB, cgroup peak 12.0 GB; success, 0 built.
   Files in scratch/fold-ds966/measure/.
6. Base dump (VERIFIED): scratch/fold-ds966/DumpCompact.lean -> hashes_0_base.txt, 17442 constants; frozenTarget
   standard axioms (dump_0_base.out). render_open --check at base: 38 open, strict 4 published / 29 glue.

# hdec-adopt5a results log

- 01:16 start. Base 883c4ddf. No ZInQKernel oleans in the worktree: base build started (one lake).
- h5-neron is NOT merged in the base (origin/wip/h5-neron = b7c1dc21, merge-base 01267822).
  Sources read with `git show origin/wip/h5-neron:scratch/h5-neron/<f>.lean` into
  scratch/hdec-adopt5a/src/ (no merge, so no file outside this task's paths changes).
- Duplicate scan (scratch/hdec-adopt3/dups.py on the five drafts): no draft declaration is a
  verbatim copy of an HDecomp declaration (11 same-last-name hits, all different code in other
  namespaces). No full name is declared in two drafts. C9's copies (FrobeniusDense, PkgI4 leaves
  R14/T24/T25/AttachedUpToTwist) come from scratch/h-decomposition/Leaves.lean, not in the build:
  kept.
- Docstring repairs applied: VSurjOfSurjective (ModCurves/Glue.lean), Ej (ModCurves/Defs.lean),
  R03_LinYang (LeafPush2/R3.lean).

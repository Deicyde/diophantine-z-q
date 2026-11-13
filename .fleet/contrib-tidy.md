# contrib-tidy (final)

**Verdict.** The Contrib folders are ready for two proof-only upstream PRs. The drafts are in
`docs/research/contrib-tidy.md`. No PR was opened.

**What changed.** These edits touch only files under `ZInQKernel/Contrib/`:
- The two verbatim copies of bp-hecke-fe's `HeckeFE.lean` are now one shared module,
  `ZInQKernel/Contrib/HeckeFE/Basic.lean` (namespace `ZInQ.Contrib.HeckeFE`). `GaussPointCount` and
  the other definitions are defined once.
- `GaussFE/` and `HeckeAll/` import the shared module.
- Provider names and types are unchanged. VERIFIED by `Expr` equality in
  `scratch/contrib-tidy/Types.lean`.
- No statement changed except the namespace of the shared copy.
- Lint: the deprecated `if_pos`-family names are replaced, no-op tactics are removed, and lines are
  wrapped to at most 100 characters. One exception is an unsplittable 115-character upstream
  identifier. Every module has a docstring.

**What compiles (VERIFIED).**
- All 15 Contrib modules build, and so does `lake build ZInQKernel`.
- `scratch/contrib-check/Check.lean` compiles unchanged. Its six `#print axioms` lines are all
  `[propext, Classical.choice, Quot.sound]`. Every one of the 389 `ZInQ.Contrib` declarations uses
  only those three axioms.
- Upstream main is `a5937595`, the merge of PR #36, with the kernel contract and CI scripts. The
  Contrib import closure (538 files) is byte-identical to it.
- Upstream's `audit_kernel.lean` passes on both file sets. For PR 1, `heckeContinuation` and
  `functionalEquation5` show `proved_exact_type`.
- Upstream's `check_kernel_contract.py` routes both PR commits (a5937595 + files, built by
  `scratch/contrib-tidy/make-pr-commits.sh`) to `proof_only_astra_review` with no lock change.

**What remains.**
- Seven `unusedSectionVars` warnings. Fixing them would change lemma signatures, which the task
  forbids.
- Create the branches with `make-pr-commits.sh HEAD <br1> <br2>`, push them and open the PRs. A PR
  must contain only `ZInQKernel/Contrib/**/*.lean`.
- Rebase if upstream main has moved past `a5937595`.
- `docs/research/gauss-proof.md` and `hecke-all.md` still cite the old file paths; they belong to
  other tasks.
- Optional: split the 2765-line `HeckeFE/Basic.lean` into smaller modules.

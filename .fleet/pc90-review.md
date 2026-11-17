# pc90-review (fleet note)

**Verdict: PR #90 (head 517e05cce) is NOT ready to land as is, for one reason only:** the retained supplement
S12 (`scratch/upstream/parity-frozen-4eaee875.tex`, 718 lines, md5 = Elliot's copy) is committed in the tree
(commit 4b2595108, whose message claims the opposite). Remove it and squash/rewrite the history before merging
publicly. Apart from that the PR is clean.

**Compiles.** `lake build ZInQKernel.OneProof.Main ZInQKernel.MainGreenTao`: 16114 jobs, success. All 50 PR
modules: 16166 jobs, success. `#print axioms`: frozenTarget, the MainGreenTao headline (unchanged) and 20 new
main theorems are standard (propext, Classical.choice, Quot.sound). No sorry/admit/axiom. Rescale's
`simp only [polePoly_eq]` builds.

**frozenTarget** takes `r t l` (H bundles), `hRC : RestrictedConverseGenuine`, `h54 : Lemma54`,
`hKum : KummerSelmerM`, `hB : BCDTThmA`, `hK : KolyvaginThm1`. `hKum` is proved in the PR (`kummerSelmerM`),
but it cannot be imported next to the H chain: the divisorSum clash (Tau Ceti vs vendored AnthropicFLT) was
confirmed by `scratch/pc90-review/Compose.lean`. Fixing that clash is the only way to shorten the list.
kolyv-cst-printed's `KolyvaginThm1Printed` swaps in for `hK` one-for-one (`Compose2.lean` compiles).

**Manuscript L1019–1121:** no error. The vector a (S12 L586–587) and the Boolean assignment (S12 L677–688)
were checked by hand. Steps 3, 7, 9, 10, 12, 14 and 15 rest on S12 only. Mazur–Rubin is not cited by the
manuscript: route departure, but off frozenTarget's path. Leaf-label issues: Lemma54 is a manuscript lemma,
not a printed one; KolyvaginThm1 over IsModular needs BCDT plus Kolyvagin together. Stale tex line numbers in
Leaves.lean. Report: docs/research/pc90-review.md.

**Remains:** remove S12 from the PR; resolve the divisorSum clash to drop hKum; the Kolyvagin and BCDT prints
are still unread.

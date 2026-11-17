# abhyankar — summary

**Proved:** `SGRDirect.NVLocal.TameBranchNormal` (nv-local, SGRDirectNVLocal.lean:627), outright, no new leaf, and with it
the sgr-fold glue field `nvLocalInertia : SGRDirect.NVLocalInertia`.

```lean
theorem Abhyankar.tameBranchNormal : SGRDirect.NVLocal.TameBranchNormal   -- no hypotheses
theorem Abhyankar.nvLocalInertia : SGRDirect.NVLocalInertia             -- := nvLocalInertia_of_tame tameBranchNormal
```
`#print axioms`: both `[propext, Classical.choice, Quot.sound]`. Statement unchanged (verbatim copy checked `rfl`,
scratch/abhyankar/Statement.lean); it is true as stated.

**Files:** ZInQKernel/Contrib/OneProof/Abhyankar.lean + 11 helpers in ZInQKernel/Contrib/OneProof/Abhyankar/ (159 KB total;
imports SGRDirectNVLocal, never Main). `lake build ZInQKernel.Contrib.OneProof.Abhyankar` OK.

**Method** (dimension-2 Abhyankar lemma, nv-local §2.3): localize; Kummer field Ω = L(f^{1/N}, g^{1/N}), N = [L:K] < p;
A[t,u] regular local dim 2; its integral closure in Ω is unramified in codim 1 (base change off fg = 0; Abhyankar for DVRs =
chain's `t2_proved` at (f), (g)) hence étale (chain's purity `purityGlobalDim2'`); étale over a regular surface germ ⇒ unique
DVR branch of t = 0; descent by going down and the trace as Reynolds operator ([Ω:L] prime to p).

**#discharges** (scratch/abhyankar/discharges.txt): 61 open, 6 discharge one (earlier contributions); none of this task's
theorems at this base, since `nvLocalInertia` exists only after sgr-fold.

**Fold:** scratch/abhyankar/autofold.json = `{"field": "nvLocalInertia", "proof": "_root_.Abhyankar.nvLocalInertia"}`.
Real dry-run possible only after sgr-fold lands; a dry-run on sgr-fold's files (git archive into /tmp) succeeds:
strict 45/10 on 55 → 45/9 on 54 (GLUE −1), strictest 43/12 → 43/11; the generated `OpenGlue9` is empty (or drop
`OpenGlue8` by hand, filling `nvLocalInertia := _root_.Abhyankar.nvLocalInertia` in `openGlue7_of_OpenGlue8`).

**Remains:** nothing for this target. Report: docs/research/abhyankar.md.

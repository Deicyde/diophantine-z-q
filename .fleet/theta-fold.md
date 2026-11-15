# theta-fold (fleet report)

**Result.** In `ZInQ.OneProof.frozenTarget`, the added-leaf field `thetaRatiosAlgebraic` (composite, GLUE) is
replaced by two printed leaves: `igusaThetaExpressions` (Igusa 1964/1967) and `linYangEx29All` (Lin–Yang 2020,
Ex. 29, relations only). The proof is igusa-alg's, theta-split's, theta-glue's and linyang-printed's. VERIFIED:
`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` OK; frozenTarget axioms
`[propext, Classical.choice, Quot.sound]`; PruneScan 0 unused of 57.
- kinds.tsv, H rows: 56 → **57** fields; strict 46/10 → **48/9**; strictest 45/11 → **47/10** (GLUE −1, fields +1).

**How.**
- `ThetaRatiosAlgebraic` (universal over all abelian varieties) does not follow from the leaves, so the consumer was
  changed. The only reader was TailK's `gluePieces_of_open4`.
- theta-split's use form `ThetaRatiosAtQM` and `thetaPointOfFibre_of_qm_atQM` moved into TailK unchanged. The
  consumer takes `hθ : QMHauptmodul → ThetaRatiosAtQM` and applies it to `l.qmHauptmodul`. `hθ` is threaded through
  `sixContactMin_of_open4` … `_open28`.
- New TailZ41: `OpenAddedLeaves18` (+2 leaves), its conversion, and `sixContactMin_of_open29`, which supplies `hθ`
  from the leaves. Main.lean is switched to it.
- PruneScan then flagged `thetaRatiosAlgebraic` in 12 generations. The prune removed those 12 fields,
  13 assignments, one constructor element and 3 dead readers.
- Contributor modules `ZInQKernel/Contrib/OneProof/LinYang{Kron,Split,Glue,Printed}.lean` (51/16/64/31 KB). They are
  deduplicated against the environment (DupScan; gt-theta's `Mat4`, the chain's `Countable B`) and trimmed to what
  the fold uses (Dead.lean).
- Hash guard: changed constants are only bundle auxiliaries, 13 conversions, 23 stack theorems (binder), the edited
  consumer and frozenTarget. DischargesTest gives the same controls, 64 open hypotheses. The docs/one-proof files and
  STATUS.md are regenerated (`--check` ok).

**What remains.**
- Both leaves' locators are UNVERIFIED and flagged "pending review"; Lin–Yang's display was not re-read.
- `QMHauptmodul` still comes from the chain. Deriving it from the leaves would need "ψ₄, ψ₆, χ₁₀, χ₁₂ have no common
  zero on Ω(ℍ)", which is not proved.
- frontier-crosswalk.tsv rows H-44, H-133, H-134, H-191 need their owner's update.

Report: docs/research/theta-fold.md. Log and tools: scratch/theta-fold/.

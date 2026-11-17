# etaw32-proof (fleet summary)

**Verdict: `hW : ZInQ.CdOpt.EtaW32Character` is proved in Lean**, outright, from Mathlib's `η` (definition plus
`eta_comp_eq_csqrt_I_inv`). No new leaf, no hypothesis, standard axioms only. Folding it removes `hW` from
`frozenTarget`: −1, no new leaf.

**What compiles** (Lean 4.35.0 / Mathlib v4.35.0, base wip/leaf-fold33b 0e3c3125):
- `ZInQKernel/Contrib/OneProof/EtaW32Character.lean`, `etaW32Character_proof : ZInQ.CdOpt.EtaW32Character`
  (`lake build +ZInQKernel.Contrib.OneProof.EtaW32Character` OK; axioms propext, Classical.choice, Quot.sound).
- `#discharges` (scratch/etaw32-proof/Discharges.lean): `DISCHARGES [hW] … still assumes: []`.
- `scratch/etaw32-proof/FoldCheck.lean`: the manual fold, `ZInQ.FrozenTarget` without `hW` (Main's body verbatim
  otherwise), standard axioms.

**How the proof works.** The law for `c = 32` comes from the S- and T-laws, with an explicit square-root branch
argument. The exponents give `e^{πi(A+B)/4} = χ₈(d)`. A strong induction on `|c|` then reduces every element of
`Γ₀(32)` with elements whose lower row is `(32, s)`, `s` odd. No generating set, no numerics, no native_decide.

**What remains.** The integrator applies the fold in `Main.lean` (binder `hW` removed, proof passed to
`grossZagierFormulaCd_of_alg`, import of the new module) and regenerates OPEN.md and kinds.tsv. Report:
docs/research/etaw32-proof.md.

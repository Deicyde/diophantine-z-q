# poincare-proof (2026-11-16)

**Verdict: the field `poincareComplement` is proved, with no new leaf (−1 hypothesis).**
`ZInQ.Contrib.OneProof.PoincareComplement.poincareComplement_of_open` (ZInQKernel/Contrib/OneProof/PoincareComplement.lean)
proves `ZInQ.Contrib.AVB1.PoincareComplement` exactly as stated (every char-0 field, no narrowing) from five fields
already in the bundles: `{l}.picRepresentableAbVar`, `{l}.picZeroAbVar`, `{l}.phiAmpleIsogeny` (t09-pic L1-L3),
`{l}.milneIsogenyQuasiInverse`, `{t}.cartierSmooth`. It also uses `AbVarBC.mulIsogeny`,
`AVGlue.imageFactorization_of_cartier` and `T09Pic.veryAmpleIsAmple`, which are already proved.

Proof: `ψ : J → Pic⁰_B` classifies `(i×1)^*Λ(L)`, `ψ∘i = λ_{i^*L}`, an isogeny by L3. With φ' a quasi-inverse of `ψ∘i`,
put `F = [d] − iφ'ψ`, `C = im F`, `m = i + g : B×C → J` and `m' = (φ'ψ, h)`. Then `m'm = [d]_J` (so m is surjective) and
`mm' = [d]×[d]` (so m is finite by `IsFinite.of_comp`).

What compiles (VERIFIED): `lake build +Main +Discharges +Contrib.OneProof.PoincareComplement` succeeds.
`#discharges` reports `DISCHARGES [OpenTextbookLeaves12.poincareComplement]`, assuming only those five fields, with standard
axioms. The autofold dry-run (scratch/poincare-proof/autofold.json) goes from strict 34/11 on 45 to 33/11 on 44, and the
generated module compiles.

What remains: the integrator's fold (run autofold without --dry-run, then the hash check and OPEN.md regeneration). Note
for later folds: the t09-pic leaves L1-L3 and milneIsogenyQuasiInverse now have this second consumer.
Report: docs/research/poincare-proof.md.

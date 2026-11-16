# sga7-35-proof (fleet summary)

**Verdict.** The field `sga7_IX_3_5_ForwardGeom` (SGA 7 IX Prop. 3.5, forward direction, over a strictly henselian
trait) **cannot be proved outright** from Mathlib, the bundle fields and ZInQKernel/. It stays a leaf. The target
(-1, no new leaf) is not met. The deep input is Grothendieck's orthogonality theorem (SGA 7 IX 2.4) with the
semistable rank count, and no field or library supplies it:
* `raynaudSemistableSH` is the converse direction;
* `sga7_IX_3_3_SH` and the Néron fields give only `T^{I'} = T^I`, which does not force unipotence over a strictly
  henselian base.

The statement uses genuine definitions; no falsity or vacuity was found.

**What compiles (VERIFIED, standard axioms).** `ZInQKernel/Contrib/OneProof/SGA7IX35Orth.lean`:
`SGA7Orth.sga7_IX_3_5_ForwardGeom_of_orth` proves the field, statement unchanged. Its inputs:
* one new leaf, `SGA7Orth.GrothendieckOrthogonalitySS`: semistable `A` over a strictly henselian `O`; a point of
  `A[ℓⁿ]` orthogonal, under Mumford's Weil pairing, to the `G_K`-invariants of `Pic⁰[ℓⁿ]` is `G_K`-invariant;
* the bundle leaves `picRepresentableAbVar`, `picZeroAbVar` and `weilPairingMumford`.

Proved glue:
* `μ_N(K̄) ⊆ K` by Hensel;
* `e(σx - x, y) = 0` for invariant `y`;
* the passage from `K^s` to `K̄`.

`#discharges` and the autofold dry run: see docs/research/sga7-35-proof.md §7.

**Rating, recommendation.** The new leaf is a **consequence**, not printed form: SGA 7 IX 2.4, plus the rank
formulas, the finite-level passage and the comparison of the pairings. Consequences count GLUE, so the fold would
raise the GLUE count by one. **Do not fold.** Keep `sga7_IX_3_5_ForwardGeom` as the printed leaf. The reduction is a
map for whoever formalizes SGA 7 IX: everything except the orthogonality theorem is done in Lean.

**Narrowing.** Every consumer goes through r6 at number fields:
* TailH, `dim A = 2` and wild `σ`;
* `goodReduction_of_QM_rational3`, QM surfaces at `ℓ = m = 3`.

All of them need unipotence in general, so no narrowing avoids the orthogonality theorem. A char-0 / perfect-residue
restriction would only remove the `k(s)`/`κ̄` reading risk of the existing leaf.

**What remains.** The locators (SGA 7 IX 2.4 and 3.5, whether 3.5 prints a clause `(T'_f)^⊥ ⊆ T_f`) are
UNVERIFIED (no network).

Report: docs/research/sga7-35-proof.md. Log: scratch/sga7-35-proof/log.md.

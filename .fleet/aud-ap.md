# aud-ap report: audit of the statements of route AP (ap-lean)

Deliverable: `docs/research/aud-ap.md`. Log: `scratch/aud-ap/log.md`. Scripts: `scratch/aud-ap/`
(`goodprimes.py`, `Derive.lean`, `Axioms.lean`, with their outputs).

## Verdict

**The statements are faithful as written.** `ZInQ.GoodPrimeAP` is 22P_AP of nt-22p §3.3. It has
the same quantifiers, `x ≥ 1`, `v ≥ 1`, the bound `max S_b` (written as "larger than every
element of `S_b`", an equivalent form since `S_b` is a non-empty Finset), and the set `G` of
`GoodSlopePrime`. It follows from Green–Tao 2008, Theorem 1.2, and the positive relative upper
density of `G` (Proposition D), with no further condition. I proved this implication in Lean
against the branch (`AudAP.goodPrimeAP_of_greenTao_propD`). The variant has the main theorem's
conclusion `FrozenTarget` and its other two hypotheses (`SixContactMin`, `CertifiedRank`), none of
which the branch changes. The new definitions match the note and the referees' corrections. They
appear only in intermediate statements, so they cannot weaken what the variant proves.

## Checks

- `lake build ZInQKernel`: success (9593 jobs), no `sorry`.
- `python3 scripts/check_target.py`: "FrozenTarget matches".
- `#print axioms` on the variant and on `slopeRepresentationAP_of_goodPrimeAP`:
  `[propext, Classical.choice, Quot.sound]`.
- grep of the new modules for `sorry`/`axiom`/`native_decide`/`implemented_by`/`extern`/`set_option`
  (and `unsafe`, `partial`, `opaque`, `macro`, `elab`, `#eval`): no hits in code.
- Diff against the merge base with `main`: only new files, plus the import, docstring bullet and
  theorem added to `Main.lean`.
- An independent transcription of `GoodSlopePrime` agrees with the CM description at every prime
  `324 < p < 20000` (240 good primes). Its relative density in `(324, 2·10⁶)` is 0.1063, against
  the Euler product 0.1060.
- Green–Tao Theorem 1.2: I checked the statement and its number in the arXiv TeX source.

## Findings (none critical or major; none in a Lean statement)

1. **Moderate (trust base).** Proposition D is still a sketch. It is the only unwritten step
   between the published theorem and `GoodPrimeAP`. The docstring says so.
2. **Minor (citation).** Green–Tao prove Theorem 1.2 only in outline. The outline is in §11
   ("Further remarks") of arXiv v6; the docstring says §10. A complete proof of the needed form is
   the main theorem of Tao–Ziegler, Acta Math. 201 (2008), with `P_i = (i − 1)m` and `m > 0`. I
   checked its statement in the TeX source, not its proof.
3. **Minor (docs).** The bullet in the `Main.lean` module docstring calls 22P_AP a consequence of
   Green–Tao alone. It also needs Proposition D.
4. **Cosmetic.** Some clauses are redundant: the seven non-divisibility clauses of `PoleAbsorbHyp`,
   and `1 ≤ x` in `GoodPrimeAP`.
5. **Observation.** The hypothesis asks for `K + 1` terms for every `K`, which is more than the 14
   terms Proposition AP uses. This is the form Green–Tao provides.

## Suggestions

- Write out Proposition D, in the form "positive relative upper density", by the route that avoids
  Hecke (nt-22p §2.2, `rv-nt22p-ap` F5).
- Cite Tao–Ziegler 2008 in the docstring of `GoodPrimeAP`, fix the section number, and add
  Proposition D to the `Main.lean` bullet.
- Optionally add `GreenTaoDense`, `PropDUpper` and `goodPrimeAP_of_greenTao_propD`
  (`scratch/aud-ap/Derive.lean`) next to `GoodPrimeAP`. The trust statement then becomes a
  kernel-checked implication from two named statements.

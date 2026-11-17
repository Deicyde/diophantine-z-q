# h29-proof (final)

**Verdict: `hL29` (TYZ Lemma 2.9 as printed, n ≠ 3) is not removable now.** It cannot be proved outright, and the
open leaves TYZProp23Printed, TYZTestVectorExists, LegendreThreeSquares and JonesPallX2Y2Z16 cannot reach it. It equates
the Brandt genus period Q(n) with Σ ε𝓛(d₁)𝓛(d₂), which means exact values of L(E_d,1)/Ω for infinitely many d.
That needs the explicit Waldspurger formula (TYZ Thm 2.1 / 4.2), and Lean does not have it. The TYZ source was not
on this host, so TYZ line numbers are quoted from the earlier reports.

**Fallback (compiled, standard axioms; LEAF +1, GLUE 0, so not a fold to make now).**
`ZInQKernel/Contrib/OneProof/TYZLemma29Genus.lean`:
`H29Genus.tyzLemma29PrintedNe3_of_genus : TYZThm21Pairs → TYZLemma28Sym → TYZLemma29PrintedNe3`.
* TYZThm21Pairs is TYZ Theorem 2.1 for every pair n = d₁d₂, with the genus characters χ_T. Rated printed form,
  restricted.
* TYZLemma28Sym is TYZ Lemma 2.8, the symmetry for n ≡ 1 (mod 8). Rated printed form, restricted.
* The glue is TYZ's own proof of Lemma 2.9, all proved in Lean:
  * (PQ), Σ_{d∣n} P = 2^k Q(n), from the project's principal genus theorem (Redei.range_sq_eq_ker_chi);
  * the product formula for n ≡ 3;
  * the divisor pairings;
  * #μ(ℚ(√−n)) = 2 for n ≠ 3.
* The same two leaves also give the w_K form at every n and TYZThm21At31.
* `#discharges` against the base and against merged origin/main (5e235a40) both print:
  `DISCHARGES [hL29] … still assumes: [TYZThm21Pairs, TYZLemma28Sym]`, axioms standard.
* Numerics: 28 runs. An independent model review found both leaves faithful. It also ran a 552-run sweep, which
  exceeded the 30-sample rule; that is noted in the log.

**Remaining.**
* Lemma 2.8 follows from TYZProp23Printed plus the uniqueness of the test vector, via the twist f ↦ f·χ₀(nrd)
  (report §4; the support of f_n is checked numerically). This is not done in Lean: it needs χ₀∘nrd on ℍ[𝔸ᶠ_ℚ]^×
  and an idele/ideal norm step. Done, it would make the fallback one leaf for one.
* Nobody has read the leaves against the TYZ source.

Report: docs/research/h29-proof.md. Log: scratch/h29-proof/log.md. Autofold spec: scratch/h29-proof/autofold.json.
The fold is manual, because hL29 is a top-level argument.

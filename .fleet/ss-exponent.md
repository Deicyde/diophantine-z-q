# ss-exponent: report

**Result: `SupersingularExponentA` is PROVED.** This was the textbook leaf introduced by tyz-318: for
`p ≡ 3 (mod 4)` and a field `k ⊆ F_{p²}` of characteristic `p`, every point of `y² = x³ + 4x` over `k`
is killed by `p + 1`.

* Theorem `ZInQ.Contrib.SSExponent.supersingularExponentA : SupersingularExponentA`, in
  `scratch/ss-exponent/SSExponent.lean`.
* No hypotheses, no sorry. Axioms are [propext, Classical.choice, Quot.sound] (VERIFIED, compiled with
  `lake env lean`, about 7 s).
* The statement text is identical to `scratch/tyz-318/Lemma318.lean` §1 (checked with `diff`).
* The file applies the theorem to `GaloisField 3 2` and `ZMod 7` as non-vacuity checks.

**Proof.** Elementary; it uses Mathlib only, with no characteristic polynomial of Frobenius, no
isogenies and no Tau Ceti.
* `#E(F_p) = p + 1`, so every subgroup of Frobenius-fixed points has order dividing `p + 1`.
* If `√−1 ∉ k`, then `k = F_p` and the claim follows directly.
* Otherwise a new abstract lemma, `nsmul_eq_zero_of_frob`, does the work. Let `G` be finite abelian
  with `π² = 1`, `i² = −1` and `πi = −iπ`, and let every `π`-fixed subgroup have order dividing
  `2^v m` (`m` odd). Then `G` is killed by `2^v m`.
* Proof of the lemma: by the weak exponent `2N`, the bound `#G[2^{v+1}] ≤ 2^{2v}`, and the
  stabilization of the chain `ker (1+i)^n` together with `(1+i)² = 2i`.

**Remains:** nothing for this target. tyz-318 had already bypassed this leaf with the weak exponent
`2(p+1)`, so no headline hypothesis changes. The result does close tyz-318's original route
(`lemma318Literal_HHprime_of_ss_sqrtTwo`) without the leaf. The file can become a Contrib module
unchanged; its only project import is `ZInQKernel.Model.Field.ShortWeierstrass`.

Deliverables: `docs/research/ss-exponent.md`, `scratch/ss-exponent/` (SSExponent.lean, log.md).

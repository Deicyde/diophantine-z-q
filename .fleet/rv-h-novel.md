# rv-h-novel (T2 of h-map): adversarial review of Theorem 4.1's novel steps

**Verdict.** I reviewed N5 L631-716 (sign cocycle, Brauer step, χ and m, β, `[L':ℚ] ≤ QM`),
L796-877 (one system at 3 and 5, break bound, odd p, p = 2, `N ≤ QM²`) and the transfer
L860-905 line by line. I found no gap, no wrong constant and no circularity. All 9 steps are
correct. Step 2 (Brauer) and step 7 (p = 2) need only cosmetic repairs:

- R1: state `ω_p(−1) = χ_p(−1)`.
- R2: "If e ≤ D" should read "Since".
- R3: cite the subgroup formula and note that it holds for all u because `L_v/ℚ₂` is Galois.

The conclusion of Theorem 4.1, with `H₆(D)` and exponent 24, survives this part of the proof
unchanged. Every constant has at least a factor Q of slack.

**Checks (VERIFIED, scripts in scratch/rv-h-novel/).**

- C1: `G₀ = |GL₄(𝔽₅)|`, `2 + 2U₀ ≤ E₀`, and the transfer chain down to `368640Q¹⁶M²⁴ ≤ Q¹⁷M²⁴`.
- C2: the local square-root criterion, on 13 levels (135 characters).
- C3: on 15 Galois fields with PARI ramification groups: Hilbert's formula, `δ ≤ e−1+e·v_p(e)`
  (attained in two cases), the Herbrand integral identity, `u_last ≤ 2δ/e`, and the dyadic
  inclusion `U^{3e+1} ⊆ U⁴`.

**Most serious issue.** Inside the scope, nothing worse than wording. The most serious finding is
about provenance: the Astra `final_source_sha256` (bfc4192d…) is the 11/4 manuscript (commit
09c0c3f3), not N5. The Herbrand-function break argument and the Silverman IV.6.4 dyadic sentence
in N5 are later text. Until this review, that text had no review tied to its hash. The steps
remain conditional on links outside the scope: W2 (`b11`, i.e. L unramified outside T and good
reduction outside S), Pan with the twist, and GR14's non-circularity (W4).

**Single next step.** Close W2. Write out and check route B1 of h-map, Lemma PR: Beckmann
specialization plus Néron–Ogg–Shafarevich at level 3 or 5. These are exactly the two premises on
which every local bound reviewed here rests.

Note: docs/research/rv-h-novel.md

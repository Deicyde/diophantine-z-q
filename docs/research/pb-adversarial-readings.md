# Adversarial AI readings: `colmezThm01` and `panThm104F` (2026-11-26)

**Result.** Both leaves match their printed sources. Each is a direct instance of the printed theorem: Colmez's
Théorème 0.1 at `K = ℚ_p`, and Pan's Theorem 1.0.4 for `p ≥ 5`. No reader found a clause of either Lean statement
that is stronger than the print, a missing hypothesis, or a definition that differs from the printed one. Pan's
journal text (J. Amer. Math. Soc. 35 (2022)) was not accessible; the reading is of arXiv:1901.07166v2, the version
the manuscript cites.

No person has read these pages. The maintainer ruled on 2026-11-26 that, with no human reader available, this
adversarial AI reading stands in for the human reading. The evidence stays AI-READ.

## 1. Method

Six independent AI readings, three per leaf, each from the page images of the scans (not only their text layer),
with verbatim quotes and printed page numbers. The three readers of a leaf were configured with three different
model families, so that they would not share blind spots.

| Lens | Task |
| --- | --- |
| Fidelity | Unfold the Lean statement into atomic clauses and map each clause to the printed text: MATCH, MATCH AFTER A PROVED IDENTIFICATION (naming the Lean theorem), DIRECT INSTANCE, MISMATCH, STRONGER or WEAKER THAN THE PRINT. |
| Skeptic | Try to break the match: hidden standing hypotheses, conventions (Frobenius, Hodge–Tate sign), whether each Lean definition means the printed notion, vacuity, quantifiers, and the statements of the proved identifications relied on. |
| Red team | Read the source cold before reading the Lean, state what it asserts, then list every difference with the Lean. |

Sources (legal copies; SHA-256):

| Source | SHA-256 |
| --- | --- |
| Colmez, *Espaces vectoriels de dimension finie et représentations de de Rham*, Astérisque 319 (2008), 117–186 (numdam scan) | `91d47dedeae0d78d689af8a6cb4ad7a02c3ab04dcd70804b96083639033ccf03` |
| Fontaine, *Le corps des périodes p-adiques*, Astérisque 223 (1994), Exp. II (numdam scan) | `74b6bfbaa3a5b5a1eb1f1cd33b0e49aaffa5bde1b8761a91f7cb51a550e9a46e` |
| Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exp. III (numdam scan) | `ace926ffda578dacfe8a333c38d450235506ebe18f558ee9bfcb96dc6f70a8ec` |
| Pan, arXiv:1901.07166v2 (PDF; LaTeX source `71e0f9f0…`) | `590171129d28a65749cf92b1f6099dbacaa90cc6698828f0a4dfd3da943f4824` |
| Berger, *Équations différentielles p-adiques et (φ,N)-modules filtrés*, Astérisque 319 (2008), 13–38 (for the volume's refereeing) | `4abd66268d63ca477a073cfead25800004a8574f24291097e5750af3c0d3ba90` |

## 2. `colmezThm01` (`PanBergerRefereed.ColmezThm01`)

| Lens | Verdict |
| --- | --- |
| Fidelity | FAITHFUL: a direct instance (`K = ℚ_p`); no issue above low severity. |
| Skeptic | No defect in the instance. Read against the full theorem, the only difference is the base field: Colmez's `K` is any finite extension of `W(k)[1/p]`, `k` perfect, and the Lean fixes `K = ℚ_p`. |
| Red team | MATCHES ONE-TO-ONE at `K = ℚ_p`: no missing hypothesis, no overclaim, no unbridged definition. |

The clauses, as the readers mapped them:

* Théorème 0.1, p. 118: "Toute représentation de de Rham de 𝒢_K est potentiellement semi-stable." Representation
  (p. 118): "un Q_p-espace vectoriel de dimension d muni d'un morphisme continu de groupes de 𝒢_K dans GL(V)". The Lean
  takes `V = E^n` for a finite `E/ℚ_p` with continuous `ρ_E`, viewed `ℚ_p`-linearly; `E = ℚ_p` gives every
  finite-dimensional representation.
* De Rham (p. 118): "B_dR^+[1/t] ⊗_{Q_p} V est isomorphe à (B_dR^+[1/t])^d en tant que 𝒢_K-module, ce qui équivaut à
  ce que le K-espace vectoriel D_dR(V) … soit de dimension d". The Lean hypothesis `IsDeRhamU` is this printed
  dimension condition at `K = ℚ_p`.
* Semi-stable (p. 118): "B_st^+[1/t] ⊗_{Q_p} V est isomorphe à (B_st^+[1/t])^d en tant que 𝒢_K-module"; potentially
  semi-stable: "s'il existe une extension finie L de K telle que V soit semi-stable en tant que Q_p-représentation de
  𝒢_L". The Lean conclusion `IsPstFBasis` asks for a finite `L` and a `B_st`-basis of `B_st ⊗ V` of `𝒢_L`-invariant
  vectors (`IsAdmissibleT`), which is such an isomorphism.
* The ring (p. 118): "Soient B_cris^+ ⊂ B_st^+ ⊂ B_dR^+ les anneaux introduits par Fontaine [14, 15, 17]"; p. 120:
  "On a alors B_st^+ = B_cris^+[u]", with `u = log[p̃]` and `log p = 0` (Prop. 5.15(iv), p. 159; Rem. 5.19,
  pp. 160–161, embeds `u` by the series of `log([p̃]/p)`). With Fontaine, Exp. II, 3.1.6 (p. 81: "c'est aussi
  B_st^+[1/t]") and 4.2.4–4.2.5 (p. 86), `B_st^+[1/t]` is the Lean's `BstFOf`. Proved identifications:
  `AcrisImage.acris_image`, `AbstractPeriods.range_bcrisEmb`, `range_bstEmb`, `bstEquiv`, `bstFOf_eq_of_gen`,
  `acrisOf_eq`.
* The Lean's quantification over every generator `ε₀` of `ℤ_p(1)` and `w` of `ker θ` is harmless: the ring does not
  depend on them (`bstFOf_eq_xi`, `bstFOf_eq_of_gen`), and generators exist.

Notes: the text layer of the numdam scan corrupts pp. 118 and 120 (for example `B_st^+ = B_cris^+[u]`); the Lean
matches the page images. Colmez's Lemma 4.1(iii) (p. 148) has a slip at `p = 2`, `n = 1` that does not affect
Théorème 0.1. Refereeing: the article itself carries no referee statement; Astérisque is refereed by the Société
Mathématique de France's policy, and in the same volume Berger's article thanks "le référée" (p. 15).

## 3. `panThm104F` (`PanBergerRefereed.PanThm104F`)

| Lens | Verdict |
| --- | --- |
| Fidelity | FAITHFUL: the `p ≥ 5` instance; no clause stronger than the print; the conclusion is weaker in form and equal in content. |
| Skeptic | No mismatch for `p ≥ 5`. Read against the full theorem, the only difference is the prime range: Pan's theorem is for every odd `p`, with an extra residual condition at `p = 3`. |
| Red team | Not a literal transcription, but every deviation is a weakening that Pan's theorem implies: `p ≥ 5`, an eigenform that need not be normalized, traces at almost all primes, a twist by any continuous character. |

The clauses:

* Conjecture 1.0.1 (p. 2): "ρ : Gal(Q̄/Q) → GL₂(Q̄_p) be a continuous, irreducible representation such that ρ is only
  ramified at finitely many places, the restriction of ρ at the decomposition group at p is potentially semi-stable in
  the sense of Fontaine, ρ is odd, i.e. det ρ(c) = −1 for any complex conjugation". Lean: `GaloisRep p 2`
  (continuous), `IsIrreducibleP` (irreducible over `ℚ̄_p`), `FinitelyRamified`, `IsOdd`: MATCH.
* Theorem 1.0.4 (p. 5): "Let p be an odd prime and ρ be as in conjecture 1.0.1. Assume that ρ|Gal(Q̄_p/Q_p) has
  distinct Hodge-Tate weights; If p = 3, …. Then ρ comes from a cuspidal eigenform up to twist." Lean: `5 ≤ p` (direct
  instance; the `p = 3` condition is void), `LocalDistinctHTP` with the Hodge–Tate weight of the cyclotomic character
  `−1` ("Our convention for the Hodge-Tate weight of ε is −1", p. 7): MATCH.
* "Potentially semi-stable in the sense of Fontaine": Fontaine, Exp. III, 5.6.1 (p. 166) defines it as potentially
  `B_st`-admissible; 1.8.5 (pp. 134–135) defines "V devient B-admissible sur L si dim_{F_L} D_{B,L}(V) = dim_E V" and
  prints "pour qu'un objet V … soit potentiellement B-admissible, il faut et il suffit qu'il existe une extension
  finie L de K … sur laquelle V devienne B-admissible", under 1.8.1's hypothesis that `B` is `H`-regular, which
  5.1.2(ii) (p. 155) supplies for `B_st`. `B_st` is identified with its image in `B_dR` (Exp. II, 4.2.4–4.2.5,
  p. 86), which is `BstFOf`. Lean: `LocalIsPstF`, on a finite model (model-independent: `localIsPstF_iff_forall`;
  generator-independent: `localIsPstF_iff_abstract`): MATCH after the proved identifications.
* The conclusion: `EigenformAwayFromLevel` is a nonzero cusp form on `Γ₁(N)` with a character, an eigenvector of the
  `T_n` with `(n, N) = 1`; `IsAttachedVia` asks the trace of `ρ_g` at geometric Frobenius ("Frob_v for a geometric
  Frobenius element", p. 6) to be `ι_p⁻¹` of the eigenvalue at almost all primes; `IsTwistOf` asks
  `ρ ≅ ψ ⊗ ρ_g` for a continuous character `ψ`. Pan's conclusion implies this by weakening only;
  `exists_normalized_of_eigenform` replaces the eigenform by a normalized one with the same eigenvalues.

Printed slips the readers found, with the reading the Lean follows: Fontaine, Exp. III, 1.8.5 prints "sous-groupes
fermés" where 5.6.1 and the finite-extension discussion need "ouverts"; 5.6.1 prints "B_cris est G_L-régulier" where
the argument needs `B_st` (5.1.2(ii) gives both); Exp. II, 3.1.3 writes the series of `λ(x)` with `[y]^n` where
`([x] − 1)^n` is meant.

Not read: the journal text of Pan's paper. Under STATEMENT-CHECKS.md ("Refereed papers read from an author copy"),
the row keeps its rating while that check is pending.

## 4. What the readings do not establish

* **Scope.** Each leaf is a direct instance, not the whole printed theorem. Colmez's Théorème 0.1 is for every
  finite extension `K` of `W(k)[1/p]`, `k` perfect; the leaf is `K = ℚ_p`. Pan's Theorem 1.0.4 is for every odd `p`,
  with a residual condition at `p = 3`; the leaf is `p ≥ 5`. The manuscript uses only `ℚ_p` and `ℓ = 5`. A literal
  transcription would need Colmez over a general base field (not expressible with the tree's period rings yet) and
  Pan's residual condition at `p = 3`.
* **Form of Pan's conclusion.** The Lean conclusion is weaker in form than "comes from a cuspidal eigenform up to
  twist": the eigenform need not be normalized, the traces must match only at almost all primes, and the twist is
  by any continuous character. All three readers found it implied by the print; two judged it equal in content.
* **Pan's journal text** (J. Amer. Math. Soc. 35 (2022)) was not read; the readings are of arXiv:1901.07166v2, the
  version the manuscript cites.
* **Refereeing of Astérisque 319** is supported only indirectly (the Société Mathématique de France's policy and a
  referee acknowledgement in another article of the same volume).
* **The manuscript's citation.** At this step the manuscript cites Berger, Invent. Math. 148 (2002), not Colmez.
  Berger's printed `B_st` is `B_max[log [π̄]]`, and his comparison with Fontaine's `D_st` is asserted without proof
  (§1.2), so a Berger leaf would also need that comparison proved; docs/research/pb-refereed-fold.md records the
  switch.

## 5. Effect on the board

Both rows are rated LEAF (strict and strictest), with flags recording the instance, the lenses and the ruling.
The strict count of the H hypotheses goes from 4/15 to 6/13 (19 hypotheses, after the Conrad App. B and `dsThm965AtPrimes` folds).

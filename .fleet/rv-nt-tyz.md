# rv-nt-tyz report: adversarial review of nt-tyz (the TYZ citation behind CR₃)

Deliverable: `docs/research/rv-nt-tyz.md`. Scripts, outputs and log: `scratch/rv-nt-tyz/`. All code
was written independently of `scratch/nt-tyz/`. The TYZ source (arXiv:1411.4728v1, `Period7.tex`) was
downloaded again; its checksum matches the one nt-tyz recorded. Every input I1–I7 was checked against
it. No input was left uncheckable.

## Verdict

- **(a) The literal Theorem 1.2 is false: PROVED.** For `n = 26565 = 3·5·7·11·23` and
  `n = 33117 = 3·7·19·83`, the class-group parities on all 46 divisors were recomputed by three
  methods (reduced forms, Rédei matrices, PARI), which agree. This gives `g(n) = 1` and
  `T_5a = T_5b = 0`, so the second sum is `0` under reading A and `1` under readings B and C. An
  exact rank bound `rank C_n(ℚ) ≥ 3` was obtained from new points, whose Kummer images together with
  those of `C_n[2]` span a 5-dimensional space. With root number `−1` and GZK, `𝓛(n) = 0`.
- **(b) Proposition N: PROVED after one minor repair.** Lemmas N1 and N2, F3–F5 and the proof of
  Proposition N were re-derived by hand and are correct. The inputs I1–I7 are quoted correctly,
  except that TYZ's Lemma 2.8 (I2) is inconsistent with their Theorem 2.1 at `m = 3`, by the odd
  factor `w_K = 3`. Only the congruence modulo 2 is used, and it holds. The genus-point coefficients
  were recomputed from the recursion on 360 abstract configurations with up to 9 primes (20 440
  coefficients), on 30 actual `n`, and on 120 configurations with `n ≡ 7`: 0 mismatches. Mutation
  tests show that the check detects errors.
- **(c) Kriz is not needed: PROVED as a deduction**, relative to Proposition 0 and tyz-5b's
  Lemma 4.1, Theorem 4.3 and Theorem 3.6. Those were not re-proved here. Their combined conclusion,
  `T_5b(d) = 1` for every CR₃-admissible `d`, was confirmed on 50 actual curves with a 2-Selmer group
  computed by an independent full 2-descent. On two curves, the CR₃ conclusion (a point with
  `x ∈ aℚ*²`) was checked end to end.

No finding invalidates (a), (b) or (c).

## Findings (severity)

- **A1 (minor).** "The only true reading admits `d₁ = 1`" is imprecise. A fourth literal reading D,
  which admits `d₁ = 1` and counts `d₁` as a distinguished factor, is also refuted by both
  counterexamples. The surviving reading is the set-partition convention (each set partition of the
  primes counted once). Proposition 3.4 likewise holds only under that convention: reading D
  disagrees with the recursion on 4876 coefficients.
- **A2 (minor, in nt-tyz's favour).** The direction of the "i.e." of Theorem 3.5(2) that Theorem 1.2
  needs (`2^{−ρ}𝓛` even ⟹ `P(n) ∈ A(K_n)^− + A[4]`) takes two lines from Theorem 3.5 and
  Lemma 3.18. So nt-tyz's argument proves reading A of Theorem 1.2 for `n ≡ 5` in full. The cases
  `n ≡ 6, 7` were not examined beyond the `n ≡ 7` coefficient lemma.
- **B1 (minor).** TYZ's Lemma 2.8 and Theorem 2.1 disagree at `m = 3` by the factor `w_K = 3`.
  I2 should be quoted as a congruence modulo 2.
- **B2, B3 (remarks).** F4 and the second half of F3 are not used by Proposition N. The `ε`-class of
  `(5, 3)` steps does not enter Lemma N2.
- **B4, C1 (scope).** The deep TYZ inputs (Theorems 3.3 and 3.5, Lemmas 3.18 and 3.21) and tyz-5b's
  elementary theorems were used as given. Their proofs were not re-verified.
- **B5 (cosmetic).** The quotation cited as L2077 is at L2076.

## Suggestions

1. Make the three edits to nt-tyz listed in §7 of the report: I2 as a congruence, reading A as an
   explicit set-partition convention, and the optional removal of F4. Optionally add the two-line
   argument for A2.
2. The recommended citation (nt-tyz §4.5) and the trust statement of CR₃ can stand as nt-tyz
   proposes.
3. Remaining independent checks for CR₃'s analytic input:
   - a referee pass over tyz-5b §§3–4 (Lemma 4.1, Theorems 3.6 and 4.3) and over Proposition 0;
   - a human reading of TYZ Lemma 3.18, Step 3 (`√2 ∉ ℍ'_n`), and of Lemma 3.21, the two TYZ
     lemmas whose proofs are the most compressed among the inputs.

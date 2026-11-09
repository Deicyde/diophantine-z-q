# Referee report on nt-tyz: the Tian–Yuan–Zhang citation behind CR₃

This report examines the three claims of `docs/research/nt-tyz.md`:

- (a) Theorem 1.2 of Tian–Yuan–Zhang (TYZ, arXiv:1411.4728v1), read literally (all `d_i > 1`), is
  false, with counterexamples `n = 26565` and `n = 33117`;
- (b) Proposition N (if `n ≡ 5 (mod 8)` is squarefree and `T_5b(n)` is odd, then `𝓛(n) ≠ 0` and
  `ord_{s=1} L(E_n, s) = 1`) follows from the inputs I1–I7, without TYZ's Proposition 3.4;
- (c) Kriz's preprint is not needed for any `d` covered by CR₃.

Everything below was checked against the TeX source of arXiv:1411.4728v1 (`Period7.tex`, 3357 lines;
the e-print was downloaded again and has the SHA-256 checksum recorded in nt-tyz), re-derived by hand,
or recomputed with code written for this review. Line numbers `Lnnnn` refer to `Period7.tex`. The
notation is that of nt-tyz: `g(d) = #2Cl(ℚ(√−d)) mod 2`, `w(π) = Π_{B∈π} g(B)` for a set partition
`π` of the primes of an odd squarefree number, `𝓛₁`, `Λ`, `T_5a`, `T_5b` as defined there.

Each step examined is marked **CORRECT** (checked here), **GAP** (missing or wrong, with a repair), or
**UNCHECKED** (not examined here).

## Verdict

- **(a) Proved.** Both counterexamples are correct. The factorizations, the 46 class-group
  parities, the genus sums under each reading, and an exact lower bound `rank C_n(ℚ) ≥ 3` were all
  recomputed independently. With the root number `−1` and Gross–Zagier–Kolyvagin this forces
  `𝓛(n) = 0`. Readings B and C of the second sum of Theorem 1.2 then give `1`, so Theorem 1.2 is
  false under both. One clarification is needed (finding A1): "reading A" must be stated as a
  set-partition convention. Admitting `d₁ = 1` alone does not single out a true statement: the
  reading that admits `d₁ = 1` *and* counts `d₁` as a distinguished factor is refuted by the same two
  values.
- **(b) Proved after one minor repair.** Lemmas N1 and N2, the facts F3–F5, and the proof of
  Proposition N are correct. Each of the inputs I1–I7 is quoted correctly from the source, with one
  exception. Lemma 2.8 of TYZ (input I2) is literally false for `m = 3`: it is off by the factor
  `w_K = 3`, an internal inconsistency of TYZ with their own Theorem 2.1 (finding B1). Lemma N1 uses
  I2 only modulo 2, where the factor is harmless, so the repair is to quote I2 as a congruence. Two
  of the facts listed, F4 and the second half of F3, are not needed for Proposition N. The `ε`-class
  of the `(5, 3)` steps does not enter Lemma N2 at all (findings B2, B3). The deep inputs (TYZ
  Theorem 3.3, Theorem 3.5 first assertion, Lemmas 3.18 and 3.21) are taken as citations; their
  proofs were not re-verified (finding B4).
- **(c) Proved, relative to the elementary results of tyz-5b.** The deduction in nt-tyz §5.1 is
  valid and uses no step from Kriz, the Cassels–Tate pairing or Smith. It rests on Proposition 0
  (descent-alt §4.1) and on tyz-5b's Lemma 4.1, Theorem 4.3 and Theorem 3.6. Those were not re-proved
  in this review (UNCHECKED here; finding C1). But their combined conclusion, `T_5b(d) = 1` for every
  CR₃-admissible `d`, was confirmed on 50 actual curves with a 2-Selmer group computed independently.

No finding invalidates any of the three claims.

## Findings

| # | Severity | Where | Finding |
|---|----------|-------|---------|
| A1 | minor | nt-tyz Verdict 2, §1.3 | "The only true reading admits the trivial factor `d₁ = 1`" is imprecise. A fourth literal reading D (admit `d₁ = 1`, and count `d₁` as a distinguished factor) gives the second sum `T_5a + Σ_π k(π)w(π) + T_5b`, which is also `1` for both counterexamples. The surviving reading is the set-partition reading: each set partition of the primes of `n` is counted once. |
| A2 | minor | nt-tyz §1.3, §2.2 F6 | nt-tyz calls the "i.e." of Theorem 3.5(2) unproved (F6). The direction that Theorem 1.2 needs (`2^{−ρ(n)}𝓛(n)` even ⟹ `P(n) ∈ A(K_n)^− + A[4]`) is immediate from Theorem 3.5 (first assertion) and Lemma 3.18 (§4.5 below). So reading A of Theorem 1.2 for `n ≡ 5` is *fully* proved by the argument of nt-tyz §4.4, not only Proposition N. For `n ≡ 7`, only the coefficient lemma was checked (§3.4). For `n ≡ 6`, nothing was checked. |
| B1 | minor | nt-tyz §4.2, I2 | TYZ's Lemma 2.8 (`Σ ε𝓛(d₁)𝓛(d₂) = Q(m)`) is off by the factor `w_K` for `m = 3`, where `w_K = 3`. TYZ's Theorem 2.1 gives `Q(3) = P(3, 1) = ±3𝓛(3)`, while Lemma 2.8 gives `Q(3) = ±𝓛(3)`, and `𝓛(3) = ±1`. The correct identity is `w_K Σ ε𝓛𝓛 = Q(m)`. Lemma N1 needs only the congruence modulo 2, which holds. |
| B2 | remark | nt-tyz §4.4, §2.2 F3, F4 | F4 (`[i]` commutes with `β'`) is not used by the proof of Proposition N: the coefficients `ℓ_e` are integers, and `X` enters only through `X^{β'} + X ∈ A(ℍ'_n)` (F5). The second half of F3 (`β` negates `√−n`) is not used either. It is needed only for the full Theorem 3.5(2) (finding A2). |
| B3 | remark | nt-tyz §4.3, I1 | The value of `ε` on `(5, 3)` steps does not enter Lemma N2: such steps occur only in chains with at least two class-3 factors, and these cancel in pairs. Mutation tests confirm this (§3.3). So I1 is needed only for the pairs `(5, 1)`, `(7, 1)`, `(7, 3)`, where `ε ≡ 1`. |
| B4 | scope | inputs I3–I6 | TYZ's Theorem 3.3 (generalized Gross–Zagier), the first assertion of Theorem 3.5, Lemma 3.18 (notably its Step 3, `√2 ∉ ℍ'_n`) and Lemma 3.21 (via Theorem 3.6) are used as citations. Their statements are unambiguous and are quoted correctly. Their proofs were read but not re-verified. |
| B5 | cosmetic | nt-tyz §1.2, §2.3 | The quotation "the contribution by `d₀ = d₀'' = n`, `d₁ = 1` is the single term `Z(n)`" is at L2076, not L2077. |
| C1 | scope | nt-tyz §5.1 | The chain uses Proposition 0 (descent-alt §4.1) and tyz-5b's Lemma 4.1, Theorem 4.3 and Theorem 3.6. These were not re-proved here. Their combined conclusion was tested on 50 actual curves with no failure (§6). |

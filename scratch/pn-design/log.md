# pn-design results log

## Step 1 (inputs I1–I7 read in Period7.tex)

- Read: L318–345 (def. of 𝓛, root number), L363 (g), L499 (§2 hyp. n ≡ 1,2,3 sqfree), L580–586
  (Prop 2.3), L1062–1082 (Lemma 2.8, 𝓛(1) = 1), L1167 (§3 hyp.), L1253–1374 (Prop 3.2, ℙ(n), Thm 3.3,
  Z(n), ℍ'_n, recursion, Thm 3.5), L1384–1402 (τ), L2170–2232 (Lemmas 3.16, 3.18), L2480–2590
  (β₁, Lemma 3.21, proof of 3.5(2)).
- `n2_check.py` (seed 1): unwound recursion coefficients c_n(e) for n ≡ 5, with ARBITRARY integer 𝓛
  (no Lemma 2.8) and ε = ±1 off (5,3), ±i at (5,3): 190 trials (1–7 primes), 0 mismatches with
  c_n(e) ≡ 𝓛(n/e) (mod 2ℤ[i]). Same with ε at (5,3) a random unit (mixed classes): 154 mismatches.
  ⇒ N2 in the 𝓛-form needs no I2/N1; it needs the ε-classes of Thm 3.3 including uniformity at (5,3).
- `enc_check.py` (seed 2): exact encodings of PropN.lean on abstract data (random classes, random g
  bits, 0–7 primes): (a) `Lam` satisfies the `LemmaTwoEight` identity mod 2 (m ≡ 1: d ≡ 1, d² < m;
  m ≡ 3: d ≡ 1) and `Lam 1 = 1`: 180 trials, 0 mismatches; (b) `Σ_{e≡5} Λ(n/e)g(e) = T_5a`,
  `Σ_{e≡7} Λ(n/e)g(e) = T_5b`: 40 trials with n ≡ 5, 0 mismatches.

## Step 2 (PropN.lean)

- Drafted `scratch/pn-design/PropN.lean`: `gNat`, `LemmaTwoEight`, `GenusData` (structure, 16
  fields), `TYZInputs`, `LamAdm`, `Lam`; sorried `lemmaN1_core`, `lemmaN2`, `finalStep`,
  `matching`; proved `mod8_div`, `div_mod8_of`, `lemmaN1` (uniqueness induction from the core),
  `genusSums_eq_zero`, `tyzRow5b_of_tyzInputs`, `tyzThm35ReadingA_of_tyzInputs`.
- `lake build ZInQKernel`: up to date (9922 jobs). `lake env lean scratch/pn-design/PropN.lean`:
  compiles; exactly 4 `sorry` warnings (lines 154, 168, 177, 188 = the four lemmas).
- Added `Witness.witnessData` / `Witness.genusData_nonempty : L n ≠ 0 → Nonempty (GenusData L n)`
  (M = ℤ[i]/(2+2i) × (ℕ →₀ ℤ[i]), P by well-founded recursion). Compiles; still exactly the 4
  `sorry`s. `#print axioms tyzRow5b_of_tyzInputs`, `lemmaN1`, `tyzThm35ReadingA_of_tyzInputs`:
  propext, sorryAx, Classical.choice, Quot.sound; `genusData_nonempty`: propext, Classical.choice, Quot.sound (no sorry).
- Corrected TYZ line locators in PropN.lean docstrings (Lemma 3.21 L2504–2516, β₁ L2496–2500,
  "β acts on ℚ(i) trivially" L2581, sign L361, Z(n) L1318, recursion L1325–1330). Recompiled:
  4 `sorry` warnings (lines 154 lemmaN1_core, 168 lemmaN2, 177 finalStep, 188 matching), no errors.

## Step 3 (plan) and deliverables

- Wrote `docs/research/pn-design.md`: inputs I1–I7 with locators (§1), field-by-field encoding
  table (§2), checks (§3), N2 without N1 with the κ-table proof (§4), ranked risks (§5), plan A–D
  with routes, reuse and sizes (§6).

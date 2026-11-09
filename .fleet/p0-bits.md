# p0-bits: Proposition 0, file 8 (Bits.lean): local classes → rows of `Σ(𝒞_d)`

Plan: `docs/research/nt-prop0.md` §2.6 and §4.1 file 8. Everything is in
`ZInQKernel/RouteK/Selmer/Bits.lean`, namespace `ZInQ.RouteK.Selmer`. The root module is
`ZInQKernel/RouteK/SelmerBits.lean`, imported from `ZInQKernel.lean`. `lake build ZInQKernel`
succeeds. There is no `sorry` and no `native_decide`. `#print axioms` on every main lemma below shows
only `propext`, `Classical.choice` and `Quot.sound`. The file has 547 lines and compiles in about 5 s.
The branch also contains the merges of origin/wip/p0-local, origin/wip/p0-charsum and origin/wip/p0-two.

Notation: `σ : Unknowns d.primeFactors`, `a(σ) = (selPair d σ).1 = classInt d σ.a0 σ.a1 σ.u`,
`b(σ) = (selPair d σ).2`, `𝒞_d = natConfig d hd`.

## Leaves

| Article (nt-prop0 section) | Lean name | Status |
| --- | --- | --- |
| §2.6 at `p ∈ S`: Lemma B class condition ⇔ `E1_p ∧ E2_p` | `classCond_dvd_iff_rows` | proved |
| §2.6 at `p ∈ S`, combined with Lemma B | `loc_padic_selPair_iff_rows` | proved |
| §2.6 at `∞`: Lemma ∞ ⇔ `(R)` | `loc_real_selPair_iff` | proved |
| §2.6 at `2`: Lemma T class condition ⇔ `a₁ = 0 ∧ b₁ = μ·u ∧ a₀ + λ·u = b₀ + λ·v` | `classCond_two_iff` | proved |
| §2.6 at `2`, with `(R)`: ⇔ row `(D)` (`twoAdicRows 5`) | `classCond_two_iff_D`, `classCond_two_and_R_iff` | proved |
| §2.6 at `2`, combined with Lemma T (`loc_two_adic_iff`, p0-two) | `loc_two_selPair_iff`, `loc_two_selPair_iff_D` | proved |
| §2.6 at `p ∉ S ∪ {2}`: `p ∤ a(σ)`, `p ∤ b(σ)` | `not_dvd_classInt`, `not_dvd_selPair` | proved |

Statements:

```lean
theorem classCond_dvd_iff_rows {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (σ : Unknowns d.primeFactors) (hpd : p ∈ d.primeFactors) :   -- [Fact p.Prime]
    (∃ i j : ℕ, i < 2 ∧ j < 2 ∧
      IsSquare (((selPair d σ).1 * d ^ i * (-1) ^ j : ℤ) : ℚ_[p]) ∧
      IsSquare (((selPair d σ).2 * 2 ^ i * (-d) ^ j : ℤ) : ℚ_[p])) ↔
      (natConfig d hd).E1 σ ⟨p, hpd⟩ ∧ (natConfig d hd).E2 σ ⟨p, hpd⟩

theorem loc_padic_selPair_iff_rows (same hypotheses) :
    Loc ℚ_[p] d (selPair d σ).1 (selPair d σ).2 ↔
      (natConfig d hd).E1 σ ⟨p, hpd⟩ ∧ (natConfig d hd).E2 σ ⟨p, hpd⟩

theorem loc_real_selPair_iff {d : ℕ} (hd0 : d ≠ 0) (σ : Unknowns d.primeFactors) :
    Loc ℝ d (selPair d σ).1 (selPair d σ).2 ↔ σ.a0 = σ.b0

theorem classCond_two_iff {d : ℕ} (hd5 : d % 8 = 5) (hsq : Squarefree d)
    (σ : Unknowns d.primeFactors) :
    (∃ i j k : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧
      IsSquare (((selPair d σ).1 * d ^ i * (-1) ^ j : ℤ) : ℚ_[2]) ∧
      IsSquare (((selPair d σ).2 * 2 ^ i * (-d) ^ j * 5 ^ k : ℤ) : ℚ_[2])) ↔
      σ.a1 = 0 ∧ σ.b1 = dot 𝒞_d.mu σ.u ∧ σ.a0 + dot 𝒞_d.lam σ.u = σ.b0 + dot 𝒞_d.lam σ.v

theorem classCond_two_iff_D (hd5) (hsq) (σ) (hR : σ.a0 = σ.b0) :
    (the same class condition) ↔ (natConfig d _).D σ

theorem not_dvd_selPair {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬p ∣ d) (σ) :
    ¬(p : ℤ) ∣ (selPair d σ).1 ∧ ¬(p : ℤ) ∣ (selPair d σ).2
```

## Statement corrections and choices

- **The place 2 is not `twoAdicRows 5` on its own.** The class condition of Lemma T is equivalent
  to `a₁ = 0 ∧ b₁ = μ·u ∧ a₀ + λ·u = b₀ + λ·v` (`classCond_two_iff`). This is `twoAdicRows 5`
  (`a₁ = 0 ∧ b₁ = μ·u ∧ λ·v = λ·u`) only together with `(R)`, as §2.6 says ("Together with (R)").
  So the row `(D)` comes as `classCond_two_iff_D` under the hypothesis `a₀ = b₀`, and as the
  conjunction form `classCond_two_and_R_iff`. Without `(R)` the two are different: for
  `a₀ ≠ b₀`, `λ·v = λ·u + 1` satisfies the class condition but not `(D)`.
- **Leaf 1 needs only `d` odd and squarefree.** `d ≡ 5 (mod 8)` is not used at `p ∣ d`.
- **Leaf 3 is stated against the explicit class condition of §2.5**, written exactly as in
  `loc_padic_dvd_iff` with the extra factor `5^k`. p0-two's `loc_two_adic_iff` has this right-hand
  side character for character. After I merged origin/wip/p0-two, the connection is a single
  `rw` (`loc_two_selPair_iff`, `loc_two_selPair_iff_D`). Bits.lean now imports
  `Selmer/Two.lean`.
- **Leaf 4** needs `p ≠ 2` (`2 ∣ a(σ)` when `a₁ = 1`) and gives non-divisibility, the form
  Lemma G2 takes (`p ∤ a`, `p ∤ b`).

## Lemmas added beyond the leaves

- Bits and exponents: `bits_exists_two`, `bits_exists_three` (`∃ i < 2` ⇔ `∃ x : ZMod 2`),
  `bits_even_val_add_iff`, `bits_even_val_iff`, `bits_eq_iff_add_eq_zero`, `bits_exists_eq_and_eq`,
  `bits_sum_add_mul`, `bits_two_core` (the final elimination of `i, j, k` at 2, by `decide` over 8
  bits).
- `intCast_eq_prod_primeFactors` (`d = Π_{q ∣ d} q` for squarefree `d`) and `classInt_mul_eq`:
  `a(σ)(−1)^s 2^t d^m = (−1)^{a₀+s} 2^{a₁+t} Π_q q^{u_q+m}`. This is the common rewriting of
  `a d^i (−1)^j` and `b 2^i (−d)^j` at all places.
- Odd `p ∣ d`: `isSquare_padic_pow_mul_iff` (`p^e z` with `p ∤ z` is a square iff `e` is even and
  `z` is a square; valid for every prime `p`, including 2), `legBit_pow`,
  `isSquare_padic_signedProd_iff` (the square class of `(−1)^s 2^t Π_q q^{e_q}` in `ℚ_p`: `e_p` even
  and `s λ_p + t μ_p + Σ_{q ≠ p} e_q [q/p] = 0`), `mu8_natCast_eq_muBit_of_prime` (the `μ` analogue
  of `lam8_natCast_eq_lamBit`), `natConfig_lam`, `natConfig_mu`, `natConfig_bit`.
- At 2: `oddClasses_pow`, `lam8_pow`, `mu8_pow`, `eq_one_iff_lam8_mu8` (an odd class is 1 iff
  `λ = μ = 0`), `isSquare_two_adic_intCast_iff` (odd `z` is a square in `ℚ₂` iff `z ≡ 1 (mod 8)`),
  `isSquare_two_adic_signedProd_iff`, `natConfig_lam_eq_lam8`, `natConfig_mu_eq_mu8`,
  `prod_primeFactors_zmod8`, `natConfig_prodClass` (`prodClass = d mod 8`),
  `odd_prime_of_mem_primeFactors`.
- `classInt_ne_zero`, and `squarefree_classInt` (`a(σ)`, `b(σ)` are squarefree; needed by file 9 for
  `Sel2` membership).
- **Assembly** (most of file 9's first conjunct):
  - `isSol_iff_selPair_mem_of_local`: for squarefree `d ≡ 5 (mod 8)`, given Lemma T (`hT`, the
    statement of §2.5) and Lemma G2 (`hG`), `(natConfig d _).IsSol σ ↔ selPair d σ ∈ Sel2 d`;
  - `isSol_iff_selPair_mem_of_G2`: the same with `hT := loc_two_adic_iff` filled in, so only `hG`
    remains:
    ```lean
    (hG : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬p ∣ d → ∀ a b : ℤ, ¬(p : ℤ) ∣ a → ¬(p : ℤ) ∣ b →
      Loc ℚ_[p] d a b)
    ```
    This is exactly p0-good's `loc_padic_good_of_units` (origin/wip/p0-good, not merged here):
    `fun p _ hp2 hpd a b ha hb => loc_padic_good_of_units hp2 hpd ha hb`.

All names were grepped against `ZInQKernel/` and against `Selmer/Two.lean` (merged) and
`Selmer/Good.lean` (origin/wip/p0-good). None collides.

## Problems

None in the mathematics. Every leaf compiled after one to three edit–compile rounds.

## Suggestions for the next agent (file 9, `Prop0.lean`)

- **First conjunct of `Prop0Statement`.** Merge origin/wip/p0-good. Then
  `isSol_iff_selPair_mem_of_G2 hd5 hsq (fun p _ hp2 hpd a b ha hb => loc_padic_good_of_units hp2 hpd ha hb) σ`
  is the first conjunct. The `Odd d` proof inside `natConfig` is `odd_of_mod_eight_eq_five hd5` in
  both statements.
- **Second conjunct, `Sel2 d ⊆ Set.range (selPair d)`.**
  - For `(a, b) ∈ Sel2 d`, `loc_padic_good_iff` (p0-good) gives `p ∤ a, b` for every odd `p ∤ d`.
  - So `|a|` is a squarefree product of primes in `{2} ∪ S`. Read `σ` off the sign, the parity and
    the divisibility by each `q ∣ d`, the converse of `prime_dvd_classInt_iff`,
    `two_dvd_classInt_iff` and `classInt_pos_iff`.
  - Then prove `classInt … = a` as in `classInt_natClass` (`Covering.lean`), which handles odd
    divisors of `d`. Here `2` may also divide `a`.

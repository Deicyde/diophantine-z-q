# dl-slots: input data and slot primes of the Route K descent lemma

Specification: `docs/research/slot-k.md` §1.1, §2.4 and §2.5 step 0, with the referee report
`docs/research/rv-slot-k-proof.md` (branch `wip/rv-slot-k-proof`). All Lean code is in namespace
`ZInQ.RouteK`, directory `ZInQKernel/RouteK/Slots/`, root module `ZInQKernel/RouteK/Slots.lean`
(imported from `ZInQKernel.lean`). `lake build ZInQKernel` succeeds. There are **no `sorry`s**, no
axioms beyond `propext`, `Classical.choice` and `Quot.sound` (checked with `#print axioms` on the
main theorems), no `native_decide`, and no named finite-check hypotheses. The only `decide` calls
are on small closed facts (`(14 : ℤ) ∣ 2730`, `¬ (9 : ℤ) ∣ 2730`, bits in `ZMod 2`).

## Leaves

| article path (note section) | Lean name | status |
| --- | --- | --- |
| slot-k §1.1, admissible `B` (hypothesis of `ZInQ.PoleCompleteness`) | `Admissible`, `poleCompleteness_iff_admissible` | proved |
| slot-k Notation, signed squarefree part `sqf` | `sqf` (via `sqfNat`, `sqfInt`); `sqf_spec`, `sqf_eq_of_eq_mul_sq`, `sqf_mul_sq`, `sqf_pos_iff` | proved |
| slot-k §1.1, `β = sqf(mB)`, `θ = sqf(m(m − B))` | `betaOf`, `thetaOf`; integer form `betaOf_thetaOf_eq_sqfInt` | proved |
| slot-k §2.4 step 0 / §4.2 L1 (multiplier) | `exists_multiplier` (strong form `exists_multiplier_pos`) | proved |
| slot-k §1.1 / §4.2 L2, (θ1)–(θ4) | `theta_props`; separately `theta1`, `theta2`, `theta2_isCoprime`, `theta3`, `theta4` | proved |
| slot-k §2.4 "Existence of the slots" (general slot lemma) | `exists_prime_slot` (Legendre form), `exists_prime_slot_bits` (bit form) | proved |
| slot-k §2.4 / §4.2 L3 (slots `q₀`, `r_p`, `r_ℓ`) | structure `Slots β θ p₀`; `exists_slots`, `exists_slots_of_admissible`, `exists_multiplier_and_slots` | proved |
| slot-k §2.4, reverse symbols by reciprocity | `Slots.rev_q₀`, `Slots.rev_rP`, `Slots.rev_rT` (from `legBit_reciprocity`) | proved |
| slot-k §2.4, `Σ_{p∈P} [q₀/p] = x`; `ω(n/β) = ω(β) + ω(θ)` | `Slots.sum_q₀_sym`; `Slots.primes`, `Slots.card_primes` | proved |

Files: `Basic.lean` (admissibility, `sqf`, `β`, `θ`), `Multiplier.lean` (L1), `Theta.lean` (L2),
`Symbols.lean` (residue bits, reciprocity in bits), `Dirichlet.lean` (slot lemma),
`Construction.lean` (L3).

## How the statements read

- `Admissible B := IsSquare B.den ∧ 0 < B ∧ B < 1/2 ∧ ∀ p ∈ poleS0, 4 ≤ padicValRat p B`. This is
  exactly the hypothesis of `PoleCompleteness`; `poleCompleteness_iff_admissible` says
  `PoleCompleteness ↔ ∀ B, Admissible B → PoleSoluble B`.
- `sqf x = sqfInt (x.num * x.den)` and `sqfInt N = sign N · ∏_{p : v_p(N) odd} p`. For `x ≠ 0`,
  `sqf x` is squarefree, `x = sqf x · t²` with `t ≠ 0` (`sqf_spec`), and it is the only squarefree
  integer with that property (`sqf_eq_of_eq_mul_sq`). Note that `sqf 0 = 0`.
- Signed divisors of 2730 are `m : ℤ` with `m ∣ 2730`. `betaOf B m = sqf (m * B)` and
  `thetaOf B m = sqf (m * (m - B))`.
- L1: `Admissible B → ∃ m : ℤ, m ∣ 2730 ∧ Odd (betaOf B m) ∧ (betaOf B m).natAbs % 8 = 7`.
- L2 (`theta_props`):
  (θ1) `0 < θ ∧ θ % 8 = 1 ∧ Int.gcd θ 2730 = 1`;
  (θ2) `∀ p prime, (p:ℤ) ∣ β → ¬ (p:ℤ) ∣ θ`;
  (θ3) `∀ ℓ [Fact ℓ.Prime], (ℓ:ℤ) ∣ θ → legendreSym ℓ β = 1`, with the signed `β`;
  (θ4) `∀ p [Fact p.Prime], p ≠ 2 → (p:ℤ) ∣ β → legendreSym p θ = 1`.
- Residue bits: `legBit p a : ZMod 2` is `0` if `(a : ZMod p)` is a square and `1` otherwise.
  `lamBit p = legBit p (-1)` and `muBit p = legBit p 2`. Main lemmas: `legBit_eq_iff_legendreSym`,
  `legBit_mul`, `legBit_prod`, `lamBit_eq` (`λ_p = [p ≡ 3 mod 4]`), `muBit_eq`
  (`μ_p = [p ≡ 3, 5 mod 8]`), and `legBit_reciprocity`: `[q/p] + [p/q] = λ_p λ_q` for distinct odd
  primes `p`, `q`.
- Slot lemma (`exists_prime_slot`): given a finset `S` of odd primes, signs `ε p = ±1`, an odd `a`
  and a finset `A`, there is a prime `q ∉ A` with `q ≡ a [ZMOD 8]` and
  `∀ p [Fact p.Prime], p ∈ S → legendreSym p q = ε p`. The bit form also gives `q ∉ S`.
- L3: `Slots β θ p₀` uses `P = primesOf β = β.natAbs.primeFactors`, `T = primesOf θ`,
  `G = P \ {p₀}` and `x = signBit β + 1`, where `signBit β = [β < 0]`. Its data are `q₀`, `rP`
  and `rT`; its fields are every condition of §2.4 (classes mod 8; `¬ (slot:ℤ) ∣ 2βθ`; pairwise
  distinctness, including `InjOn` for `rP` on `G` and `rT` on `T`; all prescribed bits).
  - `exists_slots`: if `β`, `θ` are odd and coprime and `p₀ ∈ P`, then `Nonempty (Slots β θ p₀)`.
  - `exists_multiplier_and_slots`: for admissible `B` there is an `m` as in L1 with `P ≠ ∅`, and
    the slots exist for every `p₀ ∈ P`.

## Differences from the note (statement corrections)

1. **Integer form of the (θ) proof.** The note argues from `θc² = 1 − βt²` over `ℚ`. Lean uses
   the same equation multiplied by `M² = (mk)²`, where `B = a/k²` in lowest terms:
   `ma = βs²` and `θc² = M² − ma`. The local analysis is one lemma, `local_unit_square`: if
   `θc² = (p^e M₁)² − X` with `θ` squarefree, `p ∤ M₁` and `p^(2e+j) ∣ X` (`j ≥ 1`), then `p ∤ θ`
   and `θc₁² ≡ M₁² (mod p^j)` with `p ∤ c₁`. We use `j = 3` at `p ∈ S₀` (this gives `θ ≡ 1 mod 8`
   at `p = 2`) and `j = 1` at the other primes of `β`. No `p`-adic numbers are needed.
2. **(θ4) holds for every prime `p ∣ β`**, including `p = 2` (`theta4` has no `p ≠ 2`
   hypothesis). `theta_props` states the note's version, for odd `p`.
3. **L1 holds for every `B ≠ 0`, with `m > 0`** (`exists_multiplier_pos`). Admissibility is not
   needed. The proof picks `m = 2^f m₀`, where `2^f ∥ sqf B` and `m₀ ∈ {1, 3, 5, 7}` with
   `m₀ |b'| ≡ 7 (mod 8)` (`b'` is the odd part of `sqf B`). The note's argument and the referee's
   count (8 eligible `m` per `B`) are correct; the count is not formalized.
4. **Glue-slot conditions are symmetric.** The note imposes `[r/r'] = 0` only against the
   *earlier* glue slots. `Slots` records `[r'/r] = 0` for all pairs of distinct glue slots. This
   is equivalent, because both slots are `≡ 1 (mod 4)`; the proof (`exists_glue_family`) still
   chooses them one after the other and gets the reverse direction from reciprocity.
5. **L3 needs only odd, coprime `β`, `θ` and `p₀ ∈ P`.** `|β| ≡ 7 (mod 8)` and (θ1), (θ3), (θ4)
   are not needed for the existence of the slots. They are needed later, by the Selmer
   computation (L4/L5). `exists_slots_of_admissible` gets the hypotheses from L1 and L2.
6. **`[q₀/ℓ] = 0` for `ℓ ∈ T` is kept** (field `q₀_sym_T`), because the note imposes it. The
   referee (finding 1) shows it is never used, so a consumer may ignore it.
7. `legBit p a` is `0` when `p ∣ a`; the note leaves `[a/p]` undefined there. All slot statements
   involve only `a` prime to `p`, guaranteed by the distinctness fields.
8. `q₀ = 3` is allowed when `3 ∤ βθ`, as the referee notes (§5.1, edge cases).

## Lemmas added beyond the leaves

- Squarefree parts: `sqfNat_squarefree`, `sqfNat_mul_sq`, `nat_squarefree_eq_of_mul_sq`,
  `int_squarefree_eq_of_mul_sq`, `sqfInt_spec`, `sqfInt_squarefree`, `sqfInt_eq_of_eq_mul_sq`,
  `sqfInt_mul_sq`, `sqf_intCast`, `sqf_squarefree`, `Admissible.pos`, `Admissible.ne_zero`.
- L1: `sqfInt_mul_odd_prime`.
- L2: `int_sq_modEq_one_of_odd`, `local_unit_square`, `legendreSym_eq_one_of_modEq`,
  `prime_dvd_divisor_2730`, `Admissible.decode` (`B = a/k²`, `0 < 2a < k²`, `gcd(a, k) = 1`,
  `p ∤ k` and `p⁴ ∣ a` for `p ∈ S₀`), `slot_setup` (the integer data), `prime_of_mem_poleS0'`,
  `theta_local_S0`, `theta_local_beta`.
- Bits: `legBit_eq_zero_or_one`, `legBit_congr`, `legBit_eq_zero_iff`, `legBit_eq_one_iff`,
  `legendreSym_eq_ite_legBit`, `odd_prime_mod_four`, `natCast_zmod_ne_zero_of_prime_ne`,
  `legBit_symm_of_one_mod_four`, `legBit_symm_of_three_mod_four`.
- Slots: `exists_residue_legendreSym`, `exists_glue_family` (a family of glue primes with
  prescribed bits against a fixed set, pairwise square), `mem_primesOf`, `odd_of_mem_primesOf`,
  `natAbs_eq_prod_primesOf` (`|β| = ∏_{p∈P} p` for squarefree `β`), `not_dvd_two_mul_of_not_mem`,
  `nat_mod_eight_of_modEq`.
- Reused: `ZInQ.Mult.not_dvd_2730_of_not_mem_poleS0` (`Multiplication/Certificate/Parity.lean`).

## Problems

None blocking. Notes for whoever edits these files:

- In this Mathlib, `if_pos`/`if_neg` are deprecated (they produce warnings), so these files use
  `simp only [h, ite_true, ite_false]` instead.
- `wip/dl-system` also works in namespace `ZInQ.RouteK` (directory `RouteK/System/`). I compared
  declaration names with its current branch: there are no collisions. Its declarations mostly live
  in the sub-namespace `Config`.

## Suggestions for the next agent (L5, realization)

- dl-system's `Config` uses bits `bit x y : ZMod 2` and classes `cls : S → ZMod 8`. For the actual
  primes, set the bit of the pair `(x, y)` to `legBit x y` (in the note's convention
  `L_{xy} = [y/x]`). The reciprocity axiom of `Config` then follows from `legBit_reciprocity` together with
  `lamBit_eq`, and `Config.lam`/`Config.mu` match `lamBit_eq`/`muBit_eq` through the classes
  `q₀_mod_eight`, `rP_mod_eight` and `rT_mod_eight`.
- Glued symbols: `[|β|/ℓ] = Σ_{p∈P} [p/ℓ]` follows from `natAbs_eq_prod_primesOf` and
  `legBit_prod`, and `[θ/p] = Σ_{ℓ∈T} [ℓ/p]` likewise (`θ > 0` and squarefree, by (θ1)). The
  Jacobi step `(p/θ) = (θ/p)` can be done prime by prime with `legBit_reciprocity`, since
  `Σ_{ℓ∈T} λ_ℓ = λ_θ = 0` when `θ ≡ 1 (mod 4)`.
- (θ3) with the signed `β` reads `legendreSym ℓ β = 1`. To get the note's `[|β|/ℓ] = sλ_ℓ`, use
  `β = -|β|` when `signBit β = 1`, together with `legBit_mul`.
- Define `n = β · ∏_{q ∈ D.primes} q` from `Slots.primes`. `Slots.card_primes` gives
  `ω(n/β) = ω(β) + ω(θ)`.

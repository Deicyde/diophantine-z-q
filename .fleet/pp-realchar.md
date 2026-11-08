# pp-realchar report: plan step 3.1 (classification of real Dirichlet characters)

All modules import Mathlib only. Root module: `ZInQKernel/Progressions/RealChar.lean`, imported
from `ZInQKernel.lean`. No `sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound`
(checked with `#print axioms`).

## Deliverables

| plan step | Lean name | file | status |
| --- | --- | --- | --- |
| 3.1 classification | `ZInQ.Progressions.exists_legendre_of_real_char` | `RealChar/Classification.lean` | proved |
| 3.1 (stronger form, `\|d\| ∣ q`) | `ZInQ.Progressions.exists_legendre_of_real_char_dvd` | `RealChar/Classification.lean` | proved |

Statement delivered (exactly as specified by the task):

```lean
theorem exists_legendre_of_real_char {q : ℕ} (hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 = 1) :
    ∃ d : ℤ, Squarefree d ∧ d ≠ 1 ∧ d.natAbs ≤ q ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ d → p ∣ q) ∧ (2 ∣ d → 8 ∣ q) ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q → χ p = legendreSym p d
```

The `_dvd` variant replaces `d.natAbs ≤ q` and the odd-prime-factor clause with the stronger
`d.natAbs ∣ q` (true because `2 ∣ d` forces `8 ∣ q`). Consumers bounding `|disc ℚ(√d)| ≤ 4|d|`
can use either form.

## Statement corrections

None. The plan's statement holds as written. Notes:
- "`χ(p) = (d/p)`" is formalized as `χ (p : ZMod q) = ((legendreSym p d : ℤ) : ℂ)`, with the
  primality of `p` given as an instance argument `[Fact p.Prime]`.
- The proof in fact gives `|d| ∣ q`, which is stronger than `|d| ≤ q`.

## Proof route and lemmas added (namespace `ZInQ.Progressions`)

The proof differs from the plan's sketch in one place. The local classification needs no
cyclicity of `(ZMod p^k)ˣ` and no generators of `(ZMod 2^k)ˣ`. Instead:
**a real character is `1` at every unit square**, and Hensel lifting over `ℤ` shows which
units are squares.

- `RealChar/Hensel.lean`
  - `realChar_sq_lift_step_odd`, `realChar_exists_sq_mod_pow_odd`: a square root of `n` mod an
    odd prime `p` (with `p ∤ n`) lifts to every `p^k`.
  - `realChar_exists_sq_mod_two_pow`: `n ≡ 1 (mod 8)` is a square mod every `2^k`.
- `RealChar/Local.lean`
  - `RealCharData q χ d`: the multiplicative invariant used by the induction (`Squarefree d`,
    `d.natAbs ∣ q`, `2 ∣ d → 8 ∣ q`, `χ ℓ = (d/ℓ)` for primes `ℓ ∤ 2q`).
  - `realChar_apply_sq`, `realChar_apply_sq_eq_one`, `realChar_apply_eq_one_of_dvd`: `χ² = 1`
    implies `χ(v²) = 1` for units `v`.
  - `realCharPstar p` (`= p` if `p ≡ 1 mod 4`, else `-p`), `natAbs_realCharPstar`,
    `legendreSym_realCharPstar` (`(ℓ/p) = (p*/ℓ)`, from Mathlib's reciprocity).
  - `realChar_primePow_odd`: modulo `p^k` (`p` odd), `χ` is `1` at the residues and constant
    (`= χ(g)` for one nonresidue `g`) at the nonresidues. So `d = 1` or `d = p*`.
  - `realChar_twoPow`: modulo `2^k`, `χ(ℓ)` depends only on `ℓ mod 8` and is determined by
    `χ(3), χ(5) ∈ {±1}`. The four cases give `d = 1, -1, 2, -2` (via `χ₄, χ₈, χ₈'`).
    `χ(5) = -1` forces `k ≥ 3`.
- `RealChar/CRT.lean`
  - `realCharCrtLeft`, `realCharCrtRight` (the components of `χ` mod `m·n` through
    `ZMod.chineseRemainder`), `realCharCrt_apply`, `realCharCrtLeft_sq`, `realCharCrtRight_sq`.
  - `realChar_coprime_mul`: the `d`'s of coprime moduli multiply (`legendreSym.mul`).
- `RealChar/Classification.lean`
  - `realChar_exists_data`: induction via `Nat.recOnPosPrimePosCoprime` (covers the trivial
    character too, with `d = 1`).
  - `d ≠ 1`: otherwise `χ = 1` on every unit class, using `Nat.forall_exists_prime_gt_and_eq_mod`.

## Finite-computation hypotheses

None.

## Problems

None.

## Suggestions for the next agent

- Steps 3.3–3.5 need `ε_p = (d/p)` for odd `p ∤ d`. Combined with this theorem, this gives
  `χ(p) = ε_p` for every prime `p ∤ 2q`. For the Euler factors at `p ∣ 2q`, the `_dvd` form
  (`|d| ∣ q`) shows that every odd prime dividing `d` divides `q`, so `χ(p) = 0` there.
- If a Jacobi- or Kronecker-symbol form is wanted, apply `legendreSym.to_jacobiSym`
  pointwise. The prime-only statement was enough for the plan.

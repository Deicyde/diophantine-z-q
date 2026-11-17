import ZInQKernel.Contrib.CloudB3RC53.Basic
import ZInQKernel.Contrib.OneProof.RC.KSplit.Seed

/-!
# Lane RC3: the nonempty `K`-split seed in the shared top layer's vocabulary

The shared top layer (`ZInQ.Contrib.CloudB3RC53`, file `Basic.lean`) writes the curve as
`Ecurve ℓ = curve ℓ`, the hypothesis domain as `Adm ℓ`, and the quadratic twist as `qtwist E d`.
For `E_ℓ` the twist `qtwist (Ecurve ℓ) k` is `y² = x(x − kℓ)(x + 3kℓ) = curve (kℓ)`
(`qtwist_Ecurve_eq`), so the results of `Seed.lean` restate verbatim:

* `exists_ksplit_prime_v2_eq_two_b3` (`PROVED`): arbitrarily large primes `p ≡ 1 (mod 4)` with
  `(ℓ/p) = −1`, `(k/p) = 1`, `p ∤ 6kℓ` and `v₂(p + 1 − a_p(E^{(k)})) = 2`, for `a_p` the coefficient
  of Mathlib's `L(qtwist (Ecurve ℓ) k, s)` (tex 2643–2653, 10482–10500);
* `AppGCongruenceB3` (`ELLIOT`, tex 2636–2641, 10319–10481) and `ksplit_seed_b3` (`PROVED` from it):
  Lemma `ex:sec7-ksplit-seed`, tex 2628–2654.
-/

namespace ZInQ.Manuscript.RC.KSplit

open ZInQ.Contrib.CloudB3RC53

/-- **`qtwist (Ecurve ℓ) k = curve (kℓ)`** (`PROVED`): the shared top layer's twist of
`E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` by `k` is `y² = x(x − kℓ)(x + 3kℓ)` (`b₂ = 8ℓ`, `b₄ = −6ℓ²`,
`b₆ = 0`). -/
theorem qtwist_Ecurve_eq (ℓ : ℕ) (k : ℤ) :
    qtwist (Ecurve ℓ) (k : ℚ) = ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ) := by
  simp only [qtwist, Ecurve, ZInQ.Manuscript.curve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ext <;> push_cast <;> ring

/-- **The `K`-split prime of the seed argument, shared vocabulary** (`PROVED`; tex 2643–2653,
10482–10500): `exists_ksplit_prime_v2_eq_two` for `Adm ℓ` and `a_p` the coefficient of Mathlib's
`L(qtwist (Ecurve ℓ) k, s)`. -/
theorem exists_ksplit_prime_v2_eq_two_b3 {ℓ : ℕ} (hℓ : Adm ℓ) {k : ℤ} (hk_odd : Odd k)
    (hk_sf : Squarefree k) {q₀ : ℕ} (hq₀ : q₀.Prime) (hq₀k : (q₀ : ℤ) ∣ k)
    (hq₀ℓ : ¬ q₀ ∣ 2 * ℓ) (n : ℕ) :
    ∃ p : ℕ, n < p ∧ p.Prime ∧ p % 4 = 1 ∧ jacobiSym (ℓ : ℤ) p = -1 ∧ jacobiSym k p = 1 ∧
      ¬ (p : ℤ) ∣ 6 * (k * ℓ) ∧
      (4 : ℤ) ∣ (p : ℤ) + 1 - (qtwist (Ecurve ℓ) (k : ℚ)).LFunction p ∧
      ¬ (8 : ℤ) ∣ (p : ℤ) + 1 - (qtwist (Ecurve ℓ) (k : ℚ)).LFunction p := by
  rw [qtwist_Ecurve_eq]
  exact exists_ksplit_prime_v2_eq_two hℓ.1 hℓ.2.1 hℓ.2.2 hk_odd hk_sf hq₀ hq₀k hq₀ℓ n

/-- **The App G congruence, shared vocabulary** (`ELLIOT`; tex 2636–2641, 10319–10481):
`a_p(E^{(k)}) ≡ p + 1 (mod 8)` at every prime `p ∉ S` with `p ∤ 6kℓ` and `(k/p) = 1`, for `a_p` the
coefficient of Mathlib's `L(qtwist (Ecurve ℓ) k, s)`. -/
def AppGCongruenceB3 (ℓ : ℕ) (k : ℤ) (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ 6 * (k * ℓ) → jacobiSym k p = 1 →
    (8 : ℤ) ∣ (p : ℤ) + 1 - (qtwist (Ecurve ℓ) (k : ℚ)).LFunction p

theorem appGCongruenceB3_iff (ℓ : ℕ) (k : ℤ) (S : Finset ℕ) :
    AppGCongruenceB3 ℓ k S ↔ AppGCongruence ℓ k S := by
  simp only [AppGCongruenceB3, AppGCongruence, qtwist_Ecurve_eq]

/-- **Lemma `ex:sec7-ksplit-seed`, shared vocabulary** (`PROVED` from `AppGCongruenceB3`;
tex 2628–2654): the assumed absence `NoSeed` of a nonempty `K`-split unit seed of the positive even
source for `E^{(k)}` is refuted. -/
theorem ksplit_seed_b3 {ℓ : ℕ} (hℓ : Adm ℓ) {k : ℤ} (hk_odd : Odd k) (hk_sf : Squarefree k)
    {q₀ : ℕ} (hq₀ : q₀.Prime) (hq₀k : (q₀ : ℤ) ∣ k) (hq₀ℓ : ¬ q₀ ∣ 2 * ℓ) (S : Finset ℕ)
    (NoSeed : Prop) (hG : NoSeed → AppGCongruenceB3 ℓ k S) : ¬ NoSeed :=
  ksplit_seed hℓ.1 hℓ.2.1 hℓ.2.2 hk_odd hk_sf hq₀ hq₀k hq₀ℓ S NoSeed fun h =>
    (appGCongruenceB3_iff ℓ k S).mp (hG h)

end ZInQ.Manuscript.RC.KSplit

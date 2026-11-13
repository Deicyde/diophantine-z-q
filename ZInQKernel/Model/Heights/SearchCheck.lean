import Mathlib

/-!
# A kernel-friendly checker for the small-height search

Blueprint: `model/heights/small-height-search.md` (the computational part).

Everything here is written for evaluation by the Lean kernel: loops are `Nat.rec` on a counter,
tests are `Bool`s built from the GMP-accelerated `Nat` primitives (`Nat.beq`, `Nat.ble`, `%`, `/`,
`Nat.gcd`, `Nat.log2`), and integer square roots use Newton's iteration with a verified fallback to
`Nat.sqrt` (never reached in practice).

**Enumeration.** A primitive quadratic `a X² + b X + c` with `b² - 4ac = 2k²` has `b = 2b'`,
`k = 2k'` and `a c = b'² - 2k'²`. We enumerate `i = b' + 81 ∈ [0, 162]`, `k' ∈ [1, 81]` and the
`a ∈ [max(⌈m/81⌉, 1), 81]` with `a ∣ m`, `m ≤ 81 a` and `gcd(a, 2|b'|, m/a) = 1`, where
`m = |b'² - 2k'²|`; the list `qList` records the tuples `(a, i, k')`.

**Square test.** For `x = (U + V s)/a` (`U = -b'`, `V = ±k'`), `a⁴ f(x) = u + v s` with
`(u, v) = alpha a U V`. `possSq u v` is a necessary condition for `u + v s` to be a square in `K₀`
(proved in `possSq_of_isSquare`): `N = u² - 2v² = t²` is a perfect square and `2(u ± t)` is a
perfect square `r²` for one sign, with `2u` a perfect square when `r = 0`.
-/

namespace ZInQ.Search

/-! ### Integer square roots -/

/-- Newton's iteration `g ↦ (g + n/g)/2` while it decreases, at most `fuel` steps. -/
def newton (n : ℕ) (g : ℕ) (fuel : ℕ) : ℕ :=
  (Nat.rec (motive := fun _ => ℕ → ℕ) (fun g => g)
    (fun _ r g => let g' := (g + n / g) / 2; bif Nat.blt g' g then r g' else g) fuel) g

/-- `Nat.sqrt`, computed by Newton's iteration from `2^(⌊log₂ n⌋/2 + 1)` and checked. -/
def fastSqrt (n : ℕ) : ℕ :=
  let r := newton n (2 ^ (Nat.log2 n / 2 + 1)) 12
  bif Nat.ble (r * r) n && Nat.blt n ((r + 1) * (r + 1)) then r else Nat.sqrt n

theorem fastSqrt_eq (n : ℕ) : fastSqrt n = Nat.sqrt n := by
  unfold fastSqrt
  generalize newton n (2 ^ (Nat.log2 n / 2 + 1)) 12 = r
  dsimp only
  by_cases h : r * r ≤ n ∧ n < (r + 1) * (r + 1)
  · have hb : (Nat.ble (r * r) n && Nat.blt n ((r + 1) * (r + 1))) = true := by
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; exact h
    rw [hb, Bool.cond_true]; exact Nat.eq_sqrt.mpr h
  · have hb : (Nat.ble (r * r) n && Nat.blt n ((r + 1) * (r + 1))) = false := by
      rw [← Bool.not_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; exact h
    rw [hb, Bool.cond_false]

/-- `n` is a perfect square. -/
def isSqNat (n : ℕ) : Bool := Nat.beq (fastSqrt n * fastSqrt n) n

/-! ### The square test -/

/-- One branch of the test, for `m = u ± t`. -/
def okBranch (u m : ℤ) : Bool :=
  decide (0 ≤ m) &&
    (let r := fastSqrt (2 * m).toNat
     Nat.beq (r * r) (2 * m).toNat && (!Nat.beq r 0 || (decide (0 ≤ u) && isSqNat (2 * u).toNat)))

/-- A necessary condition for `u + v s` to be a square in `K₀`. -/
def possSq (u v : ℤ) : Bool :=
  let N := u * u - 2 * v * v
  decide (0 ≤ N) &&
    (let t : ℤ := (fastSqrt N.toNat : ℤ)
     decide (t * t = N) && (okBranch u (u + t) || okBranch u (u - t)))

/-- `a⁴ f((U + V s)/a) = u + v s` for `f(x) = x³ - (11 - 6s) x`. -/
def alpha (a U V : ℤ) : ℤ × ℤ :=
  (a * (U * U * U + 6 * U * V * V - a * a * (11 * U - 12 * V)),
   a * (3 * U * U * V + 2 * V * V * V - a * a * (11 * V - 6 * U)))

/-! ### The enumeration -/

/-- `|b'|` for `b' = i - 81`. -/
def absB (i : ℕ) : ℕ := bif Nat.ble 81 i then i - 81 else 81 - i

/-- `m = |B² - 2K²|`. -/
def mOf (B K : ℕ) : ℕ := bif Nat.ble (2 * K * K) (B * B) then B * B - 2 * K * K else 2 * K * K - B * B

/-- The smallest admissible `a`: `max(⌈m/81⌉, 1)`. -/
def loOf (m : ℕ) : ℕ := Nat.max ((m + 80) / 81) 1

/-- The condition on `a`: `a ∣ m`, `m ≤ 81 a`, `gcd(a, 2B, m/a) = 1`. -/
def aCond (B m a : ℕ) : Bool :=
  Nat.beq (m % a) 0 && Nat.ble m (81 * a) && Nat.beq (Nat.gcd (Nat.gcd a (2 * B)) (m / a)) 1

/-- The admissible `a ∈ [lo, lo + cnt)`. -/
def aLoop (B m lo cnt : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) []
    (fun i r => bif aCond B m (lo + i) then (lo + i) :: r else r) cnt

/-- The admissible `a` for `b' = i - 81`, `k' = K`. -/
def cands (i K : ℕ) : List ℕ :=
  aLoop (absB i) (mOf (absB i) K) (loOf (mOf (absB i) K)) (82 - loOf (mOf (absB i) K))

/-- The tuples `(a, i, K)` with `K ∈ [1, cnt]`. -/
def kLoop (i cnt : ℕ) : List (ℕ × ℕ × ℕ) :=
  Nat.rec (motive := fun _ => List (ℕ × ℕ × ℕ)) []
    (fun j r => (cands i (j + 1)).map (fun a => (a, i, j + 1)) ++ r) cnt

/-- The tuples `(a, i, K)` with `i ∈ [0, cnt)`, `K ∈ [1, 81]`. -/
def iLoop (cnt : ℕ) : List (ℕ × ℕ × ℕ) :=
  Nat.rec (motive := fun _ => List (ℕ × ℕ × ℕ)) [] (fun i r => kLoop i 81 ++ r) cnt

/-- All tuples `(a, i, k')` of the search box. -/
def qList : List (ℕ × ℕ × ℕ) := iLoop 163

/-! ### The checks -/

/-- The six tuples `(a, i, k', sign)` whose roots pass the necessary square test: the roots
`23 - 17s`, `(5 - 4s)/2`, `3 - s`, `2 + 4s`, `1 + s`, `-3 + s`. -/
def survivorTuples : List (ℕ × ℕ × ℕ × Bool) :=
  [(1, 58, 17, false), (4, 71, 8, false), (1, 78, 1, false), (1, 79, 4, true), (1, 80, 1, true),
    (1, 84, 1, true)]

/-- The test for both roots `(81 - i ± K s)/a` of a tuple. -/
def tupleOK (t : ℕ × ℕ × ℕ) : Bool :=
  let a : ℤ := t.1
  let U : ℤ := 81 - (t.2.1 : ℤ)
  let K : ℤ := t.2.2
  (!possSq (alpha a U K).1 (alpha a U K).2 || survivorTuples.contains (t.1, t.2.1, t.2.2, true)) &&
    (!possSq (alpha a U (-K)).1 (alpha a U (-K)).2 ||
      survivorTuples.contains (t.1, t.2.1, t.2.2, false))

/-- The test for a rational `x = p/q`: `q⁴ f(p/q) = (q p³ - 11 p q³) + 6 p q³ s`. -/
def ratOK (p q : ℤ) : Bool :=
  !Nat.beq (Nat.gcd p.natAbs q.natAbs) 1 || decide (p = 0) ||
    !possSq (q * p * p * p - 11 * p * q * q * q) (6 * p * q * q * q)

/-- All rational candidates `p/q`, `|p| ≤ 9`, `1 ≤ q ≤ 9`. -/
def ratCheck : Bool :=
  (List.range 19).all fun i => (List.range 9).all fun j => ratOK ((i : ℤ) - 9) ((j : ℤ) + 1)

/-- The whole finite search. -/
def searchCheck : Bool :=
  Nat.beq qList.length 7004 && qList.all tupleOK && ratCheck

end ZInQ.Search

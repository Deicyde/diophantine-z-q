import Mathlib

/-!
# Lane RC6: the arithmetic of the reduced generic residual rank bound (5.1)

This file formalizes the counting in the proof of Lemma `ex:limits-residual-bound`
(manuscript tex 4453–4648, Section 9 `sec:limits`):

  `N(E, A, j) ≤ 56 ω(2N) + 8A + 56j + 70`.

Kinds.  Every theorem below is `PROVED` in Lean.  The cohomological inputs (Kummer theory and the
S-unit theorem, genus theory, inflation, Tate's global Euler characteristic and cohomological
dimension, local duality and the local Euler characteristic, the dimensions of Elliot's local
conditions) are not available in Mathlib for the Galois groups `G_{K,S}` and the local Galois
groups `G_{K_w}`.  They enter as explicitly named hypotheses of the theorems, and the docstring of
each such theorem records the kind of each hypothesis (`PRINT` with locator, `GLUE`, `ELLIOT`).
The theorems are therefore exactly the arithmetic of Elliot's proof: if the printed and textbook
inputs hold with the stated numbers, the stated bounds follow.

Notation (tex 4467–4471): `v = ω(2N)`, `j` the number of derivative labels, `m = v + 1 + j`,
`S₀` the finite places of `K` above `2N`, the moving prime and the derivative primes, `T` the set of
rational primes below `S₀` together with the primes ramified in `K = ℚ(√k)`, and `s = |T|`.
-/

namespace ZInQ.Manuscript.RC.Limits

open Finset

/-! ### (5.1a): the size of `T` -/

/-- The rational primes below `S₀` (tex 4468–4469): the primes dividing `2N`, the moving prime `r`
and the derivative primes `D`.  These are the rational primes charged a local condition
("No prime dividing `k` alone is charged a local condition", tex 4582). -/
def chargedPrimes (N r : ℕ) (D : Finset ℕ) : Finset ℕ :=
  (2 * N).primeFactors ∪ {r} ∪ D

/-- The set `T` of tex 4469–4470: the rational primes below `S₀` together with the primes `Ram`
ramified in `K`. -/
def primeSetT (N r : ℕ) (D Ram : Finset ℕ) : Finset ℕ :=
  chargedPrimes N r D ∪ Ram

/-- The number of charged rational primes is at most `m = v + 1 + j` (tex 4468, 4581).
PROVED. -/
theorem card_chargedPrimes_le (N r : ℕ) (D : Finset ℕ) :
    (chargedPrimes N r D).card ≤ (2 * N).primeFactors.card + 1 + D.card := by
  unfold chargedPrimes
  calc ((2 * N).primeFactors ∪ {r} ∪ D).card
      ≤ ((2 * N).primeFactors ∪ {r}).card + D.card := card_union_le _ _
    _ ≤ (2 * N).primeFactors.card + ({r} : Finset ℕ).card + D.card := by
        gcongr; exact card_union_le _ _
    _ = (2 * N).primeFactors.card + 1 + D.card := by rw [card_singleton]

/-- **(5.1a)**, tex 4466–4474.  PROVED (counting).

With `v = ω(2N)`, `ω(k) ≤ A` and `j = |D|`, and since `2 ∣ 2N`, the set `T` has
`s = |T| ≤ v + A + 1 + j`.

Input (GLUE): the primes ramified in `K = ℚ(√k)` divide `4k`, i.e. `Ram ⊆ primes(k) ∪ {2}`
(the discriminant of `ℚ(√k)`, `k` squarefree, is `k` or `4k`).  The field `K` is imaginary, so `k`
is a negative integer; `ω(k)` is the number of primes dividing `|k|`. -/
theorem card_primeSetT_le (N r A : ℕ) (k : ℤ) (D Ram : Finset ℕ) (hN : N ≠ 0)
    (hRam : Ram ⊆ k.natAbs.primeFactors ∪ {2}) (hk : k.natAbs.primeFactors.card ≤ A) :
    (primeSetT N r D Ram).card ≤ (2 * N).primeFactors.card + A + 1 + D.card := by
  have h2 : 2 ∈ (2 * N).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.prime_two, dvd_mul_right 2 N, by omega⟩
  have hsub : primeSetT N r D Ram ⊆ ((2 * N).primeFactors ∪ k.natAbs.primeFactors) ∪ {r} ∪ D := by
    intro x hx
    unfold primeSetT chargedPrimes at hx
    have hx' : x ∈ (2 * N).primeFactors ∨ x = r ∨ x ∈ D ∨ x ∈ Ram := by
      simp only [mem_union, mem_singleton] at hx; tauto
    have hRam' : x ∈ Ram → x ∈ k.natAbs.primeFactors ∨ x = 2 := by
      intro h; have := hRam h; simpa only [mem_union, mem_singleton] using this
    simp only [mem_union, mem_singleton]
    rcases hx' with h | h | h | h
    · tauto
    · tauto
    · tauto
    · rcases hRam' h with h' | h'
      · tauto
      · subst h'; tauto
  calc (primeSetT N r D Ram).card
      ≤ (((2 * N).primeFactors ∪ k.natAbs.primeFactors) ∪ {r} ∪ D).card := card_le_card hsub
    _ ≤ (((2 * N).primeFactors ∪ k.natAbs.primeFactors) ∪ {r}).card + D.card := card_union_le _ _
    _ ≤ ((2 * N).primeFactors ∪ k.natAbs.primeFactors).card + ({r} : Finset ℕ).card + D.card := by
        gcongr; exact card_union_le _ _
    _ ≤ (2 * N).primeFactors.card + k.natAbs.primeFactors.card + 1 + D.card := by
        rw [card_singleton]; gcongr; exact card_union_le _ _
    _ ≤ (2 * N).primeFactors.card + A + 1 + D.card := by omega

/-! ### (5.1b) and the global estimate -/

/-- The place count in **(5.1b)**, tex 4494 and 4516–4517: `|S_T| ≤ 2s − r`.  PROVED (counting).

"The bound on `|S_T|` counts one prime over each ramified rational prime and at most two over each
other prime."  Here `nPlaces p` is the number of places of `K` above `p` (GLUE: at most two places
over a rational prime in a quadratic field, exactly one over a ramified prime), `Ram ⊆ T` are the
`r = |Ram|` ramified primes, and the conclusion `|S_T| + r ≤ 2s` is (5.1b, first part) written
without natural-number subtraction. -/
theorem card_places_add_ram_le (T Ram : Finset ℕ) (nPlaces : ℕ → ℕ) (hRamT : Ram ⊆ T)
    (h2 : ∀ p ∈ T, nPlaces p ≤ 2) (h1 : ∀ p ∈ Ram, nPlaces p = 1) :
    (∑ p ∈ T, nPlaces p) + Ram.card ≤ 2 * T.card := by
  have hsplit := Finset.sum_sdiff hRamT (f := nPlaces)
  have hRamSum : ∑ p ∈ Ram, nPlaces p = Ram.card := by
    rw [Finset.card_eq_sum_ones]; exact Finset.sum_congr rfl h1
  have hRest : ∑ p ∈ T \ Ram, nPlaces p ≤ 2 * (T \ Ram).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun p hp => h2 p (Finset.mem_sdiff.mp hp).1
  have hcard := Finset.card_sdiff_add_card_eq_card hRamT
  omega

/-- **The global estimate at the residue field** (tex 4478–4533), genus-theory route.  PROVED
(arithmetic of the inputs).

Hypotheses and their kinds, all with trivial coefficients `𝔽₂` resp. `W = E[2] = 𝔽₂²`:
* `hKummer` (GLUE: Kummer theory and Dirichlet's `S`-unit theorem, tex 4482–4492):
  `h¹(G_{K,S_T}, 𝔽₂) = (1 + |S_T|) + dim Cl(𝒪_{K,S_T})[2]`; the unit term has dimension
  `1 + |S_T|` (unit rank `|S_T|` for imaginary quadratic `K`, and the roots of unity give one).
* `hPlaces` (PROVED above as `card_places_add_ram_le`): `|S_T| + r ≤ 2s`.
* `hCl` (GLUE, genus theory; ELLIOT gives the proof at tex 4498–4515):
  `dim Cl(𝒪_{K,S_T})[2] ≤ r − 1`.
* `hInf` (GLUE, inflation–restriction, tex 4519–4520): inflation `H¹(G_{K,S₀},𝔽₂) → H¹(G_{K,S_T},𝔽₂)`
  is injective, so `h¹(G_{K,S₀}, 𝔽₂) ≤ h¹(G_{K,S_T}, 𝔽₂)`.
* `hW1`, `hW0` (GLUE): `W = 𝔽₂²` is trivial, so `h¹(W) = 2·h¹(𝔽₂)` and `h⁰(G_{K,S₀}, W) = 2`.
* `hEuler` (PRINT, Milne, *Arithmetic Duality Theorems*, 2nd ed. 2006, Ch. I, Thm 5.1, p. 67,
  applied over the imaginary quadratic field `K`, tex 4525–4530; hypothesis check: `S₀` contains
  the places above `2`, so `#W = 4` is a unit in `R_{K,S₀}`): `χ(G_S, W) = ∏_{v arch} #H⁰(G_v, W) /
  |#W|_v = 4/16`, i.e. `h⁰ − h¹ + h² = −2` (one complex place, `[K:ℚ] = 2`); Milne ADT I, Thm 4.10(c),
  pp. 56–57, gives `H^r(G_S, W) ≅ ∏_{v real} H^r(K_v, W) = 0` for `r ≥ 3` (no real place), which is
  why the total residual cohomology is `h⁰ + h¹ + h²`.

Conclusion: `h² = h¹ − 4`, `h¹(G_{K,S₀}, W) ≤ 4s`, and the total residual cohomology dimension of
the global complex is at most `8s − 2`, in particular at most `8s + 2`. -/
theorem global_estimate (s r placesST clDim h1ST h1S0F2 h0 h1 h2 : ℕ)
    (hKummer : h1ST = (1 + placesST) + clDim)
    (hPlaces : placesST + r ≤ 2 * s)
    (hCl : clDim + 1 ≤ r)
    (hInf : h1S0F2 ≤ h1ST)
    (hW1 : h1 = 2 * h1S0F2) (hW0 : h0 = 2)
    (hEuler : (h0 : ℤ) - h1 + h2 = -2) :
    (h2 : ℤ) = h1 - 4 ∧ h1 ≤ 4 * s ∧ h0 + h1 + h2 + 2 ≤ 8 * s ∧ h0 + h1 + h2 ≤ 8 * s + 2 := by
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **The weaker global estimate without genus theory** (tex 4534–4542).  PROVED (arithmetic of
the inputs).

Inputs: `hGenQ` (GLUE): the maximal pro-2 quotient of the Galois group of the maximal extension of
`ℚ` unramified outside `T ∪ {∞}` has `s + 1` generators (squareclasses of `−1` and of the primes in
`T`); `hSchreier` (GLUE, Schreier index formula for an index-two open subgroup of a pro-2 group:
`d(H) ≤ 2(d(G) − 1) + 1`): the subgroup for `K` has at most `2s + 1` generators; `hQuot` (GLUE):
the maximal pro-2 quotient of `G_{K,S₀}` is a quotient of it, and `h¹(·, 𝔽₂)` is at most the number
of generators; `hW1`, `hW0`, `hEuler` as in `global_estimate` (PRINT: Milne ADT I.5.1).
"In either computation the `H²` estimate is supplied by the global Euler characteristic."
Conclusion: `h¹(G_{K,S₀}, W) ≤ 4s + 2` and total dimension at most `8s + 2`. -/
theorem global_estimate_weak (s dQ dK h1S0F2 h0 h1 h2 : ℕ)
    (hGenQ : dQ = s + 1) (hSchreier : dK ≤ 2 * (dQ - 1) + 1) (hQuot : h1S0F2 ≤ dK)
    (hW1 : h1 = 2 * h1S0F2) (hW0 : h0 = 2)
    (hEuler : (h0 : ℤ) - h1 + h2 = -2) :
    h1 ≤ 4 * s + 2 ∧ h0 + h1 + h2 ≤ 8 * s + 2 := by
  refine ⟨by omega, by omega⟩

/-! ### The local terms (tex 4544–4582) -/

/-- **The local Galois cohomology of the trivial module `W = 𝔽₂²`** (tex 4545–4550).  PROVED
(arithmetic of the inputs): `(h⁰, h¹, h²)(K_w, W) = (2, 4 + 2d_w, 2)`, with `d_w = [K_w : ℚ₂]` if
`w ∣ 2` and `d_w = 0` otherwise.

Inputs: `hH0` (GLUE: `W` is trivial, so `H⁰ = W`); `hH2` (PRINT: local duality, Milne ADT, 2nd ed.,
Ch. I, Cor. 2.3, p. 28: `H²(K_w, W) ≅ H⁰(K_w, W^D)^*`, and `W^D = Hom(W, μ₂)` is again trivial of
dimension 2); `hχ` (PRINT: local Euler characteristic, Milne ADT I, Thm 2.8, p. 31:
`χ(G, W) = (R : #W·R)⁻¹`, i.e. `h⁰ − h¹ + h² = −2 d_w` for `#W = 4`).  These three inputs are
derived from the PRINT propositions over Mathlib's continuous cohomology in
`LocalPrints.local_cohomology_dims`. -/
theorem local_dims (d h0 h1 h2 : ℕ) (hH0 : h0 = 2) (hH2 : h2 = 2)
    (hχ : (h0 : ℤ) - h1 + h2 = -(2 * d)) :
    h1 = 4 + 2 * d ∧ h0 + h1 + h2 = 8 + 2 * d := by
  refine ⟨by omega, by omega⟩

/-- The local conditions of the Selmer cone (4.3) at a finite place, as listed in the table of
tex 4561–4573.  The derivative conditions are those of Lemma `ex:limits-derivative-switch`
(strict `D⁰`, finite `D⁰ ⊕ F[−1]`, singular `D⁰ ⊕ S[−1]`, relaxed `D⁰ ⊕ (F ⊕ S)[−1]`). -/
inductive LocalCondition where
  /-- the derived Kummer condition at an old place (Lemma `ex:arith-local-kummer`) -/
  | oldKummer
  /-- the unramified condition at a good place `w ∤ 2` -/
  | unramified
  /-- the zero condition -/
  | zero
  /-- the full condition -/
  | full
  /-- the derivative strict condition `D⁰` -/
  | derivStrict
  /-- the derivative finite or singular condition `D⁰ ⊕ F[−1]`, `D⁰ ⊕ S[−1]` -/
  | derivFiniteOrSingular
  /-- the derivative relaxed condition `D⁰ ⊕ (F ⊕ S)[−1]` (it does not include `D²`) -/
  | derivRelaxed
  deriving DecidableEq

namespace LocalCondition

/-- The second column of the table (tex 4563–4572): `∑_a h^a(U_w)`, the total residual dimension of
the local condition `U_w` at a place with local degree `d = d_w`.

Inputs behind the values (ELLIOT, tex 4551–4556 and Lemma `ex:limits-derivative-switch`): the old
Kummer condition has residual dimensions `(2, 2 + d_w)` in degrees 0 and 1, since
`E^{(h)}(K_w)^∧_2 ≅ ℤ₂^{d_w} ⊕ (finite 2-primary torsion with two generators)` (`E^{(h)}[2]` is
rational) and derived reduction keeps the two-dimensional degree-zero torsion; the unramified
condition `[W →(Φ−1) W]` with trivial `W` has `(2, 2)`; the full condition is the whole local
complex (`8 + 2d_w`, see `local_dims`); the derivative conditions retain `D⁰` (dimension 2) and add
`0`, `2` or `4` dimensions in degree one. -/
def dim : LocalCondition → ℕ → ℕ
  | oldKummer, d => 4 + d
  | unramified, _ => 4
  | zero, _ => 0
  | full, d => 8 + 2 * d
  | derivStrict, _ => 2
  | derivFiniteOrSingular, _ => 4
  | derivRelaxed, _ => 6

end LocalCondition

/-- `∑_a h^a(K_w, W) = 8 + 2 d_w` (tex 4549, `local_dims`). -/
def localComplexDim (d : ℕ) : ℕ := 8 + 2 * d

/-- The third column of the table: `∑ h^a(U_w) + ∑ h^a(K_w, W)`, the contribution of one place to
the total rank of the Selmer cone (4.3).  "Cone shifts do not change this sum" (tex 4560). -/
def placeCost (c : LocalCondition) (d : ℕ) : ℕ := c.dim d + localComplexDim d

/-- **The table of tex 4561–4573**, third column, row by row.  PROVED. -/
theorem placeCost_table (d : ℕ) :
    placeCost .oldKummer d = 12 + 3 * d ∧ placeCost .unramified 0 = 12 ∧
    placeCost .zero 0 = 8 ∧ placeCost .full 0 = 16 ∧ placeCost .derivStrict 0 = 10 ∧
    placeCost .derivFiniteOrSingular 0 = 12 ∧ placeCost .derivRelaxed 0 = 14 := by
  simp only [placeCost, LocalCondition.dim, localComplexDim]
  exact ⟨by omega, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- Every place costs at most `16 + 4 d_w` (the full condition is the largest).  PROVED. -/
theorem placeCost_le (c : LocalCondition) (d : ℕ) : placeCost c d ≤ 16 + 4 * d := by
  cases c <;> simp only [placeCost, LocalCondition.dim, localComplexDim] <;> omega

/-- The cost of one rational prime: the sum of the costs of its places, each place given by its
local condition and its local degree `d_w`. -/
def primeCost (places : List (LocalCondition × ℕ)) : ℕ :=
  (places.map fun x => placeCost x.1 x.2).sum

theorem primeCost_le_aux (places : List (LocalCondition × ℕ)) :
    primeCost places ≤ 16 * places.length + 4 * (places.map Prod.snd).sum := by
  induction places with
  | nil => simp [primeCost]
  | cons x xs ih =>
    have hx := placeCost_le x.1 x.2
    simp only [primeCost, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    nlinarith

/-- **Each charged rational prime costs at most 48** (tex 4576–4581).  PROVED.

"There are at most two places over each rational prime, and `∑_{w∣2} d_w = 2`."  For any choice of
the local conditions, a prime with at most two places and `∑ d_w ≤ 2` costs at most `40 ≤ 48`. -/
theorem primeCost_le_48 (places : List (LocalCondition × ℕ)) (hlen : places.length ≤ 2)
    (hd : (places.map Prod.snd).sum ≤ 2) : primeCost places ≤ 48 := by
  have := primeCost_le_aux places
  omega

/-- The old prime two costs at most 30 (tex 4577–4578): at most two places, all with the old
Kummer condition, and `∑_{w∣2} d_w = 2`.  PROVED. -/
theorem primeCost_oldTwo (places : List (LocalCondition × ℕ)) (hlen : places.length ≤ 2)
    (hK : ∀ x ∈ places, x.1 = .oldKummer) (hd : (places.map Prod.snd).sum = 2) :
    primeCost places ≤ 30 := by
  have key : ∀ l : List (LocalCondition × ℕ), (∀ x ∈ l, x.1 = .oldKummer) →
      primeCost l = 12 * l.length + 3 * (l.map Prod.snd).sum := by
    intro l hl
    induction l with
    | nil => simp [primeCost]
    | cons x xs ih =>
      have hx : x.1 = .oldKummer := hl x (List.mem_cons_self ..)
      have ih' := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
      simp only [primeCost, List.map_cons, List.sum_cons, List.length_cons] at ih' ⊢
      rw [ih', hx]
      simp only [placeCost, LocalCondition.dim, localComplexDim]
      ring
  rw [key places hK]
  omega

/-- Any other old rational prime costs at most 24 (tex 4578–4579): at most two places, old Kummer,
odd residue characteristic (`d_w = 0`).  PROVED. -/
theorem primeCost_oldOdd (places : List (LocalCondition × ℕ)) (hlen : places.length ≤ 2)
    (hK : ∀ x ∈ places, x = (.oldKummer, 0)) : primeCost places ≤ 24 := by
  have key : ∀ l : List (LocalCondition × ℕ), (∀ x ∈ l, x = (.oldKummer, 0)) →
      primeCost l = 12 * l.length := by
    intro l hl
    induction l with
    | nil => simp [primeCost]
    | cons x xs ih =>
      have hx := hl x (List.mem_cons_self ..)
      have ih' := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
      simp only [primeCost, List.map_cons, List.sum_cons, List.length_cons] at ih' ⊢
      rw [ih', hx]
      simp only [placeCost, LocalCondition.dim, localComplexDim]
      ring
  rw [key places hK]
  omega

/-- The moving prime costs at most 32 (tex 4579): at most two places, odd (`d_w = 0`), any local
condition (at most 16 each, the full condition).  PROVED. -/
theorem primeCost_moving (places : List (LocalCondition × ℕ)) (hlen : places.length ≤ 2)
    (hodd : ∀ x ∈ places, x.2 = 0) : primeCost places ≤ 32 := by
  have h0 : (places.map Prod.snd).sum = 0 := by
    rw [List.sum_eq_zero]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hodd x hx
  have := primeCost_le_aux places
  omega

/-- The costs of the derivative conditions are at most 14 (tex 4569–4571). -/
theorem placeCost_deriv_le (c : LocalCondition)
    (hc : c = .derivStrict ∨ c = .derivFiniteOrSingular ∨ c = .derivRelaxed) :
    placeCost c 0 ≤ 14 := by
  rcases hc with rfl | rfl | rfl <;> simp [placeCost, LocalCondition.dim, localComplexDim]

/-- A derivative prime costs at most 28, and at most 14 when it is inert (one place)
(tex 4579–4580).  PROVED. -/
theorem primeCost_derivative (places : List (LocalCondition × ℕ))
    (hderiv : ∀ x ∈ places, x.2 = 0 ∧
      (x.1 = .derivStrict ∨ x.1 = .derivFiniteOrSingular ∨ x.1 = .derivRelaxed)) :
    primeCost places ≤ 14 * places.length := by
  induction places with
  | nil => simp [primeCost]
  | cons x xs ih =>
    have hx := hderiv x (List.mem_cons_self ..)
    have ih' := ih fun y hy => hderiv y (List.mem_cons_of_mem _ hy)
    have hcost : placeCost x.1 x.2 ≤ 14 := by rw [hx.1]; exact placeCost_deriv_le _ hx.2
    simp only [primeCost, List.map_cons, List.sum_cons, List.length_cons] at ih' ⊢
    omega

/-- **All finite local terms cost at most `48m`** (tex 4581–4582).  PROVED.

Summing `primeCost_le_48` over the charged rational primes (the primes below `S₀`, at most
`m = v + 1 + j` of them by `card_chargedPrimes_le`). -/
theorem local_total_le (charged : Finset ℕ) (places : ℕ → List (LocalCondition × ℕ))
    (hlen : ∀ p ∈ charged, (places p).length ≤ 2)
    (hd : ∀ p ∈ charged, ((places p).map Prod.snd).sum ≤ 2) :
    ∑ p ∈ charged, primeCost (places p) ≤ 48 * charged.card := by
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun p hp => primeCost_le_48 _ (hlen p hp) (hd p hp)

/-- **The archimedean allowance** (tex 4584–4591).  PROVED (arithmetic of the input).

`K` has no real places; its complex place has full cohomology `W` in degree zero only
(`hW`, GLUE: `H⁰(ℂ, W) = W`, `dim W = 2`).  Even retaining both an ordinary full term and a full
local condition costs `2 + 2 ≤ 4` additional generators. -/
theorem archimedean_le (hFullTerm hFullCond : ℕ) (hW1 : hFullTerm = 2) (hW2 : hFullCond = 2) :
    hFullTerm + hFullCond ≤ 4 := by omega

/-! ### The bound (5.1) -/

/-- **The display (5.1)**, tex 4601–4609, step by step.  PROVED.

`(8s + 2) + 48m + 4 ≤ 8(s + 1) + 6 + 48(v + 1 + j) ≤ 56v + 8A + 56j + 70`, using `m = v + 1 + j` and
(5.1a) `s ≤ v + A + 1 + j`. -/
theorem display_5_1 (s m v A j : ℕ) (hs : s ≤ v + A + 1 + j) (hm : m = v + 1 + j) :
    (8 * s + 2) + 48 * m + 4 ≤ 8 * (s + 1) + 6 + 48 * (v + 1 + j) ∧
    8 * (s + 1) + 6 + 48 * (v + 1 + j) ≤ 56 * v + 8 * A + 56 * j + 70 := by
  refine ⟨by omega, by omega⟩

/-- The constant of Lemma `ex:limits-residual-bound`: `56 ω(2N) + 8A + 56j + 70` (tex 4459).  It
involves only `ω(2N)`, `A` and `j`: it is "independent of the number and sizes of active primes and
of `v₂(r_i − 1)`" (tex 4461–4462). -/
def residualBoundConstant (v A j : ℕ) : ℕ := 56 * v + 8 * A + 56 * j + 70

/-- **The reduced generic residual rank bound, arithmetic core** (tex 4453–4610).  PROVED
(arithmetic of the inputs).

Let `rankTot` be the total rank of the finite free model of the smaller-support Selmer cone
`C_{S₀}` at the residue field.  The hypotheses are:
* `hCone` (Lemma `ex:limits-inner-limit` applied separately to the global and local complexes,
  then the mapping cone, tex 4593–4597; "Further cancellation can only decrease it"): `rankTot` is
  at most the global total plus the local total plus the archimedean allowance;
* `hGlobal`: global total `≤ 8s + 2` (`global_estimate` or `global_estimate_weak`);
* `hLocal`: local total `≤ 48 · #(charged primes)` (`local_total_le`);
* `hArch`: archimedean allowance `≤ 4` (`archimedean_le`);
* the counting hypotheses of (5.1a) (`card_primeSetT_le`; GLUE input `hRam`).
Conclusion: `rankTot ≤ 56 ω(2N) + 8A + 56j + 70` with `j = |D|`. -/
theorem residual_rank_bound (N r A : ℕ) (k : ℤ) (D Ram : Finset ℕ) (hN : N ≠ 0)
    (hRam : Ram ⊆ k.natAbs.primeFactors ∪ {2}) (hk : k.natAbs.primeFactors.card ≤ A)
    (rankTot globalTot localTot archTot : ℕ)
    (hCone : rankTot ≤ globalTot + localTot + archTot)
    (hGlobal : globalTot ≤ 8 * (primeSetT N r D Ram).card + 2)
    (hLocal : localTot ≤ 48 * (chargedPrimes N r D).card)
    (hArch : archTot ≤ 4) :
    rankTot ≤ residualBoundConstant (2 * N).primeFactors.card A D.card := by
  have hs := card_primeSetT_le N r A k D Ram hN hRam hk
  have hm := card_chargedPrimes_le N r D
  have h51 := display_5_1 (primeSetT N r D Ram).card ((2 * N).primeFactors.card + 1 + D.card)
    (2 * N).primeFactors.card A D.card hs rfl
  unfold residualBoundConstant
  have : localTot ≤ 48 * ((2 * N).primeFactors.card + 1 + D.card) :=
    hLocal.trans (Nat.mul_le_mul_left 48 hm)
  omega

/-- **Assembled form**: the global estimate, the local table and the archimedean allowance
together give (5.1).  PROVED (arithmetic of the inputs; see the docstrings of `global_estimate`,
`local_dims`, `LocalCondition.dim` for the kinds of the inputs).

Here `places p` lists, for each charged rational prime `p`, its places (at most two) with their
local conditions and local degrees `d_w` (with `∑ d_w ≤ 2`), and the global complex is bounded by
the genus-theory route. -/
theorem residual_rank_bound_assembled (N r A : ℕ) (k : ℤ) (D Ram : Finset ℕ) (hN : N ≠ 0)
    (hRam : Ram ⊆ k.natAbs.primeFactors ∪ {2}) (hk : k.natAbs.primeFactors.card ≤ A)
    (places : ℕ → List (LocalCondition × ℕ))
    (hlen : ∀ p ∈ chargedPrimes N r D, (places p).length ≤ 2)
    (hd : ∀ p ∈ chargedPrimes N r D, ((places p).map Prod.snd).sum ≤ 2)
    (globalTot rankTot : ℕ)
    (hGlobal : globalTot ≤ 8 * (primeSetT N r D Ram).card + 2)
    (hCone : rankTot ≤ globalTot + ∑ p ∈ chargedPrimes N r D, primeCost (places p) + 4) :
    rankTot ≤ residualBoundConstant (2 * N).primeFactors.card A D.card :=
  residual_rank_bound N r A k D Ram hN hRam hk rankTot globalTot _ 4 hCone hGlobal
    (local_total_le _ places hlen hd) le_rfl

/-- `ω(2·11) = 2`: the prime factors of `22`. -/
theorem primeFactors_twentytwo : (2 * 11).primeFactors = {2, 11} := by
  rw [Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.prime_two.primeFactors,
    (by norm_num : Nat.Prime 11).primeFactors]
  rfl

/-- Non-vacuity of `residual_rank_bound_assembled`: an instance with `N = 11`, the moving prime
`13`, two derivative primes `19, 23` and the ramified set `{2, 5}` of `ℚ(√−5)`; the prime two
carries two old Kummer places with `d_w = 1`, every other charged prime two full places with
`d_w = 0`, and the global total is the full allowance `8s + 2`.  The resulting total rank is
`312 ≤ 312`, so the bound is attained by the arithmetic in this configuration. -/
example :
    let places : ℕ → List (LocalCondition × ℕ) := fun p =>
      if p = 2 then [(.oldKummer, 1), (.oldKummer, 1)] else [(.full, 0), (.full, 0)]
    8 * (primeSetT 11 13 {19, 23} {2, 5}).card + 2 +
        ∑ p ∈ chargedPrimes 11 13 {19, 23}, primeCost (places p) + 4 ≤
      residualBoundConstant (2 * 11).primeFactors.card 1 2 := by
  intro places
  have hT : primeSetT 11 13 {19, 23} {2, 5} = {2, 11, 13, 19, 23, 5} := by
    simp only [primeSetT, chargedPrimes, primeFactors_twentytwo]; decide
  have hC : chargedPrimes 11 13 {19, 23} = {2, 11, 13, 19, 23} := by
    simp only [chargedPrimes, primeFactors_twentytwo]; decide
  rw [hT, hC, primeFactors_twentytwo]
  decide

/-! ### The interface for the cohomological layer -/

/-- The data of one finite place `w` of `K` charged in the Selmer cone (4.3): its local condition,
its local degree `d_w` (`[K_w : ℚ₂]` if `w ∣ 2`, else `0`), the total residual dimension of the
local condition, and the residual dimensions of the full local complex `RΓ(K_w, W)`. -/
structure PlaceData where
  /-- the local condition `U_w` -/
  cond : LocalCondition
  /-- `d_w` -/
  deg : ℕ
  /-- `∑_a h^a(U_w)` (the actual residual dimension of the local condition) -/
  condDim : ℕ
  /-- `h⁰(K_w, W)` -/
  localH0 : ℕ
  /-- `h¹(K_w, W)` -/
  localH1 : ℕ
  /-- `h²(K_w, W)` -/
  localH2 : ℕ

/-- The contribution of a place to the total rank of the Selmer cone (tex 4558–4560). -/
def PlaceData.cost (w : PlaceData) : ℕ := w.condDim + (w.localH0 + w.localH1 + w.localH2)

/-- The counts a place must satisfy (tex 4544–4573): the local cohomology of `W` (PRINT, Milne ADT
I.2.3 and I.2.8; see `LocalPrints.local_cohomology_dims`) and the table value of the condition
(ELLIOT, tex 4551–4573). -/
structure PlaceData.Counts (w : PlaceData) : Prop where
  /-- `h⁰(K_w, W) = 2` (`W` trivial) -/
  h0 : w.localH0 = 2
  /-- `h²(K_w, W) = 2` (local duality, Milne ADT I, Cor. 2.3, p. 28) -/
  h2 : w.localH2 = 2
  /-- local Euler characteristic (Milne ADT I, Thm 2.8, p. 31): `h⁰ − h¹ + h² = −2 d_w` -/
  euler : (w.localH0 : ℤ) - w.localH1 + w.localH2 = -(2 * w.deg)
  /-- the second column of the table of tex 4561–4573 -/
  cond : w.condDim = w.cond.dim w.deg

/-- A place satisfying its counts costs exactly the table value `placeCost` (third column).
PROVED. -/
theorem PlaceData.cost_eq (w : PlaceData) (hw : w.Counts) : w.cost = placeCost w.cond w.deg := by
  have := local_dims w.deg w.localH0 w.localH1 w.localH2 hw.h0 hw.h2 hw.euler
  simp only [PlaceData.cost, placeCost, localComplexDim, hw.cond]
  omega

/-- **The cohomological counts behind (5.1)**, as clearly named hypotheses (tex 4466–4600).

This is the interface between the algebra of Lemma `ex:limits-residual-bound` (this file, PROVED)
and the cohomological layer that proves the counts for the actual complexes.  Each field records one
count used by Elliot, with its tex lines and source; `ResidualRankCounts.rank_le` derives the bound
`N(E,A,j) ≤ 56 ω(2N) + 8A + 56j + 70` from them.  The global counts are for the residual coefficient
module `W = E[2] = 𝔽₂²` (trivial) over the imaginary quadratic field `K = ℚ(√k)`; `S₀` and `T` are as
in the module docstring; `G_{K,S}` is the Galois group of the maximal extension of `K` unramified
outside `S` (not available in Mathlib, hence numbers). -/
structure ResidualRankCounts where
  /-- the conductor `N` of `E` (tex 4467) -/
  N : ℕ
  N_ne_zero : N ≠ 0
  /-- the radicand of `K = ℚ(√k)` -/
  k : ℤ
  /-- the bound `ω(k) ≤ A` (tex 4454–4455) -/
  A : ℕ
  omega_k_le : k.natAbs.primeFactors.card ≤ A
  /-- the moving prime `r_i` (tex 4468) -/
  r : ℕ
  /-- the derivative primes; `j = |D|` (tex 4454, 4469) -/
  D : Finset ℕ
  /-- the rational primes ramified in `K` (tex 4470); `r = |Ram|` in tex 4481 -/
  Ram : Finset ℕ
  /-- GLUE (tex 4470): ramified primes divide `4k` -/
  ram_sub : Ram ⊆ k.natAbs.primeFactors ∪ {2}
  /-- number of places of `K` above a rational prime (tex 4516–4517) -/
  nPlaces : ℕ → ℕ
  /-- GLUE: at most two places over each rational prime (tex 4517) -/
  nPlaces_le_two : ∀ p ∈ primeSetT N r D Ram, nPlaces p ≤ 2
  /-- GLUE: one place over each ramified prime (tex 4516) -/
  nPlaces_ram : ∀ p ∈ Ram, nPlaces p = 1
  /-- `dim_{𝔽₂} Cl(𝒪_{K,S_T})[2]` (tex 4487) -/
  clDim : ℕ
  /-- (5.1b), genus theory (tex 4494–4517; ELLIOT's proof, GLUE): `dim Cl(𝒪_{K,S_T})[2] ≤ r − 1` -/
  genus : clDim + 1 ≤ Ram.card
  /-- `h¹(G_{K,S_T}, 𝔽₂)` (tex 4486) -/
  h1ST : ℕ
  /-- Kummer theory and the `S`-unit theorem (tex 4482–4492; GLUE):
  `h¹(G_{K,S_T}, 𝔽₂) = (1 + |S_T|) + dim Cl(𝒪_{K,S_T})[2]` -/
  kummer : h1ST = (1 + ∑ p ∈ primeSetT N r D Ram, nPlaces p) + clDim
  /-- `h¹(G_{K,S₀}, 𝔽₂)` -/
  h1S0F2 : ℕ
  /-- inflation from `G_{K,S₀}` into `G_{K,S_T}` is injective on `H¹` (tex 4519–4520; GLUE) -/
  inflation : h1S0F2 ≤ h1ST
  /-- `h⁰, h¹, h²` of `G_{K,S₀}` with coefficients `W` (tex 4521–4531) -/
  h0 : ℕ
  h1 : ℕ
  h2 : ℕ
  /-- `h⁰(G_{K,S₀}, W) = 2` (tex 4522) -/
  h0_eq : h0 = 2
  /-- `W = 𝔽₂²`: `h¹(W) = 2 h¹(𝔽₂)` (tex 4523) -/
  h1_eq : h1 = 2 * h1S0F2
  /-- global Euler characteristic (tex 4525–4531; PRINT, Milne ADT I, Thm 5.1, p. 67; `H^{>2} = 0`
  by Milne ADT I, Thm 4.10(c), pp. 56–57, as `K` has no real place): `h⁰ − h¹ + h² = −2` -/
  euler : (h0 : ℤ) - h1 + h2 = -2
  /-- the places of `K` above each charged rational prime (tex 4576–4582) -/
  places : ℕ → List PlaceData
  /-- at most two places over each rational prime (tex 4576) -/
  places_length : ∀ p ∈ chargedPrimes N r D, (places p).length ≤ 2
  /-- `∑_{w ∣ p} d_w ≤ 2` (tex 4576–4577; `d_w = 0` for odd `p`, `∑_{w∣2} d_w = 2`) -/
  places_deg : ∀ p ∈ chargedPrimes N r D, ((places p).map PlaceData.deg).sum ≤ 2
  /-- every charged place satisfies its local counts (tex 4544–4573) -/
  places_counts : ∀ p ∈ chargedPrimes N r D, ∀ w ∈ places p, w.Counts
  /-- the archimedean allowance (tex 4584–4591) -/
  archTot : ℕ
  arch_le : archTot ≤ 4
  /-- the total rank of the finite free model of the smaller-support Selmer cone `C_{S₀}` at the
  residue field (tex 4593–4597, via Lemma `ex:limits-inner-limit`; "Further cancellation can only
  decrease it") -/
  rankTot : ℕ
  /-- the cone has a finite free model of total rank at most the sum of the pieces (tex 4594–4597) -/
  cone : rankTot ≤ (h0 + h1 + h2) +
    ∑ p ∈ chargedPrimes N r D, ((places p).map PlaceData.cost).sum + archTot

/-- The cost of the places over one charged prime, from its counts. -/
theorem ResidualRankCounts.prime_cost_le (R : ResidualRankCounts) (p : ℕ)
    (hp : p ∈ chargedPrimes R.N R.r R.D) : ((R.places p).map PlaceData.cost).sum ≤ 48 := by
  have hcost : ((R.places p).map PlaceData.cost).sum =
      primeCost ((R.places p).map fun w => (w.cond, w.deg)) := by
    unfold primeCost
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun w hw => ?_
    exact w.cost_eq (R.places_counts p hp w hw)
  rw [hcost]
  apply primeCost_le_48
  · rw [List.length_map]; exact R.places_length p hp
  · rw [List.map_map]; exact R.places_deg p hp

/-- **Lemma `ex:limits-residual-bound`, from the counts** (tex 4453–4610).  PROVED.

Given the cohomological counts (`ResidualRankCounts`), the total rank of the reduced generic
residual model is at most `N(E, A, j) ≤ 56 ω(2N) + 8A + 56j + 70`, with `j = |D|`.  The transfer to
the original support (tex 4612–4647: Nekovář Prop. 7.8.8(ii), contractibility of the active
comparison blocks after inverting `t`, minimal models over `𝔽₂((t))[G]`) does not change this
count; its algebra is in `ResidualAlgebra`. -/
theorem ResidualRankCounts.rank_le (R : ResidualRankCounts) :
    R.rankTot ≤ residualBoundConstant (2 * R.N).primeFactors.card R.A R.D.card := by
  have hRamT : R.Ram ⊆ primeSetT R.N R.r R.D R.Ram := fun x hx => by
    unfold primeSetT; exact Finset.mem_union_right _ hx
  have hplaces := card_places_add_ram_le _ _ R.nPlaces hRamT R.nPlaces_le_two R.nPlaces_ram
  obtain ⟨-, -, -, hglob⟩ := global_estimate (primeSetT R.N R.r R.D R.Ram).card R.Ram.card
    (∑ p ∈ primeSetT R.N R.r R.D R.Ram, R.nPlaces p) R.clDim R.h1ST R.h1S0F2 R.h0 R.h1 R.h2
    R.kummer hplaces R.genus R.inflation R.h1_eq R.h0_eq R.euler
  have hloc : ∑ p ∈ chargedPrimes R.N R.r R.D, ((R.places p).map PlaceData.cost).sum ≤
      48 * (chargedPrimes R.N R.r R.D).card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun p hp => R.prime_cost_le p hp
  exact residual_rank_bound R.N R.r R.A R.k R.D R.Ram R.N_ne_zero R.ram_sub R.omega_k_le
    R.rankTot (R.h0 + R.h1 + R.h2) _ R.archTot R.cone hglob hloc R.arch_le

end ZInQ.Manuscript.RC.Limits

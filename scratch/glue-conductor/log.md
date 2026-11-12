# glue-conductor results log

Task: glue cluster of Glazer's uniform conductor bound (h-trust D1-D4, D5's use of Carayol).
Source: diophantine_zq.tex L796-857 (conductor paragraph), constants L385-400.

## Step 1. Breaks.lean (Mathlib only) — COMPILES, no sorry (VERIFIED, `lake env lean`, 2026-11-11)

Ramification data as the sequence g i = |G_i| (lower numbering). Proved:
- `herbrand_integral`: δ_{n+1}/e = 1 − 1/e + Σ_{i=1}^n (φ(i)−φ(i−1))(1 − 1/g_i) (step-function form of N5's Herbrand integral).
- `phi_le_self`: φ(m) ≤ m for antitone g (elementary half of ψ(u) ≥ u).
- `phi_le_two_delta`: g_i ≥ 2 for i ≤ b ⇒ φ(b) ≤ 2δ/e.
- `two_delta_le`: δ ≤ e−1+e·v_p(e), e ≤ a!, a ≥ 1 ⇒ 2δ ≤ 2(1+log₂ a!)e ≤ 4a²e.
- `upper_break_le` (D1 combined): Serre bound on Hilbert's δ, e ≤ a!, G_b ≠ 1 ⇒ φ(b) ≤ 4a².
- `swan_le`, `artin_le` (D4, p ≤ R): codim ≤ 2, trivial above upper index U ⇒ Sw ≤ 2U, a ≤ 2+2U.
- `wild_trivial_of_tame`, `swan_eq_zero_of_tame` (D4, p > R): e < p ⇒ G_1 = 1 ⇒ Sw = 0.
- `char_trivial_of_odd_pgroup` (D2 last sentence): β² = 1 on a group of p-power-order elements, p odd ⇒ β = 1.
- `card_GL4_F5`: |GL₄(F₅)| = 116064000000 = G₀; `card_GL4_F3`: |GL₄(F₃)| = 24261120 (Mathlib `Matrix.card_GL_field`).
- `max_le_U0`: e ≤ D ⇒ max(4D², 3e) ≤ 4(DG₀)²; `two_add_two_U0_le_E0`: 2 + 2·4(DG₀)² ≤ 10(DG₀)².

## Step 2. Level.lean (imports ZInQKernel.Hypotheses.Height) — COMPILES, no sorry (VERIFIED)
- `level_le`: R : ℝ, R ≥ 1, max S ≤ R, N ≠ 0, v_p(N) ≤ E₀ (p ≤ R), v_p(N) ≤ 2 (p > R),
  p | N ⇒ p ∈ S ∨ p | M_S(u)  ⟹  (N:ℝ) ≤ heightQ R · (contactSupport S u)².
  `#print axioms`: propext, Classical.choice, Quot.sound.
- `prod_small_le`: ∏_{p∈s} p^E ≤ R^(R·E) for a finset s of primes ≤ R (R real ≥ 1).

## Step 3. D1 over genuine definitions (appended to Breaks.lean) — COMPILES, no sorry (VERIFIED)
- `ramGroup L P i := (P^(i+1)).inertia Gal(L/ℚ)` (Mathlib `Ideal.inertia`; lower ramification
  group G_i of a Galois number field, global form), `ramCard = Nat.card`.
- Leaves (`def … : Prop`): `HilbertDifferentFormula` (∃ n, G_n = ⊥ and the exact power of P in
  `differentIdeal ℤ (𝓞 L)` is Σ_{i<n}(|G_i|−1); Serre CL IV §1 Prop 4, UNVERIFIED numbering);
  `SerreDifferentBound` (¬ P^(e−1+e·v_p(e)+1) ∣ differentIdeal ℤ (𝓞 L), e = `P.ramificationIdx ℤ`;
  Serre CL III §6 remark after Prop 13, UNVERIFIED numbering).
- `D1_genuine`: leaves + Galois L, P over (p), e ≤ a!, G_b ≠ ⊥ ⇒ φ(b) ≤ 4a² (φ = Herbrand φ of the
  genuine |G_i|). Uses Mathlib `Ideal.card_inertia_eq_ramificationIdxIn` for |G_0| = e.
  The residue-separability instance is inferred by Mathlib (no extra hypothesis; rechecked after removal).
- `#print axioms` for `upper_break_le`, `D1_genuine`, `card_GL4_F5`: propext, Classical.choice, Quot.sound.

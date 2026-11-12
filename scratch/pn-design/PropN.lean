import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import ZInQKernel.Hypotheses.CR3Literature

/-!
# Proposition N (nt-tyz §4) in Lean: `TYZInputs → TYZRow5b`

Design draft (`docs/research/pn-design.md`). The hypothesis `Literature.TYZRow5b` is replaced by
`TYZInputs`, a conjunction of consequences of statements printed in Tian–Yuan–Zhang
(arXiv:1411.4728v1, cited as TYZ; line numbers `Lnnnn` refer to `Period7.tex`):

* an integer function `L` (TYZ's `𝓛`, §1, L338–345) with `L 1 = 1` (L1082) and Lemma 2.8 with
  Proposition 2.3 modulo 2 (L1062–1066, L580–586): `LemmaTwoEight L`;
* the defining property of `𝓛` for `n ≡ 5 (mod 8)` (L338–345), with the continuation of
  `L(C_n, s)`: `L n ≠ 0 → ∃ F, IsLContinuation … F ∧ analyticOrderAt F 1 ≤ 1`;
* for each squarefree `n ≡ 5 (mod 8)`, the genus-point data `GenusData L n` over the
  `ℤ[i]`-module `M = A(ℍ'_n)` (§3.1, L1314–1330; Theorem 3.3, L1299–1311; Theorem 3.5,
  L1353–1356; τ, L1384–1402; Lemmas 3.16, 3.18, L2182–2232; Lemma 3.21, L2494–2510; the remark
  "β acts on ℚ(i) trivially", L2585).

Lean proves `tyzRow5b_of_tyzInputs` from four lemmas whose proofs are left `sorry` here, to be
proved in parallel against these fixed statements:

* `lemmaN1_core`  — Lemma N1's combinatorial content: `Λ` satisfies the I2 identity mod 2
  (`lemmaN1`, the uniqueness induction, is proved here from it);
* `lemmaN2`       — Lemma N2 in its `𝓛`-form: `P(n) = Σ_e 𝓛(n/e) Z(e) + 2X`;
* `finalStep`     — §4.4: if `𝓛(n) = 0`, the integers `a = Σ_{e≡5} 𝓛(n/e) g(e)` and
  `N = Σ_{e≡7} 𝓛(n/e) g(e)` are even;
* `matching`      — `Σ_{e≡5} Λ(n/e) g(e) = T5aCl n` and `Σ_{e≡7} Λ(n/e) g(e) = T5bCl n` in `𝔽₂`.
-/

noncomputable section

namespace ZInQ.PropN

open ZInQ.Literature ZInQ.RouteK.Rank5b

/-! ### TYZ's `g` on natural numbers, and `i` -/

/-- TYZ's genus class number `g(e) = #(2 Cl(ℚ(√−e)))` (L363) as a function on `ℕ` (`gCl` needs
`e ≠ 0`; the value at `0` is never used). -/
def gNat (e : ℕ) : ℕ := if h : e = 0 then 0 else haveI : NeZero e := ⟨h⟩; gCl e

/-- The Gaussian integer `i`. -/
def gi : GaussianInt := ⟨0, 1⟩

/-- `(1 + i)³ = 2i(1 + i) = −2 + 2i`; its associate `2 + 2i = −i(1+i)³` generates the kernel of
`y ↦ τ(y/2)`. -/
def twoTwoI : GaussianInt := ⟨2, 2⟩

/-! ### The inputs -/

/-- **Lemma 2.8 with Proposition 2.3, modulo 2** (TYZ L1062–1066, L580–586; §2 assumes `n ≡ 1, 2, 3`
positive squarefree, L499): `Σ ε(d₁, d₂) 𝓛(d₁)𝓛(d₂) = Q(m) ≡ g(m) (mod 2)` over the non-ordered
decompositions `m = d₁d₂` with `d₂ ≡ 1 (mod 8)`.

* `m ≡ 1`: both factors are `≡ 1`; each unordered pair `{d, m/d}` (`d ≠ m/d` as `m > 1` is
  squarefree) is counted once, through its member with `d² < m`.
* `m ≡ 3`: `d₂ ≡ 1` and `d₁ ≡ 3` are distinguished by their classes; the sum is over `d₂ = d`.

The signs `ε = ±1` vanish modulo 2. Restricted to `m > 1` (for `m = 3` automatic). -/
def LemmaTwoEight (L : ℕ → ℤ) : Prop :=
  (∀ m : ℕ, Squarefree m → 1 < m → m % 8 = 1 →
    (((∑ d ∈ m.divisors.filter (fun d => d % 8 = 1 ∧ d * d < m), L d * L (m / d) : ℤ) :
      ZMod 2) = (gNat m : ZMod 2))) ∧
  (∀ m : ℕ, Squarefree m → m % 8 = 3 →
    (((∑ d ∈ m.divisors.filter (fun d => d % 8 = 1), L (m / d) * L d : ℤ) : ZMod 2) =
      (gNat m : ZMod 2)))

/-- **The genus-point data of TYZ §3 for one squarefree `n ≡ 5 (mod 8)`.** `M` plays the role of
`A(ℍ'_n)` (a `ℤ[i]`-module, L1324), `Z e` of the genus point `Z(e)` and `P e` of the point `P(e)`
for `e ∣ n` (L1316–1330; `ℍ'_e ⊂ ℍ'_n`), `τ y` of `τ(y/2)` (L1384–1402), and `β` of the action of a
lifting `β' ∈ Gal(ℚ̄/ℚ)` of `β₁ = r_∞(−1) r₂(−2)` (L2486–2490) on `A(ℍ'_n)`. -/
structure GenusData (L : ℕ → ℤ) (n : ℕ) where
  /-- `A(ℍ'_n)`. -/
  M : Type
  [addCommGroup : AddCommGroup M]
  [module : Module GaussianInt M]
  /-- `Z(e)`, the genus point (L1316). -/
  Z : ℕ → M
  /-- `P(e)` (L1326). -/
  P : ℕ → M
  /-- `ε(d₀, d₁) ∈ μ₄` of Theorem 3.3 (L1309–1310). -/
  ε : ℕ → ℕ → GaussianInt
  /-- Theorem 3.3: `ε(d₀, d₁) = ±i` if `(d₀, d₁) ≡ (5, 3) (mod 8)`. -/
  eps_53 : ∀ d₀ d₁ : ℕ, d₀ * d₁ ∣ n → d₀ % 8 = 5 → d₁ % 8 = 3 → ε d₀ d₁ = gi ∨ ε d₀ d₁ = -gi
  /-- Theorem 3.3: `ε(d₀, d₁) = ±1` otherwise (the odd classes `(5,1)`, `(7,1)`, `(7,3)`). -/
  eps_pm1 : ∀ d₀ d₁ : ℕ, d₀ * d₁ ∣ n →
    (d₀ % 8 = 5 ∧ d₁ % 8 = 1 ∨ d₀ % 8 = 7 ∧ d₁ % 8 = 1 ∨ d₀ % 8 = 7 ∧ d₁ % 8 = 3) →
    ε d₀ d₁ = 1 ∨ ε d₀ d₁ = -1
  /-- **I1**, the recursion defining `P` (L1326–1328), for every `d ∣ n` with `d ≡ 5, 7 (mod 8)`:
  `P(d) = Z(d) − Σ_{d = d₀d₁, d₁ ≡ 1, 3, d₁ > 1} ε(d₀, d₁) 𝓛(d₁) P(d₀)` (for odd `d ≡ 5, 7`, the
  classes `d₁ ≡ 1, 3` force `d₀ ≡ 5, 7`). -/
  recursion : ∀ d ∈ n.divisors, (d % 8 = 5 ∨ d % 8 = 7) →
    P d = Z d - ∑ d₁ ∈ d.divisors.filter (fun d₁ => 1 < d₁ ∧ (d₁ % 8 = 1 ∨ d₁ % 8 = 3)),
      (ε (d / d₁) d₁ * (L d₁ : GaussianInt)) • P (d / d₁)
  /-- **I3**, Theorem 3.5 (first assertion, L1356) with `𝒫(n) = 0` if `𝓛(n) = 0` (L1295):
  `P(n)` then vanishes in `A(ℍ'_n) ⊗ ℚ`, i.e. is torsion. -/
  torsion_of_zero : L n = 0 → IsOfFinAddOrder (P n)
  /-- `y ↦ τ(y/2)`, `ℤ[i] → A[(1+i)³] = A(ℚ(i)) ⊂ A(ℍ'_n)` (L1386–1399). -/
  τ : GaussianInt →+ M
  /-- `τ` is an isomorphism `ℂ/(1+i)ℤ[i] → A(ℂ)` (L1386): `τ(y/2) = 0 ↔ y ∈ 2(1+i)ℤ[i]`. -/
  τ_eq_zero : ∀ y, τ y = 0 ↔ twoTwoI ∣ y
  /-- **I4**, Lemma 3.18 (L2230–2232, `n` odd): `A(ℍ'_n)_tors = A[(1+i)³] = τ(½ℤ[i])`. -/
  tors_mem_range : ∀ x : M, IsOfFinAddOrder x → ∃ y, τ y = x
  /-- `β'` acting on `A(ℍ'_n)` (additive; `ℍ'_n/ℚ` is Galois, F5 from Proposition 3.2(1)). -/
  β : M →+ M
  /-- `β'` fixes `A[(1+i)³] = A(ℚ(i))` (Lemma 3.16, L2182–2185), since `β` acts trivially on
  `ℚ(i)` (L2585). -/
  β_τ : ∀ y, β (τ y) = τ y
  /-- **I5**, Lemma 3.21(1) (L2496–2498): `Z(e)^{β'+1} ∈ g(e) τ((1−i)/2) + ℤ τ(1)` for `e ≡ 5`. -/
  beta_five : ∀ e ∈ n.divisors, e % 8 = 5 →
    ∃ k : ℤ, β (Z e) + Z e = (gNat e : ℤ) • τ ⟨1, -1⟩ + k • τ 2
  /-- **I5**, Lemma 3.21(4) (L2506–2508): `Z(e)^{β'+1} = g(e) τ(1/2)` for `e ≡ 7`. -/
  beta_seven : ∀ e ∈ n.divisors, e % 8 = 7 → β (Z e) + Z e = (gNat e : ℤ) • τ 1

attribute [instance] GenusData.addCommGroup GenusData.module

/-- **The TYZ inputs of Proposition N.** There is an integer function `L` (TYZ's `𝓛`, integral by
Theorems 1.1, 1.2 and 3.5(1); a choice of the sign of each value, L357) such that
`L 1 = 1` (L1082), Lemma 2.8 with Proposition 2.3 holds modulo 2, `L n ≠ 0` gives analytic rank
at most one for `n ≡ 5 (mod 8)` (the definition of `𝓛`, L338–345, `𝓛(n) = 0` if
`ord_{s=1} > 1`, with the continuation of `L(C_n, s)`; `E_n ≅ C_n` over `ℚ`), and every squarefree
`n ≡ 5 (mod 8)` carries the genus-point data of TYZ §3. -/
def TYZInputs : Prop :=
  ∃ L : ℕ → ℤ, L 1 = 1 ∧ LemmaTwoEight L ∧
    (∀ n : ℕ, n % 8 = 5 → Squarefree n → L n ≠ 0 →
      ∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(n : ℚ) ^ 2)) F ∧ analyticOrderAt F 1 ≤ 1) ∧
    (∀ n : ℕ, n % 8 = 5 → Squarefree n → Nonempty (GenusData L n))

/-! ### `Λ` (nt-tyz §4.3) -/

/-- The partitions counted by `Λ(m)`: all blocks `≡ 1` or `3 (mod 8)`, at most one block `≡ 3`
(for `m ≡ 1` this means none, for `m ≡ 3` exactly one). -/
def LamAdm (m : ℕ) (P : Finpartition (Finset.univ : Finset m.primeFactors)) : Prop :=
  (∀ B ∈ P.parts, dProd B % 8 = 1 ∨ dProd B % 8 = 3) ∧
  (P.parts.filter fun B => dProd B % 8 = 3).card ≤ 1

instance (m : ℕ) (P : Finpartition (Finset.univ : Finset m.primeFactors)) :
    Decidable (LamAdm m P) := by
  unfold LamAdm; infer_instance

/-- `Λ(m) = Σ_π Π_{B∈π} g(d_B)` over the set partitions of the primes of `m` counted by `LamAdm`
(nt-tyz §4.3): `Λ(m) = 𝓛₁(m)` for `m ≡ 1`, `Λ(m) = Σ_{d≡3} g(d)𝓛₁(m/d)` for `m ≡ 3`, `Λ(1) = 1`. -/
def Lam (m : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset m.primeFactors),
    if LamAdm m P then ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0

/-! ### The four lemmas (statements fixed; proofs `sorry`) -/

/-- **Lemma N1, combinatorial core**: `Λ(1) = 1` and `Λ` satisfies the identity of
`LemmaTwoEight` modulo 2. (nt-tyz §4.3: a partition with `b` class-1 blocks refines
`2^{b−1} − 1` unordered pairs; with one class-3 block and a set `S` of class-1 blocks it arises
`2^{|S|} − 1` times.) -/
theorem lemmaN1_core :
    Lam 1 = 1 ∧
    (∀ m : ℕ, Squarefree m → 1 < m → m % 8 = 1 →
      ∑ d ∈ m.divisors.filter (fun d => d % 8 = 1 ∧ d * d < m), Lam d * Lam (m / d) =
        (gNat m : ZMod 2)) ∧
    (∀ m : ℕ, Squarefree m → m % 8 = 3 →
      ∑ d ∈ m.divisors.filter (fun d => d % 8 = 1), Lam (m / d) * Lam d = (gNat m : ZMod 2)) := by
  sorry

/-- **Lemma N2** (`𝓛`-form): for squarefree `n ≡ 5 (mod 8)`, unwinding the recursion gives
`P(n) = Σ_{e ∣ n, e ≡ 5, 7} 𝓛(n/e) Z(e) + 2X` with `X ∈ A(ℍ'_n)`. Uses only `recursion`,
`eps_53`, `eps_pm1` and `L 1 = 1`; no Lemma 2.8. (Inductive identity: for `d ∣ n`, `d ≡ 5, 7`,
`P(d) ≡ Σ_e φ(d, e) 𝓛(d/e) Z(e)` mod `2M`, with `φ = i` for `(d, e) ≡ (7, 5)` and `1` otherwise;
the induction step pairs `d₁ ↔ (d/e)/d₁`.) -/
theorem lemmaN2 {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) (hn : n % 8 = 5) (hsq : Squarefree n)
    (hL1 : L 1 = 1) :
    ∃ X : G.M, G.P n =
      ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7), L (n / e) • G.Z e + (2 : ℤ) • X := by
  sorry

/-- **The final step** (nt-tyz §4.4): if `𝓛(n) = 0`, then `a = Σ_{e≡5} 𝓛(n/e) g(e)` and
`N = Σ_{e≡7} 𝓛(n/e) g(e)` are even. Uses `torsion_of_zero`, `τ_eq_zero`, `tors_mem_range`, `β_τ`,
`beta_five`, `beta_seven`. -/
theorem finalStep {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) (hn : n % 8 = 5) (hL : L n = 0)
    {X : G.M}
    (hX : G.P n =
      ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7), L (n / e) • G.Z e + (2 : ℤ) • X) :
    (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), L (n / e) * (gNat e : ℤ) : ℤ) : ZMod 2) = 0) ∧
    (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), L (n / e) * (gNat e : ℤ) : ℤ) : ZMod 2) = 0) := by
  sorry

/-- **Matching** (nt-tyz §4.4, last line): the brackets in `Λ` are the fork's genus sums,
`Σ_{e≡5} Λ(n/e) g(e) = T_5a(n)` and `Σ_{e≡7} Λ(n/e) g(e) = T_5b(n)` (split a partition at its
unique block of class 5, resp. 7). -/
theorem matching {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) :
    ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), Lam (n / e) * (gNat e : ZMod 2) = T5aCl n ∧
    ∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), Lam (n / e) * (gNat e : ZMod 2) = T5bCl n := by
  sorry

/-! ### Lemma N1 from its core (uniqueness of the solution of the I2 recursion) -/

theorem mod8_div {m d : ℕ} (hd : d ∣ m) : m % 8 = (m / d % 8) * (d % 8) % 8 := by
  conv_lhs => rw [← Nat.div_mul_cancel hd]
  exact Nat.mul_mod _ _ _

theorem div_mod8_of {m d a b : ℕ} (hd : d ∣ m) (hm : m % 8 = a) (hdb : d % 8 = b)
    (hb : b = 1 ∨ b = 3 ∨ b = 5 ∨ b = 7) :
    m / d % 8 = (a * b) % 8 := by
  have h := mod8_div hd
  have hx : m / d % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [hm, hdb] at h
  subst hm hdb
  rcases hb with hb | hb | hb | hb <;> rw [hb] at h ⊢ <;>
    interval_cases hq : m / d % 8 <;> omega

/-- **Lemma N1**: `𝓛(m) ≡ Λ(m) (mod 2)` for squarefree `m ≡ 1, 3 (mod 8)`. -/
theorem lemmaN1 {L : ℕ → ℤ} (h1 : L 1 = 1) (h2 : LemmaTwoEight L) :
    ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((L m : ℤ) : ZMod 2) = Lam m := by
  obtain ⟨c1, c2, c3⟩ := lemmaN1_core
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hsq hcl
  have hm0 : m ≠ 0 := hsq.ne_zero
  rcases hcl with h | h
  · by_cases hm1 : m = 1
    · subst hm1; rw [h1, c1]; simp
    have hm : 1 < m := by omega
    have hL := h2.1 m hsq hm h
    have hΛ := c2 m hsq hm h
    set D := m.divisors.filter (fun d => d % 8 = 1 ∧ d * d < m) with hD
    have h1D : 1 ∈ D := by
      rw [hD, Finset.mem_filter, Nat.mem_divisors]; exact ⟨⟨one_dvd _, hm0⟩, rfl, by omega⟩
    push_cast at hL
    rw [← Finset.add_sum_erase _ _ h1D] at hL hΛ
    have hrest : ∑ d ∈ D.erase 1, ((L d : ZMod 2) * (L (m / d) : ZMod 2)) =
        ∑ d ∈ D.erase 1, Lam d * Lam (m / d) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      simp only [hD, Finset.mem_erase, Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨hd1, ⟨hdm, -⟩, hd8, hdd⟩ := hd
      have hd0 : d ≠ 0 := by rintro rfl; simp at hdm; omega
      have hdlt : d < m := lt_of_le_of_lt (Nat.le_mul_self d) hdd
      have hqlt : m / d < m := Nat.div_lt_self (by omega) (by omega)
      have hq8 : m / d % 8 = 1 := by rw [div_mod8_of hdm h hd8 (Or.inl rfl)]
      rw [ih d hdlt (hsq.squarefree_of_dvd hdm) (Or.inl hd8),
        ih (m / d) hqlt (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm)) (Or.inl hq8)]
    rw [hrest, Nat.div_one, h1] at hL
    rw [Nat.div_one, c1] at hΛ
    simp only [Int.cast_one, one_mul] at hL hΛ
    exact add_right_cancel (hL.trans hΛ.symm)
  · have hm : 1 < m := by omega
    have hL := h2.2 m hsq h
    have hΛ := c3 m hsq h
    set D := m.divisors.filter (fun d => d % 8 = 1) with hD
    have h1D : 1 ∈ D := by
      rw [hD, Finset.mem_filter, Nat.mem_divisors]; exact ⟨⟨one_dvd _, hm0⟩, rfl⟩
    push_cast at hL
    rw [← Finset.add_sum_erase _ _ h1D] at hL hΛ
    have hrest : ∑ d ∈ D.erase 1, ((L (m / d) : ZMod 2) * (L d : ZMod 2)) =
        ∑ d ∈ D.erase 1, Lam (m / d) * Lam d := by
      refine Finset.sum_congr rfl fun d hd => ?_
      simp only [hD, Finset.mem_erase, Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨hd1, ⟨hdm, -⟩, hd8⟩ := hd
      have hd0 : d ≠ 0 := by rintro rfl; simp at hdm; omega
      have hdle : d ≤ m := Nat.le_of_dvd (by omega) hdm
      have hdlt : d < m := lt_of_le_of_ne hdle (by rintro rfl; omega)
      have hqlt : m / d < m := Nat.div_lt_self (by omega) (by omega)
      have hq8 : m / d % 8 = 3 := by rw [div_mod8_of hdm h hd8 (Or.inl rfl)]
      rw [ih d hdlt (hsq.squarefree_of_dvd hdm) (Or.inl hd8),
        ih (m / d) hqlt (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm)) (Or.inr hq8)]
    rw [hrest, Nat.div_one, h1] at hL
    rw [Nat.div_one, c1] at hΛ
    simp only [Int.cast_one, mul_one] at hL hΛ
    exact add_right_cancel (hL.trans hΛ.symm)

/-! ### Proposition N -/

/-- `𝓛(n) = 0` forces both genus sums to vanish (reading A of TYZ Theorem 3.5(2), `n ≡ 5`). -/
theorem genusSums_eq_zero {L : ℕ → ℤ} (hL1 : L 1 = 1) (h28 : LemmaTwoEight L) {n : ℕ}
    (hn : n % 8 = 5) (hsq : Squarefree n) (G : GenusData L n) (hL : L n = 0) :
    T5aCl n = 0 ∧ T5bCl n = 0 := by
  obtain ⟨X, hX⟩ := lemmaN2 G hn hsq hL1
  obtain ⟨h5, h7⟩ := finalStep G hn hL hX
  obtain ⟨m5, m7⟩ := matching hn hsq
  have key : ∀ c : ℕ, (c = 5 ∨ c = 7) →
      (((∑ e ∈ n.divisors.filter (fun e => e % 8 = c), L (n / e) * (gNat e : ℤ) : ℤ) : ZMod 2)) =
      ∑ e ∈ n.divisors.filter (fun e => e % 8 = c), Lam (n / e) * (gNat e : ZMod 2) := by
    intro c hc
    push_cast
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨hen, -⟩, he8⟩ := he
    have hq : n / e % 8 = 1 ∨ n / e % 8 = 3 := by
      rw [div_mod8_of hen hn he8 (by omega)]; rcases hc with rfl | rfl <;> norm_num
    rw [lemmaN1 hL1 h28 (n / e) (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hen)) hq]
  constructor
  · rw [← m5, ← key 5 (Or.inl rfl), h5]
  · rw [← m7, ← key 7 (Or.inr rfl), h7]

/-- **`TYZRow5b` from the TYZ inputs** (Proposition N, row `(7, 3)`). -/
theorem tyzRow5b_of_tyzInputs (h : TYZInputs) : TYZRow5b := by
  obtain ⟨L, hL1, h28, hI7, hG⟩ := h
  intro d hd hsq h5b
  by_cases hLd : L d = 0
  · exfalso
    obtain ⟨G⟩ := hG d hd hsq
    have h0 := (genusSums_eq_zero hL1 h28 hd hsq G hLd).2
    rw [h0] at h5b
    exact zero_ne_one h5b
  · exact hI7 d hd hsq hLd

/-- **Reading A of TYZ Theorem 3.5(2) for `n ≡ 5 (mod 8)`** (both rows) from the TYZ inputs. -/
theorem tyzThm35ReadingA_of_tyzInputs (h : TYZInputs) : TYZThm35ReadingA := by
  obtain ⟨L, hL1, h28, hI7, hG⟩ := h
  intro d hd hsq F hF h2
  obtain ⟨G⟩ := hG d hd hsq
  refine genusSums_eq_zero hL1 h28 hd hsq G ?_
  by_contra hLd
  obtain ⟨F', hF', hle⟩ := hI7 d hd hsq hLd
  rw [hF'.eq hF] at hle
  exact absurd (hle.trans_lt (by norm_num)) (not_lt.mpr h2)

end ZInQ.PropN

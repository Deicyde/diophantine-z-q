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
  `ℤ[i]`-module `M = A(ℍ'_n)` (§3.1, L1314–1330, recursion L1325–1330; Theorem 3.3,
  L1299–1311; Theorem 3.5, L1353–1356; τ, L1384–1402; Lemmas 3.16, 3.18, L2182–2232;
  Lemma 3.21, L2504–2517; the remark "β acts on ℚ(i) trivially", L2581).

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
for `e ∣ n` (L1318–1330; `ℍ'_e ⊂ ℍ'_n`), `τ y` of `τ(y/2)` (L1384–1402), and `β` of the action of a
lifting `β' ∈ Gal(ℚ̄/ℚ)` of `β₁ = r_∞(−1) r₂(−2)` (L2496–2500) on `A(ℍ'_n)`. -/
structure GenusData (L : ℕ → ℤ) (n : ℕ) where
  /-- `A(ℍ'_n)`. -/
  M : Type
  [addCommGroup : AddCommGroup M]
  [module : Module GaussianInt M]
  /-- `Z(e)`, the genus point (L1318). -/
  Z : ℕ → M
  /-- `P(e)` (L1325–1330). -/
  P : ℕ → M
  /-- `ε(d₀, d₁) ∈ μ₄` of Theorem 3.3 (L1309–1310). -/
  ε : ℕ → ℕ → GaussianInt
  /-- Theorem 3.3: `ε(d₀, d₁) = ±i` if `(d₀, d₁) ≡ (5, 3) (mod 8)`. -/
  eps_53 : ∀ d₀ d₁ : ℕ, d₀ * d₁ ∣ n → d₀ % 8 = 5 → d₁ % 8 = 3 → ε d₀ d₁ = gi ∨ ε d₀ d₁ = -gi
  /-- Theorem 3.3: `ε(d₀, d₁) = ±1` otherwise (the odd classes `(5,1)`, `(7,1)`, `(7,3)`). -/
  eps_pm1 : ∀ d₀ d₁ : ℕ, d₀ * d₁ ∣ n →
    (d₀ % 8 = 5 ∧ d₁ % 8 = 1 ∨ d₀ % 8 = 7 ∧ d₁ % 8 = 1 ∨ d₀ % 8 = 7 ∧ d₁ % 8 = 3) →
    ε d₀ d₁ = 1 ∨ ε d₀ d₁ = -1
  /-- **I1**, the recursion defining `P` (L1325–1330), for every `d ∣ n` with `d ≡ 5, 7 (mod 8)`:
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
  `ℚ(i)` (L2581). -/
  β_τ : ∀ y, β (τ y) = τ y
  /-- **I5**, Lemma 3.21(1) (L2506–2508): `Z(e)^{β'+1} ∈ g(e) τ((1−i)/2) + ℤ τ(1)` for `e ≡ 5`. -/
  beta_five : ∀ e ∈ n.divisors, e % 8 = 5 →
    ∃ k : ℤ, β (Z e) + Z e = (gNat e : ℤ) • τ ⟨1, -1⟩ + k • τ 2
  /-- **I5**, Lemma 3.21(4) (L2514–2516): `Z(e)^{β'+1} = g(e) τ(1/2)` for `e ≡ 7`. -/
  beta_seven : ∀ e ∈ n.divisors, e % 8 = 7 → β (Z e) + Z e = (gNat e : ℤ) • τ 1

attribute [instance] GenusData.addCommGroup GenusData.module

/-- **The TYZ inputs of Proposition N.** There is an integer function `L` (TYZ's `𝓛`, integral by
Theorems 1.1, 1.2 and 3.5(1); a choice of the sign of each value, L361) such that
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

/-! ### Lemma N2: helpers (prefix `n2_`) -/

theorem n2_div_mod8 {m q a c : ℕ} (hq : q ∣ m) (hm : m % 8 = a) (hc : q % 8 = c)
    (hc' : c = 1 ∨ c = 3 ∨ c = 5 ∨ c = 7) : m / q % 8 = (a * c) % 8 := by
  have h : m % 8 = (m / q % 8) * (q % 8) % 8 := by
    conv_lhs => rw [← Nat.div_mul_cancel hq]
    exact Nat.mul_mod _ _ _
  have hx : m / q % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [hm, hc] at h
  subst hm hc
  rcases hc' with hb | hb | hb | hb <;> rw [hb] at h ⊢ <;>
    interval_cases hr : m / q % 8 <;> omega

theorem n2_mod8_mul {m q : ℕ} (hq : q ∣ m) : (q % 8) * (m / q % 8) % 8 = m % 8 := by
  conv_rhs => rw [← Nat.mul_div_cancel' hq]
  exact (Nat.mul_mod _ _ _).symm

/-- The ring `ℤ[i]/(2)`. -/
abbrev n2_R : Type := GaussianInt ⧸ Ideal.span {(2 : GaussianInt)}

abbrev n2_π : GaussianInt →+* n2_R := Ideal.Quotient.mk _

theorem n2_two : (2 : n2_R) = 0 := by
  rw [show (2 : n2_R) = n2_π 2 from (map_ofNat n2_π 2).symm]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

theorem n2_neg (x : n2_R) : -x = x :=
  neg_eq_iff_add_eq_zero.mpr (by rw [← two_mul, n2_two, zero_mul])

/-- The class of `i` in `ℤ[i]/(2)`. -/
def n2_I : n2_R := n2_π gi

/-- The class of `ε(d₀, d₁)` modulo 2, from the classes `a = d₀ % 8`, `c = d₁ % 8`. -/
def n2_epsR (a c : ℕ) : n2_R := if a = 5 ∧ c = 3 then n2_I else 1

/-- `φ(d, e)` modulo 2, from `a = d % 8`, `b = e % 8`. -/
def n2_phi (a b : ℕ) : n2_R := if a = 7 ∧ b = 5 then n2_I else 1

theorem n2_eps {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) {x y : ℕ} (hxy : x * y ∣ n)
    (hx : x % 8 = 5 ∨ x % 8 = 7) (hy : y % 8 = 1 ∨ y % 8 = 3) :
    n2_π (G.ε x y) = n2_epsR (x % 8) (y % 8) := by
  by_cases h53 : x % 8 = 5 ∧ y % 8 = 3
  · rw [n2_epsR, ite_eq_left h53, n2_I]
    rcases G.eps_53 x y hxy h53.1 h53.2 with h | h <;> simp [h, n2_neg]
  · rw [n2_epsR, ite_eq_right h53]
    have : x % 8 = 5 ∧ y % 8 = 1 ∨ x % 8 = 7 ∧ y % 8 = 1 ∨ x % 8 = 7 ∧ y % 8 = 3 := by omega
    rcases G.eps_pm1 x y hxy this with h | h <;> simp [h, n2_neg]

/-- `κ(q) = ε(d/q, q) φ(d/q, e)` modulo 2 takes the same value at `q` and `m/q` (`m = d/e`). -/
theorem n2_kappa {a b c c' x x' : ℕ} (ha : a = 5 ∨ a = 7) (hb : b = 5 ∨ b = 7)
    (hc : c = 1 ∨ c = 3) (hc' : c' = 1 ∨ c' = 3) (hx : x = a * c % 8) (hx' : x' = a * c' % 8)
    (h : c * c' % 8 = a * b % 8) :
    n2_epsR x c * n2_phi x b = n2_epsR x' c' * n2_phi x' b := by
  subst hx hx'
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hc' with rfl | rfl <;> revert h <;> norm_num [n2_epsR, n2_phi]

/-- The surviving term: `ε(e, d/e) ≡ φ(d, e)`. -/
theorem n2_last {a b : ℕ} (ha : a = 5 ∨ a = 7) (hb : b = 5 ∨ b = 7) :
    n2_epsR b (a * b % 8) * n2_phi b b = n2_phi a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [n2_epsR, n2_phi]

/-- The coefficient of `Z(e)` in `P(d)`, defined by the recursion of TYZ §3.1. -/
def n2_c (ε : ℕ → ℕ → GaussianInt) (L : ℕ → ℤ) (e : ℕ) : ℕ → GaussianInt
  | d => (if e = d then 1 else 0) -
      ∑ q ∈ (d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3))).attach,
        (ε (d / q) q * (L q : GaussianInt)) * n2_c ε L e (d / q)
decreasing_by
  have h := q.2
  simp only [Finset.mem_filter, Nat.mem_divisors] at h
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h.1.2) h.2.1

theorem n2_c_eq (ε : ℕ → ℕ → GaussianInt) (L : ℕ → ℤ) (e d : ℕ) :
    n2_c ε L e d = (if e = d then 1 else 0) -
      ∑ q ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)),
        (ε (d / q) q * (L q : GaussianInt)) * n2_c ε L e (d / q) := by
  rw [n2_c]
  congr 1
  exact Finset.sum_attach _ (fun q => (ε (d / q) q * (L q : GaussianInt)) * n2_c ε L e (d / q))

theorem n2_mem_Q {n d q : ℕ} (hd : d ∈ n.divisors) (hcl : d % 8 = 5 ∨ d % 8 = 7)
    (hq : q ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3))) :
    q ∣ d ∧ 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3) ∧ d / q < d ∧ d / q ∈ n.divisors ∧
      (d / q % 8 = 5 ∨ d / q % 8 = 7) := by
  simp only [Finset.mem_filter, Nat.mem_divisors] at hq
  obtain ⟨⟨hqd, hd0⟩, hq1, hq8⟩ := hq
  refine ⟨hqd, hq1, hq8, Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hq1, ?_, ?_⟩
  · rw [Nat.mem_divisors] at hd ⊢
    exact ⟨(Nat.div_dvd_of_dvd hqd).trans hd.1, hd.2⟩
  · rcases hcl with h | h <;> rcases hq8 with h' | h' <;>
      rw [n2_div_mod8 hqd h h' (by omega)] <;> norm_num

/-- `P(d) = Σ_e c_d(e) Z(e)` over the fixed index set `e ∣ n`, `e ≡ 5, 7`. -/
theorem n2_P_eq {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) :
    ∀ d ∈ n.divisors, (d % 8 = 5 ∨ d % 8 = 7) →
      G.P d = ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7),
        n2_c G.ε L e d • G.Z e := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd hcl
  have hdE : d ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7) :=
    Finset.mem_filter.mpr ⟨hd, hcl⟩
  rw [G.recursion d hd hcl]
  have hstep : ∀ q ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)),
      (G.ε (d / q) q * (L q : GaussianInt)) • G.P (d / q) =
        ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7),
          ((G.ε (d / q) q * (L q : GaussianInt)) * n2_c G.ε L e (d / q)) • G.Z e := by
    intro q hq
    obtain ⟨-, -, -, hlt, hdn, hcl'⟩ := n2_mem_Q hd hcl hq
    rw [ih (d / q) hlt hdn hcl', Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← mul_smul]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  conv_rhs => enter [2, e]; rw [n2_c_eq]
  simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', hdE, ite_true]

/-- `e ∣ d/q ↔ q ∣ d/e` for divisors `e, q` of `d`. -/
theorem n2_dvd_iff {d e q : ℕ} (he : e ∣ d) (hq : q ∣ d) : e ∣ d / q ↔ q ∣ d / e := by
  rw [Nat.dvd_div_iff_mul_dvd hq, Nat.dvd_div_iff_mul_dvd he, mul_comm]

/-- **The inductive identity**: `c_d(e) ≡ φ(d, e) 𝓛(d/e)` modulo `2ℤ[i]` (and `c_d(e) ≡ 0` if
`e ∤ d`). -/
theorem n2_c_mod {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) (hsq : Squarefree n) (hL1 : L 1 = 1)
    {e : ℕ} (he : e % 8 = 5 ∨ e % 8 = 7) :
    ∀ d ∈ n.divisors, (d % 8 = 5 ∨ d % 8 = 7) →
      n2_π (n2_c G.ε L e d) =
        if e ∣ d then n2_phi (d % 8) (e % 8) * ((L (d / e) : ℤ) : n2_R) else 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd hcl
  have hd0 : d ≠ 0 := by omega
  have he0 : e ≠ 0 := by omega
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  rw [n2_c_eq, map_sub, map_sum]
  have hterm : ∀ q ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)),
      n2_π ((G.ε (d / q) q * (L q : GaussianInt)) * n2_c G.ε L e (d / q)) =
        if e ∣ d / q then n2_epsR (d / q % 8) (q % 8) * ((L q : ℤ) : n2_R) *
          (n2_phi (d / q % 8) (e % 8) * ((L (d / q / e) : ℤ) : n2_R)) else 0 := by
    intro q hq
    obtain ⟨hqd, -, hq8, hlt, hdqn, hcl'⟩ := n2_mem_Q hd hcl hq
    rw [map_mul, map_mul, n2_eps G (by rw [Nat.div_mul_cancel hqd]; exact hdn) hcl' hq8,
      map_intCast, ih (d / q) hlt hdqn hcl']
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm]
  by_cases hed : e ∣ d
  swap
  · have hne : e ≠ d := by rintro rfl; exact hed dvd_rfl
    rw [ite_eq_right hed, ite_eq_right hne, map_zero, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [ite_eq_right]
    intro h
    exact hed (h.trans (Nat.div_dvd_of_dvd (n2_mem_Q hd hcl hq).1))
  rw [ite_eq_left hed]
  by_cases hee : e = d
  · subst hee
    rw [ite_eq_left rfl, map_one, Nat.div_self (Nat.pos_of_ne_zero he0), hL1, Finset.sum_eq_zero,
      sub_zero, n2_phi, ite_eq_right (by omega), Int.cast_one, one_mul]
    intro q hq
    obtain ⟨hqd, hq1, -, -, -, -⟩ := n2_mem_Q hd hcl hq
    rw [ite_eq_right]
    intro h
    have hpos : 0 < e / q := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hqd) (by omega)
    have h1 := Nat.le_of_dvd hpos h
    have h2 := Nat.div_lt_self (Nat.pos_of_ne_zero he0) hq1
    omega
  rw [ite_eq_right hee, map_zero, zero_sub, n2_neg]
  obtain ⟨m, hm⟩ : ∃ m, d / e = m := ⟨_, rfl⟩
  rw [hm]
  have hdem : e * m = d := by rw [← hm]; exact Nat.mul_div_cancel' hed
  have hm1 : 1 < m := by
    rcases (show m = 0 ∨ m = 1 ∨ 1 < m by omega) with h | h | h
    · subst h; omega
    · subst h; omega
    · exact h
  have hm0 : m ≠ 0 := by omega
  have hmd : m ∣ d := Dvd.intro_left e hdem
  have hdme : d / m = e := Nat.div_eq_of_eq_mul_left (by omega) hdem.symm
  have hm8 : m % 8 = d % 8 * (e % 8) % 8 := by
    rw [← hm]; exact n2_div_mod8 hed rfl rfl (by omega)
  have hm13 : m % 8 = 1 ∨ m % 8 = 3 := by
    rw [hm8]; rcases hcl with h | h <;> rcases he with h' | h' <;> rw [h, h'] <;> norm_num
  have hmQ : m ∈ d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3)) := by
    rw [Finset.mem_filter, Nat.mem_divisors]; exact ⟨⟨hmd, hd0⟩, hm1, hm13⟩
  have hdiv : ∀ q, q ∣ m → d / q / e = m / q := fun q _ => by
    rw [Nat.div_div_eq_div_mul, mul_comm, ← Nat.div_div_eq_div_mul, hm]
  rw [← Finset.add_sum_erase _ _ hmQ]
  have hrest : ∑ q ∈ (d.divisors.filter (fun q => 1 < q ∧ (q % 8 = 1 ∨ q % 8 = 3))).erase m,
      (if e ∣ d / q then n2_epsR (d / q % 8) (q % 8) * ((L q : ℤ) : n2_R) *
          (n2_phi (d / q % 8) (e % 8) * ((L (d / q / e) : ℤ) : n2_R)) else 0) = 0 := by
    refine Finset.sum_involution (fun q _ => if e ∣ d / q then m / q else q) ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨hqm, hqQ⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqd, hq1, hq8, -, -, hcl'⟩ := n2_mem_Q hd hcl hqQ
      by_cases h : e ∣ d / q
      · have hqm' : q ∣ m := by rw [← hm]; exact (n2_dvd_iff hed hqd).mp h
        have hq'd : m / q ∣ d := (Nat.div_dvd_of_dvd hqm').trans hmd
        have h' : e ∣ d / (m / q) := by
          rw [n2_dvd_iff hed hq'd, hm]; exact Nat.div_dvd_of_dvd hqm'
        simp only [h, h', ↓reduceIte]
        rw [hdiv q hqm', hdiv (m / q) (Nat.div_dvd_of_dvd hqm'), Nat.div_div_self hqm' hm0]
        have hq'8 : m / q % 8 = 1 ∨ m / q % 8 = 3 := by
          rcases hm13 with h1 | h1 <;> rcases hq8 with h2 | h2 <;>
            rw [n2_div_mod8 hqm' h1 h2 (by omega)] <;> norm_num
        have hk := n2_kappa hcl he hq8 hq'8 (n2_div_mod8 hqd rfl rfl (by omega))
          (n2_div_mod8 hq'd rfl rfl (by omega)) (by rw [n2_mod8_mul hqm', hm8])
        linear_combination (((L q : ℤ) : n2_R) * ((L (m / q) : ℤ) : n2_R)) * hk +
          (n2_epsR (d / (m / q) % 8) (m / q % 8) * n2_phi (d / (m / q) % 8) (e % 8) *
            ((L q : ℤ) : n2_R) * ((L (m / q) : ℤ) : n2_R)) * n2_two
      · simp only [h, ↓reduceIte, add_zero]
    · intro q hq hf
      obtain ⟨hqm, hqQ⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqd, hq1, -, -, -, -⟩ := n2_mem_Q hd hcl hqQ
      have h : e ∣ d / q := by
        by_contra h; apply hf; simp only [h, ↓reduceIte]
      have hqm' : q ∣ m := by rw [← hm]; exact (n2_dvd_iff hed hqd).mp h
      simp only [h, ↓reduceIte]
      intro heq
      have hmqq : q * q = m := by
        conv_rhs => rw [← Nat.div_mul_cancel hqm', heq]
      have hu := hsq q (by rw [hmqq]; exact hmd.trans hdn)
      rw [Nat.isUnit_iff] at hu
      omega
    · intro q hq
      obtain ⟨hqm, hqQ⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqd, hq1, hq8, -, -, -⟩ := n2_mem_Q hd hcl hqQ
      by_cases h : e ∣ d / q
      · have hqm' : q ∣ m := by rw [← hm]; exact (n2_dvd_iff hed hqd).mp h
        simp only [h, ↓reduceIte]
        refine Finset.mem_erase.mpr ⟨(Nat.div_lt_self (by omega) hq1).ne, ?_⟩
        rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨(Nat.div_dvd_of_dvd hqm').trans hmd, hd0⟩, ?_, ?_⟩
        · obtain ⟨k, hk⟩ := id hqm'
          rw [hk, Nat.mul_div_cancel_left _ (by omega : 0 < q)]
          rcases k with _ | _ | k
          · simp at hk; omega
          · simp at hk; omega
          · omega
        · rcases hm13 with h1 | h1 <;> rcases hq8 with h2 | h2 <;>
            rw [n2_div_mod8 hqm' h1 h2 (by omega)] <;> norm_num
      · simp only [h, ↓reduceIte]; exact hq
    · intro q hq
      obtain ⟨-, hqQ⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqd, -, -, -, -, -⟩ := n2_mem_Q hd hcl hqQ
      by_cases h : e ∣ d / q
      · have hqm' : q ∣ m := by rw [← hm]; exact (n2_dvd_iff hed hqd).mp h
        have hq'd : m / q ∣ d := (Nat.div_dvd_of_dvd hqm').trans hmd
        have h' : e ∣ d / (m / q) := by
          rw [n2_dvd_iff hed hq'd, hm]; exact Nat.div_dvd_of_dvd hqm'
        simp only [h, h', ↓reduceIte]
        exact Nat.div_div_self hqm' hm0
      · simp only [h, ↓reduceIte]
  rw [hrest, add_zero]
  simp only [hdme, dvd_rfl, ↓reduceIte, Nat.div_self (Nat.pos_of_ne_zero he0), hL1, Int.cast_one,
    mul_one]
  rw [hm8]
  linear_combination ((L m : ℤ) : n2_R) * n2_last hcl he

theorem lemmaN2 {L : ℕ → ℤ} {n : ℕ} (G : GenusData L n) (hn : n % 8 = 5) (hsq : Squarefree n)
    (hL1 : L 1 = 1) :
    ∃ X : G.M, G.P n =
      ∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7), L (n / e) • G.Z e + (2 : ℤ) • X := by
  have hn0 : n ≠ 0 := by omega
  have hnD : n ∈ n.divisors := Nat.mem_divisors_self n hn0
  have hP := n2_P_eq G n hnD (Or.inl hn)
  have hw : ∀ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7),
      ∃ w : GaussianInt, n2_c G.ε L e n = (L (n / e) : GaussianInt) + 2 * w := by
    intro e he
    obtain ⟨hen, he8⟩ := Finset.mem_filter.mp he
    have h := n2_c_mod G hsq hL1 he8 n hnD (Or.inl hn)
    rw [ite_eq_left (Nat.dvd_of_mem_divisors hen), n2_phi, ite_eq_right (by omega), one_mul] at h
    have h0 : n2_π (n2_c G.ε L e n - (L (n / e) : GaussianInt)) = 0 := by
      rw [map_sub, h, map_intCast, sub_self]
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
    obtain ⟨w, hw⟩ := h0
    exact ⟨w, by linear_combination hw⟩
  choose! w hw using hw
  refine ⟨∑ e ∈ n.divisors.filter (fun e => e % 8 = 5 ∨ e % 8 = 7), w e • G.Z e, ?_⟩
  rw [hP, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [hw e he, add_smul, Int.cast_smul_eq_zsmul, mul_smul, two_smul, two_smul]

end ZInQ.PropN
#print axioms ZInQ.PropN.lemmaN2

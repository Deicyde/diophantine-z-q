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


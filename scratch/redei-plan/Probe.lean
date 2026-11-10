import ZInQKernel.RouteK.Rank5b.Sec3.TYZ

/-!
# redei-plan probe: Rédei's formula in class-number form (statements only)

`docs/research/redei-plan.md`. This file is outside `ZInQKernel/` and is not imported by any library.
It checks that the target statements and the key intermediate statements of the plan typecheck
against Mathlib v4.35.0 and against `ZInQKernel.RouteK.Rank5b.Sec3`. Number-theoretic statements
are `sorry`; the plumbing from the target theorem to the hypothesis is proved.

Route (c) of the plan: genus theory in `𝓞 ℚ(√−n)` with
* (G1) ambiguous classes: `Cl[2]` is the image of `ψ : 𝔽₂^{ramified primes} → Cl`, which kills
  the vector of `(√−n)`;
* genus characters `χ_q([𝔞]) = (N𝔞 / q)` for the odd primes `q ∣ n`, which kill `2Cl`;
* Dirichlet's theorem (in Mathlib) and split primes: `χ` is onto a space of size `2^{t−1}`;
* counting: `[Cl : 2Cl] = #Cl[2] ≤ 2^{t−1} ≤ #im χ`, so `2Cl = ker χ` (principal genus theorem),
  hence `Cl[2] ∩ 2Cl = ψ(ker of the Rédei matrix)`;
* 𝔽₂ linear algebra: that kernel is the trivial one iff `redeiG = 1`.
No Hilbert symbols, no Hasse–Minkowski, no explicit ring of integers.
-/

noncomputable section

open NumberField Pointwise ZInQ.RouteK.Selmer
open scoped nonZeroDivisors

namespace ZInQ.RouteK.Rank5b.RedeiProbe

/-! ## 1. The field `ℚ(√−n)` and TYZ's `g` -/

/-- `ℚ(√−n)`, as Mathlib's quadratic algebra `ℚ[ω]/(ω² = −n)`. -/
abbrev QNeg (n : ℕ) : Type := QuadraticAlgebra ℚ (-(n : ℚ)) 0

/-- `−n` is not a square in `ℚ` for `n ≠ 0`; this makes `QNeg n` a field (Mathlib's instance). -/
instance factNeg (n : ℕ) [NeZero n] : Fact (¬ IsSquare (-(n : ℚ))) := by
  refine ⟨fun ⟨r, hr⟩ => ?_⟩
  have h0 : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  nlinarith [mul_self_nonneg r]

example (n : ℕ) [NeZero n] : Field (QNeg n) := inferInstance
example (n : ℕ) : CharZero (QNeg n) := inferInstance
example (n : ℕ) : FiniteDimensional ℚ (QNeg n) := inferInstance

instance (n : ℕ) [NeZero n] : NumberField (QNeg n) where

example (n : ℕ) [NeZero n] : IsGalois ℚ (QNeg n) := inferInstance
example (n : ℕ) [NeZero n] : Fintype (ClassGroup (𝓞 (QNeg n))) := inferInstance

/-- **TYZ's genus class number** (arXiv:1411.4728, §1): `g(n) = #(2 Cl(ℚ(√−n)))`, the order of the
subgroup of squares of the class group of the ring of integers. -/
def gCl (n : ℕ) [NeZero n] : ℕ :=
  Nat.card (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range

/-- `d_B ≠ 0`. -/
instance neZero_dProd {d : ℕ} (B : Finset d.primeFactors) : NeZero (dProd B) :=
  ⟨Finset.prod_ne_zero_iff.mpr fun p _ => (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩

/-! ## 2. The target theorem and the hypothesis in class-number form -/

/-- **Target (Rédei's formula, tyz-5b Proposition 2.3).** For odd squarefree `d` and a nonempty
set `B` of primes of `d`, the parity of `#(2 Cl(ℚ(√−d_B)))` is the bit `gBit d B` defined by
Rédei's determinant formulas. -/
theorem gCl_eq_gBit {d : ℕ} (hd : Odd d) (hsq : Squarefree d) {B : Finset d.primeFactors}
    (hB : B.Nonempty) : ((gCl (dProd B) : ℕ) : ZMod 2) = gBit d B := by
  sorry

/-- The genus sum of row 5b with TYZ's `g`: `Σ_π Π_{B∈π} #(2 Cl(ℚ(√−d_B))) mod 2`. -/
def T5bCl (d : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset d.primeFactors),
    if Admissible5bNat d P then ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0

/-- CR₃ in Tian–Yuan–Zhang's own terms, with class numbers. Its trust statement would cite only
Tian–Yuan–Zhang and Gross–Zagier–Kolyvagin. -/
def CertifiedRankTYZCl : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 → T5bCl d = 1 →
    ∀ ab ∈ Sel2 d, Loc ℚ d ab.1 ab.2

/-- The two genus sums agree, by the target theorem (blocks of a partition are nonempty). -/
theorem T5bCl_eq_T5b {d : ℕ} (hd : Odd d) (hsq : Squarefree d) : T5bCl d = T5b d := by
  unfold T5bCl T5b
  refine Finset.sum_congr rfl fun P _ => ?_
  split_ifs
  · refine Finset.prod_congr rfl fun B hB => ?_
    exact gCl_eq_gBit hd hsq (Finset.nonempty_iff_ne_empty.mpr (P.ne_bot hB))
  · rfl

theorem certifiedRankTYZ_iff : CertifiedRankTYZCl ↔ CertifiedRankTYZ := by
  have key : ∀ d : ℕ, d % 8 = 5 → Squarefree d → T5bCl d = T5b d := fun d h5 hsq =>
    T5bCl_eq_T5b (Nat.odd_iff.mpr (by omega)) hsq
  constructor
  · intro h d h5 hsq h8 hT
    exact h d h5 hsq h8 (by rw [key d h5 hsq]; exact hT)
  · intro h d h5 hsq h8 hT
    exact h d h5 hsq h8 (by rw [← key d h5 hsq]; exact hT)

/-! ## 3. Intermediate statements (route (c)) -/

section NT

variable (n : ℕ) [NeZero n]

local notation "K" => QNeg n
local notation "O" => 𝓞 (QNeg n)

/-! ### 3.1 Field facts (`Redei/Field.lean`) -/

theorem card_gal : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
  sorry

/-- `ω = √−n` is an algebraic integer. -/
theorem isIntegral_omega : IsIntegral ℤ (QuadraticAlgebra.omega : K) := by
  sorry

/-- `θ = (1 + √−n)/2` is an algebraic integer when `n ≡ 3 (mod 4)`. -/
theorem isIntegral_theta (h3 : n % 4 = 3) :
    IsIntegral ℤ ((1 + QuadraticAlgebra.omega) / 2 : K) := by
  sorry

/-- The norm of `ℚ(√−n)/ℚ` is `x σ(x)` and is `≥ 0`. -/
theorem norm_eq_mul_conj (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (x : K) :
    algebraMap ℚ K (Algebra.norm ℚ x) = x * σ x := by
  sorry

theorem norm_nonneg (x : K) : 0 ≤ Algebra.norm ℚ x := by
  sorry

/-! ### 3.2 Primes (`Redei/Primes.lean`) -/

/-- Splitting trichotomy for a prime `P` of `𝓞 K` over `p` (Galois fundamental identity
`#primesOver · e · f = 2`). -/
theorem prime_trichotomy (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) {p : ℕ} (hp : p.Prime)
    (P : Ideal O) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (σ • P ≠ P ∧ P * (σ • P) = Ideal.span {(p : O)} ∧ Ideal.absNorm P = p) ∨
    (σ • P = P ∧ P = Ideal.span {(p : O)} ∧ Ideal.absNorm P = p ^ 2) ∨
    (σ • P = P ∧ P ^ 2 = Ideal.span {(p : O)} ∧ Ideal.absNorm P = p) := by
  sorry

/-- A ramified prime divides the discriminant: `p ∣ n`, or `p = 2` and `n ≡ 1 (mod 4)`.
(For ramified `P`, `σ` acts trivially on `𝓞/P`, so `x − σx ∈ P`; take `x = ω` or `θ`.) -/
theorem dvd_of_ramified {p : ℕ} (hp : p.Prime) (P : Ideal O) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (hram : P ^ 2 = Ideal.span {(p : O)}) :
    p ∣ n ∨ (p = 2 ∧ n % 4 = 1) := by
  sorry

/-- The primes of the discriminant of `ℚ(√−n)`, `n` odd squarefree. -/
def ramSet : Finset ℕ := if n % 4 = 3 then n.primeFactors else insert 2 n.primeFactors

/-- For `p` in `ramSet n`, the unique prime of `𝓞 K` above `p`; it is ramified of norm `p`. -/
def ramIdeal (p : ℕ) : Ideal O := sorry

theorem ramIdeal_spec (hn : Odd n) (hsq : Squarefree n) {p : ℕ} (hp : p ∈ ramSet n) :
    (ramIdeal n p).IsMaximal ∧ ramIdeal n p ^ 2 = Ideal.span {(p : O)} ∧
      Ideal.absNorm (ramIdeal n p) = p := by
  sorry

theorem ramIdeal_mem (p : ℕ) : ramIdeal n p ∈ (Ideal O)⁰ := by
  sorry

/-- `(√−n) = Π_{p ∣ n} 𝔭_p`. -/
theorem span_omega (hn : Odd n) (hsq : Squarefree n) :
    Ideal.span {(⟨QuadraticAlgebra.omega, isIntegral_omega n⟩ : O)} =
      ∏ p ∈ n.primeFactors, ramIdeal n p := by
  sorry

/-- `𝔞 σ(𝔞) = (N𝔞)`. -/
theorem mul_conj_ideal (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (I : Ideal O) :
    I * (σ • I) = Ideal.span {((Ideal.absNorm I : ℕ) : O)} := by
  sorry

/-! ### 3.3 Ambiguous classes (G1) (`Redei/Ambiguous.lean`) -/

/-- The classes of the ramified primes: `ψ(e) = Π_p [𝔭_p]^{e_p}`. -/
def psi : Multiplicative (ramSet n → ZMod 2) →* ClassGroup O := sorry

theorem psi_single (p : ramSet n) :
    psi n (Multiplicative.ofAdd (Pi.single p 1)) =
      ClassGroup.mk0 ⟨ramIdeal n p, ramIdeal_mem n p⟩ := by
  sorry

/-- The vector of `(√−n)` is in the kernel of `ψ`. -/
theorem psi_ones (hn : Odd n) (hsq : Squarefree n) :
    psi n (Multiplicative.ofAdd fun p : ramSet n =>
      if (p : ℕ) ∈ n.primeFactors then (1 : ZMod 2) else 0) = 1 := by
  sorry

/-- A σ-invariant ideal has its class in the subgroup generated by the ramified primes. -/
theorem mem_range_psi_of_conj_eq (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (hn : Odd n) (hsq : Squarefree n)
    (I : (Ideal O)⁰) (hI : σ • (I : Ideal O) = I) : ClassGroup.mk0 I ∈ (psi n).range := by
  sorry

/-- **(G1)** `Cl[2] = im ψ`. -/
theorem range_psi (hn : Odd n) (hsq : Squarefree n) :
    (psi n).range = (powMonoidHom 2 : ClassGroup O →* ClassGroup O).ker := by
  sorry

/-! ### 3.4 Genus characters (`Redei/Genus.lean`) -/

/-- Every class contains an integral ideal prime to `q`. -/
theorem exists_mk0_coprime (q : ℕ) (hq : q.Prime) (c : ClassGroup O) :
    ∃ I : (Ideal O)⁰, ClassGroup.mk0 I = c ∧ ¬ q ∣ Ideal.absNorm (I : Ideal O) := by
  sorry

/-- The genus character `χ_q([𝔞]) = (N𝔞 / q)`, for a prime `q ∣ n`. -/
def chi (q : n.primeFactors) : ClassGroup O →* Multiplicative (ZMod 2) := sorry

theorem chi_mk0 (hn : Odd n) (hsq : Squarefree n) (q : n.primeFactors) (I : (Ideal O)⁰)
    (hI : ¬ (q : ℕ) ∣ Ideal.absNorm (I : Ideal O)) :
    chi n q (ClassGroup.mk0 I) =
      Multiplicative.ofAdd (legBit q ((Ideal.absNorm (I : Ideal O) : ℕ) : ℤ)) := by
  sorry

/-- The Rédei matrix: `χ_q(ψ(e)) = Σ_p R_{qp} e_p`, with `R_{qp} = (p/q)` for `p ≠ q`,
`R_{qq} = (n/q / q)`, and `R_{q2} = (2/q)`. -/
def redeiEntry (q : n.primeFactors) (p : ramSet n) : ZMod 2 :=
  if (p : ℕ) = 2 then legBit q 2
  else if (p : ℕ) = q then legBit q ((n / q : ℕ) : ℤ) else legBit q (p : ℤ)

theorem chi_psi (hn : Odd n) (hsq : Squarefree n) (q : n.primeFactors)
    (e : ramSet n → ZMod 2) :
    Multiplicative.toAdd (chi n q (psi n (Multiplicative.ofAdd e))) =
      ∑ p, redeiEntry n q p * e p := by
  sorry

/-! ### 3.5 Split primes and Dirichlet (`Redei/Dirichlet.lean`) -/

/-- A prime `p ∤ 2n` with `−n` a square mod `p` has a prime of norm `p` above it. -/
theorem exists_absNorm_eq_of_isSquare {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n)
    (hsq : IsSquare (-(n : ZMod p))) :
    ∃ P : (Ideal O)⁰, Ideal.absNorm (P : Ideal O) = p := by
  sorry

/-- **Surjectivity of the genus characters** (Dirichlet's theorem
`Nat.forall_exists_prime_gt_and_eq_mod`, CRT, Jacobi reciprocity). The image of `χ` is all of
`𝔽₂^{primes of n}` if `n ≡ 1 (mod 4)` and the sum-zero hyperplane if `n ≡ 3 (mod 4)`. -/
theorem exists_chi_eq (hn : Odd n) (hsq : Squarefree n) (ε : n.primeFactors → ZMod 2)
    (hε : n % 4 = 3 → ∑ q, ε q = 0) :
    ∃ c : ClassGroup O, ∀ q, chi n q c = Multiplicative.ofAdd (ε q) := by
  sorry

/-! ### 3.6 Counting and the 4-rank (`Redei/FourRank.lean`) -/

/-- Pure group theory: for a finite commutative group, `#G²` is odd iff `G[2] ∩ G² = 1`. -/
theorem odd_card_range_sq_iff {G : Type*} [CommGroup G] [Finite G] :
    Odd (Nat.card (powMonoidHom 2 : G →* G).range) ↔
      (powMonoidHom 2 : G →* G).ker ⊓ (powMonoidHom 2 : G →* G).range = ⊥ := by
  sorry

/-- **Principal genus theorem**: `2Cl = ker χ`. -/
theorem range_sq_eq_ker_chi (hn : Odd n) (hsq : Squarefree n) :
    (powMonoidHom 2 : ClassGroup O →* ClassGroup O).range = ⨅ q, (chi n q).ker := by
  sorry

/-- **Rédei's theorem** (4-rank 0 form): `g(n)` is odd iff the kernel of the Rédei matrix is
spanned by the vector of `(√−n)`. -/
theorem odd_gCl_iff (hn : Odd n) (hsq : Squarefree n) :
    Odd (gCl n) ↔ ∀ e : ramSet n → ZMod 2, (∀ q, ∑ p, redeiEntry n q p * e p = 0) →
      e = 0 ∨ e = fun p : ramSet n => if (p : ℕ) ∈ n.primeFactors then (1 : ZMod 2) else 0 := by
  sorry

end NT

/-! ### 3.7 𝔽₂ linear algebra (`Redei/Kernel.lean`, generic `Sec3` setting) -/

section Lin

open Sec3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The kernel of `(L_B | z_B)` (with the column `z_B` only when `y(B) = 0`) is the trivial one
iff `redeiG = 1` (tyz-5b §2.2, Cases 1 and 2; uses Lemma 2.2(1), (2)). -/
theorem kernel_trivial_iff_redeiG {a : ι → ι → ZMod 2} {y z : ι → ZMod 2} (hrec : Recip a y)
    {B : Finset ι} (hB : B.Nonempty) :
    (∀ (e : ι → ZMod 2) (e₂ : ZMod 2), (∀ i ∉ B, e i = 0) → (∑ i ∈ B, y i = 1 → e₂ = 0) →
        (∀ q ∈ B, ∑ p ∈ B, lapl a B q p * e p + e₂ * z q = 0) →
        e₂ = 0 ∧ ((∀ i ∈ B, e i = 0) ∨ (∀ i ∈ B, e i = 1))) ↔
      redeiG a y z B = 1 := by
  sorry

end Lin

end ZInQ.RouteK.Rank5b.RedeiProbe

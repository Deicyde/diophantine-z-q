import ZInQKernel.RouteK.Rank5b.Sec3.TYZ

/-!
# CR₃ in Tian–Yuan–Zhang's own terms (class numbers), and Rédei's formula as a Prop

`docs/research/redei-plan.md` ("cheap step worth taking now"); the statements are those of the
probe `scratch/redei-plan/Probe.lean`.

* `QNeg n`: the field `ℚ(√−n)`, as Mathlib's `QuadraticAlgebra ℚ (−n) 0`;
* `gCl n = #(2 Cl(ℚ(√−n)))`: TYZ's genus class number `g(n)`, the order of the subgroup of squares
  of the class group of the ring of integers;
* `T5bCl d`: the genus sum `T5b d` with `gCl (dProd B)` in place of the bit `gBit d B`;
* `CertifiedRankTYZCl`: the hypothesis `CertifiedRankTYZ` with `T5bCl d = 1` in place of
  `T5b d = 1`;
* `RedeiFormula`: Rédei's formula (tyz-5b Proposition 2.3) for exactly the blocks read by the
  genus sum: `gCl (dProd B) ≡ gBit d B (mod 2)` for odd squarefree `d` and nonempty `B` with
  `d_B ≡ 7, 3` or `1 (mod 8)`;
* `T5bCl_eq_T5b` and `certifiedRankTYZ_iff_of_redeiFormula :
  RedeiFormula → (CertifiedRankTYZCl ↔ CertifiedRankTYZ)`.

`RedeiFormula` is proved in `RouteK/Redei/FourRank.lean` (`ZInQ.RouteK.Redei.redeiFormula`).
-/

noncomputable section

open NumberField

namespace ZInQ.RouteK.Rank5b

open Selmer

/-- `ℚ(√−n)`, as Mathlib's quadratic algebra `ℚ[ω]/(ω² = −n)`. -/
abbrev QNeg (n : ℕ) : Type := QuadraticAlgebra ℚ (-(n : ℚ)) 0

/-- `−n` is not a square in `ℚ` for `n ≠ 0`; this makes `QNeg n` a field (Mathlib's instance). -/
instance QNeg.factNotIsSquare (n : ℕ) [NeZero n] : Fact (¬ IsSquare (-(n : ℚ))) := by
  refine ⟨fun ⟨r, hr⟩ => ?_⟩
  have h0 : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  nlinarith [mul_self_nonneg r]

instance QNeg.numberField (n : ℕ) [NeZero n] : NumberField (QNeg n) where

/-- `d_B ≠ 0`. -/
instance neZero_dProd {d : ℕ} (B : Finset d.primeFactors) : NeZero (dProd B) :=
  ⟨Finset.prod_ne_zero_iff.mpr fun p _ => (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩

/-- **TYZ's genus class number** (Tian–Yuan–Zhang, arXiv:1411.4728, §1): `g(n) = #(2 Cl(ℚ(√−n)))`,
the order of the subgroup of squares of the class group of the ring of integers of `ℚ(√−n)`. -/
def gCl (n : ℕ) [NeZero n] : ℕ :=
  Nat.card (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* ClassGroup (𝓞 (QNeg n))).range

/-- **The genus sum of row 5b with TYZ's `g`**: `T_5b(d) = Σ_π Π_{B∈π} #(2 Cl(ℚ(√−d_B))) mod 2`,
over the same set partitions as `T5b` (one block with `d_B ≡ 7`, one with `d_B ≡ 3`, all others
`≡ 1 (mod 8)`). -/
def T5bCl (d : ℕ) : ZMod 2 :=
  ∑ P : Finpartition (Finset.univ : Finset d.primeFactors),
    if Admissible5bNat d P then ∏ B ∈ P.parts, ((gCl (dProd B) : ℕ) : ZMod 2) else 0

/-- **Rédei's formula** (L. Rédei, *Arithmetischer Beweis des Satzes über die Anzahl der durch vier
teilbaren Invarianten der absoluten Klassengruppe im quadratischen Zahlkörper*, J. Reine Angew.
Math. 171 (1934), 55–60; tyz-5b Proposition 2.3), for the blocks read by the genus sum: for odd
squarefree `d` and a nonempty set `B` of primes of `d` with `d_B ≡ 7, 3` or `1 (mod 8)`, the parity
of `#(2 Cl(ℚ(√−d_B)))` is the bit `gBit d B` given by Rédei's determinant formulas
(`Sec3.redeiG`).

The scope is exactly that of `T5b`: the blocks of a set partition are nonempty, and the partitions
counted by `Admissible5bNat` have only blocks with `d_B ≡ 7, 3, 1 (mod 8)`; blocks with
`d_B ≡ 5 (mod 8)` never occur.

It is stated here as a Prop so that the modules downstream do not depend on its proof. It is
proved as `ZInQ.RouteK.Redei.redeiFormula` (`RouteK/Redei/FourRank.lean`), following
`docs/research/redei-plan.md`, route (c): ambiguous classes, genus characters, Dirichlet's theorem
and 𝔽₂ linear algebra. -/
def RedeiFormula : Prop :=
  ∀ d : ℕ, Odd d → Squarefree d → ∀ B : Finset d.primeFactors, B.Nonempty →
    (dProd B % 8 = 7 ∨ dProd B % 8 = 3 ∨ dProd B % 8 = 1) →
      ((gCl (dProd B) : ℕ) : ZMod 2) = gBit d B

/-- **CR₃ in Tian–Yuan–Zhang's own terms** (class numbers): for squarefree `d ≡ 5 (mod 8)` with
`#Sel₂(C_d) = 8` and odd genus sum `T5bCl d = Σ_π Π_{B∈π} #(2 Cl(ℚ(√−d_B)))`, every 2-Selmer class
of `C_d` comes from a rational point (`Loc`).

Trust statement (no Rédei needed: `g` is TYZ's own class number):
* **Tian–Yuan–Zhang** (Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent
  number problem*, Asian J. Math. 21 (2017), no. 4, 721–774; arXiv:1411.4728), Theorem 3.5 and the
  argument of the proof of Theorem 3.5(2) (§3.3), as completed in `docs/research/nt-tyz.md` §4,
  Proposition N: for squarefree `n ≡ 5 (mod 8)`, if the genus sum
  `Σ_{d₀ ≡ 7, d₁ ≡ 3 (8)} g(d₀) g(d₁) 𝓛₁(n/d₀d₁)` (= `T5bCl n` mod 2) is odd, then `𝓛(n) ≠ 0` and
  `ord_{s=1} L(C_n, s) = 1`.
* **Gross–Zagier** with an auxiliary imaginary quadratic field satisfying the Heegner hypothesis
  and with `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein;
  `docs/research/pc-audit.md` RK7): analytic rank one gives `rank C_d(ℚ) ≥ 1`; with
  `dim Sel₂(C_d) = 3` every Selmer class is then the image of a rational point
  (`docs/research/pc-audit.md` RK9; `Selmer.loc_iff_kummer`).

It is equivalent to `CertifiedRankTYZ`: `certifiedRankTYZ_iff_of_redeiFormula` with Rédei's
formula, which is proved (`RouteK.Redei.redeiFormula`); unconditionally,
`RouteK.Redei.certifiedRankTYZ_iff'`. -/
def CertifiedRankTYZCl : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 → T5bCl d = 1 →
    ∀ ab ∈ Sel2 d, Loc ℚ d ab.1 ab.2

/-- The two genus sums agree under Rédei's formula (blocks of a partition are nonempty, and the
admissible partitions have blocks of classes `7, 3, 1 (mod 8)` only). -/
theorem T5bCl_eq_T5b (hR : RedeiFormula) {d : ℕ} (hd : Odd d) (hsq : Squarefree d) :
    T5bCl d = T5b d := by
  unfold T5bCl T5b
  refine Finset.sum_congr rfl fun P _ => ?_
  split_ifs with hP
  · refine Finset.prod_congr rfl fun B hB => ?_
    exact hR d hd hsq B (Finset.nonempty_iff_ne_empty.mpr (P.ne_bot hB)) (hP.2.2 B hB)
  · rfl

/-- Under Rédei's formula, CR₃ in class-number form is CR₃^TYZ. -/
theorem certifiedRankTYZ_iff_of_redeiFormula (hR : RedeiFormula) :
    CertifiedRankTYZCl ↔ CertifiedRankTYZ := by
  have key : ∀ d : ℕ, d % 8 = 5 → Squarefree d → T5bCl d = T5b d := fun d h5 hsq =>
    T5bCl_eq_T5b hR (Nat.odd_iff.mpr (by omega)) hsq
  constructor
  · intro h d h5 hsq h8 hT
    exact h d h5 hsq h8 (by rw [key d h5 hsq]; exact hT)
  · intro h d h5 hsq h8 hT
    exact h d h5 hsq h8 (by rw [← key d h5 hsq]; exact hT)

end ZInQ.RouteK.Rank5b

import ZInQKernel.Contrib.G9.Reduction
import ZInQKernel.Contrib.G9.G9Weights

/-!
# R10 amended: the de Rham comparison for abelian varieties with the full Hodge–Tate weights

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task r10-amend, 2026-11-13).

R10's Lean form (`PkgI4.DeRhamComparison`, Leaves.lean `PkgI4Sec`; restated verbatim in
`ZInQKernel/Contrib/G9/I4Layer.lean`) gives the Hodge–Tate multiplicities `g` at the weights `0`
and `−1` of `V_p(A)` for an abelian variety `A` of dimension `g` over a finite `F/ℚ_p`. It does
not say that every other weight has multiplicity `0`. That vanishing is part of the published
theorem (the Hodge–Tate decomposition
`ℂ_p ⊗_{ℚ_p} H¹_et(A_F̄, ℚ_p) ≅ (ℂ_p ⊗_F H¹(A, 𝒪_A)) ⊕ (ℂ_p(−1) ⊗_F H⁰(A, Ω¹_A))`, Faltings,
JAMS 1 (1988), Ch. III Thm 4.1 as cited by the manuscript; Fontaine, Invent. Math. 65 (1982) for
abelian varieties; Tate 1967 §4 for good reduction; together with Tate's
`ℂ_p(j)^{G_F} = 0` for `j ≠ 0`, Tate 1967 §3.3; locators UNVERIFIED, no source on this host; see
`docs/research/r10-amend.md` §2).

`DeRhamComparisonHT` is R10 plus that clause. The clause has no dimension hypothesis: it holds for
every abelian variety. It is exactly g9-derham's bridge `G9Bridge.R10Weights`, so

`deRhamComparisonHT_iff : DeRhamComparisonHT ↔ PkgI4.DeRhamComparison ∧ G9Bridge.R10Weights`.

Sign convention (checked against the definitions): `htMultOver p ρ w` is
`dim_F Hom_{G_F}(V, ℂ_p(−w))`, i.e. `dim_F (ℂ_p(−w) ⊗ V^∨)^{G_F}`, and `ℚ_p(1)` has weight `−1`.
For `V = V_p(A)`, `V^∨ = H¹_et`, so `ℂ_p(i) ⊗ V^∨ ≅ ℂ_p(i)^g ⊕ ℂ_p(i−1)^g`, whose `G_F`-invariants
have `F`-dimension `g·[i = 0] + g·[i = 1]`: multiplicity `g` at `w = 0` and `w = −1`, and `0` at
every other `w`.
-/

namespace ZInQ.Contrib.R10

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4

/-- **R10, amended (I4-L0 with the full weight multiset).** For an abelian variety `A` over a
finite extension `F` of `ℚ_p`: if `dim A = g`, then `V_p(A)` is de Rham as a `G_F`-representation,
with Hodge–Tate weights `0` and `−1` each of multiplicity `g` (this is the old R10,
`PkgI4.DeRhamComparison`); and every weight other than `0` and `−1` has multiplicity `0`.
Faltings 1988 Ch. III Thm 4.1 / Fontaine 1982 (Hodge–Tate decomposition) with Tate 1967 §3.3
(`ℂ_p(j)^{G_F} = 0`, `j ≠ 0`); de Rham part as in R10 (Scholze 2013 Cor. 1.8 with Thms 9.1, 9.3;
Faltings 1989; Tsuji 1999); locators UNVERIFIED. -/
def DeRhamComparisonHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F),
    (∀ g : ℕ, A.dim = (g : WithBot ℕ∞) →
      IsDeRhamOver p (A.galRep p) ∧ htMultOver p (A.galRep p) 0 = g ∧
        htMultOver p (A.galRep p) (-1) = g) ∧
    ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p (A.galRep p) w = 0

/-- The amended R10 implies the old R10. -/
theorem deRhamComparison_of_HT (h : DeRhamComparisonHT) : PkgI4.DeRhamComparison :=
  fun p _ F _ _ _ A g hg => (h p F A).1 g hg

/-- The amended R10 implies g9-derham's bridge `R10Weights` (finding F1 of g9-derham). -/
theorem r10Weights_of_HT (h : DeRhamComparisonHT) : G9Bridge.R10Weights :=
  fun p _ F _ _ _ A w hw0 hw1 => (h p F A).2 w hw0 hw1

/-- The amended R10 implies g9-derham run 3c's weight clause `DeRhamComparisonWeights`
(`R10Weights` with a dimension hypothesis). -/
theorem deRhamComparisonWeights_of_HT (h : DeRhamComparisonHT) : DeRhamComparisonWeights :=
  fun p _ F _ _ _ A _ _ w hw0 hw1 => (h p F A).2 w hw0 hw1

/-- The amendment adds exactly the clause `R10Weights` to R10, and nothing else. -/
theorem deRhamComparisonHT_iff :
    DeRhamComparisonHT ↔ PkgI4.DeRhamComparison ∧ G9Bridge.R10Weights :=
  ⟨fun h => ⟨deRhamComparison_of_HT h, r10Weights_of_HT h⟩,
    fun ⟨h1, h2⟩ p _ F _ _ _ A =>
      ⟨fun g hg => h1 p F A g hg, fun w hw0 hw1 => h2 p F A w hw0 hw1⟩⟩

/-- Equivalent multiplicity form: if `dim A = g`, then `htMultOver w = g · #{w ∈ {0, −1}}` for
every `w`. -/
theorem htMultOver_eq_of_HT (h : DeRhamComparisonHT) (p : ℕ) [Fact p.Prime] (F : Type) [Field F]
    [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : PkgI4.I3.AbVar F) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞)) (w : ℤ) :
    htMultOver p (A.galRep p) w = g * ({0, -1} : Multiset ℤ).count w := by
  obtain ⟨h1, h2⟩ := h p F A
  obtain ⟨_, h0, hm1⟩ := h1 g hg
  by_cases hw0 : w = 0
  · subst hw0; rw [h0]; simp
  by_cases hw1 : w = -1
  · subst hw1; rw [hm1]; simp
  rw [h2 w hw0 hw1]
  simp [hw0, hw1]

end ZInQ.Contrib.R10

#print axioms ZInQ.Contrib.R10.deRhamComparison_of_HT
#print axioms ZInQ.Contrib.R10.r10Weights_of_HT
#print axioms ZInQ.Contrib.R10.deRhamComparisonWeights_of_HT
#print axioms ZInQ.Contrib.R10.deRhamComparisonHT_iff
#print axioms ZInQ.Contrib.R10.htMultOver_eq_of_HT

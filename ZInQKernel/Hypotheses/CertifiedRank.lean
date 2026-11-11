import ZInQKernel.RouteK.Assembly.Realize

/-!
# Hypothesis CR₃: certified rank for congruent number curves

The deep input of Route K (`docs/research/slot-k.md` §4.1), stated through the explicit Selmer
system `Σ(𝒞_d)` of `ZInQKernel/RouteK/System/` and the configuration `𝒞_d` of an odd number `d`
(`ZInQ.RouteK.natConfig`), so that no Selmer group, Galois cohomology or L-function enters Lean.
Together with the descent lemma (`ZInQ.RouteK.descent_lemma`, proved) it gives pole completeness
(`ZInQ.poleCompleteness_of_certifiedRank`).
-/

namespace ZInQ

/-- **Hypothesis CR₃** (certified rank). Let `d > 0` be squarefree with `d ≡ 5 (mod 8)`, and let
`a` be a squarefree (signed) divisor of `d` with `|a| ≡ 7 (mod 8)`. If the system `Σ(𝒞_d)` of the
configuration of `d` has exactly 8 solutions (dimension 3) and one of them has first coordinate the
class of `a` (`a₀ = [a < 0]`, `a₁ = 0`, `u_p = [p ∣ a]`), then the congruent number curve
`C_d : y² = x³ − d²x` has a rational point `(x, y)` with `x ≠ 0` and `x ∈ a ℚ*²`.

**Trust statement.** CR₃ is not proved in Lean. It is the only input of the Route K proof of pole
completeness that Lean does not prove, and it follows from published (or preprint) theorems:

* *Proposition 0* (`docs/research/descent-alt.md` §4.1; the place-2 rows for `d ≡ 5 (mod 8)` are
  rechecked in slot-k §2.1): `Σ(𝒞_d)` is the 2-Selmer group `Sel₂(C_d)` written in coordinates, a
  solution standing for the pair of Kummer classes `((−1)^{a₀}2^{a₁}Π p^{u_p}, (−1)^{b₀}2^{b₁}Π p^{v_p})`.
  So the hypotheses say `dim Sel₂(C_d) = 3` and `a ∈ π₁(Sel₂(C_d))`.
* *Rank one*, by either of two routes:
  - Kriz's 2-converse theorem (arXiv:2002.04767, Theorem 10.13; `E = C_d`, CM by `ℤ[i]`, `p = 2`;
    Kriz's standing assumption `f₀ ≥ 4` holds since `d ≥ 21` here) together with the corank lemma
    (manuscript line 1072; Cassels–Tate: the pairing on `Ш/Ш_div` is nondegenerate and alternating,
    so `dim (Ш/Ш_div)[2]` is even, with no finiteness of `Ш` assumed)
    gives `rank C_d(ℚ) = 1` and `Ш(C_d)[2] = 0`;
  - or, for exactly the 2-adic shape `d ≡ 5`, `|a| ≡ 7 (mod 8)` assumed here, Tian–Yuan–Zhang
    (Asian J. Math. 21 (2017): Theorem 3.5 and the argument of the proof of Theorem 3.5(2), §3.3,
    as completed in `docs/research/nt-tyz.md` §4, Proposition N) shows `L(C_d, 1) = 0` with
    `L'(C_d, 1) ≠ 0`, and Gross–Zagier–Kolyvagin gives rank one (`docs/research/tyz-5b.md`).
    Tian–Yuan–Zhang's hypothesis is reached through Proposition 0 (`docs/research/descent-alt.md`;
    `RouteK.Selmer.prop0Statement`), Corollary 4.4 and Theorem 3.6 of `docs/research/tyz-5b.md`
    (`RouteK.Rank5b.det_M5b_eq_one`, `RouteK.Rank5b.det_M5b_eq_T5b`) and Rédei's formula
    (`RouteK.Redei.redeiFormula`), all proved in Lean.
* Either way `C_d(ℚ)/2C_d(ℚ) = Sel₂(C_d)` (pc-audit RK9), so the class `a` comes from a rational
  point. That point is not torsion: the torsion classes are `1, −1, d, −d`, and `|a| ≢ 1, d`
  (`|a| ≡ 7`, `d ≡ 5 (mod 8)`). For a non-torsion point the first Kummer coordinate is the class of
  `x ≠ 0`, so `x ∈ a ℚ*²`, i.e. `x / a` is a square.

The restrictions `d ≡ 5`, `|a| ≡ 7 (mod 8)` are exactly what the slot construction produces
(slot-k §2.6, the K-TYZ-β rule), so CR₃ is as narrow as the proof allows short of naming the slot
configurations themselves; `RouteK.Rank.CertifiedRankDLRk` (`RouteK/RankDL.lean`) names them. -/
def CertifiedRank : Prop :=
  ∀ (d : ℕ) (a : ℤ) (hd : d % 8 = 5), Squarefree d → Squarefree a → a ∣ (d : ℤ) →
    a.natAbs % 8 = 7 →
    (RouteK.natConfig d (RouteK.odd_of_mod_eight_eq_five hd)).sols.card = 8 →
    (∃ σ ∈ (RouteK.natConfig d (RouteK.odd_of_mod_eight_eq_five hd)).sols,
      σ.first = RouteK.natClass d a) →
    ∃ x y : ℚ, y ^ 2 = x ^ 3 - (d : ℚ) ^ 2 * x ∧ x ≠ 0 ∧ IsSquare (x / a)

end ZInQ

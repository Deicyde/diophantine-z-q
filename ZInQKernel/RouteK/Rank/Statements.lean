import ZInQKernel.RouteK.Rank.RK9
import ZInQKernel.RouteK.Rank5b.Sec3.RedeiStatement
import ZInQKernel.RouteK.Selmer.Prop0

/-!
# CR₃ as "`C_d(ℚ)` has a point of infinite order"

With RK9 proved (`loc_of_mem_sel2_of_infinite_order`), the hypotheses CR₃^Sel, CR₃^TYZ and
CR₃^TYZ_Cl (`Selmer.CertifiedRankSel`, `Rank5b.CertifiedRankTYZ`, `Rank5b.CertifiedRankTYZCl`), whose
conclusion is "every 2-Selmer class of `C_d` comes from a rational point", follow from forms whose
conclusion is only that `C_d(ℚ)` has a point of infinite order (equivalently, `d` is a congruent
number), which each route in their trust statements provides. Mordell–Weil for `C_d` over `ℚ`
enters as the explicit hypothesis `hfg`; `fg_points` (`RouteK/RankMW.lean`) proves it, and
`RouteK/RankVariants.lean` states the derivations and the main theorem without it.
-/

namespace ZInQ.RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.RouteK.Selmer ZInQ.RouteK.Rank5b

/-- **Hypothesis CR₃^Rk** (CR₃^Sel with the conclusion "positive rank"). Let `d > 0` be squarefree
with `d ≡ 5 (mod 8)`. If `Sel₂(C_d)` (`Sel2 d`) has exactly 8 elements and contains a pair `(a, b)`
with `|a| ≡ 7 (mod 8)`, then `C_d : y² = x³ − d²x` (`shortCurve (−d²)` over `ℚ`) has a rational
point of infinite order.

**Trust statement.** Not proved in Lean. Lean derives it from `CertifiedRankTYZClRk`
(`Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk`, `certifiedRankRk_of_certifiedRankTYZRk`):
the premises give `T5b d = 1` by Corollary 4.4 and Theorem 3.6 of `docs/research/tyz-5b.md`
(`det_M5b_eq_one`, `det_M5b_eq_T5b`), and Rédei's formula (`RouteK.Redei.redeiFormula`) makes
that `T5bCl d = 1`. So it rests on Tian–Yuan–Zhang as completed by Proposition N
(`docs/research/nt-tyz.md` §4; model reviews `docs/research/rv-nt-tyz.md`,
`docs/research/rv-prop-n.md`) and on Gross–Zagier with an auxiliary field, exactly as
`CertifiedRankTYZClRk` (see there and `docs/research/cr3-trust.md`). Kriz's 2-converse
(arXiv:2002.04767, Theorem 10.13, a preprint) with the corank lemma is an alternative, not needed.
The step to "every Selmer class comes from a rational point" (pc-audit RK9) is proved in Lean
(`loc_of_mem_sel2_of_infinite_order`, with `fg_points`). -/
def CertifiedRankRk : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 → (∃ ab ∈ Sel2 d, ab.1.natAbs % 8 = 7) →
    ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P

/-- **Hypothesis CR₃^TYZ,Rk** (CR₃^TYZ with the conclusion "positive rank"). For squarefree
`d ≡ 5 (mod 8)` with odd genus sum `T5b d` (`Rank5b.T5b`, Rédei bits), `C_d(ℚ)` has a point of
infinite order.

**Trust statement.** Not proved in Lean. It is provided by Tian–Yuan–Zhang (Theorem 3.5 and the
argument of the proof of Theorem 3.5(2), §3.3, completed in `docs/research/nt-tyz.md` §4,
Proposition N: `ord_{s=1} L(C_d, s) = 1`) and Gross–Zagier with an auxiliary imaginary quadratic
field (`docs/research/pc-audit.md` RK7: analytic rank one gives `rank C_d(ℚ) ≥ 1`); see
`CertifiedRankTYZClRk` and `Rank5b.CertifiedRankTYZ` for the precise citations.
Rédei's formula, which identifies `T5b d` with the genus sum of class numbers in Tian–Yuan–Zhang's
hypothesis, is proved in Lean (`RouteK.Redei.redeiFormula`; see `CertifiedRankTYZClRk`).
Neither `#Sel₂(C_d) = 8` nor RK9 is part of this statement: RK9 is proved in Lean
(`loc_of_mem_sel2_of_infinite_order`). -/
def CertifiedRankTYZRk : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → T5b d = 1 →
    ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P

/-- **Hypothesis CR₃^TYZ_Cl,Rk** (CR₃^TYZ_Cl with the conclusion "positive rank"). For squarefree
`d ≡ 5 (mod 8)` with odd genus sum of class numbers `T5bCl d = Σ_π Π_{B∈π} #(2 Cl(ℚ(√−d_B)))`,
`C_d(ℚ)` has a point of infinite order.

**Trust statement.** Not proved in Lean. It is Tian–Yuan–Zhang (Asian J. Math. 21 (2017),
721–774, read as arXiv:1411.4728v1): Theorem 3.5 (first assertion) with Theorem 3.3,
Proposition 3.2, Lemmas 2.8, 3.16, 3.18, 3.21 and Proposition 2.3, as completed by Proposition N
(`docs/research/nt-tyz.md` §4, model reviews `docs/research/rv-nt-tyz.md` and
`docs/research/rv-prop-n.md`; not refereed): if `T5bCl d` is odd, TYZ's `𝓛(d) ≠ 0`, and with the
root number `−1` (Birch–Stephens) `ord_{s=1} L(C_d, s) = 1`. Then Gross–Zagier (Invent. Math. 84
(1986)), with an auxiliary imaginary quadratic field (Bump–Friedberg–Hoffstein), gives a point of
infinite order. `T5bCl d` is TYZ's `(7, 3)` genus sum with `g(d_B) = #2Cl(ℚ(√−d_B))`, so no Rédei
formula is needed; TYZ's Theorem 1.2 is not cited (false as printed). Lean derives every other
form of CR₃ from it (the forms with the premise `#Sel₂ = 8` through RK9 and Mordell–Weil,
`certifiedRankTYZ_of_certifiedRankTYZRk'`, `certifiedRankTYZCl_of_certifiedRankTYZClRk'`).
Step-by-step outline: `docs/research/cr3-trust.md`. -/
def CertifiedRankTYZClRk : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → T5bCl d = 1 →
    ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P

theorem ne_zero_of_mod_eight_eq_five {d : ℕ} (h : d % 8 = 5) : d ≠ 0 := by omega

/-- **CR₃^Rk from CR₃^TYZ,Rk.** The premises of CR₃^Rk give `T5b d = 1` by Corollary 4.4
(`det_M5b_eq_one`) and Theorem 3.6 (`det_M5b_eq_T5b`), so CR₃^Rk is the weaker hypothesis. -/
theorem certifiedRankRk_of_certifiedRankTYZRk (h : CertifiedRankTYZRk) : CertifiedRankRk :=
  fun d hd5 hsq h8 ⟨_, hab, h7⟩ =>
    h d hd5 hsq ((det_M5b_eq_T5b hd5 hsq).symm.trans (det_M5b_eq_one hd5 hsq h8 hab h7))

/-- **CR₃^Sel from CR₃^Rk** and Mordell–Weil for `C_d(ℚ)`, by RK9. -/
theorem certifiedRankSel_of_certifiedRankRk
    (hfg : ∀ d : ℕ, d ≠ 0 → AddGroup.FG (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point)
    (h : CertifiedRankRk) : CertifiedRankSel := fun d hd5 hsq h8 h7 =>
  loc_of_mem_sel2_of_infinite_order (ne_zero_of_mod_eight_eq_five hd5)
    (hfg d (ne_zero_of_mod_eight_eq_five hd5)) (h d hd5 hsq h8 h7) h8

/-- **CR₃^TYZ from CR₃^TYZ,Rk** and Mordell–Weil for `C_d(ℚ)`, by RK9. -/
theorem certifiedRankTYZ_of_certifiedRankTYZRk
    (hfg : ∀ d : ℕ, d ≠ 0 → AddGroup.FG (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point)
    (h : CertifiedRankTYZRk) : CertifiedRankTYZ := fun d hd5 hsq h8 hT =>
  loc_of_mem_sel2_of_infinite_order (ne_zero_of_mod_eight_eq_five hd5)
    (hfg d (ne_zero_of_mod_eight_eq_five hd5)) (h d hd5 hsq hT) h8

/-- **CR₃^TYZ_Cl from CR₃^TYZ_Cl,Rk** and Mordell–Weil for `C_d(ℚ)`, by RK9. -/
theorem certifiedRankTYZCl_of_certifiedRankTYZClRk
    (hfg : ∀ d : ℕ, d ≠ 0 → AddGroup.FG (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point)
    (h : CertifiedRankTYZClRk) : CertifiedRankTYZCl := fun d hd5 hsq h8 hT =>
  loc_of_mem_sel2_of_infinite_order (ne_zero_of_mod_eight_eq_five hd5)
    (hfg d (ne_zero_of_mod_eight_eq_five hd5)) (h d hd5 hsq hT) h8

/-- **`ZInQ.CertifiedRank` from CR₃^Rk** and Mordell–Weil for `C_d(ℚ)` (RK9 and Proposition 0). -/
theorem certifiedRank_of_certifiedRankRk
    (hfg : ∀ d : ℕ, d ≠ 0 → AddGroup.FG (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point)
    (h : CertifiedRankRk) : CertifiedRank :=
  Selmer.certifiedRank_of_certifiedRankSel (certifiedRankSel_of_certifiedRankRk hfg h)

end ZInQ.RouteK.Rank

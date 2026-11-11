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

**Trust statement.** CR₃^Rk is not proved in Lean. It says `rank C_d(ℚ) ≥ 1`, which is provided
by either of:

* Kriz's 2-converse theorem (arXiv:2002.04767, Theorem 10.13; `E = C_d`, CM by `ℤ[i]`, `p = 2`;
  its standing assumption `f₀ ≥ 4` holds since `d ≥ 21`, see `Selmer.CertifiedRankSel`) together
  with the corank lemma (Cassels–Tate on `Ш/Ш_div`), giving `rank C_d(ℚ) = 1`;
* or, for the 2-adic shape `d ≡ 5`, `|a| ≡ 7 (mod 8)`, Tian–Yuan–Zhang (Asian J. Math. 21 (2017):
  Theorem 3.5 and the argument of the proof of Theorem 3.5(2), §3.3, as completed in
  `docs/research/nt-tyz.md` §4, Proposition N), which gives `ord_{s=1} L(C_d, s) = 1`, and
  Gross–Zagier (`docs/research/pc-audit.md` RK7), which gives `rank C_d(ℚ) ≥ 1`. Tian–Yuan–Zhang's
  hypothesis is reached through Corollary 4.4 and Theorem 3.6 of `docs/research/tyz-5b.md`
  (`certifiedRankRk_of_certifiedRankTYZRk`) and Rédei's formula (`RouteK.Redei.redeiFormula`), all
  proved in Lean.

The step from positive rank to "every Selmer class comes from a rational point"
(`docs/research/pc-audit.md` RK9) is proved in Lean (`loc_of_mem_sel2_of_infinite_order`), from
Mordell–Weil for `C_d(ℚ)` (hypothesis `hfg` of `certifiedRankSel_of_certifiedRankRk`). -/
def CertifiedRankRk : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 → (∃ ab ∈ Sel2 d, ab.1.natAbs % 8 = 7) →
    ∃ P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point, ¬IsOfFinAddOrder P

/-- **Hypothesis CR₃^TYZ,Rk** (CR₃^TYZ with the conclusion "positive rank"). For squarefree
`d ≡ 5 (mod 8)` with odd genus sum `T5b d` (`Rank5b.T5b`, Rédei bits), `C_d(ℚ)` has a point of
infinite order.

**Trust statement.** Not proved in Lean. It is provided by Tian–Yuan–Zhang (Theorem 3.5 and the
argument of the proof of Theorem 3.5(2), §3.3, completed in `docs/research/nt-tyz.md` §4,
Proposition N: `ord_{s=1} L(C_d, s) = 1`) and Gross–Zagier (`docs/research/pc-audit.md` RK7:
analytic rank one gives `rank C_d(ℚ) ≥ 1`); see `Rank5b.CertifiedRankTYZ` for the precise citations.
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

**Trust statement.** Not proved in Lean. It is Tian–Yuan–Zhang (arXiv:1411.4728, Theorem 3.5 and
the argument of the proof of Theorem 3.5(2), §3.3, completed in `docs/research/nt-tyz.md` §4,
Proposition N: `ord_{s=1} L(C_d, s) = 1`) followed by Gross–Zagier (`docs/research/pc-audit.md`
RK7: `rank C_d(ℚ) ≥ 1`); see `Rank5b.CertifiedRankTYZCl`. No Rédei formula is needed, and RK9 is
proved in Lean (`loc_of_mem_sel2_of_infinite_order`). -/
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

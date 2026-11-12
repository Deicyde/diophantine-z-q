import ZInQKernel.RouteK.Rank
import ZInQKernel.RouteK.RankMW
import ZInQKernel.RouteK.Rank5bSec3

/-!
# CR₃ in positive-rank form, with Mordell–Weil proved

`RouteK/Rank/Statements.lean` derives CR₃^Sel, CR₃^TYZ and CR₃^TYZ_Cl from forms whose conclusion
is "`C_d(ℚ)` has a point of infinite order", assuming Mordell–Weil for `C_d(ℚ)`. That assumption is
`fg_points` (`RouteK/RankMW.lean`), so here the derivations are unconditional, and the main theorem
is stated from SixContactMin and each positive-rank form:

* `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankRk`:
  `RouteK.Rank.CertifiedRankRk` (Tian–Yuan–Zhang with Proposition N, and Gross–Zagier with an
  auxiliary field; Kriz's 2-converse is an alternative that is not needed);
* `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZRk`:
  `RouteK.Rank.CertifiedRankTYZRk` (odd genus sum `T5b d` gives positive rank);
* `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk`:
  `RouteK.Rank.CertifiedRankTYZClRk` (the same with Tian–Yuan–Zhang's class numbers; Rédei's
  formula `RouteK.Rank5b.RedeiFormula` is proved, `RouteK.Redei.redeiFormula`). Lean derives
  every other form of CR₃ from it; the trust statement is `docs/research/cr3-trust.md`.
-/

namespace ZInQ

namespace RouteK.Rank

/-- Mordell–Weil for every `C_d`, `d ≠ 0` (`fg_points`), in the form `Statements.lean` takes. -/
theorem fg_points_all : ∀ d : ℕ, d ≠ 0 → AddGroup.FG (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point :=
  fun d hd => fg_points d hd

/-- **CR₃^Sel from CR₃^Rk** (RK9 with Mordell–Weil). -/
theorem certifiedRankSel_of_certifiedRankRk' (h : CertifiedRankRk) : Selmer.CertifiedRankSel :=
  certifiedRankSel_of_certifiedRankRk fg_points_all h

/-- **CR₃ from CR₃^Rk.** -/
theorem certifiedRank_of_certifiedRankRk' (h : CertifiedRankRk) : CertifiedRank :=
  certifiedRank_of_certifiedRankRk fg_points_all h

/-- **CR₃^TYZ from CR₃^TYZ,Rk.** -/
theorem certifiedRankTYZ_of_certifiedRankTYZRk' (h : CertifiedRankTYZRk) :
    Rank5b.CertifiedRankTYZ :=
  certifiedRankTYZ_of_certifiedRankTYZRk fg_points_all h

/-- **CR₃^TYZ_Cl from CR₃^TYZ_Cl,Rk.** -/
theorem certifiedRankTYZCl_of_certifiedRankTYZClRk' (h : CertifiedRankTYZClRk) :
    Rank5b.CertifiedRankTYZCl :=
  certifiedRankTYZCl_of_certifiedRankTYZClRk fg_points_all h

end RouteK.Rank

/-- **Theorem 1.1** from 6C_min and CR₃^Rk: for squarefree `d ≡ 5 (mod 8)` with `#Sel₂(C_d) = 8`
and a Selmer class `(a, b)` with `|a| ≡ 7 (mod 8)`, `C_d(ℚ)` has a point of infinite order. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankRk
    (hH : SixContactMin) (hCR : RouteK.Rank.CertifiedRankRk) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankSel hH
    (RouteK.Rank.certifiedRankSel_of_certifiedRankRk' hCR)

/-- **Theorem 1.1** from 6C_min and CR₃^TYZ,Rk: for squarefree `d ≡ 5 (mod 8)` with odd genus sum
`T5b d`, `C_d(ℚ)` has a point of infinite order. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZRk
    (hH : SixContactMin) (hCR : RouteK.Rank.CertifiedRankTYZRk) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZ hH
    (RouteK.Rank.certifiedRankTYZ_of_certifiedRankTYZRk' hCR)

/-- **Theorem 1.1** from 6C_min and CR₃^TYZ_Cl,Rk (odd genus sum of class numbers gives a point of
infinite order on `C_d`). Rédei's formula, needed to pass from class numbers to Rédei's bits, is
proved (`RouteK.Redei.redeiFormula`). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
    (hH : SixContactMin) (hCR : RouteK.Rank.CertifiedRankTYZClRk) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZCl hH
    (RouteK.Rank.certifiedRankTYZCl_of_certifiedRankTYZClRk' hCR)

end ZInQ

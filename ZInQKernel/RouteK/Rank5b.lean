import ZInQKernel.Main
import ZInQKernel.RouteK.Rank5b.Bordered
import ZInQKernel.RouteK.Rank5b.Matrices
import ZInQKernel.RouteK.Rank5b.Kernel
import ZInQKernel.RouteK.Rank5b.Row5b
import ZInQKernel.RouteK.Rank5b.Check

/-!
# Route K, row 5b (root module)

The elementary half of the Tian–Yuan–Zhang route for CR₃^Sel (`docs/research/tyz-5b.md` §4):

* `Rank5b.Bordered`: Lemma 4.2 (`RouteK.Rank5b.det_border_eq_dotProduct`);
* `Rank5b.Matrices`: the data `a_ij`, `y_i`, `z_i`, Smith's matrices `L`, `M₁`, `M_5b`;
* `Rank5b.Kernel`: Lemma 4.1 on a configuration of class 5 (`Config.solEquivTorsH`,
  `Config.hEquivKer`, `Config.card_sols_eq`);
* `Rank5b.Row5b`: Lemma 4.1 for `Sel₂(C_n)` (`sel2_ncard_eq_four_mul`, `sel2HEquivKer`),
  Theorem 4.3 (`det_M5b_eq_dot`), Corollary 4.4 (`det_M5b_eq_one`), the hypothesis
  `CertifiedRank5b` and `certifiedRankSel_of_certifiedRank5b`;
* `Rank5b.Check`: kernel cross-checks `det M_5b = 1` for `n = 21` and `det M_5b = 0` for `n = 5`.

The main theorem under CR₃^5b in place of CR₃ is
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRank5b`.
-/

namespace ZInQ

/-- **Main theorem, with CR₃^5b in place of CR₃.** Under hypotheses H (`SixContactMin`),
CR₃^5b (`RouteK.Rank5b.CertifiedRank5b`: for squarefree `n ≡ 5 (mod 8)` with `#Sel₂(C_n) = 8` and
Smith's row-5b determinant `det M_5b = 1`, every 2-Selmer class of `C_n` comes from a rational
point; a consequence of Tian–Yuan–Zhang with Proposition N, and Gross–Zagier with an auxiliary
field, see `docs/research/cr3-trust.md`) and 22P, there is an integer
polynomial in `292890231905` variables, of degree below `2↑↑7` and with coefficients below
`2↑↑8`, whose rational zero projection to the first variable is exactly `ℤ`.

CR₃^5b implies CR₃^Sel by tyz-5b Corollary 4.4 (`RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b`,
proved in Lean from Proposition 0). The variant without 22P is
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank5b`
(`RouteK/Rank5bSec3.lean`). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_certifiedRank5b
    (hH : SixContactMin) (hCR5 : RouteK.Rank5b.CertifiedRank5b)
    (h22 : FixedPrimePattern) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel hH
    (RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b hCR5) h22

end ZInQ

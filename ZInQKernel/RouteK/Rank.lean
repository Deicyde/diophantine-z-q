import ZInQKernel.RouteK.Rank.KummerAt
import ZInQKernel.RouteK.Rank.Delta
import ZInQKernel.RouteK.Rank.Image
import ZInQKernel.RouteK.Rank.Counting
import ZInQKernel.RouteK.Rank.Torsion2
import ZInQKernel.RouteK.Rank.RK9
import ZInQKernel.RouteK.Rank.Statements

/-!
# RK9: the complete 2-descent on `C_d` and CR₃ as "positive rank"

`docs/research/pc-audit.md` RK9, proved in Lean (namespace `ZInQ.RouteK.Rank`):

* `KummerAt`: the Kummer map `kummerAt b e` at a root `e` of `x³ + b x` is a homomorphism;
* `Delta`: the complete 2-descent map `deltaHom` of `C_d : y² = x³ − d²x` (`P ↦ (x, x − d)` in
  `(K*/K*²)²`, Silverman X.1.4), and the halving lemma;
* `Image`: over `ℚ`, `ker δ_d = 2C_d(ℚ)` (`delta_eq_one_iff`) and the image lies in `Sel2 d`
  (`selRep_mem_sel2`);
* `Counting`: a finitely generated abelian group with `#A[2] = 4` and an element of infinite order
  has `#(A/2A) ≥ 8` (`eight_le_card_quotient_two`);
* `Torsion2`: `#C_d(K)[2] = 4`;
* `RK9`: `loc_of_mem_sel2_of_infinite_order`;
* `Statements`: `CertifiedRankRk`, `CertifiedRankTYZRk`, `CertifiedRankTYZClRk` and the theorems
  deriving CR₃^Sel, CR₃^TYZ and CR₃^TYZ_Cl from them (with Mordell–Weil for `C_d(ℚ)` as the
  hypothesis `hfg`).
-/

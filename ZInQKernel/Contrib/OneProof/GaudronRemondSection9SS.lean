import ZInQKernel.Contrib.OneProof.GaudronRemondSection9
import ZInQKernel.Contrib.OneProof.SemistablePrintedReadings

/-! # fold-b112: Gaudron–Rémond §9 over the printed semistability

Task fold-b112 (2026-11-17), report `docs/research/fold-b112.md`. On the base of this fold the research field for
step E4 (`diophantine_zq.tex` L894-895) is `bostLowerBoundAnSS` (`ZInQ.SemistabAssembly.BostLowerBoundAnSS`, Bost's
bound over `IsAnStableHeightSS`, semistability as printed; semistab-assembly), not the field `bostLowerBoundAn` that
bost-gr9 replaced. This file states bost-gr9's leaf `ZInQ.BostGR9.GaudronRemondSec9LowerAn` with the same change
semistab-assembly made to the two sibling rows (`IsAnStableHeight` replaced by `IsAnStableHeightSS`):

* `GaudronRemondSec9LowerAnSS`: the leaf (GR14 §9, `h_F(A) ≥ -(3/2) dim A`) over the printed semistability;
* `gaudronRemondSec9LowerAn_of_ss`: it implies bost-gr9's `GaudronRemondSec9LowerAn` (so it feeds bost-gr9's proved
  route to R21 unchanged);
* `gaudronRemondSec9LowerAnSS_of_bostLowerBoundAnSS`: it is implied by the field it replaces, so adopting it never
  strengthens the hypothesis set (the converse fails: `ZInQ.BostGR9.sec9_bound_lt_bost`).

No `sorry`, no `axiom`. -/

open ZInQ.SemistabAssembly

namespace ZInQ.BostGR9

/-- **Leaf GR14-§9 over the printed semistability** (step E4, `diophantine_zq.tex` L894-895, cited
there as "recorded in [gr2014, Section 9]"). Source: É. Gaudron and G. Rémond, *Théorème des
périodes et degrés minimaux d'isogénies*, Comment. Math. Helv. 89 (2014), Cor. 8.4, p. 400 (GR1;
attribution: Bost), `h(A) ≥ -(g/2) log(2π)`, with the normalization `h_F(A) = h(A) - (g/2) log π`
on p. 352; two-lens statement check 2026-11-24. This leaf is the weaker bound, implied by that one
(`gaudronRemondSec9LowerAnSS_of_bostLowerBoundAnSS`). Duke 163 p. 2098: citation only
(É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057-2108, §9,
proof of Lemme 9.1, citing GR1 Cor. 8.4; docs/research/locators.md row R21). For every abelian
variety `A` of dimension `g` over a number field, `h(A) ≥ -(3/2) g`, `h` the stable Faltings height
in Faltings' original normalization. `GaudronRemondSec9LowerAn` verbatim with
`ZInQ.R3Residual.IsAnStableHeight` replaced by `ZInQ.SemistabAssembly.IsAnStableHeightSS`
(semistable reduction as printed: the identity component of the special fibre is semi-abelian, over
`k(𝔭)` and over its algebraic closure; semistab-assembly). -/
def GaudronRemondSec9LowerAnSS : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsAnStableHeightSS A x → -(3 / 2) * (g : ℝ) ≤ x

/-- The leaf over the printed semistability gives bost-gr9's leaf (`isAnStableHeightSS_of`). -/
theorem gaudronRemondSec9LowerAn_of_ss (h : GaudronRemondSec9LowerAnSS) : GaudronRemondSec9LowerAn :=
  fun K _ _ A g hg x hx => h K A g hg x (isAnStableHeightSS_of hx)

/-- **Never stronger than the replaced field** `bostLowerBoundAnSS`: Bost's bound (Deligne's normalization)
converted to Faltings' (`deligne_bound_iff`) and `(1/2) log(2π²) < 3/2` (`half_log_two_pi_sq_lt`). -/
theorem gaudronRemondSec9LowerAnSS_of_bostLowerBoundAnSS (h : BostLowerBoundAnSS) :
    GaudronRemondSec9LowerAnSS := by
  intro K _ _ A g hg x hx
  have h1 := (deligne_bound_iff g x).mp (h K A g hg x hx)
  have h2 := half_log_two_pi_sq_lt
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  nlinarith

end ZInQ.BostGR9

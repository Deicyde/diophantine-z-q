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

**Trust statement.** CR₃ is not proved in Lean. Lean derives it from `RouteK.Rank.CertifiedRankRk`
(`certifiedRank_of_certifiedRankRk'`), and that from `RouteK.Rank.CertifiedRankTYZClRk`
(`Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk`, `certifiedRankRk_of_certifiedRankTYZRk`).
The latter says: for squarefree `d ≡ 5 (mod 8)` with odd genus sum of class numbers `T5bCl d`,
`C_d(ℚ)` has a point of infinite order. Its proof is published mathematics, one short repository
argument, and the match of the Lean definitions with TYZ's quantities (model reviews);
`docs/research/cr3-trust.md` lists every step with its supplier:

* *Tian–Yuan–Zhang* (Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent
  number problem*, Asian J. Math. 21 (2017), 721–774; read in arXiv:1411.4728v1 only):
  Theorem 3.5 (first assertion), Theorem 3.3, Proposition 3.2, Lemmas 2.8, 3.16, 3.18, 3.21,
  Proposition 2.3 and the recursion of §3.1. Their proofs use Waldspurger's formula and the
  Gross–Zagier formula of Yuan–Zhang–Zhang. TYZ's Theorem 1.2 is not cited: as printed (all
  `d_i > 1`) it is false (`docs/research/nt-tyz.md` §1.4).
* *Proposition N* (`docs/research/nt-tyz.md` §4; model reviews `docs/research/rv-nt-tyz.md` and
  `docs/research/rv-prop-n.md`): from these inputs, if the `(7, 3)` genus sum `T_5b(d)` is odd
  then TYZ's `𝓛(d) ≠ 0`, so `ord_{s=1} L(C_d, s) ≤ 1`, and the root number `−1` (Birch–Stephens)
  gives `= 1`. It replaces TYZ's Proposition 3.4 by a direct parity count (Lemmas N1, N2). Not
  refereed.
* *Gross–Zagier* (Invent. Math. 84 (1986)), with an imaginary quadratic field satisfying the
  Heegner hypothesis and `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein): analytic rank one gives a
  point of infinite order. `C_d` is modular since it has CM (Deuring, Shimura). Neither BCDT nor
  Kolyvagin's MPIM preprint is needed; Kolyvagin's published papers enter only inside
  Tian–Yuan–Zhang.

Everything else is proved in Lean: Rédei's formula (`RouteK.Redei.redeiFormula`, which turns
`T5bCl` into Rédei's bits `T5b`), Theorem 3.6 and Corollary 4.4 of `docs/research/tyz-5b.md`
(`RouteK.Rank5b.det_M5b_eq_T5b`, `det_M5b_eq_one`: the premises here give `T5b d = 1`),
Proposition 0 (`RouteK.Selmer.prop0Statement`: `Σ(𝒞_d)` is `Sel₂(C_d)`), Mordell–Weil for `C_d`
(`RouteK.Rank.fg_points`), and the step from a point of infinite order and `#Sel₂(C_d) = 8` to a
point in the class `a` (`RouteK.Rank.loc_of_mem_sel2_of_infinite_order`; pc-audit RK9).
Kriz's 2-converse (arXiv:2002.04767, Theorem 10.13, a preprint) with the corank lemma is an
alternative route; it is not needed (`docs/research/nt-tyz.md` §5.1). Weaker forms that Lean also
accepts: `RouteK.Rank.CertifiedRankDLRk` and `CertifiedRankDLAdmRk` (only the curves the proof
uses). -/
def CertifiedRank : Prop :=
  ∀ (d : ℕ) (a : ℤ) (hd : d % 8 = 5), Squarefree d → Squarefree a → a ∣ (d : ℤ) →
    a.natAbs % 8 = 7 →
    (RouteK.natConfig d (RouteK.odd_of_mod_eight_eq_five hd)).sols.card = 8 →
    (∃ σ ∈ (RouteK.natConfig d (RouteK.odd_of_mod_eight_eq_five hd)).sols,
      σ.first = RouteK.natClass d a) →
    ∃ x y : ℚ, y ^ 2 = x ^ 3 - (d : ℚ) ^ 2 * x ∧ x ≠ 0 ∧ IsSquare (x / a)

end ZInQ

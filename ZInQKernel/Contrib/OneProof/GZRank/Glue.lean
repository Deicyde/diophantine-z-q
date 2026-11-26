import ZInQKernel.Contrib.OneProof.GZRank.Row
import ZInQKernel.Contrib.OneProof.GZRank.Consumer
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent

/-!
# Modularity in Gross–Zagier's form, and the point of infinite order

`exists_newform_lseries_eq`: from Breuil–Conrad–Diamond–Taylor's Theorem A as printed
(`BCDTPrint.BCDTThmAPrinted`) and Carayol's Corollaire 0.8 (`CarayolCor08`), every elliptic curve
`E` over `ℚ` has a newform `g` of weight 2, some level `M` and trivial nebentypus with
`L(E, s) = L(g, s)`: the hypothesis of Gross–Zagier, Chapter V, §2, p. 310. The steps:

1. BCDT gives an eigenform `f` on `Γ₁(N)` with `L(E, s) = L(f, s)` on a right half-plane;
   `BCDTPrint.coeff_eq_of_eq_cuspLSeries` turns this into `a_n(f) = a_n(E)` for all `n ≥ 1`, and
   `BCDTPrint.mem_cuspFormCharSpace_one_of_eigen` proves the trivial nebentypus (all proved).
2. `NewformGlueG0.exists_newform_almost_all_prime_coeff` (Li's old/new decomposition, proved)
   gives a newform `g` of a level `M ∣ N` with `g.χ = 1` and `a_p(g) = a_p(E)` at all but
   finitely many primes.
3. Carayol's corollary gives `L(E, s) = L(g, s)`, bad primes included.

`nonTorsion_of_prints` then derives `PoleRC.NonTorsion.NonTorsionOfAnalyticRankOne` from
Gross–Zagier's Theorem (7.3)(1) (`GZThm73NonTorsion`), through
`SilvermanRank.analyticRankOne_iff_value_deriv` (proved).

Why step 3 is a printed row and not a Lean proof: the Hecke theory in the tree places the BCDT
form `f` in the span of the level raises `g(dz)`, `d ∣ N / M`, of newforms with the eigenvalues of
`E` away from a finite set, but nothing in it constrains the Euler factors at the primes dividing
`N / M`. At such a prime `p`, writing `L_p(E) = 1 / Q(X)` and `L_p(g) = 1 / P(X)`, the local
factor of `∑ c_d d^{-s}` is `P / Q`, and the coefficient identities in the tree are consistent
with `P ≠ Q`: if `E` has additive reduction at `p ∤ M`, then `Q = 1` and
`f = g − a_p(g) g(pz) + p g(p²z)` is not excluded; if `E` has multiplicative reduction at
`p ∤ M`, then `Q = 1 − εX` (`ε = ±1`) divides `P = 1 − ε(1 + p)X + pX²`, excluded only by the
Ramanujan bound `|a_p(g)| ≤ 2√p`. Ruling these out is the local-global compatibility of Carayol's
Théorème (A) (or the conductor), which has no Lean statement here.
-/

noncomputable section

namespace ZInQ.Manuscript.PoleS12.GZRank

open CongruenceSubgroup UpperHalfPlane Matrix.SpecialLinearGroup HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.BCDTPrint ZInQ.Contrib.RC53Assist.NewformGlueG0

/-- **PROVED** from BCDT Theorem A as printed and Carayol's Corollaire 0.8: modularity in the
form Gross–Zagier assume on p. 310, a newform `g` of weight 2, some level `M` and trivial
nebentypus with `L(E, s) = L(g, s)` on a right half-plane. -/
theorem exists_newform_lseries_eq (hB : BCDTThmAPrinted) (hC : CarayolCor08)
    (E : WeierstrassCurve ℚ) (hE : E.IsElliptic) :
    ∃ (M : ℕ) (_ : NeZero M) (g : HeckeRing.GL2.Newform M 2), g.χ = 1 ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → E.LSeries s = cuspLSeries g.toCuspForm s := by
  obtain ⟨N, _, h⟩ := hB E hE
  obtain ⟨f, ⟨hf0, heig⟩, σ, hL⟩ := h
  have hf := coeff_eq_of_eq_cuspLSeries E hf0 hL
  have hmem := mem_cuspFormCharSpace_one_of_eigen E hE f hf heig
  set f₀ := TauCeti.cuspFormCharSpaceOneEquiv N 2 ⟨f, hmem⟩
  have hf₀ : ⇑f₀ = ⇑f := TauCeti.coe_cuspFormCharSpaceOneEquiv_apply _
  have hc : ∀ n : ℕ, 0 < n → (qExpansion 1 f₀).coeff n = (E.LFunction n : ℂ) := by
    intro n hn
    rw [show qExpansion 1 f₀ = qExpansion 1 f from congrArg (qExpansion 1) hf₀]
    exact hf n hn
  obtain ⟨M, hM, g, -, hgχ, S, hS⟩ :=
    exists_newform_almost_all_prime_coeff E hE N (Nat.pos_of_ne_zero (NeZero.ne N)) f₀ hc
  exact ⟨M, hM, g, hgχ, hC M g hgχ E hE ⟨S, hS⟩⟩

/-- **PROVED** from Gross–Zagier (7.3)(1), BCDT Theorem A as printed and Carayol's
Corollaire 0.8: analytic rank one gives a point of infinite order, the consumer's only use of its
rank hypothesis. -/
theorem nonTorsion_of_prints (hGZ : GZThm73NonTorsion) (hB : BCDTThmAPrinted)
    (hC : CarayolCor08) : PoleRC.NonTorsion.NonTorsionOfAnalyticRankOne := by
  intro E hE hA
  obtain ⟨F, hF, hL, h1, hd⟩ := (SilvermanRank.analyticRankOne_iff_value_deriv E).mp hA
  obtain ⟨M, hM, g, hgχ, hLg⟩ := exists_newform_lseries_eq hB hC E hE
  exact hGZ M g hgχ E hE hLg F hF hL h1 hd

end ZInQ.Manuscript.PoleS12.GZRank

#print axioms ZInQ.Manuscript.PoleS12.GZRank.exists_newform_lseries_eq
#print axioms ZInQ.Manuscript.PoleS12.GZRank.nonTorsion_of_prints

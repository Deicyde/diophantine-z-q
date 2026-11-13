import ZInQKernel.HDecomp.QM.Pairs
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# curve-glue, part 3: C3K `RatFactorAlgClosed` from a plane-curve statement and algebra

Task curve-glue (2026-11-13). `RatFactorAlgClosed` (C3K) is copied verbatim from
`scratch/curve-facts/CurveFacts.lean` (§7 there) with `ptOf` and `Mob.ratEval`. See
`docs/research/curve-glue.md`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

namespace AV

namespace Pin

open CategoryTheory AlgebraicGeometry Limits
open PkgI3

/-! ## §0 Copied verbatim from `scratch/curve-facts/CurveFacts.lean` -/

namespace Mob

open Polynomial

variable {K : Type} [Field K]

open scoped Classical in
/-- The value at a finite point `t` of the rational map `[F : G] : P¹ → P¹`. -/
def ratEval (F G : K[X]) (t : K) : OnePoint K :=
  if G.eval t = 0 then OnePoint.infty else OnePoint.some (F.eval t / G.eval t)

end Mob

/-- The point of `X` at which a field point `p : Spec K → X` sits. -/
abbrev ptOf {K : Type} [Field K] {X : Scheme.{0}} (p : Spec (CommRingCat.of K) ⟶ X) : X :=
  (Scheme.SpecToEquivOfField K X p).1

open Polynomial in
/-- **(C3K) Factorization on a connected component where `σ` is nonconstant**, over an
algebraically closed field of characteristic 0 (in characteristic `p` the Frobenius
`σ = ρ^p` is a counterexample). Glue (a standard consequence of textbook results, see
`docs/research/curve-facts.md` §3). -/
def RatFactorAlgClosed : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p₁ p₂ : Spec (CommRingCat.of K) ⟶ X, p₁ ≫ f = 𝟙 _ → p₂ ≫ f = 𝟙 _ →
        connectedComponent (ptOf p₁) = connectedComponent (ptOf p₀) →
        connectedComponent (ptOf p₂) = connectedComponent (ptOf p₀) →
        σ.val p₁ = σ.val p₂ → ρ.val p₁ = ρ.val p₂) →
      ∃ F G : K[X], IsCoprime F G ∧ ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t : K,
        σ.val p = OnePoint.some t → ρ.val p = Mob.ratEval F G t


/-! ## §1 Algebra: an irreducible `P(x, y)` of `y`-degree `≥ 2` has a fibre with two roots -/

namespace Alg

open Polynomial

variable {K : Type} [Field K]

/-- `P(t, u)` for `P ∈ K[x][y]` (outer variable `y`, coefficients in `K[x]`). -/
def evalXY (t u : K) (P : K[X][X]) : K := (P.map (evalRingHom t)).eval u

/-- **Two roots in some fibre** (Lean-proved algebra; char. 0 is essential). If `P ∈ K[x][y]` is
irreducible of `y`-degree `d ≥ 2`, `K` algebraically closed of characteristic 0, then for some
`t ∈ K` the polynomial `P(t, y)` has two distinct roots. Proof: `P` is primitive and stays
irreducible over `K(x)` (Gauss), hence separable (char. 0), so the resultant
`r = Res_y(P, ∂P/∂y) ∈ K[x]` is nonzero; at any `t` with `r(t) · lc(P)(t) ≠ 0`, `P(t, y)` has
degree `d` and is separable, so it has `d ≥ 2` distinct roots. -/
theorem exists_two_roots [IsAlgClosed K] [CharZero K] {P : K[X][X]} (hirr : Irreducible P)
    (h2 : 2 ≤ P.natDegree) :
    ∃ t u u' : K, u ≠ u' ∧ evalXY t u P = 0 ∧ evalXY t u' P = 0 := by
  classical
  have hd0 : P.natDegree ≠ 0 := by omega
  have hP0 : P ≠ 0 := fun h => by simp [h] at h2
  set φ := algebraMap K[X] (FractionRing K[X]) with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hirr' : Irreducible (P.map φ) :=
    ((hirr.isPrimitive hd0).irreducible_iff_irreducible_map_fraction_map).1 hirr
  have hsep : (P.map φ).Separable := hirr'.separable
  have hres := resultant_ne_zero _ _ hsep
  rw [derivative_map, natDegree_map_eq_of_injective hinj,
    natDegree_map_eq_of_injective hinj, resultant_map_map] at hres
  set r := resultant P (derivative P) P.natDegree (derivative P).natDegree with hr
  have hr0 : r ≠ 0 := fun h => hres (by rw [h, map_zero])
  have hlc0 : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  -- a good fibre
  obtain ⟨t, ht⟩ : ∃ t : K, (r * P.leadingCoeff).eval t ≠ 0 := by
    by_contra! h
    exact mul_ne_zero hr0 hlc0 (Polynomial.funext fun t => by rw [h t, eval_zero])
  rw [eval_mul] at ht
  have hrt : r.eval t ≠ 0 := left_ne_zero_of_mul ht
  have hlt : P.leadingCoeff.eval t ≠ 0 := right_ne_zero_of_mul ht
  set ψ := evalRingHom t with hψ
  set Pt := P.map ψ with hPt
  have hdeg : Pt.natDegree = P.natDegree := natDegree_map_of_leadingCoeff_ne_zero ψ hlt
  have hdeg' : ((derivative P).map ψ).natDegree = (derivative P).natDegree := by
    refine natDegree_map_of_leadingCoeff_ne_zero ψ ?_
    rw [leadingCoeff_derivative, map_mul, map_natCast]
    exact mul_ne_zero hlt (by exact_mod_cast hd0)
  have hPt0 : Pt ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; omega
  have hrest : resultant Pt (derivative Pt) ≠ 0 := by
    rw [derivative_map, hdeg, hdeg', resultant_map_map]
    exact hrt
  have hsep' : Pt.Separable := by
    have h := mt resultant_eq_zero_iff.2 hrest
    push Not at h
    exact h (Or.inl hPt0)
  have hcard : Pt.roots.card = P.natDegree := by
    rw [← (IsAlgClosed.splits Pt).natDegree_eq_card_roots, hdeg]
  have hnd : Pt.roots.Nodup := nodup_roots hsep'
  have h1 : 1 < Pt.roots.toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup hnd, hcard]; omega
  obtain ⟨u, hu, u', hu', hne⟩ := Finset.one_lt_card.1 h1
  exact ⟨t, u, u', hne, (mem_roots hPt0).1 (Multiset.mem_toFinset.1 hu),
    (mem_roots hPt0).1 (Multiset.mem_toFinset.1 hu')⟩

end Alg

end Pin

end AV

end LeafQM

end

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

/-- An irreducible `P ∈ K[x][y]` of `y`-degree 1 has coprime coefficients. -/
theorem isCoprime_coeff_of_irreducible {P : K[X][X]} (hirr : Irreducible P)
    (h1 : P.natDegree = 1) : IsCoprime (P.coeff 1) (P.coeff 0) := by
  have hP : P = C (P.coeff 1) * X + C (P.coeff 0) := eq_X_add_C_of_natDegree_le_one h1.le
  refine IsRelPrime.isCoprime fun d hdA hdB => ?_
  obtain ⟨a, ha⟩ := hdA
  obtain ⟨b, hb⟩ := hdB
  have hfac : P = C d * (C a * X + C b) := by
    rw [hP, ha, hb, C_mul, C_mul]; ring
  rcases hirr.isUnit_or_isUnit hfac with h | h
  · exact isUnit_C.mp h
  · exfalso
    have h0 := natDegree_eq_zero_of_isUnit h
    have : P.natDegree ≤ 0 := by
      rw [hfac]; exact (natDegree_C_mul_le _ _).trans h0.le
    omega

end Alg

/-! ## §2 The geometric glue (G1) and the reduction -/

open Polynomial in
/-- **(G1) The image of a connected component under `(σ, ρ)` is a plane curve.** Setting of C3K
(without characteristic 0): `X → Spec K` proper and smooth of relative dimension 1, `K`
algebraically closed, `σ, ρ : X → P¹`, `W` the connected component of the `K`-point `p₀`, and
`σ` nonconstant on the `K`-points of `W`. Then either `ρ ≡ ∞` on the `K`-points of `W`, or there
is an irreducible `P ∈ K[x][y]` of `y`-degree `≥ 1` such that
(a) `P(σ(p), ρ(p)) = 0` at every `K`-point `p` of `W` with both values finite;
(b) every `(t, u) ∈ K²` with `P(t, u) = 0` is `(σ(p), ρ(p))` for a `K`-point `p` of `W`;
(c) a `K`-point `p` of `W` with `σ(p) = t` finite and `ρ(p) = ∞` has `lc_y(P)(t) = 0`.

Why true (STANDARD; references UNVERIFIED): `W` is a complete nonsingular irreducible curve
(smooth ⇒ normal, so connected components are irreducible), so its image `D` under
`(σ, ρ) : W → P¹ × P¹` is closed (properness) and irreducible, and not a point (σ nonconstant).
If `ρ ≢ ∞`, `D ∩ 𝔸²` is a nonempty open, hence dense, subset of `D`, an irreducible closed curve
in `𝔸²`, so `D ∩ 𝔸² = V(P)` with `P` irreducible (`K[x, y]` is a UFD and height-one primes are
principal: Hartshorne I.1.12 / Ex. I.1.1-type facts); `P ∉ K[x]` because `σ` is nonconstant on
the dense set `W ∩ (σ, ρ)⁻¹(𝔸²)`. (a) is `D ∩ 𝔸² ⊆ V(P)`. (b): `V(P) ⊆ D`, and every closed point
of `D` is the image of a closed point of `W` (the fibre is a nonempty closed subset of a scheme of
finite type over `K`), i.e. of a `K`-point (Nullstellensatz). (c): `D` lies in the closure of
`V(P)` in `𝔸¹ × P¹`, which lies in `V(P^h)`, `P^h(x; y₀ : y₁) = Σ a_i(x) y₁^i y₀^{d−i}`, whose
points over `y = ∞` (`y₀ = 0`) have `a_d(x) = 0`.

Classified as **glue** (several textbook facts: image of a proper curve, plane curves as
hypersurfaces, closure and homogenization). Characteristic 0 is not used here; it enters only
through the Lean-proved `Alg.exists_two_roots`. Not in Mathlib v4.35 (no `P¹ × P¹`, no plane
curves). -/
def ImagePlaneCurve : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)), IsProper f → SmoothOfRelativeDimension 1 f →
    ∀ (σ ρ : ToP1 X) (p₀ : Spec (CommRingCat.of K) ⟶ X), p₀ ≫ f = 𝟙 _ →
      (∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧ σ.val p ≠ σ.val p₀) →
      (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
        connectedComponent (ptOf p) = connectedComponent (ptOf p₀) →
        ρ.val p = OnePoint.infty) ∨
      ∃ P : K[X][X], Irreducible P ∧ 1 ≤ P.natDegree ∧
        (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t u : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.some u → Alg.evalXY t u P = 0) ∧
        (∀ t u : K, Alg.evalXY t u P = 0 → ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ ∧
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) ∧
          σ.val p = OnePoint.some t ∧ ρ.val p = OnePoint.some u) ∧
        (∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
          connectedComponent (ptOf p) = connectedComponent (ptOf p₀) → ∀ t : K,
          σ.val p = OnePoint.some t → ρ.val p = OnePoint.infty → P.leadingCoeff.eval t = 0)

open Polynomial in
/-- **C3K from (G1) and the Lean-proved algebra.** The fibre condition and
`Alg.exists_two_roots` force `deg_y P = 1`, `P = A y + B` with `A, B` coprime, and then
`ρ = [−B : A] ∘ σ` at every `K`-point of `W` with finite `σ`-value (clause (c) for `ρ = ∞`). -/
theorem ratFactorAlgClosed_of (hG : ImagePlaneCurve) : RatFactorAlgClosed := by
  intro K _ _ _ X f hP hS σ ρ p₀ hp₀ hne hfib
  rcases hG K X f hP hS σ ρ p₀ hp₀ hne with hinf | ⟨P, hirr, hdeg, ha, hb, hc⟩
  · refine ⟨1, 0, isCoprime_one_left, fun p hp hpc t _ => ?_⟩
    rw [hinf p hp hpc]
    simp [Mob.ratEval]
  · have hd1 : P.natDegree = 1 := by
      by_contra h
      obtain ⟨t, u, u', hne', hu, hu'⟩ := Alg.exists_two_roots hirr (by omega)
      obtain ⟨p, hp, hpc, hpt, hpu⟩ := hb t u hu
      obtain ⟨p', hp', hpc', hpt', hpu'⟩ := hb t u' hu'
      have e := hfib p p' hp hp' hpc hpc' (hpt.trans hpt'.symm)
      rw [hpu, hpu'] at e
      exact hne' (OnePoint.coe_injective e)
    have hcop := Alg.isCoprime_coeff_of_irreducible hirr hd1
    have hPe : P = C (P.coeff 1) * Polynomial.X + C (P.coeff 0) :=
      eq_X_add_C_of_natDegree_le_one hd1.le
    have hev : ∀ t u : K, Alg.evalXY t u P = (P.coeff 1).eval t * u + (P.coeff 0).eval t := by
      intro t u
      rw [Alg.evalXY]
      conv_lhs => rw [hPe]
      simp
    have hlc : P.leadingCoeff = P.coeff 1 := by rw [leadingCoeff, hd1]
    have hnotboth : ∀ t : K, (P.coeff 1).eval t = 0 → (P.coeff 0).eval t ≠ 0 := by
      intro t h1 h0
      obtain ⟨a, b, hab⟩ := hcop
      have e := congrArg (eval t) hab
      simp [eval_add, eval_mul, h1, h0] at e
    refine ⟨-(P.coeff 0), P.coeff 1, hcop.symm.neg_left, fun p hp hpc t ht => ?_⟩
    induction hρ : ρ.val p using OnePoint.rec with
    | infty =>
      have e := hc p hp hpc t ht hρ
      rw [hlc] at e
      unfold Mob.ratEval
      split_ifs
      rfl
    | coe u =>
      have e := ha p hp hpc t u ht hρ
      rw [hev] at e
      by_cases hA : (P.coeff 1).eval t = 0
      · exfalso
        rw [hA, zero_mul, zero_add] at e
        exact hnotboth t hA e
      · unfold Mob.ratEval
        split_ifs
        rw [eval_neg]
        refine congrArg _ ?_
        field_simp
        linear_combination e

end Pin

end AV

end LeafQM

end

#print axioms LeafQM.AV.Pin.ratFactorAlgClosed_of
#print axioms LeafQM.AV.Pin.Alg.exists_two_roots

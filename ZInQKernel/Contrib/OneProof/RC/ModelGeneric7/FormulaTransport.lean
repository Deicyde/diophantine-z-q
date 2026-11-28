import ZInQKernel.Contrib.OneProof.RC.ModelGeneric7.SeamFormula
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric7.PairMap
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric6.ComplexStep

/-! **Formula-carrying seams along ring maps of fields** (rc-model-generic7, item 2).

The seams of `FormulaSeam` (R0) are built from the vendored Vélu formulas, and the formulas
commute with ring maps. This file proves, with no function-field transport:

* `veluX_map`, `veluY_map`, `oddOrderSummingSet_map`, `velu2X_map`, `velu2Y_map`: the vendored
  formulas along a ring map `σ` of fields.
* `PtRel P P'`: two points (of possibly different curves over one field) are both zero or
  have the same coordinates. `PtRel.eq`, `PtRel.cast_eq`.
* `stepRel`: a formula step over `K₁` and a formula step over `K₂` at the image generator
  commute with the point maps of `σ`.
* `formulaSeam_rel`: the same for the whole `FormulaSeam` composite: if `g` over `K₁` and `G`
  over `K₂` satisfy `FormulaSeam` at `(E, H, c, n)` and `(E.map σ, ⟨σ c⟩, σ c, n)`, then
  `G (σ P)` and `σ (g P)` have the same coordinates.
* `rationalPoints_atkinRat_formulaSeam` (item 2 for R0 seams): over every algebraically closed
  field `K` of characteristic 0 with `#K = 𝔠`, for a pair `(E, C)` representing
  `rationalPoints x` and the R0 seam `g` at a generator `c` of `C_Q = (N/Q) • C`,
  `rationalPoints (x ∘ atkinRatAlg) = [(E.cyclicQuotientCurve C_Q Q, g(E[Q] ⊔ C))]`. The proof
  transports only the algebraic statement of `ModelGeneric6.rationalPoints_atkinRat_complex_moduli`
  along a ring isomorphism `σ : K ≃+* ℂ` (`IsAlgClosed.ringEquiv_of_equiv_of_charZero`), through
  `rationalPoints_comp`, `cyclicQuotientCurve_map` (T2), `formulaSeam_rel` and the injectivity of
  `pairClassesMap σ`. No complex-analytic step is transported.
* `atkinClass_independent_formulaSeam`: the class does not depend on the representative or on
  the generator.

Provenance: on the spot (c). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ZInQ.Manuscript.RC.ModelGeneric7

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.ModelLevels
open scoped TauCeti.ExactDivisor Cardinal

section Formulas

variable {F F' : Type*} [Field F] [Field F'] (W : WeierstrassCurve F) (σ : F →+* F')

/-- The coordinate-pair embedding of a ring map of fields. -/
def pairEmb : F × F ↪ F' × F' :=
  ⟨Prod.map σ σ, σ.injective.prodMap σ.injective⟩

theorem veluX_map (S : Finset (F × F)) (x : F) :
    (W.map σ).veluX (S.map (pairEmb σ)) (σ x) = σ (W.veluX S x) := by
  simp only [veluX, Finset.sum_map, pairEmb, Function.Embedding.coeFn_mk, Prod.map_fst,
    Prod.map_snd, map_veluT, map_veluU, map_add, map_sum, map_div₀, map_sub, map_pow]

theorem veluY_map (S : Finset (F × F)) (x y : F) :
    (W.map σ).veluY (S.map (pairEmb σ)) (σ x) (σ y) = σ (W.veluY S x y) := by
  simp only [veluY, Finset.sum_map, pairEmb, Function.Embedding.coeFn_mk, Prod.map_fst,
    Prod.map_snd, map_veluT, map_veluU, map_veluGx, map_veluGy, map_a₁, map_a₃, map_add, map_sum,
    map_div₀, map_sub, map_pow, map_mul, map_ofNat]

theorem velu2X_map (x₀ y₀ x : F) :
    (W.map σ).velu2X (σ x₀) (σ y₀) (σ x) = σ (W.velu2X x₀ y₀ x) := by
  simp only [velu2X, map_add, map_div₀, map_sub, map_veluGx]

theorem velu2Y_map (x₀ y₀ x y : F) :
    (W.map σ).velu2Y (σ x₀) (σ y₀) (σ x) (σ y) = σ (W.velu2Y x₀ y₀ x y) := by
  simp only [velu2Y, map_add, map_div₀, map_sub, map_mul, map_pow, map_veluGx, map_a₁]

end Formulas

section PtRel

variable {K : Type*} [Field K] [DecidableEq K]

/-- Two points of possibly different curves over `K` are both zero, or both nonzero with the
same coordinates. -/
def PtRel {V V' : WeierstrassCurve K} (P : V.toAffine.Point) (P' : V'.toAffine.Point) : Prop :=
  (P = 0 ↔ P' = 0) ∧ P.coordsOrZero = P'.coordsOrZero

theorem PtRel.refl {V : WeierstrassCurve K} (P : V.toAffine.Point) : PtRel P P :=
  ⟨Iff.rfl, rfl⟩

theorem ptRel_zero {V V' : WeierstrassCurve K} :
    PtRel (0 : V.toAffine.Point) (0 : V'.toAffine.Point) :=
  ⟨⟨fun _ => rfl, fun _ => rfl⟩, rfl⟩

theorem PtRel.symm {V V' : WeierstrassCurve K} {P : V.toAffine.Point} {P' : V'.toAffine.Point}
    (h : PtRel P P') : PtRel P' P :=
  ⟨h.1.symm, h.2.symm⟩

theorem PtRel.trans {V V' V'' : WeierstrassCurve K} {P : V.toAffine.Point}
    {P' : V'.toAffine.Point} {P'' : V''.toAffine.Point} (h : PtRel P P') (h' : PtRel P' P'') :
    PtRel P P'' :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

theorem PtRel.eq {V : WeierstrassCurve K} {P P' : V.toAffine.Point} (h : PtRel P P') : P = P' := by
  rcases P with _ | ⟨x, y, hP⟩ <;> rcases P' with _ | ⟨x', y', hP'⟩
  · rfl
  · exact absurd (h.1.mp rfl) (Point.some_ne_zero hP')
  · exact absurd (h.1.mpr rfl) (Point.some_ne_zero hP)
  · have h2 := h.2
    simp only [Point.coordsOrZero, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rfl

theorem PtRel.cast_eq {V V' : WeierstrassCurve K} (e : V = V') {P : V.toAffine.Point}
    {P' : V'.toAffine.Point} (h : PtRel P P') :
    cast (congrArg (fun V : WeierstrassCurve K => V.toAffine.Point) e) P = P' := by
  subst e
  exact h.eq

theorem ptRel_pointCast {V V' : WeierstrassCurve K} (e : V = V')
    (P : V.toAffine.Point) : PtRel (pointCast e P) P := by
  subst e
  exact PtRel.refl P

theorem ptRel_some {V V' : WeierstrassCurve K} {x y x' y' : K} (h : V.toAffine.Nonsingular x y)
    (h' : V'.toAffine.Nonsingular x' y') (hx : x = x') (hy : y = y') :
    PtRel (Point.some x y h) (Point.some x' y' h') :=
  ⟨⟨fun e => absurd e (Point.some_ne_zero h), fun e => absurd e (Point.some_ne_zero h')⟩,
    by simp [Point.coordsOrZero, hx, hy]⟩

variable {K' : Type*} [Field K'] [DecidableEq K'] (σ : K →+* K')

theorem coordsOrZero_pointMapAlong {V : WeierstrassCurve K} (P : V.toAffine.Point) :
    (pointMapAlong σ V P).coordsOrZero = Prod.map σ σ P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · change ((0, 0) : K' × K') = (σ 0, σ 0)
    rw [map_zero]
  · rfl

theorem PtRel.map {V V' : WeierstrassCurve K} {P : V.toAffine.Point} {P' : V'.toAffine.Point}
    (h : PtRel P P') : PtRel (pointMapAlong σ V P) (pointMapAlong σ V' P') := by
  refine ⟨?_, by rw [coordsOrZero_pointMapAlong, coordsOrZero_pointMapAlong, h.2]⟩
  rw [← (pointMapAlong σ V).map_zero, (pointMapAlong_injective σ V).eq_iff,
    ← (pointMapAlong σ V').map_zero, (pointMapAlong_injective σ V').eq_iff]
  exact h.1

end PtRel

section Steps

variable {K₁ K₂ : Type} [Field K₁] [Field K₂] [DecidableEq K₁] [DecidableEq K₂]
  [IsAlgClosed K₁] [IsAlgClosed K₂] (σ : K₁ →+* K₂)

theorem oddOrderSummingSet_map (E : WeierstrassCurve K₁) (Q : E.toAffine.Point) (n : ℕ) :
    (E.map σ).oddOrderSummingSet (pointMapAlong σ E Q) n =
      (E.oddOrderSummingSet Q n).map (pairEmb σ) := by
  rw [Finset.map_eq_image, oddOrderSummingSet, oddOrderSummingSet, Finset.image_image]
  refine Finset.image_congr fun k _ => ?_
  change (k • pointMapAlong σ E Q).coordsOrZero = Prod.map σ σ (k • Q).coordsOrZero
  rw [← map_nsmul, coordsOrZero_pointMapAlong]

/-- The order-two Vélu point map commutes with the point maps of `σ`, up to `PtRel`. -/
theorem veluPointMap2_rel (E : WeierstrassCurve K₁) {x₀ y₀ : K₁} (h2 : (2 : K₁) ≠ 0)
    (hQ : E.toAffine.Equation x₀ y₀) (hgy : E.veluGy x₀ y₀ = 0)
    (hΔ : (E.veluQuotient2 x₀ y₀).Δ ≠ 0) (h2' : (2 : K₂) ≠ 0)
    (hQ' : (E.map σ).toAffine.Equation (σ x₀) (σ y₀)) (hgy' : (E.map σ).veluGy (σ x₀) (σ y₀) = 0)
    (hΔ' : ((E.map σ).veluQuotient2 (σ x₀) (σ y₀)).Δ ≠ 0) (P : E.toAffine.Point) :
    PtRel (veluPointMap2 h2' hQ' hgy' hΔ' (pointMapAlong σ E P))
      (pointMapAlong σ _ (veluPointMap2 h2 hQ hgy hΔ P)) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, rfl⟩
  · by_cases hx : x = x₀
    · rw [veluPointMap2_some_of_eq h2 hQ hgy hΔ h hx, pointMapAlong_apply, Point.mapAlong_some,
        veluPointMap2_some_of_eq h2' hQ' hgy' hΔ' _ (by rw [hx])]
      exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, rfl⟩
    · have hx' : σ x ≠ σ x₀ := fun e => hx (σ.injective e)
      rw [veluPointMap2_some_of_ne h2 hQ hgy hΔ h hx, pointMapAlong_apply, Point.mapAlong_some,
        veluPointMap2_some_of_ne h2' hQ' hgy' hΔ' _ hx', pointMapAlong_apply, Point.mapAlong_some]
      exact ptRel_some _ _ (velu2X_map E σ x₀ y₀ x) (velu2Y_map E σ x₀ y₀ x y)

/-- **A formula step commutes with the point maps of `σ`.** For a step `f` over `K₁` with kernel
`⟨c'⟩` and its formula, and a step `F` over `K₂` on `E.map σ` with kernel `⟨σ c'⟩` and its formula,
`F (σ P)` and `σ (f P)` have the same coordinates. -/
theorem stepRel (E : WeierstrassCurve K₁) (c' : E.toAffine.Point) (p : ℕ)
    {V₁ : WeierstrassCurve K₁} {V₂ : WeierstrassCurve K₂}
    (f : E.toAffine.Point →+ V₁.toAffine.Point) (F : (E.map σ).toAffine.Point →+ V₂.toAffine.Point)
    (hf : f.ker = AddSubgroup.zmultiples c')
    (hF : F.ker = AddSubgroup.zmultiples (pointMapAlong σ E c'))
    (hfo : StepFormula E c' p f) (hFo : StepFormula (E.map σ) (pointMapAlong σ E c') p F)
    (P : E.toAffine.Point) :
    PtRel (F (pointMapAlong σ E P)) (pointMapAlong σ V₁ (f P)) := by
  by_cases hP : P ∈ AddSubgroup.zmultiples c'
  · have h0 : f P = 0 := by rw [← AddMonoidHom.mem_ker, hf]; exact hP
    have h0' : F (pointMapAlong σ E P) = 0 := by
      rw [← AddMonoidHom.mem_ker, hF, ← AddMonoidHom.map_zmultiples]
      exact AddSubgroup.mem_map_of_mem _ hP
    rw [h0, h0', (pointMapAlong σ V₁).map_zero]
    exact ptRel_zero
  have hmP : pointMapAlong σ E P ∉ AddSubgroup.zmultiples (pointMapAlong σ E c') := by
    rw [← AddMonoidHom.map_zmultiples]
    rintro ⟨R, hR, hRP⟩
    exact hP (pointMapAlong_injective σ E hRP ▸ hR)
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd (AddSubgroup.zero_mem _) hP
  have hmP' : (Point.some (σ x) (σ y) ((Affine.map_nonsingular _ σ.injective x y).mpr h) :
      (E.map σ).toAffine.Point) ∉ AddSubgroup.zmultiples (pointMapAlong σ E c') := hmP
  by_cases hp2 : p = 2
  · obtain ⟨x₀, y₀, hns, h2, hgy, hΔ, hc', hf2⟩ := hfo.2 hp2
    obtain ⟨x₀', y₀', hns', h2', hgy', hΔ', hc'', hF2⟩ := hFo.2 hp2
    rw [hc', pointMapAlong_apply, Point.mapAlong_some] at hc''
    obtain ⟨rfl, rfl⟩ := (Point.some.inj hc'').imp Eq.symm Eq.symm
    have e1 : PtRel (F (pointMapAlong σ E (.some x y h)))
        (veluPointMap2 h2' hns'.1 hgy' hΔ' (pointMapAlong σ E (.some x y h))) :=
      hF2 _
    have e2 := veluPointMap2_rel σ E h2 hns.1 hgy hΔ h2' hns'.1 hgy' hΔ' (.some x y h)
    have e3 : PtRel (veluPointMap2 h2 hns.1 hgy hΔ (.some x y h)) (f (.some x y h)) :=
      PtRel.symm (hf2 (.some x y h))
    exact e1.trans (e2.trans (PtRel.map σ e3))
  · obtain ⟨hne, hco⟩ := hfo.1 hp2 x y h hP
    obtain ⟨hne', hco'⟩ := hFo.1 hp2 (σ x) (σ y) _ hmP'
    rw [pointMapAlong_apply, Point.mapAlong_some]
    refine ⟨⟨fun e => absurd e hne', fun e => ?_⟩, ?_⟩
    · exact absurd ((pointMapAlong_injective σ V₁) (e.trans (pointMapAlong σ V₁).map_zero.symm))
        hne
    · rw [hco', coordsOrZero_pointMapAlong, hco, oddOrderSummingSet_map]
      simp only [Prod.map_apply]
      rw [veluX_map, veluY_map]

/-- **`FormulaSeam` composites commute with the point maps of `σ`** (up to `PtRel`). -/
theorem formulaSeam_rel {E : WeierstrassCurve K₁} {H : AddSubgroup E.toAffine.Point}
    {c : E.toAffine.Point} {n : ℕ}
    {g : E.toAffine.Point →+ (E.cyclicQuotientCurve H n).toAffine.Point}
    (hg : FormulaSeam E H c n g) :
    ∀ {E₂ : WeierstrassCurve K₂} {H₂ : AddSubgroup E₂.toAffine.Point} {c₂ : E₂.toAffine.Point}
      {G : E₂.toAffine.Point →+ (E₂.cyclicQuotientCurve H₂ n).toAffine.Point},
      FormulaSeam E₂ H₂ c₂ n G → E₂ = E.map σ → PtRel c₂ (pointMapAlong σ E c) →
      ∀ (P₂ : E₂.toAffine.Point) (P : E.toAffine.Point), PtRel P₂ (pointMapAlong σ E P) →
        PtRel (G P₂) (pointMapAlong σ _ (g P)) := by
  induction hg with
  | one E H c hcH hc =>
    intro E₂ H₂ c₂ G hG hE hc₂ P₂ P hP
    cases hG with
    | one =>
      exact (ptRel_pointCast _ P₂).trans (hP.trans (PtRel.map σ (ptRel_pointCast _ P).symm))
    | step _ _ _ _ _ _ hn => omega
  | step E H c n hcH hc hn hE f hker hform hmap g' hg' ih =>
    intro E₂ H₂ c₂ G hG hE₂ hc₂ P₂ P hP
    cases hG with
    | one _ _ _ _ _ => omega
    | step _ _ _ _ hcH₂ hc₂' hn₂ hE₂' F hker₂ hform₂ hmap₂ G' hG' =>
      subst hE₂
      have hcc := hc₂.eq
      subst hcc
      have hPP := hP.eq
      subst hPP
      have hmc : (n / n.minFac) • pointMapAlong σ E c =
          pointMapAlong σ E ((n / n.minFac) • c) := (map_nsmul _ _ _).symm
      rw [hmc] at hker₂ hform₂
      have hs := stepRel σ E ((n / n.minFac) • c) n.minFac f F hker hker₂ hform hform₂
      have hH₂ : H₂ = H.map (pointMapAlong σ E) := by
        rw [hcH₂, hcH, AddMonoidHom.map_zmultiples]
      have hcurve : (E.map σ).stepCurve H₂ n.minFac = (E.stepCurve H n.minFac).map σ := by
        rw [hH₂, ← ptMap_eq_pointMapAlong]
        exact P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.P2MKcCQJbc.stepCurve_map
          σ E H n.minFac
      have key := ih hG' hcurve (hs c) (F (pointMapAlong σ E P)) (f P) (hs P)
      change PtRel (pointCast _ (G' (F (pointMapAlong σ E P))))
        (pointMapAlong σ _ (pointCast _ (g' (f P))))
      exact (ptRel_pointCast _ _).trans (key.trans (PtRel.map σ (ptRel_pointCast _ _).symm))

end Steps

section Item2

variable {N : ℕ} [NeZero N]

open ModelGeneric6 in
/-- `C_Q` of the mapped pair is the image of `C_Q`. -/
theorem smulSubgroup_map {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B) (m : ℕ)
    (C : AddSubgroup A) : smulSubgroup m (C.map φ) = (smulSubgroup m C).map φ := by
  ext y
  simp only [smulSubgroup, AddSubgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨m • a, ⟨a, ha, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨φ a, ⟨a, ha, rfl⟩, by simp⟩

/-- The `Q`-torsion maps onto the `Q`-torsion along a ring isomorphism. -/
theorem torsionBy_map_ringEquiv {K₁ K₂ : Type*} [Field K₁] [Field K₂] [DecidableEq K₁]
    [DecidableEq K₂] (σ : K₁ ≃+* K₂) (E : WeierstrassCurve K₁) (Q : ℕ) :
    (Submodule.torsionBy ℤ (E.map (σ : K₁ →+* K₂)).toAffine.Point (Q : ℤ)).toAddSubgroup =
      (Submodule.torsionBy ℤ E.toAffine.Point (Q : ℤ)).toAddSubgroup.map
        (pointMapAlong (σ : K₁ →+* K₂) E) := by
  ext P₂
  simp only [ModelGeneric6.mem_torsionBy_iff, AddSubgroup.mem_map]
  constructor
  · intro h
    obtain ⟨P, rfl⟩ := Point.mapAlong_surjective (σ : K₁ →+* K₂) (σ : K₁ →+* K₂).injective
      σ.surjective P₂
    refine ⟨P, ?_, rfl⟩
    apply pointMapAlong_injective (σ : K₁ →+* K₂) E
    rw [map_nsmul, map_zero]
    exact h
  · rintro ⟨P, hP, rfl⟩
    rw [← map_nsmul, hP, map_zero]

open ModelGeneric6 ModelGeneric2 in
/-- **Item 2 for formula-carrying seams: the moduli action of `atkinRat` over every algebraically
closed field of characteristic 0 and cardinality `𝔠`.** For a pair `(E, C)` representing
`rationalPoints x`, a generator `c` of `C_Q = (N/Q) • C`, and the R0 seam `g` at `c`
(`FormulaSeam E C_Q c Q g`, kernel `C_Q`), the class `rationalPoints (x ∘ atkinRatAlg)` is the
class of `(E.cyclicQuotientCurve C_Q Q, g(E[Q] ⊔ C))`. Transports the algebraic statement of
`rationalPoints_atkinRat_complex_moduli` along a ring isomorphism `K ≃+* ℂ`. -/
theorem rationalPoints_atkinRat_formulaSeam {K : Type} [Field K] [DecidableEq K] [IsAlgClosed K]
    [CharZero K] (hcard : Cardinal.mk K = Cardinal.continuum) (h₂ : 2 ≤ N)
    {q e Q : ℕ} (hq : q.Prime) (he : 0 < e) (hQe : Q = q ^ e) (hQ : Q ∥ N)
    (x : ModelGeneric.Y0RationalAlgebra h₂ →ₐ[ℚ] K)
    (E : WeierstrassCurve K) [hE : E.IsElliptic] (C : CyclicSubgroups E.toAffine.Point N)
    (hEC : (Quot.mk _ ⟨E, hE, C⟩ : PairClasses K N) = rationalPoints h₂ x)
    (c : E.toAffine.Point) (hcC : smulSubgroup (N / Q) C.1 = AddSubgroup.zmultiples c)
    (hc : addOrderOf c = Q)
    [hE' : (E.cyclicQuotientCurve (smulSubgroup (N / Q) C.1) Q).IsElliptic]
    (g : E.toAffine.Point →+ (E.cyclicQuotientCurve (smulSubgroup (N / Q) C.1) Q).toAffine.Point)
    (hg : g.ker = smulSubgroup (N / Q) C.1)
    (hgF : FormulaSeam E (smulSubgroup (N / Q) C.1) c Q g) :
    rationalPoints h₂ (x.comp (ModelGeneric5.atkinRatAlg h₂ hQ)) =
      Quot.mk _ ⟨_, hE', atkinImage E hq he hQe (Nat.mul_div_cancel' hQ.dvd).symm hQ.coprime
        (Nat.cast_ne_zero.mpr (NeZero.ne N)) two_ne_zero C g hg⟩ := by
  -- A ring isomorphism `K ≃+* ℂ`.
  have hKC : Nonempty (K ≃ ℂ) := Cardinal.eq.1 (hcard.trans Cardinal.mk_complex.symm)
  obtain ⟨σ⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := K) (L := ℂ)
    (by rw [hcard]; exact Cardinal.aleph0_lt_continuum) hKC
  let s : K →+* ℂ := σ
  let m := pointMapAlong s E
  -- The mapped pair represents `rationalPoints (σ ∘ x)`.
  let E₂ := E.map s
  let C₂ : CyclicSubgroups E₂.toAffine.Point N := cyclicMap s E C
  have hEC₂ : (Quot.mk _ ⟨E₂, inferInstance, C₂⟩ : PairClasses ℂ N) =
      rationalPoints h₂ (s.toRatAlgHom.comp x) := by
    rw [rationalPoints_comp h₂ s.toRatAlgHom x, ← hEC]
    rfl
  have hC₂Q : smulSubgroup (N / Q) C₂.1 = (smulSubgroup (N / Q) C.1).map m :=
    smulSubgroup_map m (N / Q) C.1
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hQ.dvd)
  have hmc : addOrderOf (m c) = Q :=
    (addOrderOf_injective m (pointMapAlong_injective s E) c).trans hc
  have hC₂c : smulSubgroup (N / Q) C₂.1 = AddSubgroup.zmultiples (m c) := by
    rw [hC₂Q, hcC, AddMonoidHom.map_zmultiples]
  -- The complex R0 seam at `σ c`.
  obtain ⟨hV₂, ι₂, hι₂, hfin₂, -, G, hGker, hGseam, hGF⟩ :=
    exists_formulaSeam (k := ℂ) Q hQ0 (fun ℓ hℓ _ => Nat.cast_ne_zero.mpr hℓ.ne_zero) E₂
      (smulSubgroup (N / Q) C₂.1) (m c) hC₂c hmc
  haveI := hV₂
  have hcx := rationalPoints_atkinRat_complex_moduli h₂ hq he hQe hQ (s.toRatAlgHom.comp x) E₂ C₂
    hEC₂ ι₂ hι₂ hfin₂ G hGker hGseam
  rw [AlgHom.comp_assoc, rationalPoints_comp h₂ s.toRatAlgHom] at hcx
  apply pairClassesMap_injective σ N
  refine hcx.trans ?_
  rw [pairClassesMap_mk]
  congr 1
  -- The curves: T2.
  have hcurve : E₂.cyclicQuotientCurve (smulSubgroup (N / Q) C₂.1) Q =
      (E.cyclicQuotientCurve (smulSubgroup (N / Q) C.1) Q).map s := by
    rw [hC₂Q]
    exact cyclicQuotientCurve_map s E _ Q
  -- The points: `formulaSeam_rel`.
  have hrel : ∀ P : E.toAffine.Point, pointCast hcurve (G (m P)) =
      pointMapAlong s _ (g P) := by
    intro P
    rw [pointCast_apply]
    exact PtRel.cast_eq hcurve
      (formulaSeam_rel s hgF hGF rfl (PtRel.refl _) (m P) P (PtRel.refl _))
  refine enhancedCurve_eq hcurve fun P => ?_
  rw [← pointCast_apply]
  change P ∈ (atkinSum Q C₂.1).map G ↔
    pointCast hcurve P ∈ ((atkinSum Q C.1).map g).map (pointMapAlong s _)
  have hsum : atkinSum Q C₂.1 = (atkinSum Q C.1).map m := by
    rw [atkinSum, atkinSum, AddSubgroup.map_sup, torsionBy_map_ringEquiv σ E Q]
    rfl
  have hcomp : (pointCast hcurve).comp (G.comp m) = (pointMapAlong s _).comp g :=
    AddMonoidHom.ext hrel
  have hR : ((atkinSum Q C.1).map g).map (pointMapAlong s _) =
      ((atkinSum Q C₂.1).map G).map (pointCast hcurve) := by
    rw [AddSubgroup.map_map, ← hcomp, hsum, AddSubgroup.map_map, AddSubgroup.map_map]
    rfl
  rw [hR, AddSubgroup.mem_map_iff_mem (pointCast_injective hcurve)]

open ModelGeneric6 ModelGeneric2 in
/-- **Independence of the representative and of the generator (corollary).** -/
theorem atkinClass_independent_formulaSeam {K : Type} [Field K] [DecidableEq K] [IsAlgClosed K]
    [CharZero K] (hcard : Cardinal.mk K = Cardinal.continuum) (h₂ : 2 ≤ N)
    {q e Q : ℕ} (hq : q.Prime) (he : 0 < e) (hQe : Q = q ^ e) (hQ : Q ∥ N)
    (x : ModelGeneric.Y0RationalAlgebra h₂ →ₐ[ℚ] K)
    (E₁ : WeierstrassCurve K) [hE₁ : E₁.IsElliptic] (C₁ : CyclicSubgroups E₁.toAffine.Point N)
    (hEC₁ : (Quot.mk _ ⟨E₁, hE₁, C₁⟩ : PairClasses K N) = rationalPoints h₂ x)
    (c₁ : E₁.toAffine.Point) (hcC₁ : smulSubgroup (N / Q) C₁.1 = AddSubgroup.zmultiples c₁)
    (hc₁ : addOrderOf c₁ = Q)
    [hE₁' : (E₁.cyclicQuotientCurve (smulSubgroup (N / Q) C₁.1) Q).IsElliptic]
    (g₁ : E₁.toAffine.Point →+
      (E₁.cyclicQuotientCurve (smulSubgroup (N / Q) C₁.1) Q).toAffine.Point)
    (hg₁ : g₁.ker = smulSubgroup (N / Q) C₁.1)
    (hgF₁ : FormulaSeam E₁ (smulSubgroup (N / Q) C₁.1) c₁ Q g₁)
    (E₂ : WeierstrassCurve K) [hE₂ : E₂.IsElliptic] (C₂ : CyclicSubgroups E₂.toAffine.Point N)
    (hEC₂ : (Quot.mk _ ⟨E₂, hE₂, C₂⟩ : PairClasses K N) = rationalPoints h₂ x)
    (c₂ : E₂.toAffine.Point) (hcC₂ : smulSubgroup (N / Q) C₂.1 = AddSubgroup.zmultiples c₂)
    (hc₂ : addOrderOf c₂ = Q)
    [hE₂' : (E₂.cyclicQuotientCurve (smulSubgroup (N / Q) C₂.1) Q).IsElliptic]
    (g₂ : E₂.toAffine.Point →+
      (E₂.cyclicQuotientCurve (smulSubgroup (N / Q) C₂.1) Q).toAffine.Point)
    (hg₂ : g₂.ker = smulSubgroup (N / Q) C₂.1)
    (hgF₂ : FormulaSeam E₂ (smulSubgroup (N / Q) C₂.1) c₂ Q g₂) :
    (Quot.mk _ ⟨_, hE₁', atkinImage E₁ hq he hQe (Nat.mul_div_cancel' hQ.dvd).symm hQ.coprime
        (Nat.cast_ne_zero.mpr (NeZero.ne N)) two_ne_zero C₁ g₁ hg₁⟩ : PairClasses K N) =
      Quot.mk _ ⟨_, hE₂', atkinImage E₂ hq he hQe (Nat.mul_div_cancel' hQ.dvd).symm hQ.coprime
        (Nat.cast_ne_zero.mpr (NeZero.ne N)) two_ne_zero C₂ g₂ hg₂⟩ := by
  rw [← rationalPoints_atkinRat_formulaSeam hcard h₂ hq he hQe hQ x E₁ C₁ hEC₁ c₁ hcC₁ hc₁ g₁ hg₁
      hgF₁,
    ← rationalPoints_atkinRat_formulaSeam hcard h₂ hq he hQe hQ x E₂ C₂ hEC₂ c₂ hcC₂ hc₂ g₂ hg₂
      hgF₂]

end Item2

end ZInQ.Manuscript.RC.ModelGeneric7

#print axioms ZInQ.Manuscript.RC.ModelGeneric7.veluX_map
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.veluY_map
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.oddOrderSummingSet_map
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.veluPointMap2_rel
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.stepRel
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.formulaSeam_rel
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.torsionBy_map_ringEquiv
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.rationalPoints_atkinRat_formulaSeam
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.atkinClass_independent_formulaSeam

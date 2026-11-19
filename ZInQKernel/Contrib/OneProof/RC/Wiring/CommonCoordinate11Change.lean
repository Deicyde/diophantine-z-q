import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate10Collapse

/-!
# Changing the model changes the Knudsen–Mumford coordinate by the comparison determinant

Manuscript `diophantine_zq.tex`, proof of Lemma `ex:arith-common-coordinate` (tex 4183–4194):

> In the original integral determinant bases, the support triangle therefore gives
> `l_q u_rel = e_q² ε_q u_prim` (4.7). […] To see the unit assertion, retain the finite
> mapping-cone bases. Their comparison is a sign; replacing them by the retained homotopy
> equivalent free models contributes only determinants of unit disks.

The coordinates of the support triangle are Knudsen–Mumford coordinates of models of the actual
complexes, at the transported class `p z` and the transported functional `λ ∘ i` (`primCoord`,
`relCoord`). Over a field this file shows that the coordinate does not depend on the model, up to
the determinant of the induced change of bases of the determinant line, and computes it.

* `retractCmp R₁ R₂ n = p₂ ∘ i₁`: the comparison between two models of one complex `X`; it
  commutes with the differentials (`retractCmp_d`). From `1 − i₁ p₁ = d h₁ + h₁ d`, for a cycle
  `z` and a closed functional `λ`: `p₂ z = (p₂ i₁)(p₁ z) + d (p₂ h₁ z)` (`retract_p_transport`)
  and `λ i₂ = (λ i₁)(p₁ i₂) + (λ h₁ i₂) d` (`retract_lam_transport`).
* **Class transport** (`kmCoord_change_retract`): for two retracts `R₁, R₂` of `X` onto one
  block complex `D`, the coordinate at `(p₂ z, λ ∘ i₂)` equals the coordinate at
  `(g₁ (p₁ z), (λ ∘ i₁) ∘ g₂')` with `g₁ = p₂ i₁`, `g₂' = p₁ i₂`: the two vectors differ by a
  boundary and a coboundary of `D` (`kmCoord_add_boundary`, `kmCoord_add_coboundary`).
* **The minimal model** `minBlock F`: `p₁ i₂ p₂ i₁ = 1` in every degree, because the homotopy
  terms vanish with the differentials of `minBlock F` (`retractCmp_minBlock_inv`). In degrees
  one and two the comparison is multiplication by its H-coefficient (`cmpCoefOne`, `cmpCoefTwo`,
  both nonzero), and **`kmCoord_minBlock_change_retract`**: the coordinate changes by the factor
  `a₁ / a₂`. It is exactly `1` for compatible bases: when `a₁ = a₂`
  (`kmCoord_minBlock_change_retract_eq`), in particular when both retracts induce the same basis
  vectors of the determinant line (`kmCoord_minBlock_change_retract_eq_of_line`).
* **The relaxed (cone) model versus the minimal model.** For the full-condition model
  `relModel` of the relaxed complex built on `D = minBlock F` (old summands `D`, new summands `N`
  with the block `B`, `T = 0`), a model cycle has zero `N`-part (`fullPre_cycle_inr`) and a
  closed model functional has `μ_N = −μ_D Q B⁻¹` (`fullPre_closed_inr`). For any retract `R'` of
  the relaxed complex onto `minBlock F`, **`kmCoord_minBlock_relModel_div`**:
  `u_min = (c₁ / c₂ · det B) · u_cone`, where `c₁, c₂` are the H-coefficients of the comparison
  `p' ∘ i_R` in degrees one and two (`relCoefOne`, `relCoefTwo`, both nonzero). For a support
  triangle with `D = minBlock F` whose new block is the two-place block, `det B = q⁴ l_q`
  (`SupportTriangle.kmCoord_minBlock_relCoord_twoPlace`).

What this shows about tex 4183–4194: the minimal model and the cone model of the relaxed complex
`C_{T ∪ q}` differ by `det B = q⁴ l_q` (times the H-coefficients of the comparison), and `q⁴ l_q`
is not a unit. So the "original integral determinant bases" of (4.7) must be the cone (iterated
mapping-cone) bases, in which the new block is retained, and not minimal-model bases. Between
models related by unit-determinant comparisons (for instance two retracts inducing the same
basis of the determinant line) the coordinate is unchanged.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix Module ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CommonCoordinate (twoPlaceBlock det_twoPlaceBlock)
open ZInQ.Manuscript.RC.Central (quotientFactor quotientDet_eq)

/-! ### Comparing two models of one complex -/

section Transport

variable {F : Type} [Field F] {X Y₁ Y₂ : GCx F}

/-- **The comparison of two models** of one complex `X` (tex 4189–4191, 4423–4437): for retracts
`R₁ : X → Y₁` and `R₂ : X → Y₂`, the map `p₂ ∘ i₁ : Y₁ⁿ → Y₂ⁿ`. Kind: definition. -/
def retractCmp (R₁ : GRetract X Y₁) (R₂ : GRetract X Y₂) (n : ℤ) : Y₁.X n →ₗ[F] Y₂.X n :=
  R₂.p.f n n rfl ∘ₗ R₁.i.f n n rfl

/-- The comparison is `y ↦ p₂ (i₁ y)`. (tex 4189–4191) Kind: PROVED (definitional). -/
theorem retractCmp_apply (R₁ : GRetract X Y₁) (R₂ : GRetract X Y₂) (n : ℤ) (y : Y₁.X n) :
    retractCmp R₁ R₂ n y = R₂.p.f n n rfl (R₁.i.f n n rfl y) :=
  rfl

/-- The comparison commutes with the differentials. (tex 4189–4191, 4423–4437)
Kind: PROVED. -/
theorem retractCmp_d (R₁ : GRetract X Y₁) (R₂ : GRetract X Y₂) (a b : ℤ) (h : a + 1 = b)
    (y : Y₁.X a) : Y₂.d a b h (retractCmp R₁ R₂ a y) = retractCmp R₁ R₂ b (Y₁.d a b h y) := by
  rw [retractCmp_apply, retractCmp_apply, ← GRetract.p_d, ← GRetract.i_d]

/-- **Transport of a cycle between two models** (tex 4189–4191, 4423–4437): for a cycle `z` of
degree one, `p₂ z = (p₂ i₁)(p₁ z) + d (p₂ (h₁ z))`, from `z − i₁ p₁ z = d (h₁ z) + h₁ (d z)` and
`p₂ d = d p₂`. Kind: PROVED. -/
theorem retract_p_transport (R₁ : GRetract X Y₁) (R₂ : GRetract X Y₂) {z : X.X 1}
    (hz : X.d 1 2 rfl z = 0) :
    R₂.p.f 1 1 rfl z = retractCmp R₁ R₂ 1 (R₁.p.f 1 1 rfl z) +
      Y₂.d 0 1 rfl (R₂.p.f 0 0 rfl (R₁.h 1 0 rfl z)) := by
  have e := R₁.homotopy 1 z
  rw [R₁.dh_congr (n := 1) (show (1 : ℤ) - 1 = 0 by norm_num) _ rfl] at e
  have e2 : R₁.h (1 + 1) 1 rfl (X.d 1 (1 + 1) rfl z) = 0 := by
    change R₁.h 2 1 rfl (X.d 1 2 rfl z) = 0
    rw [hz, map_zero]
  rw [e2, add_zero] at e
  have e3 := congrArg (R₂.p.f 1 1 rfl) e
  rw [map_sub, GRetract.p_d] at e3
  rw [retractCmp_apply, ← e3]
  abel

/-- **Transport of a closed functional between two models** (tex 4189–4191, 4423–4437): for a
closed functional `λ` on degree two, `λ (i₂ y) = λ (i₁ (p₁ i₂ y)) + λ (h₁ (i₂ (d y)))`, from
`x − i₁ p₁ x = d (h₁ x) + h₁ (d x)` at `x = i₂ y`, `λ d = 0` and `d i₂ = i₂ d`. Kind: PROVED. -/
theorem retract_lam_transport (R₁ : GRetract X Y₁) (R₂ : GRetract X Y₂) (lam : X.X 2 →ₗ[F] F)
    (hlam : lam ∘ₗ X.d 1 2 rfl = 0) (y : Y₂.X 2) :
    lam (R₂.i.f 2 2 rfl y) = lam (R₁.i.f 2 2 rfl (retractCmp R₂ R₁ 2 y)) +
      lam (R₁.h 3 2 rfl (R₂.i.f 3 3 rfl (Y₂.d 2 3 rfl y))) := by
  have e := R₁.homotopy 2 (R₂.i.f 2 2 rfl y)
  rw [R₁.dh_congr (n := 2) (show (2 : ℤ) - 1 = 1 by norm_num) _ rfl] at e
  have e2 : X.d 2 (2 + 1) rfl (R₂.i.f 2 2 rfl y) = R₂.i.f 3 3 rfl (Y₂.d 2 3 rfl y) :=
    (GRetract.i_d R₂ 2 3 rfl y).symm
  rw [e2] at e
  have e3 := congrArg lam e
  have e4 : lam (X.d 1 2 rfl (R₁.h 2 1 rfl (R₂.i.f 2 2 rfl y))) = 0 :=
    LinearMap.congr_fun hlam _
  rw [map_sub, map_add, e4, zero_add] at e3
  rw [retractCmp_apply]
  exact sub_eq_iff_eq_add'.mp e3

end Transport

/-! ### Class transport on a block-complex model -/

section Block

variable {F : Type} [Field F] {X : GCx F} {D : BlockComplex F}

/-- The transported class `p z` is a cycle of the block model. (tex 4166–4170)
Kind: PROVED. -/
theorem retract_p_one_cycle (R : GRetract X D.toGCx) {z : X.X 1} (hz : X.d 1 2 rfl z = 0) :
    D.toFour.d1 *ᵥ (R.p.f 1 1 rfl z : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → F) = 0 :=
  retract_p_cycle R (rfl : (1 : ℤ) + 1 = 2) hz

/-- The transported functional `λ ∘ i` is closed on the block model. (tex 4166–4172)
Kind: PROVED. -/
theorem retract_funVec_closed (R : GRetract X D.toGCx) (lam : X.X 2 →ₗ[F] F)
    (hlam : lam ∘ₗ X.d 1 2 rfl = 0) :
    funVec (ι := Fin D.m1 ⊕ Unit ⊕ Fin D.m2) (lam ∘ₗ R.i.f 2 2 rfl) ᵥ* D.toFour.d1 = 0 :=
  funVec_vecMul_eq_zero _ D.toFour.d1 (retract_closed_comp_i R (rfl : (1 : ℤ) + 1 = 2) lam hlam)

/-- The comparison `g₁ = p₂ i₁` carries cycles of the block model to cycles.
(tex 4189–4191) Kind: PROVED. -/
theorem retractCmp_one_cycle (R₁ R₂ : GRetract X D.toGCx)
    {y : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → F} (hy : D.toFour.d1 *ᵥ y = 0) :
    D.toFour.d1 *ᵥ (retractCmp R₁ R₂ 1 y : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → F) = 0 := by
  have h := retractCmp_d R₁ R₂ 1 2 rfl y
  have hy' : D.toGCx.d 1 2 rfl y = 0 := hy
  rw [hy', map_zero] at h
  exact h

/-- The functional `(λ ∘ i₁) ∘ g₂'`, `g₂' = p₁ i₂`, is closed on the block model.
(tex 4189–4191) Kind: PROVED. -/
theorem retractCmp_funVec_closed (R₁ R₂ : GRetract X D.toGCx) (lam : X.X 2 →ₗ[F] F)
    (hlam : lam ∘ₗ X.d 1 2 rfl = 0) :
    funVec (ι := Fin D.m1 ⊕ Unit ⊕ Fin D.m2) ((lam ∘ₗ R₁.i.f 2 2 rfl) ∘ₗ retractCmp R₂ R₁ 2) ᵥ*
      D.toFour.d1 = 0 := by
  apply funVec_vecMul_eq_zero _ D.toFour.d1
  apply LinearMap.ext
  intro (y : D.toGCx.X 1)
  change lam (R₁.i.f 2 2 rfl (retractCmp R₂ R₁ 2 (D.toGCx.d 1 2 rfl y))) = 0
  rw [← retractCmp_d]
  exact LinearMap.congr_fun (retract_closed_comp_i R₁ (rfl : (1 : ℤ) + 1 = 2) lam hlam) _

/-- **Class transport between two retracts onto one block complex** (tex 4183–4194, 4189–4191:
"replacing them by the retained homotopy equivalent free models"; tex 3877–3892): for retracts
`R₁, R₂` of `X` onto `D`, a cycle `z` and a closed functional `λ`, and any orientation `σ`, the
Knudsen–Mumford coordinate at `(p₂ z, λ ∘ i₂)` equals the coordinate at
`(g₁ (p₁ z), (λ ∘ i₁) ∘ g₂')`, with `g₁ = p₂ i₁` and `g₂' = p₁ i₂`. Indeed
`p₂ z − g₁ (p₁ z) = d⁰ (p₂ (h₁ z))` (`retract_p_transport`) and
`λ ∘ i₂ − (λ ∘ i₁) ∘ g₂' = μ d²` with `μ` the coordinate vector of `λ ∘ h₁ ∘ i₂`
(`retract_lam_transport`), and the coordinate depends only on the classes
(`kmCoord_add_boundary`, `kmCoord_add_coboundary`). Kind: PROVED. -/
theorem kmCoord_change_retract (R₁ R₂ : GRetract X D.toGCx) {z : X.X 1}
    (hz : X.d 1 2 rfl z = 0) (lam : X.X 2 →ₗ[F] F) (hlam : lam ∘ₗ X.d 1 2 rfl = 0)
    (σ : (Fin D.m0 ⊕ Unit) ⊕ (Fin D.m1 ⊕ Unit ⊕ Fin D.m2) ≃
      (Fin D.m0 ⊕ Unit ⊕ Fin D.m1) ⊕ (Fin D.m2 ⊕ Unit)) :
    kmCoord D.toFour (R₂.p.f 1 1 rfl z)
        (funVec (ι := Fin D.m1 ⊕ Unit ⊕ Fin D.m2) (lam ∘ₗ R₂.i.f 2 2 rfl))
        (retract_p_one_cycle R₂ hz) (retract_funVec_closed R₂ lam hlam) σ =
      kmCoord D.toFour (retractCmp R₁ R₂ 1 (R₁.p.f 1 1 rfl z))
        (funVec (ι := Fin D.m1 ⊕ Unit ⊕ Fin D.m2)
          ((lam ∘ₗ R₁.i.f 2 2 rfl) ∘ₗ retractCmp R₂ R₁ 2))
        (retractCmp_one_cycle R₁ R₂ (retract_p_one_cycle R₁ hz))
        (retractCmp_funVec_closed R₁ R₂ lam hlam) σ := by
  set w : Fin D.m0 → F := R₂.p.f 0 0 rfl (R₁.h 1 0 rfl z) with hw
  set z₁ : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → F := retractCmp R₁ R₂ 1 (R₁.p.f 1 1 rfl z) with hz₁
  set μ : Fin D.m2 → F := funVec (ι := Fin D.m2) (lam ∘ₗ R₁.h 3 2 rfl ∘ₗ R₂.i.f 3 3 rfl)
    with hμ
  have hzv : (R₂.p.f 1 1 rfl z : Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → F) = z₁ + D.toFour.d0 *ᵥ w :=
    retract_p_transport R₁ R₂ hz
  have hlamv : funVec (ι := Fin D.m1 ⊕ Unit ⊕ Fin D.m2) (lam ∘ₗ R₂.i.f 2 2 rfl) =
      funVec (ι := Fin D.m1 ⊕ Unit ⊕ Fin D.m2) ((lam ∘ₗ R₁.i.f 2 2 rfl) ∘ₗ retractCmp R₂ R₁ 2) +
        μ ᵥ* D.toFour.d2 := by
    funext k
    have e := retract_lam_transport R₁ R₂ lam hlam
      (Pi.single k 1 : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → F)
    have e2 := funVec_dotProduct (ι := Fin D.m2) (lam ∘ₗ R₁.h 3 2 rfl ∘ₗ R₂.i.f 3 3 rfl)
      (D.d2 *ᵥ (Pi.single k 1 : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → F))
    rw [dotProduct_mulVec, dotProduct_single, mul_one] at e2
    refine e.trans ?_
    exact congrArg (fun t => lam (R₁.i.f 2 2 rfl (retractCmp R₂ R₁ 2
      (Pi.single k 1 : Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → F))) + t) e2
  have h3 := retractCmp_one_cycle R₁ R₂ (retract_p_one_cycle R₁ hz)
  have h4 := retractCmp_funVec_closed R₁ R₂ lam hlam
  exact (kmCoord_congr D.toFour _ (cycle_add_boundary D.toFour h3 w) _
    (closed_add_coboundary D.toFour h4 μ) hzv hlamv σ).trans
    ((kmCoord_add_coboundary D.toFour (cycle_add_boundary D.toFour h3 w) h4 σ μ).trans
      (kmCoord_add_boundary D.toFour h3 h4 σ w))

end Block

/-! ### The minimal model: the factor of a change of retract -/

section MinChange

variable {F : Type} [Field F] {X : GCx F}

/-- **The determinant line of the minimal model is one-dimensional** (tex 3877–3892, 4636–4640):
every vector on `F^{0 ⊕ 1 ⊕ 0}` is its H-coordinate times the basis vector. Kind: PROVED. -/
theorem minLine_eq (v : Fin 0 ⊕ Unit ⊕ Fin 0 → F) :
    v = v (Sum.inr (Sum.inl ())) • Pi.single (Sum.inr (Sum.inl ())) 1 := by
  funext k
  rcases k with k | (u | k)
  · exact k.elim0
  · cases u
    simp
  · exact k.elim0

/-- **The H-coefficient** of a linear endomorphism `g` of `F^{0 ⊕ 1 ⊕ 0}`: the H-coordinate of
the image of the basis vector (tex 4189–4191: the determinant of the change of bases on the
determinant line). Kind: definition. -/
def minLineCoef (g : (Fin 0 ⊕ Unit ⊕ Fin 0 → F) →ₗ[F] (Fin 0 ⊕ Unit ⊕ Fin 0 → F)) : F :=
  g (Pi.single (Sum.inr (Sum.inl ())) 1) (Sum.inr (Sum.inl ()))

/-- An endomorphism of `F^{0 ⊕ 1 ⊕ 0}` is multiplication by its H-coefficient.
(tex 4189–4191) Kind: PROVED. -/
theorem minLineCoef_apply (g : (Fin 0 ⊕ Unit ⊕ Fin 0 → F) →ₗ[F] (Fin 0 ⊕ Unit ⊕ Fin 0 → F))
    (v : Fin 0 ⊕ Unit ⊕ Fin 0 → F) : g v = minLineCoef g • v := by
  have hv := minLine_eq v
  have hg := minLine_eq (g (Pi.single (Sum.inr (Sum.inl ())) 1))
  rw [hv, map_smul, hg, smul_comm]
  rfl

/-- If `g' ∘ g = 1` on `F^{0 ⊕ 1 ⊕ 0}`, the H-coefficients are inverse to each other.
(tex 4189–4191) Kind: PROVED. -/
theorem minLineCoef_mul_eq_one
    (g g' : (Fin 0 ⊕ Unit ⊕ Fin 0 → F) →ₗ[F] (Fin 0 ⊕ Unit ⊕ Fin 0 → F))
    (h : ∀ v, g' (g v) = v) : minLineCoef g' * minLineCoef g = 1 := by
  have e1 := congrFun (h (Pi.single (Sum.inr (Sum.inl ())) 1)) (Sum.inr (Sum.inl ()))
  rw [minLineCoef_apply g', minLineCoef_apply g] at e1
  simpa using e1

/-- **On the minimal model the comparison is inverted by the comparison back**
(tex 4189–4191, 4423–4437): for a retract `R₁` of `X` onto `minBlock F` and any retract `R₂`,
`p₁ i₂ p₂ i₁ = 1` in every degree. The homotopy terms of `1 − i₂ p₂ = d h₂ + h₂ d` vanish after
`p₁ ( · ) i₁`, since `p₁ d = d p₁`, `d i₁ = i₁ d` and the differentials of `minBlock F` are zero.
With two retracts onto `minBlock F` this gives both `p₁ i₂ p₂ i₁ = 1` and `p₂ i₁ p₁ i₂ = 1`.
Kind: PROVED. -/
theorem retractCmp_minBlock_inv {Y : GCx F} (R₁ : GRetract X (minBlock F).toGCx)
    (R₂ : GRetract X Y) (n : ℤ) (y : (minBlock F).toGCx.X n) :
    retractCmp R₂ R₁ n (retractCmp R₁ R₂ n y) = y := by
  have e := R₂.homotopy n (R₁.i.f n n rfl y)
  have e1 : X.d n (n + 1) rfl (R₁.i.f n n rfl y) = 0 := by
    rw [← GRetract.i_d, minBlock_toGCx_d, map_zero]
  rw [e1, map_zero, add_zero] at e
  have e2 := congrArg (R₁.p.f n n rfl) e
  rw [map_sub, R₁.p_i, GRetract.p_d, minBlock_toGCx_d] at e2
  rw [retractCmp_apply, retractCmp_apply]
  exact (sub_eq_zero.mp e2).symm

/-- **The degree-one coefficient of a change of retract** `a₁ = (g₁ e)_H`, `g₁ = p₂ i₁`, `e` the
basis vector of `H₁` (tex 4189–4191). Kind: definition. -/
def cmpCoefOne (R₁ R₂ : GRetract X (minBlock F).toGCx) : F :=
  minLineCoef (retractCmp R₁ R₂ 1)

/-- **The degree-two coefficient of a change of retract** `a₂ = ((p₂ i₁) e)_H`, `e` the basis
vector of `H₂` (tex 4189–4191). Kind: definition. -/
def cmpCoefTwo (R₁ R₂ : GRetract X (minBlock F).toGCx) : F :=
  minLineCoef (retractCmp R₁ R₂ 2)

/-- `a₁` is the H-coordinate of `p₂ (i₁ e)`. (tex 4189–4191) Kind: PROVED (definitional). -/
theorem cmpCoefOne_eq (R₁ R₂ : GRetract X (minBlock F).toGCx) :
    cmpCoefOne R₁ R₂ = (R₂.p.f 1 1 rfl (R₁.i.f 1 1 rfl
      (Pi.single (Sum.inr (Sum.inl ())) 1 : Fin 0 ⊕ Unit ⊕ Fin 0 → F)) :
        Fin 0 ⊕ Unit ⊕ Fin 0 → F) (Sum.inr (Sum.inl ())) :=
  rfl

/-- `a₂` is the H-coordinate of `p₂ (i₁ e)` in degree two. (tex 4189–4191)
Kind: PROVED (definitional). -/
theorem cmpCoefTwo_eq (R₁ R₂ : GRetract X (minBlock F).toGCx) :
    cmpCoefTwo R₁ R₂ = (R₂.p.f 2 2 rfl (R₁.i.f 2 2 rfl
      (Pi.single (Sum.inr (Sum.inl ())) 1 : Fin 0 ⊕ Unit ⊕ Fin 0 → F)) :
        Fin 0 ⊕ Unit ⊕ Fin 0 → F) (Sum.inr (Sum.inl ())) :=
  rfl

/-- In degree one the comparison `g₁` is multiplication by `a₁`. (tex 4189–4191)
Kind: PROVED. -/
theorem retractCmp_one_smul (R₁ R₂ : GRetract X (minBlock F).toGCx)
    (y : Fin 0 ⊕ Unit ⊕ Fin 0 → F) :
    (retractCmp R₁ R₂ 1 y : Fin 0 ⊕ Unit ⊕ Fin 0 → F) = cmpCoefOne R₁ R₂ • y :=
  minLineCoef_apply _ y

/-- In degree two the comparison `p₂ i₁` is multiplication by `a₂`. (tex 4189–4191)
Kind: PROVED. -/
theorem retractCmp_two_smul (R₁ R₂ : GRetract X (minBlock F).toGCx)
    (y : Fin 0 ⊕ Unit ⊕ Fin 0 → F) :
    (retractCmp R₁ R₂ 2 y : Fin 0 ⊕ Unit ⊕ Fin 0 → F) = cmpCoefTwo R₁ R₂ • y :=
  minLineCoef_apply _ y

/-- The degree-one coefficients of the two comparisons are inverse: `a₁(R₂, R₁) a₁ = 1`.
(tex 4189–4191) Kind: PROVED. -/
theorem cmpCoefOne_mul (R₁ R₂ : GRetract X (minBlock F).toGCx) :
    cmpCoefOne R₂ R₁ * cmpCoefOne R₁ R₂ = 1 :=
  minLineCoef_mul_eq_one _ _ (retractCmp_minBlock_inv R₁ R₂ 1)

/-- The degree-two coefficients of the two comparisons are inverse: `a₂(R₂, R₁) a₂ = 1`.
(tex 4189–4191) Kind: PROVED. -/
theorem cmpCoefTwo_mul (R₁ R₂ : GRetract X (minBlock F).toGCx) :
    cmpCoefTwo R₂ R₁ * cmpCoefTwo R₁ R₂ = 1 :=
  minLineCoef_mul_eq_one _ _ (retractCmp_minBlock_inv R₁ R₂ 2)

/-- `a₁ ≠ 0`. (tex 4189–4191) Kind: PROVED. -/
theorem cmpCoefOne_ne_zero (R₁ R₂ : GRetract X (minBlock F).toGCx) : cmpCoefOne R₁ R₂ ≠ 0 :=
  right_ne_zero_of_mul_eq_one (cmpCoefOne_mul R₁ R₂)

/-- `a₂ ≠ 0`. (tex 4189–4191) Kind: PROVED. -/
theorem cmpCoefTwo_ne_zero (R₁ R₂ : GRetract X (minBlock F).toGCx) : cmpCoefTwo R₁ R₂ ≠ 0 :=
  right_ne_zero_of_mul_eq_one (cmpCoefTwo_mul R₁ R₂)

/-- **`g₂' = p₁ i₂` is multiplication by `a₂⁻¹`** in degree two. (tex 4189–4191)
Kind: PROVED. -/
theorem retractCmp_two_inv_smul (R₁ R₂ : GRetract X (minBlock F).toGCx)
    (y : Fin 0 ⊕ Unit ⊕ Fin 0 → F) :
    (retractCmp R₂ R₁ 2 y : Fin 0 ⊕ Unit ⊕ Fin 0 → F) = (cmpCoefTwo R₁ R₂)⁻¹ • y := by
  rw [← eq_inv_of_mul_eq_one_left (cmpCoefTwo_mul R₁ R₂)]
  exact retractCmp_two_smul R₂ R₁ y

/-- **The coordinate under a change of retract onto the minimal model** (tex 4183–4194,
4189–4191; tex 3877–3892, 4157–4194: the minimal model `F --0--> F`): for retracts `R₁, R₂` of
`X` onto `minBlock F`, a cycle `z`, a closed functional `λ` and any orientation `σ` (e.g.
`σBlock 0 0 0` of `primCoord`),
`kmCoord(p₂ z, λ ∘ i₂) = (a₁ / a₂) · kmCoord(p₁ z, λ ∘ i₁)` with `a₁ = cmpCoefOne R₁ R₂`,
`a₂ = cmpCoefTwo R₁ R₂`: by class transport (`kmCoord_change_retract`) the new vectors are
`a₁ (p₁ z)` and `a₂⁻¹ (λ ∘ i₁)`, and the coordinate is bihomogeneous (`kmCoord_smul_smul`).
Kind: PROVED. -/
theorem kmCoord_minBlock_change_retract (R₁ R₂ : GRetract X (minBlock F).toGCx) {z : X.X 1}
    (hz : X.d 1 2 rfl z = 0) (lam : X.X 2 →ₗ[F] F) (hlam : lam ∘ₗ X.d 1 2 rfl = 0)
    (σ : (Fin (minBlock F).m0 ⊕ Unit) ⊕ (Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2) ≃
      (Fin (minBlock F).m0 ⊕ Unit ⊕ Fin (minBlock F).m1) ⊕ (Fin (minBlock F).m2 ⊕ Unit)) :
    kmCoord (minBlock F).toFour (R₂.p.f 1 1 rfl z)
        (funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
          (lam ∘ₗ R₂.i.f 2 2 rfl))
        (retract_p_one_cycle R₂ hz) (retract_funVec_closed R₂ lam hlam) σ =
      (cmpCoefOne R₁ R₂ / cmpCoefTwo R₁ R₂) *
        kmCoord (minBlock F).toFour (R₁.p.f 1 1 rfl z)
          (funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
            (lam ∘ₗ R₁.i.f 2 2 rfl))
          (retract_p_one_cycle R₁ hz) (retract_funVec_closed R₁ lam hlam) σ := by
  refine (kmCoord_change_retract R₁ R₂ hz lam hlam σ).trans ?_
  have h1 := retractCmp_one_smul R₁ R₂ (R₁.p.f 1 1 rfl z)
  have h2 : funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
        ((lam ∘ₗ R₁.i.f 2 2 rfl) ∘ₗ retractCmp R₂ R₁ 2) =
      cmpCoefTwo R₂ R₁ • funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
        (lam ∘ₗ R₁.i.f 2 2 rfl) := by
    funext k
    have e := retractCmp_two_smul R₂ R₁ (Pi.single k 1)
    exact (congrArg (lam ∘ₗ R₁.i.f 2 2 rfl) e).trans ((lam ∘ₗ R₁.i.f 2 2 rfl).map_smul _ _)
  refine (kmCoord_congr _ _ (cycle_smul _ (retract_p_one_cycle R₁ hz) _) _
    (closed_smul _ (retract_funVec_closed R₁ lam hlam) _) h1 h2 σ).trans ?_
  refine (kmCoord_smul_smul (minBlock F).toFour (retract_p_one_cycle R₁ hz)
    (retract_funVec_closed R₁ lam hlam) σ _ _).trans ?_
  rw [eq_inv_of_mul_eq_one_left (cmpCoefTwo_mul R₁ R₂), div_eq_mul_inv]

/-- **For compatible bases the factor is exactly `1`** (tex 4189–4191: "Their comparison is a
sign; replacing them by the retained homotopy equivalent free models contributes only
determinants of unit disks"): if `a₁ = a₂`, the two retracts give the same coordinate.
Kind: PROVED. -/
theorem kmCoord_minBlock_change_retract_eq (R₁ R₂ : GRetract X (minBlock F).toGCx)
    {z : X.X 1} (hz : X.d 1 2 rfl z = 0) (lam : X.X 2 →ₗ[F] F)
    (hlam : lam ∘ₗ X.d 1 2 rfl = 0)
    (σ : (Fin (minBlock F).m0 ⊕ Unit) ⊕ (Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2) ≃
      (Fin (minBlock F).m0 ⊕ Unit ⊕ Fin (minBlock F).m1) ⊕ (Fin (minBlock F).m2 ⊕ Unit))
    (h : cmpCoefOne R₁ R₂ = cmpCoefTwo R₁ R₂) :
    kmCoord (minBlock F).toFour (R₂.p.f 1 1 rfl z)
        (funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
          (lam ∘ₗ R₂.i.f 2 2 rfl))
        (retract_p_one_cycle R₂ hz) (retract_funVec_closed R₂ lam hlam) σ =
      kmCoord (minBlock F).toFour (R₁.p.f 1 1 rfl z)
        (funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
          (lam ∘ₗ R₁.i.f 2 2 rfl))
        (retract_p_one_cycle R₁ hz) (retract_funVec_closed R₁ lam hlam) σ := by
  refine (kmCoord_minBlock_change_retract R₁ R₂ hz lam hlam σ).trans ?_
  rw [h, div_self (cmpCoefTwo_ne_zero R₁ R₂), one_mul]

/-- If `p₂ (i₁ e₁) = e₁` for the basis vector `e₁` of `H₁`, then `a₁ = 1`. (tex 4189–4191)
Kind: PROVED. -/
theorem cmpCoefOne_eq_one (R₁ R₂ : GRetract X (minBlock F).toGCx)
    (h1 : (R₂.p.f 1 1 rfl (R₁.i.f 1 1 rfl
      (Pi.single (Sum.inr (Sum.inl ())) 1 : Fin 0 ⊕ Unit ⊕ Fin 0 → F)) :
        Fin 0 ⊕ Unit ⊕ Fin 0 → F) = Pi.single (Sum.inr (Sum.inl ())) 1) :
    cmpCoefOne R₁ R₂ = 1 :=
  (cmpCoefOne_eq R₁ R₂).trans ((congrArg (fun v : Fin 0 ⊕ Unit ⊕ Fin 0 → F =>
    v (Sum.inr (Sum.inl ()))) h1).trans (Pi.single_eq_same _ _))

/-- If `p₂ (i₁ e₂) = e₂` for the basis vector `e₂` of `H₂`, then `a₂ = 1`. (tex 4189–4191)
Kind: PROVED. -/
theorem cmpCoefTwo_eq_one (R₁ R₂ : GRetract X (minBlock F).toGCx)
    (h2 : (R₂.p.f 2 2 rfl (R₁.i.f 2 2 rfl
      (Pi.single (Sum.inr (Sum.inl ())) 1 : Fin 0 ⊕ Unit ⊕ Fin 0 → F)) :
        Fin 0 ⊕ Unit ⊕ Fin 0 → F) = Pi.single (Sum.inr (Sum.inl ())) 1) :
    cmpCoefTwo R₁ R₂ = 1 :=
  (cmpCoefTwo_eq R₁ R₂).trans ((congrArg (fun v : Fin 0 ⊕ Unit ⊕ Fin 0 → F =>
    v (Sum.inr (Sum.inl ()))) h2).trans (Pi.single_eq_same _ _))

/-- **Retracts agreeing on the determinant line give the same coordinate** (tex 4189–4191):
if `p₂ i₁` fixes the basis vectors `e₁` of `H₁` and `e₂` of `H₂`, then `a₁ = a₂ = 1` and the
coordinate is unchanged. Kind: PROVED. -/
theorem kmCoord_minBlock_change_retract_eq_of_line (R₁ R₂ : GRetract X (minBlock F).toGCx)
    {z : X.X 1} (hz : X.d 1 2 rfl z = 0) (lam : X.X 2 →ₗ[F] F)
    (hlam : lam ∘ₗ X.d 1 2 rfl = 0)
    (σ : (Fin (minBlock F).m0 ⊕ Unit) ⊕ (Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2) ≃
      (Fin (minBlock F).m0 ⊕ Unit ⊕ Fin (minBlock F).m1) ⊕ (Fin (minBlock F).m2 ⊕ Unit))
    (h1 : (R₂.p.f 1 1 rfl (R₁.i.f 1 1 rfl
      (Pi.single (Sum.inr (Sum.inl ())) 1 : Fin 0 ⊕ Unit ⊕ Fin 0 → F)) :
        Fin 0 ⊕ Unit ⊕ Fin 0 → F) = Pi.single (Sum.inr (Sum.inl ())) 1)
    (h2 : (R₂.p.f 2 2 rfl (R₁.i.f 2 2 rfl
      (Pi.single (Sum.inr (Sum.inl ())) 1 : Fin 0 ⊕ Unit ⊕ Fin 0 → F)) :
        Fin 0 ⊕ Unit ⊕ Fin 0 → F) = Pi.single (Sum.inr (Sum.inl ())) 1) :
    kmCoord (minBlock F).toFour (R₂.p.f 1 1 rfl z)
        (funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
          (lam ∘ₗ R₂.i.f 2 2 rfl))
        (retract_p_one_cycle R₂ hz) (retract_funVec_closed R₂ lam hlam) σ =
      kmCoord (minBlock F).toFour (R₁.p.f 1 1 rfl z)
        (funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
          (lam ∘ₗ R₁.i.f 2 2 rfl))
        (retract_p_one_cycle R₁ hz) (retract_funVec_closed R₁ lam hlam) σ :=
  kmCoord_minBlock_change_retract_eq R₁ R₂ hz lam hlam σ
    ((cmpCoefOne_eq_one R₁ R₂ h1).trans (cmpCoefTwo_eq_one R₁ R₂ h2).symm)

end MinChange

/-! ### The relaxed (cone) model versus the minimal model -/

section Relaxed

variable {F : Type} [Field F]

/-- **A cycle of a full-condition complex with `T = 0` has zero `N`-part** (tex 5398–5424): the
`N`-row of `d¹ z = 0` reads `T z_D + B z_N = 0`, and `B` is invertible. Kind: PROVED. -/
theorem fullPre_cycle_inr {C : FullPreComplex F} (hB : IsUnit C.B.det) (hT : C.T = 0)
    {z : C.D1 ⊕ C.N → F} (hz : C.toFour.d1 *ᵥ z = 0) : z ∘ Sum.inr = 0 := by
  have h2 : C.T *ᵥ (z ∘ Sum.inl) + C.B *ᵥ (z ∘ Sum.inr) = 0 := by
    have h := congrArg (· ∘ Sum.inr) hz
    simp only [FullPreComplex.toFour] at h
    rw [← Sum.elim_comp_inl_inr z, fromBlocks_mulVec] at h
    simpa using h
  rw [hT, zero_mulVec, zero_add] at h2
  have e2 := congrArg (C.B⁻¹ *ᵥ ·) h2
  simpa only [mulVec_mulVec, nonsing_inv_mul _ hB, one_mulVec, mulVec_zero] using e2

/-- **A closed functional of a full-condition complex has `μ_N = −μ_D Q B⁻¹`** (tex 5398–5424):
the `N`-column of `μ d¹ = 0` reads `μ_D Q + μ_N B = 0`. Kind: PROVED. -/
theorem fullPre_closed_inr {C : FullPreComplex F} (hB : IsUnit C.B.det)
    {lam : C.D2 ⊕ C.N → F} (hlam : lam ᵥ* C.toFour.d1 = 0) :
    lam ∘ Sum.inr = -((lam ∘ Sum.inl) ᵥ* (C.Q * C.B⁻¹)) := by
  have hsplit : lam ᵥ* fromBlocks C.P C.Q C.T C.B =
      Sum.elim ((lam ∘ Sum.inl) ᵥ* C.P + (lam ∘ Sum.inr) ᵥ* C.T)
        ((lam ∘ Sum.inl) ᵥ* C.Q + (lam ∘ Sum.inr) ᵥ* C.B) := by
    rw [← Sum.elim_comp_inl_inr lam, vecMul_fromBlocks]
  have h : lam ᵥ* fromBlocks C.P C.Q C.T C.B = 0 := hlam
  rw [hsplit] at h
  have h2 : (lam ∘ Sum.inl) ᵥ* C.Q + (lam ∘ Sum.inr) ᵥ* C.B = 0 := by
    have := congrArg (· ∘ Sum.inr) h
    simpa using this
  have e : (lam ∘ Sum.inr) ᵥ* C.B = -((lam ∘ Sum.inl) ᵥ* C.Q) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h2
  have e2 := congrArg (· ᵥ* C.B⁻¹) e
  simp only [vecMul_vecMul, mul_nonsing_inv _ hB, vecMul_one, neg_vecMul] at e2
  exact e2

/-- **The algebra of the comparison** (tex 4183–4194): from `K₁ = −a b`, `K₂ = δ⁻¹ (−c d)`,
`a = c u`, `d = b v` and `δ ≠ 0`, `v K₁ = (u δ) K₂`. Kind: PROVED. -/
theorem kmCoord_change_alg {a b c d u v δ K₁ K₂ : F} (h1 : K₁ = -(a * b))
    (h2 : K₂ = δ⁻¹ * -(c * d)) (h3 : a = c * u) (h4 : d = b * v) (hδ : δ ≠ 0) :
    v * K₁ = (u * δ) * K₂ := by
  subst h1 h2 h3 h4
  field_simp

/-- Division of the comparison identity by a nonzero coefficient. (tex 4183–4194)
Kind: PROVED. -/
theorem kmCoord_change_div {u v δ K₁ K₂ : F} (h : v * K₁ = (u * δ) * K₂) (hv : v ≠ 0) :
    K₁ = (u / v * δ) * K₂ := by
  calc K₁ = v⁻¹ * (v * K₁) := by rw [← mul_assoc, inv_mul_cancel₀ hv, one_mul]
    _ = v⁻¹ * ((u * δ) * K₂) := by rw [h]
    _ = (u / v * δ) * K₂ := by ring

variable {CP CR : GCx F} (E : SplitInclusion CP CR) (R : GRetract CP (minBlock F).toGCx)
  {Q' : GCx F} (RQ : GRetract E.quotientCx Q') {N : Type} [Fintype N] [DecidableEq N]
  (b1 : Basis N F (Q'.X 1)) (b2 : Basis N F (Q'.X 2))
  (hQ' : ∀ n, n ≠ 1 → n ≠ 2 → Subsingleton (Q'.X n))

/-- **The degree-one coefficient of the comparison of the cone model with a minimal model**
(tex 4183–4194, 5398–5424): for the full-condition model `relModel` of `C_R` on
`D = minBlock F` with its retract `R_R`, and a retract `R'` of `C_R` onto `minBlock F`, the
H-coordinate `c₁` of `p' (i_R e)`, `e` the basis vector of `H₁ ⊂ D¹ ⊕ N`. Kind: definition. -/
def relCoefOne (R' : GRetract CR (minBlock F).toGCx) : F :=
  (R'.p.f 1 1 rfl ((relRetract E R RQ b1 b2 hQ').i.f 1 1 rfl
    (Pi.single (Sum.inl (Sum.inr (Sum.inl ()))) 1 : (Fin 0 ⊕ Unit ⊕ Fin 0) ⊕ N → F)) :
      Fin 0 ⊕ Unit ⊕ Fin 0 → F) (Sum.inr (Sum.inl ()))

/-- **The degree-two coefficient of the comparison of the cone model with a minimal model**
(tex 4183–4194, 5398–5424): the H-coordinate `c₂` of `p' (i_R e)`, `e` the basis vector of
`H₂ ⊂ D² ⊕ N`. Kind: definition. -/
def relCoefTwo (R' : GRetract CR (minBlock F).toGCx) : F :=
  (R'.p.f 2 2 rfl ((relRetract E R RQ b1 b2 hQ').i.f 2 2 rfl
    (Pi.single (Sum.inl (Sum.inr (Sum.inl ()))) 1 : (Fin 0 ⊕ Unit ⊕ Fin 0) ⊕ N → F)) :
      Fin 0 ⊕ Unit ⊕ Fin 0 → F) (Sum.inr (Sum.inl ()))

/-- The transported class `p_R z` is a cycle of the cone model. (tex 4166–4170)
Kind: PROVED. -/
theorem relRetract_p_one_cycle {z : CR.X 1} (hz : CR.d 1 2 rfl z = 0) :
    (relModel E R RQ b1 b2).toFour.d1 *ᵥ
      ((relRetract E R RQ b1 b2 hQ').p.f 1 1 rfl z : (relModel E R RQ b1 b2).D1 ⊕
        (relModel E R RQ b1 b2).N → F) = 0 :=
  retract_p_cycle (relRetract E R RQ b1 b2 hQ') (rfl : (1 : ℤ) + 1 = 2) hz

/-- The transported functional `λ ∘ i_R` is closed on the cone model. (tex 4166–4172)
Kind: PROVED. -/
theorem relRetract_funVec_closed (lam : CR.X 2 →ₗ[F] F) (hlam : lam ∘ₗ CR.d 1 2 rfl = 0) :
    funVec (ι := (relModel E R RQ b1 b2).D2 ⊕ (relModel E R RQ b1 b2).N)
        (lam ∘ₗ (relRetract E R RQ b1 b2 hQ').i.f 2 2 rfl) ᵥ*
      (relModel E R RQ b1 b2).toFour.d1 = 0 :=
  funVec_vecMul_eq_zero _ (relModel E R RQ b1 b2).toFour.d1
    (retract_closed_comp_i (relRetract E R RQ b1 b2 hQ') (rfl : (1 : ℤ) + 1 = 2) lam hlam)

/-- **A cycle of the cone model on `minBlock F` is a multiple of the H-vector** (tex 5398–5424):
its `N`-part vanishes (`T = 0`, `B` invertible) and `D¹ = F^{0 ⊕ 1 ⊕ 0}`. Kind: PROVED. -/
theorem relModel_cycle_eq (hB : IsUnit (relModel E R RQ b1 b2).B.det)
    {v : (Fin 0 ⊕ Unit ⊕ Fin 0) ⊕ N → F} (hv : (relModel E R RQ b1 b2).toFour.d1 *ᵥ v = 0) :
    v = v (Sum.inl (Sum.inr (Sum.inl ()))) • Pi.single (Sum.inl (Sum.inr (Sum.inl ()))) 1 := by
  have hN := fullPre_cycle_inr hB (relModel_P E R RQ b1 b2).2 hv
  funext k
  rcases k with k | k
  · have e := congrFun (minLine_eq (v ∘ Sum.inl)) k
    refine e.trans ?_
    simp [Pi.single_apply]
  · have e : v (Sum.inr k) = 0 := congrFun hN k
    simp [e]

/-- **The class coordinate under the comparison** (tex 4183–4194): for a cycle `z` of `C_R`,
`(p' z)_H = (p_R z)_H · c₁`. Since `d` vanishes on `minBlock F`, `p' z = (p' i_R)(p_R z)`
(`retract_p_transport`), and `p_R z` is a multiple of the H-vector (`relModel_cycle_eq`).
Kind: PROVED. -/
theorem relCoef_cycle (hB : IsUnit (relModel E R RQ b1 b2).B.det)
    (R' : GRetract CR (minBlock F).toGCx) {z : CR.X 1} (hz : CR.d 1 2 rfl z = 0) :
    (R'.p.f 1 1 rfl z : Fin 0 ⊕ Unit ⊕ Fin 0 → F) (Sum.inr (Sum.inl ())) =
      ((relRetract E R RQ b1 b2 hQ').p.f 1 1 rfl z : (Fin 0 ⊕ Unit ⊕ Fin 0) ⊕ N → F)
          (Sum.inl (Sum.inr (Sum.inl ()))) * relCoefOne E R RQ b1 b2 hQ' R' := by
  have hA := retract_p_transport (relRetract E R RQ b1 b2 hQ') R' hz
  rw [minBlock_toGCx_d, add_zero] at hA
  have hv := relModel_cycle_eq E R RQ b1 b2 hB (relRetract_p_one_cycle E R RQ b1 b2 hQ' hz)
  rw [hA, retractCmp_apply]
  refine (congrArg (fun v => (R'.p.f 1 1 rfl ((relRetract E R RQ b1 b2 hQ').i.f 1 1 rfl v) :
    Fin 0 ⊕ Unit ⊕ Fin 0 → F) (Sum.inr (Sum.inl ()))) hv).trans ?_
  exact (congrArg (fun x => (R'.p.f 1 1 rfl x : Fin 0 ⊕ Unit ⊕ Fin 0 → F)
    (Sum.inr (Sum.inl ()))) (((relRetract E R RQ b1 b2 hQ').i.f 1 1 rfl).map_smul _ _)).trans
    (congrFun ((R'.p.f 1 1 rfl).map_smul _ _) _)

/-- **The functional coordinate under the comparison** (tex 4183–4194): for a closed functional
`λ` on `C²_R`, `(λ ∘ i_R)_{H} = (λ ∘ i')_H · c₂`. By `retract_lam_transport` (with the roles of
the retracts exchanged) `λ ∘ i_R = (λ ∘ i') ∘ (p' i_R) + (λ h' i_R) ∘ d²`, the last term vanishes
since the model is zero in degree three, and `p' i_R` maps the H-vector to `c₂` times the
H-vector. Kind: PROVED. -/
theorem relCoef_closed (R' : GRetract CR (minBlock F).toGCx) (lam : CR.X 2 →ₗ[F] F)
    (hlam : lam ∘ₗ CR.d 1 2 rfl = 0) :
    funVec (ι := (relModel E R RQ b1 b2).D2 ⊕ (relModel E R RQ b1 b2).N)
        (lam ∘ₗ (relRetract E R RQ b1 b2 hQ').i.f 2 2 rfl) (Sum.inl (Sum.inr (Sum.inl ()))) =
      funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2) (lam ∘ₗ R'.i.f 2 2 rfl)
          (Sum.inr (Sum.inl ())) * relCoefTwo E R RQ b1 b2 hQ' R' := by
  have e := retract_lam_transport R' (relRetract E R RQ b1 b2 hQ') lam hlam
    (Pi.single (Sum.inl (Sum.inr (Sum.inl ()))) 1 : (Fin 0 ⊕ Unit ⊕ Fin 0) ⊕ N → F)
  have : Subsingleton ((relModel E R RQ b1 b2).toGCx.X 3) :=
    inferInstanceAs (Subsingleton (Fin 0 → F))
  have h0 : (relModel E R RQ b1 b2).toGCx.d 2 3 rfl
      (Pi.single (Sum.inl (Sum.inr (Sum.inl ()))) 1 : (Fin 0 ⊕ Unit ⊕ Fin 0) ⊕ N → F) = 0 :=
    Subsingleton.elim _ _
  rw [h0, map_zero, map_zero, map_zero, add_zero] at e
  have hm := minLine_eq (retractCmp (relRetract E R RQ b1 b2 hQ') R' 2
    (Pi.single (Sum.inl (Sum.inr (Sum.inl ()))) 1 : (Fin 0 ⊕ Unit ⊕ Fin 0) ⊕ N → F) :
      Fin 0 ⊕ Unit ⊕ Fin 0 → F)
  refine e.trans ?_
  exact (congrArg (lam ∘ₗ R'.i.f 2 2 rfl) hm).trans
    (((lam ∘ₗ R'.i.f 2 2 rfl).map_smul _ _).trans (mul_comm _ _))

/-- **The coordinate of the cone model on `minBlock F`** (tex 5509–5516, 5577–5595): for a
cycle `v` and a closed functional `w` of `relModel`,
`kmCoord(relModel, v, w) = det(B)⁻¹ · (−v_H w_H)`: cancelling the block divides by `det B`
(`kmCoord_fullCancel`), the cancelled model is `minBlock F` (`cancel_relModel_toFour`), and
there the coordinate is `−v_H w_H` (`kmCoord_minBlock`). Kind: PROVED. -/
theorem kmCoord_relModel_eq (hB : IsUnit (relModel E R RQ b1 b2).B.det)
    {v : (relModel E R RQ b1 b2).D1 ⊕ (relModel E R RQ b1 b2).N → F}
    {w : (relModel E R RQ b1 b2).D2 ⊕ (relModel E R RQ b1 b2).N → F}
    (hv : (relModel E R RQ b1 b2).toFour.d1 *ᵥ v = 0)
    (hw : w ᵥ* (relModel E R RQ b1 b2).toFour.d1 = 0) :
    kmCoord (relModel E R RQ b1 b2).toFour v w hv hw
        (σFull (relModel E R RQ b1 b2).m0 (relModel E R RQ b1 b2).m1 (relModel E R RQ b1 b2).m2
          (relModel E R RQ b1 b2).N) =
      ((relModel E R RQ b1 b2).B.det)⁻¹ *
        -(v (Sum.inl (Sum.inr (Sum.inl ()))) * w (Sum.inl (Sum.inr (Sum.inl ())))) := by
  refine (kmCoord_fullCancel hB (z := v) (lam := w) (hz := hv) (hlam := hw)).trans ?_
  have h4 := cancel_relModel_toFour E R RQ b1 b2 hB
  have key : ∀ (h1 : ((relModel E R RQ b1 b2).cancel hB).toFour.d1 *ᵥ (v ∘ Sum.inl) = 0)
      (h2 : (w ∘ Sum.inl) ᵥ* ((relModel E R RQ b1 b2).cancel hB).toFour.d1 = 0),
      kmCoord ((relModel E R RQ b1 b2).cancel hB).toFour (v ∘ Sum.inl) (w ∘ Sum.inl) h1 h2
          (σBlock (relModel E R RQ b1 b2).m0 (relModel E R RQ b1 b2).m1
            (relModel E R RQ b1 b2).m2) =
        -((v ∘ Sum.inl) (Sum.inr (Sum.inl ())) * (w ∘ Sum.inl) (Sum.inr (Sum.inl ()))) := by
    rw [h4]
    intro h1 h2
    exact kmCoord_minBlock _ _ h1 h2
  exact congrArg (fun t => ((relModel E R RQ b1 b2).B.det)⁻¹ * t) (key _ _)

/-- **Minimal model versus cone model, undivided form** (tex 4183–4194, 4189–4191): for the cone
model `relModel` of `C_R` on `D = minBlock F` with `B` invertible, a retract `R'` of `C_R` onto
`minBlock F`, a cycle `z` and a closed functional `λ`,
`c₂ · u_min = (c₁ · det B) · u_cone`, where `u_min = kmCoord(minBlock F, p' z, λ ∘ i')`,
`u_cone = kmCoord(relModel, p_R z, λ ∘ i_R)` and `c₁, c₂` are the H-coefficients of `p' ∘ i_R`
(`relCoefOne`, `relCoefTwo`). Kind: PROVED. -/
theorem kmCoord_minBlock_relModel (hB : IsUnit (relModel E R RQ b1 b2).B.det)
    (R' : GRetract CR (minBlock F).toGCx) {z : CR.X 1} (hz : CR.d 1 2 rfl z = 0)
    (lam : CR.X 2 →ₗ[F] F) (hlam : lam ∘ₗ CR.d 1 2 rfl = 0) :
    relCoefTwo E R RQ b1 b2 hQ' R' *
        kmCoord (minBlock F).toFour (R'.p.f 1 1 rfl z)
          (funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
            (lam ∘ₗ R'.i.f 2 2 rfl))
          (retract_p_one_cycle R' hz) (retract_funVec_closed R' lam hlam)
          (σBlock (minBlock F).m0 (minBlock F).m1 (minBlock F).m2) =
      (relCoefOne E R RQ b1 b2 hQ' R' * (relModel E R RQ b1 b2).B.det) *
        kmCoord (relModel E R RQ b1 b2).toFour ((relRetract E R RQ b1 b2 hQ').p.f 1 1 rfl z)
          (funVec (ι := (relModel E R RQ b1 b2).D2 ⊕ (relModel E R RQ b1 b2).N)
            (lam ∘ₗ (relRetract E R RQ b1 b2 hQ').i.f 2 2 rfl))
          (relRetract_p_one_cycle E R RQ b1 b2 hQ' hz)
          (relRetract_funVec_closed E R RQ b1 b2 hQ' lam hlam)
          (σFull (relModel E R RQ b1 b2).m0 (relModel E R RQ b1 b2).m1
            (relModel E R RQ b1 b2).m2 (relModel E R RQ b1 b2).N) :=
  kmCoord_change_alg (kmCoord_minBlock _ _ _ _) (kmCoord_relModel_eq E R RQ b1 b2 hB _ _)
    (relCoef_cycle E R RQ b1 b2 hQ' hB R' hz) (relCoef_closed E R RQ b1 b2 hQ' R' lam hlam)
    hB.ne_zero

/-- `c₁ ≠ 0`: at the cycle `z = i' e` (`e` the basis vector of `H₁`) the class coordinate
`(p' z)_H = 1` equals `(p_R z)_H · c₁` (`relCoef_cycle`). (tex 4183–4194) Kind: PROVED. -/
theorem relCoefOne_ne_zero (hB : IsUnit (relModel E R RQ b1 b2).B.det)
    (R' : GRetract CR (minBlock F).toGCx) : relCoefOne E R RQ b1 b2 hQ' R' ≠ 0 := by
  intro h0
  obtain ⟨e, he⟩ : ∃ e : (minBlock F).toGCx.X 1,
      e = (Pi.single (Sum.inr (Sum.inl ())) 1 : Fin 0 ⊕ Unit ⊕ Fin 0 → F) := ⟨_, rfl⟩
  have hz : CR.d 1 2 rfl (R'.i.f 1 1 rfl e) = 0 := by
    rw [← GRetract.i_d, minBlock_toGCx_d, map_zero]
  have h := relCoef_cycle E R RQ b1 b2 hQ' hB R' hz
  rw [h0, mul_zero] at h
  have h1 := congrArg (fun v : Fin 0 ⊕ Unit ⊕ Fin 0 → F => v (Sum.inr (Sum.inl ())))
    ((R'.p_i 1 e).trans he)
  exact one_ne_zero ((Pi.single_eq_same _ _).symm.trans (h1.symm.trans h))

/-- `c₂ ≠ 0`: the functional `ℓ = (p' i_R ·)_H` on `C²` of the cone model is closed, so its
`N`-part is `−ℓ_D Q B⁻¹` (`fullPre_closed_inr`) and `ℓ_D = c₂ e`; if `c₂ = 0` then `ℓ = 0`, but
`ℓ (p_R i' e) = e_H = 1` (`retractCmp_minBlock_inv`). (tex 4183–4194) Kind: PROVED. -/
theorem relCoefTwo_ne_zero (hB : IsUnit (relModel E R RQ b1 b2).B.det)
    (R' : GRetract CR (minBlock F).toGCx) : relCoefTwo E R RQ b1 b2 hQ' R' ≠ 0 := by
  intro h0
  let ℓ : ((relModel E R RQ b1 b2).D2 ⊕ (relModel E R RQ b1 b2).N → F) →ₗ[F] F :=
    (LinearMap.proj (Sum.inr (Sum.inl ())) : (Fin 0 ⊕ Unit ⊕ Fin 0 → F) →ₗ[F] F) ∘ₗ
      retractCmp (relRetract E R RQ b1 b2 hQ') R' 2
  have hcl : funVec ℓ ᵥ* (relModel E R RQ b1 b2).toFour.d1 = 0 := by
    apply funVec_vecMul_eq_zero ℓ
    apply LinearMap.ext
    intro (x : (relModel E R RQ b1 b2).toGCx.X 1)
    change (retractCmp (relRetract E R RQ b1 b2 hQ') R' 2
      ((relModel E R RQ b1 b2).toGCx.d 1 2 rfl x) : Fin 0 ⊕ Unit ⊕ Fin 0 → F)
        (Sum.inr (Sum.inl ())) = 0
    rw [← retractCmp_d, minBlock_toGCx_d]
    rfl
  have hN := fullPre_closed_inr hB hcl
  have hl : funVec ℓ ∘ Sum.inl = 0 := by
    funext k
    rcases k with k | (u | k)
    · exact k.elim0
    · exact h0
    · exact k.elim0
  rw [hl, zero_vecMul, neg_zero] at hN
  have hz : funVec ℓ = 0 := by
    funext k
    rcases k with k | k
    · exact congrFun hl k
    · exact congrFun hN k
  obtain ⟨e, he⟩ : ∃ e : (minBlock F).toGCx.X 2,
      e = (Pi.single (Sum.inr (Sum.inl ())) 1 : Fin 0 ⊕ Unit ⊕ Fin 0 → F) := ⟨_, rfl⟩
  have hinv := retractCmp_minBlock_inv R' (relRetract E R RQ b1 b2 hQ') 2 e
  have e1 := funVec_dotProduct ℓ (retractCmp R' (relRetract E R RQ b1 b2 hQ') 2 e)
  rw [hz] at e1
  have e2 : ℓ (retractCmp R' (relRetract E R RQ b1 b2 hQ') 2 e) = 1 := by
    have h1 := congrArg (fun v : Fin 0 ⊕ Unit ⊕ Fin 0 → F => v (Sum.inr (Sum.inl ())))
      (hinv.trans he)
    exact h1.trans (Pi.single_eq_same _ _)
  exact one_ne_zero (e2.symm.trans (e1.trans (zero_dotProduct _)))

/-- **Minimal model versus cone model** (tex 4183–4194, 4189–4191; the support triangle of
Lemma `ex:arith-common-coordinate`, tex 4157–4194): for the cone model `relModel` of the relaxed
complex `C_R` on `D = minBlock F` with `B` invertible, a retract `R'` of `C_R` onto
`minBlock F`, a cycle `z` and a closed functional `λ`,
`u_min = (c · det B) · u_cone` with `c = c₁ / c₂` the ratio of the H-coefficients of the
comparison `p' ∘ i_R` in degrees one and two (`relCoefOne`, `relCoefTwo`, both nonzero).
So the minimal model differs from the cone model by `det B`, times the comparison factor. When
the new block is the two-place block, `det B = q⁴ l_q` is not a unit
(`SupportTriangle.kmCoord_minBlock_relCoord_twoPlace`), so the "original integral determinant
bases" of (4.7) are the cone bases, not minimal ones. Kind: PROVED. -/
theorem kmCoord_minBlock_relModel_div (hB : IsUnit (relModel E R RQ b1 b2).B.det)
    (R' : GRetract CR (minBlock F).toGCx) {z : CR.X 1} (hz : CR.d 1 2 rfl z = 0)
    (lam : CR.X 2 →ₗ[F] F) (hlam : lam ∘ₗ CR.d 1 2 rfl = 0) :
    kmCoord (minBlock F).toFour (R'.p.f 1 1 rfl z)
        (funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
          (lam ∘ₗ R'.i.f 2 2 rfl))
        (retract_p_one_cycle R' hz) (retract_funVec_closed R' lam hlam)
        (σBlock (minBlock F).m0 (minBlock F).m1 (minBlock F).m2) =
      (relCoefOne E R RQ b1 b2 hQ' R' / relCoefTwo E R RQ b1 b2 hQ' R' *
          (relModel E R RQ b1 b2).B.det) *
        kmCoord (relModel E R RQ b1 b2).toFour ((relRetract E R RQ b1 b2 hQ').p.f 1 1 rfl z)
          (funVec (ι := (relModel E R RQ b1 b2).D2 ⊕ (relModel E R RQ b1 b2).N)
            (lam ∘ₗ (relRetract E R RQ b1 b2 hQ').i.f 2 2 rfl))
          (relRetract_p_one_cycle E R RQ b1 b2 hQ' hz)
          (relRetract_funVec_closed E R RQ b1 b2 hQ' lam hlam)
          (σFull (relModel E R RQ b1 b2).m0 (relModel E R RQ b1 b2).m1
            (relModel E R RQ b1 b2).m2 (relModel E R RQ b1 b2).N) :=
  kmCoord_change_div (kmCoord_minBlock_relModel E R RQ b1 b2 hQ' hB R' hz lam hlam)
    (relCoefTwo_ne_zero E R RQ b1 b2 hQ' hB R')

end Relaxed

/-! ### The support triangle with a minimal primitive model -/

namespace SupportTriangle

variable {F : Type} [Field F] (S : SupportTriangle F)

/-- The degree-one H-coefficient of the comparison `p' ∘ i_R` between the cone model of `C_R`
and a retract `R'` of `C_R` onto `minBlock F` (tex 4183–4194). Kind: definition. -/
def minCoefOne (R' : GRetract S.CR (minBlock F).toGCx) : F :=
  (R'.p.f 1 1 rfl (S.retract.i.f 1 1 rfl
    (Pi.single (Sum.inl (Sum.inr (Sum.inl ()))) 1 : S.model.D1 ⊕ S.model.N → F)) :
      Fin 0 ⊕ Unit ⊕ Fin 0 → F) (Sum.inr (Sum.inl ()))

/-- The degree-two H-coefficient of the comparison `p' ∘ i_R` (tex 4183–4194).
Kind: definition. -/
def minCoefTwo (R' : GRetract S.CR (minBlock F).toGCx) : F :=
  (R'.p.f 2 2 rfl (S.retract.i.f 2 2 rfl
    (Pi.single (Sum.inl (Sum.inr (Sum.inl ()))) 1 : S.model.D2 ⊕ S.model.N → F)) :
      Fin 0 ⊕ Unit ⊕ Fin 0 → F) (Sum.inr (Sum.inl ()))

/-- **Minimal model versus cone model for a support triangle** (tex 4183–4194, 4189–4191): if
the primitive model is the minimal model (`S.D = minBlock F`) and `B` is invertible, then for
every retract `R'` of `C_R` onto `minBlock F`, cycle `z` and closed functional `λ`,
`u_min = (c₁ / c₂ · det B) · u_cone`, with `u_cone` the coordinate of the model `S.model` used
by `relCoord` (`kmCoord_minBlock_relModel_div`). Kind: PROVED. -/
theorem kmCoord_minBlock_model (hD : S.D = minBlock F) (hB : IsUnit S.model.B.det)
    (R' : GRetract S.CR (minBlock F).toGCx) {z : S.CR.X 1} (hz : S.CR.d 1 2 rfl z = 0)
    (lam : S.CR.X 2 →ₗ[F] F) (hlam : lam ∘ₗ S.CR.d 1 2 rfl = 0) :
    kmCoord (minBlock F).toFour (R'.p.f 1 1 rfl z)
        (funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
          (lam ∘ₗ R'.i.f 2 2 rfl))
        (retract_p_one_cycle R' hz) (retract_funVec_closed R' lam hlam)
        (σBlock (minBlock F).m0 (minBlock F).m1 (minBlock F).m2) =
      (S.minCoefOne R' / S.minCoefTwo R' * S.model.B.det) *
        kmCoord S.model.toFour (S.retract.p.f 1 1 rfl z)
          (funVec (ι := S.model.D2 ⊕ S.model.N) (lam ∘ₗ S.retract.i.f 2 2 rfl))
          (retract_p_cycle S.retract (rfl : (1 : ℤ) + 1 = 2) hz)
          (funVec_vecMul_eq_zero _ S.model.toFour.d1
            (retract_closed_comp_i S.retract (rfl : (1 : ℤ) + 1 = 2) lam hlam))
          (σFull S.model.m0 S.model.m1 S.model.m2 S.model.N) := by
  cases S
  subst hD
  exact kmCoord_minBlock_relModel_div _ _ _ _ _ _ hB R' hz lam hlam

/-- **At the actual cycle and functional the cone coordinate is `relCoord`** (tex 4183–4194):
with `S.D = minBlock F` and `B` invertible,
`kmCoord(minBlock F, p' z_R, λ_R ∘ i') = (c₁ / c₂ · det B) · u_rel`. Kind: PROVED. -/
theorem kmCoord_minBlock_relCoord (hD : S.D = minBlock F) (hB : IsUnit S.model.B.det)
    (R' : GRetract S.CR (minBlock F).toGCx) :
    kmCoord (minBlock F).toFour (R'.p.f 1 1 rfl S.zR)
        (funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
          (S.lamR ∘ₗ R'.i.f 2 2 rfl))
        (retract_p_one_cycle R' S.hzR) (retract_funVec_closed R' S.lamR S.hlamR)
        (σBlock (minBlock F).m0 (minBlock F).m1 (minBlock F).m2) =
      (S.minCoefOne R' / S.minCoefTwo R' * S.model.B.det) * S.relCoord :=
  S.kmCoord_minBlock_model hD hB R' S.hzR S.lamR S.hlamR

/-- **The determinant of the new block of the model is `q⁴ l_q`** (tex 4180–4182) when the matrix
of `d_{Q'}` is the two-place block `diag(z Fr_q − q, z⁻¹ Fr_q − q)` up to relabelling.
Kind: PROVED. -/
theorem model_det_eq {Fr : Matrix (Fin 2) (Fin 2) F} {q qi a zq zqi : F}
    (hq : q * qi = 1) (ha : Fr.trace = a) (hd : Fr.det = q) (e : S.N ≃ Fin 2 ⊕ Fin 2)
    (he : LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) =
      (twoPlaceBlock Fr q zq zqi).submatrix e e) :
    S.model.B.det = q ^ 4 * quotientFactor Fr qi zq zqi := by
  have h1 : S.model.B.det = ((twoPlaceBlock Fr q zq zqi).submatrix e e).det :=
    congrArg Matrix.det ((relModel_B S.E S.R S.RQ S.b1 S.b2).trans he)
  rw [h1, det_submatrix_equiv_self, det_twoPlaceBlock, quotientDet_eq zq zqi hq ha hd]

/-- **The minimal model differs from the cone model by `q⁴ l_q`** (tex 4180–4194): for a support
triangle with minimal primitive model (`S.D = minBlock F`) whose new block is the two-place
block, with `l_q ≠ 0`, and any retract `R'` of `C_R` onto `minBlock F`,
`kmCoord(minBlock F, p' z_R, λ_R ∘ i') = (c₁ / c₂ · q⁴ l_q) · u_rel`. Since `q⁴ l_q` is not a
unit of `Λ`, the integral determinant bases of (4.7) must be the cone (iterated mapping-cone)
bases, in which the new block is kept, and not those of a minimal model. Kind: PROVED. -/
theorem kmCoord_minBlock_relCoord_twoPlace (hD : S.D = minBlock F)
    {Fr : Matrix (Fin 2) (Fin 2) F} {q qi a zq zqi : F} (hq : q * qi = 1) (ha : Fr.trace = a)
    (hd : Fr.det = q) (hl : quotientFactor Fr qi zq zqi ≠ 0) (e : S.N ≃ Fin 2 ⊕ Fin 2)
    (he : LinearMap.toMatrix S.b1 S.b2 (S.Q'.d 1 2 rfl) =
      (twoPlaceBlock Fr q zq zqi).submatrix e e)
    (R' : GRetract S.CR (minBlock F).toGCx) :
    kmCoord (minBlock F).toFour (R'.p.f 1 1 rfl S.zR)
        (funVec (ι := Fin (minBlock F).m1 ⊕ Unit ⊕ Fin (minBlock F).m2)
          (S.lamR ∘ₗ R'.i.f 2 2 rfl))
        (retract_p_one_cycle R' S.hzR) (retract_funVec_closed R' S.lamR S.hlamR)
        (σBlock (minBlock F).m0 (minBlock F).m1 (minBlock F).m2) =
      (S.minCoefOne R' / S.minCoefTwo R' * (q ^ 4 * quotientFactor Fr qi zq zqi)) *
        S.relCoord := by
  rw [← S.model_det_eq hq ha hd e he]
  exact S.kmCoord_minBlock_relCoord hD (S.isUnit_relModel_det hq ha hd hl e he) R'

end SupportTriangle

end ZInQ.Manuscript.RC.Wiring

import Mathlib

/-!
# Lane RC16: derivative local conditions and the determinant-preserving switch

This file formalizes, as linear algebra over a field `K` (the "stated fraction or test field" of
the manuscript), the lemma `ex:limits-derivative-switch`
("Derivative local conditions and determinant-preserving switch", manuscript lines 4833-4907),
including the gap B2-a (the equal-valuation claim, lines 4900-4906) of the step-by-step check.

* Part 1 (lines 4834-4842, 4853-4874): the graded local model
  `L_v = D⁰ ⊕ (F_v ⊕ S_v)[-1] ⊕ D²[-2]` with zero differential, the four local conditions
  `U_str, U_rel, U_F, U_S`, and their orthogonals: `derivative_conditions_orthogonal`
  (with `planePairing_eq_of_isotropic`, `derivative_conditions_nested`).
* Part 2 (lines 4888-4898): the switch at a new inert prime, with `T = K²`, the Weil pairing
  `e₂ = det`, and the cross pairing `β(x,y) = ε e₂(x, J y)`: `switch_pair_orthogonal`,
  `lagrangian_finrank_eq_two`, `relaxed_image_eq_span`, `span_pair_orthogonal_eq`,
  `relaxed_image_inf_singPlane`, `switch_new_H1_spanned`, `switch_new_H1_spanned_of_loc`.
* Part 3 (lines 4900-4906, gap B2-a): the finite and singular determinant exact sequences
  (`ker_bdryF`, `range_bdryF`, `ker_bdryS`, `range_bdryS`) and their class-functional
  coordinates `coordF`, `coordS`: `switch_coord_indep_F`, `switch_coord_indep_S`,
  `switch_exists_admissible_F`, `switch_exists_admissible_S`, `switch_coord_relation`,
  `switch_equal_valuation`, `switch_integral_complement_not_unit`,
  `switch_unit_complement_fractional`.
* Non-vacuity examples for each part.

Everything is `PROVED` (Lean proof) except the inputs that are modelling choices, recorded as
`GLUE` in the docstrings (the duality `H²(C_str) ≅ H¹(C_rel)^∨` of Nekovář, Sections 6.3.3-6.3.4,
and the identification of the relaxed localization image with its exact annihilator, which enters
as the hypothesis `U = U^⊥`).
-/

namespace ZInQ.Manuscript.RC.Uniform

open Module
open scoped Matrix

noncomputable section

/-! ## Part 1. The graded local model and the four derivative conditions -/

section LocalModel

variable {K : Type*} [Field K]
variable {D0 F S D2 L1 : Type*} [AddCommGroup D0] [Module K D0] [AddCommGroup F] [Module K F]
  [AddCommGroup S] [Module K S] [AddCommGroup D2] [Module K D2] [AddCommGroup L1] [Module K L1]

/-- The degree-one part of the transported local pairing on `F_v ⊕ S_v` (manuscript lines
4859-4863, 4888-4890): from the cross pairing `β : F_v × S_v → K` and a sign `σ`,
`⟨(x,y),(x',y')⟩ = β(x,y') + σ β(x',y)`.
The planes `F_v ⊕ 0` and `0 ⊕ S_v` are isotropic by construction. The manuscript's pairing is the
symmetric one, `σ = 1` (lines 5035-5054: "symmetric hyperbolic planes"); `σ` is kept general.
`PROVED` (definition). -/
def planePairing (β : F →ₗ[K] S →ₗ[K] K) (σ : K) : LinearMap.BilinForm K (F × S) :=
  β.compl₁₂ (LinearMap.fst K F S) (LinearMap.snd K F S) +
    σ • (β.compl₁₂ (LinearMap.fst K F S) (LinearMap.snd K F S)).flip

@[simp] theorem planePairing_apply (β : F →ₗ[K] S →ₗ[K] K) (σ : K) (a b : F × S) :
    planePairing β σ a b = β a.1 b.2 + σ * β b.1 a.2 := by
  simp [planePairing]

/-- `planePairing` is no loss of generality: every bilinear form on `F_v ⊕ S_v` for which both
planes are isotropic and which is graded-symmetric up to the sign `σ` (`⟨b, a⟩ = σ ⟨a, b⟩`) equals
`planePairing β σ`, with `β(x, y) = ⟨(x,0), (0,y)⟩` its cross pairing. `PROVED`. -/
theorem planePairing_eq_of_isotropic (P : LinearMap.BilinForm K (F × S)) (σ : K)
    (hF : ∀ x x' : F, P (x, 0) (x', 0) = 0) (hS : ∀ y y' : S, P (0, y) (0, y') = 0)
    (hσ : ∀ a b, P b a = σ * P a b) :
    P = planePairing (P.compl₁₂ (LinearMap.inl K F S) (LinearMap.inr K F S)) σ := by
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  obtain ⟨x, y⟩ := a
  obtain ⟨x', y'⟩ := b
  rw [planePairing_apply]
  simp only [LinearMap.compl₁₂_apply, LinearMap.inl_apply, LinearMap.inr_apply]
  have ha : ((x, y) : F × S) = (x, 0) + (0, y) := by simp
  have hb : ((x', y') : F × S) = (x', 0) + (0, y') := by simp
  conv_lhs => rw [ha, hb]
  simp only [map_add, LinearMap.add_apply, hF, hS, hσ (x', 0) (0, y)]
  ring

variable (K F S) in
/-- The finite plane `F_v = F_v ⊕ 0` inside `F_v ⊕ S_v`. -/
def finPlane : Submodule K (F × S) := Submodule.prod ⊤ ⊥

variable (K F S) in
/-- The singular plane `S_v = 0 ⊕ S_v` inside `F_v ⊕ S_v`. -/
def singPlane : Submodule K (F × S) := Submodule.prod ⊥ ⊤

theorem mem_finPlane {z : F × S} : z ∈ finPlane K F S ↔ z.2 = 0 := by
  simp [finPlane, Submodule.mem_prod]

theorem mem_singPlane {z : F × S} : z ∈ singPlane K F S ↔ z.1 = 0 := by
  simp [singPlane, Submodule.mem_prod]

/-- The orthogonal of the finite plane is the finite plane (`F_v` is isotropic and the cross
pairing is perfect). `PROVED`. -/
theorem orthogonal_finPlane (β : F →ₗ[K] S →ₗ[K] K) (hβ : Function.Injective β.flip) (σ : K) :
    (planePairing β σ).orthogonal (finPlane K F S) = finPlane K F S := by
  ext z
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_finPlane]
  constructor
  · intro h
    apply hβ
    ext x
    have := h (x, 0) (mem_finPlane.2 rfl)
    simpa using this
  · intro hz n hn
    rw [mem_finPlane] at hn
    simp [hz, hn]

/-- The orthogonal of the singular plane is the singular plane. `PROVED`. -/
theorem orthogonal_singPlane (β : F →ₗ[K] S →ₗ[K] K) (hβ : Function.Injective β) {σ : K}
    (hσ : σ ≠ 0) :
    (planePairing β σ).orthogonal (singPlane K F S) = singPlane K F S := by
  ext z
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_singPlane]
  constructor
  · intro h
    apply hβ
    ext y
    have := h (0, y) (mem_singPlane.2 rfl)
    simp only [planePairing_apply, map_zero, LinearMap.zero_apply, zero_add, mul_eq_zero,
      hσ, false_or] at this
    simpa using this
  · intro hz n hn
    rw [mem_singPlane] at hn
    simp [hz, hn]

/-- The degree-one pairing is nondegenerate: `(F_v ⊕ S_v)^⊥ = 0`. `PROVED`. -/
theorem orthogonal_top_plane (β : F →ₗ[K] S →ₗ[K] K) (hβl : Function.Injective β)
    (hβr : Function.Injective β.flip) {σ : K} (hσ : σ ≠ 0) :
    (planePairing β σ).orthogonal ⊤ = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hz
  have hz2 : z.2 = 0 := by
    have : z ∈ (planePairing β σ).orthogonal (finPlane K F S) :=
      (LinearMap.BilinForm.mem_orthogonal_iff).2 fun n _ => hz n Submodule.mem_top
    rw [orthogonal_finPlane β hβr σ, mem_finPlane] at this
    exact this
  have hz1 : z.1 = 0 := by
    have : z ∈ (planePairing β σ).orthogonal (singPlane K F S) :=
      (LinearMap.BilinForm.mem_orthogonal_iff).2 fun n _ => hz n Submodule.mem_top
    rw [orthogonal_singPlane β hβl hσ, mem_singPlane] at this
    exact this
  rw [Submodule.mem_bot]
  exact Prod.ext hz1 hz2

/-- The degree-one pairing is nondegenerate (separating on both sides). `PROVED`. -/
theorem planePairing_nondegenerate (β : F →ₗ[K] S →ₗ[K] K) (hβl : Function.Injective β)
    (hβr : Function.Injective β.flip) {σ : K} (hσ : σ ≠ 0) :
    (planePairing β σ).Nondegenerate := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have hz2 : z.2 = 0 := by
      apply hβr
      ext x
      have := hz (x, 0)
      rw [planePairing_apply] at this
      simp only [map_zero, zero_add, mul_eq_zero, hσ, false_or] at this
      simpa using this
    have hz1 : z.1 = 0 := by
      apply hβl
      ext y
      have := hz (0, y)
      rw [planePairing_apply] at this
      simpa using this
    exact Prod.ext hz1 hz2
  · have hmem : z ∈ (planePairing β σ).orthogonal ⊤ :=
      (LinearMap.BilinForm.mem_orthogonal_iff).2 fun n _ => hz n
    rw [orthogonal_top_plane β hβl hβr hσ, Submodule.mem_bot] at hmem
    exact hmem

/-- A graded local condition `U = U⁰ ⊕ U¹[-1] ⊕ U²[-2]` inside the graded local model
`L_v = D⁰ ⊕ L¹[-1] ⊕ D²[-2]` with zero differential (manuscript lines 4858-4861): one subspace in
each degree. -/
@[ext] structure GradedCondition (K D0 L1 D2 : Type*) [Field K] [AddCommGroup D0] [Module K D0]
    [AddCommGroup L1] [Module K L1] [AddCommGroup D2] [Module K D2] where
  /-- the degree-zero part `U⁰ ⊆ D⁰` -/
  deg0 : Submodule K D0
  /-- the degree-one part `U¹ ⊆ L¹ = F_v ⊕ S_v` -/
  deg1 : Submodule K L1
  /-- the degree-two part `U² ⊆ D²` -/
  deg2 : Submodule K D2

/-- The orthogonal `U^⊥` of a graded local condition under the transported pairing
`L_v ⊗ L_v → K[-2]` (manuscript line 4872): in degree `i` it is the annihilator of `U^{2-i}`.
Degrees `0` and `2` use the duality `p : D⁰ × D² → K` through Mathlib's
`Submodule.dualAnnihilator`; degree `1` uses `LinearMap.BilinForm.orthogonal`. -/
def GradedCondition.orth (p : D0 →ₗ[K] D2 →ₗ[K] K) (P : LinearMap.BilinForm K L1)
    (U : GradedCondition K D0 L1 D2) : GradedCondition K D0 L1 D2 where
  deg0 := U.deg2.dualAnnihilator.comap p
  deg1 := P.orthogonal U.deg1
  deg2 := U.deg0.dualAnnihilator.comap p.flip

variable (K D0 F S D2)

/-- `U_str = D⁰` (manuscript line 4866). -/
def Ustr : GradedCondition K D0 (F × S) D2 := ⟨⊤, ⊥, ⊥⟩

/-- `U_rel = D⁰ ⊕ (F_v ⊕ S_v)[-1]` (manuscript line 4867); it omits `D²[-2]`. -/
def Urel : GradedCondition K D0 (F × S) D2 := ⟨⊤, ⊤, ⊥⟩

/-- `U_F = D⁰ ⊕ F_v[-1]` (manuscript line 4868). -/
def UF : GradedCondition K D0 (F × S) D2 := ⟨⊤, finPlane K F S, ⊥⟩

/-- `U_S = D⁰ ⊕ S_v[-1]` (manuscript line 4869). -/
def US : GradedCondition K D0 (F × S) D2 := ⟨⊤, singPlane K F S, ⊥⟩

variable {K D0 F S D2}

theorem orth_deg0_of_deg2_bot (p : D0 →ₗ[K] D2 →ₗ[K] K) (P : LinearMap.BilinForm K L1)
    (U : GradedCondition K D0 L1 D2) (hU : U.deg2 = ⊥) : (U.orth p P).deg0 = ⊤ := by
  simp [GradedCondition.orth, hU]

theorem orth_deg2_of_deg0_top (p : D0 →ₗ[K] D2 →ₗ[K] K) (hp : Function.Injective p.flip)
    (P : LinearMap.BilinForm K L1) (U : GradedCondition K D0 L1 D2) (hU : U.deg0 = ⊤) :
    (U.orth p P).deg2 = ⊥ := by
  simp only [GradedCondition.orth, hU, Submodule.dualAnnihilator_top, Submodule.comap_bot]
  exact LinearMap.ker_eq_bot.2 hp

theorem orth_eq_of (p : D0 →ₗ[K] D2 →ₗ[K] K) (hp : Function.Injective p.flip)
    (P : LinearMap.BilinForm K L1) (U V : GradedCondition K D0 L1 D2) (hU0 : U.deg0 = ⊤)
    (hU2 : U.deg2 = ⊥) (hV0 : V.deg0 = ⊤) (hV2 : V.deg2 = ⊥)
    (h1 : P.orthogonal U.deg1 = V.deg1) : U.orth p P = V := by
  refine GradedCondition.ext ?_ ?_ ?_
  · rw [orth_deg0_of_deg2_bot p P U hU2, hV0]
  · exact h1
  · rw [orth_deg2_of_deg0_top p hp P U hU0, hV2]

/-- **Derivative local conditions** (manuscript lines 4834-4842 and 4853-4874,
`ex:limits-derivative-switch`, first paragraph): "Thus `U_str^⊥ = U_rel` and the two plane
conditions are self-orthogonal under the transported duality."
With `D⁰, D²` in perfect duality `p` ("`D^0` and `D^2` are dual") and `F_v, S_v` isotropic planes
with perfect cross pairing `β`, we prove all four identities
`U_str^⊥ = U_rel`, `U_rel^⊥ = U_str`, `U_F^⊥ = U_F`, `U_S^⊥ = U_S`.
`PROVED`. DEPARTURE: the graded complex with zero differential is modelled degreewise (three
spaces and the pairings `p` in degrees `(0,2)` and `planePairing β σ` in degree `(1,1)`); the graded
sign of the pairing is irrelevant for annihilators and is absorbed in `σ ≠ 0`. The degree-one
pairing is written in the form forced by the isotropy of `F_v` and `S_v`
(`planePairing_eq_of_isotropic`). The pairing and isotropy homotopies of the integral model are
not modelled: the assertion is made after passage to the field, as in lines 4885-4887. -/
theorem derivative_conditions_orthogonal (p : D0 →ₗ[K] D2 →ₗ[K] K) [p.IsPerfPair]
    (β : F →ₗ[K] S →ₗ[K] K) [β.IsPerfPair] {σ : K} (hσ : σ ≠ 0) :
    (Ustr K D0 F S D2).orth p (planePairing β σ) = Urel K D0 F S D2 ∧
    (Urel K D0 F S D2).orth p (planePairing β σ) = Ustr K D0 F S D2 ∧
    (UF K D0 F S D2).orth p (planePairing β σ) = UF K D0 F S D2 ∧
    (US K D0 F S D2).orth p (planePairing β σ) = US K D0 F S D2 := by
  have hp : Function.Injective p.flip := (LinearMap.IsPerfPair.bijective_right p).injective
  have hβl : Function.Injective β := (LinearMap.IsPerfPair.bijective_left β).injective
  have hβr : Function.Injective β.flip := (LinearMap.IsPerfPair.bijective_right β).injective
  refine ⟨orth_eq_of p hp _ _ _ rfl rfl rfl rfl LinearMap.BilinForm.orthogonal_bot,
    orth_eq_of p hp _ _ _ rfl rfl rfl rfl (orthogonal_top_plane β hβl hβr hσ),
    orth_eq_of p hp _ _ _ rfl rfl rfl rfl (orthogonal_finPlane β hβr σ),
    orth_eq_of p hp _ _ _ rfl rfl rfl rfl (orthogonal_singPlane β hβl hσ)⟩

/-- The four conditions retain `D⁰` in degree zero and omit `D²[-2]` (manuscript lines 4874-4876:
"All four maps retain local degree-zero cohomology. In particular, the relaxed condition here
omits `D^2[-2]` and is not the full local complex"), and they are nested
`U_str ≤ U_F, U_S ≤ U_rel` degreewise, the degree-one quotients being the planes `F_v`, `S_v`
of the cone triangles (lines 4877-4882). `PROVED`. -/
theorem derivative_conditions_nested :
    (Ustr K D0 F S D2).deg1 ≤ (UF K D0 F S D2).deg1 ∧
    (Ustr K D0 F S D2).deg1 ≤ (US K D0 F S D2).deg1 ∧
    (UF K D0 F S D2).deg1 ≤ (Urel K D0 F S D2).deg1 ∧
    (US K D0 F S D2).deg1 ≤ (Urel K D0 F S D2).deg1 ∧
    (Ustr K D0 F S D2).deg0 = ⊤ ∧ (Urel K D0 F S D2).deg2 = ⊥ :=
  ⟨bot_le, bot_le, le_top, le_top, rfl, rfl⟩

/-- Multiplication `K × K → K` is a perfect pairing (used for the non-vacuity example). -/
theorem mul_isPerfPair : (LinearMap.mul K K).IsPerfPair := by
  refine LinearMap.IsPerfPair.of_injective ?_ ?_
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    simpa using LinearMap.congr_fun hx 1
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    simpa using LinearMap.congr_fun hx 1

/-- Non-vacuity: the hypotheses of `derivative_conditions_orthogonal` are satisfiable
(`D⁰ = D² = F = S = K` with the multiplication pairings). -/
example : (UF K K K K K).orth (LinearMap.mul K K) (planePairing (LinearMap.mul K K) 1) =
    UF K K K K K := by
  have := (mul_isPerfPair (K := K))
  exact (derivative_conditions_orthogonal (LinearMap.mul K K) (LinearMap.mul K K)
    one_ne_zero).2.2.1

end LocalModel

/-! ## Part 2. The switch at a new inert prime -/

section Switch

variable {K : Type*} [Field K]

/-- The Weil pairing on `T = K²`: `e₂(x, y) = det [x; y] = x₀ y₁ - x₁ y₀` (alternating,
nondegenerate). -/
def weil : LinearMap.BilinForm K (Fin 2 → K) :=
  LinearMap.mk₂ K (fun x y => x 0 * y 1 - x 1 * y 0)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem weil_apply (x y : Fin 2 → K) : weil x y = x 0 * y 1 - x 1 * y 0 := rfl

/-- `e₂` is the determinant. -/
theorem weil_eq_det (x y : Fin 2 → K) : weil x y = (Matrix.of ![x, y]).det := by
  simp [Matrix.det_fin_two, weil_apply]

theorem weil_self (x : Fin 2 → K) : weil x x = 0 := by
  rw [weil_apply]; ring

theorem weil_swap (x y : Fin 2 → K) : weil y x = -weil x y := by
  simp only [weil_apply]; ring

theorem weil_mulVec (M : Matrix (Fin 2) (Fin 2) K) (x y : Fin 2 → K) :
    weil (M *ᵥ x) (M *ᵥ y) = M.det * weil x y := by
  simp only [weil_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem eq_zero_of_weil_left {x : Fin 2 → K} (h : ∀ y, weil x y = 0) : x = 0 := by
  have h0 := h ![0, 1]
  have h1 := h ![1, 0]
  simp [weil_apply] at h0 h1
  funext i; fin_cases i <;> simp [h0, h1]

theorem eq_zero_of_weil_right {y : Fin 2 → K} (h : ∀ x, weil x y = 0) : y = 0 := by
  apply eq_zero_of_weil_left
  intro x
  rw [weil_swap, h x, neg_zero]

/-- For `v ≠ 0`, `e₂(x, v) = 0` iff `x ∈ K v`. -/
theorem weil_eq_zero_iff {v : Fin 2 → K} (hv : v ≠ 0) (x : Fin 2 → K) :
    weil x v = 0 ↔ x ∈ K ∙ v := by
  constructor
  · intro h
    rw [weil_apply] at h
    rw [Submodule.mem_span_singleton]
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1; apply hv; funext i; fin_cases i <;> simp [h0, h1]
      have hx0 : x 0 = 0 := by
        rw [h0, mul_zero, sub_zero] at h
        exact (mul_eq_zero.1 h).resolve_right h1
      refine ⟨x 1 / v 1, ?_⟩
      funext i; fin_cases i
      · simp [h0, hx0]
      · simp [h1]
    · refine ⟨x 0 / v 0, ?_⟩
      funext i; fin_cases i
      · simp [h0]
      · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
        field_simp
        linear_combination h
  · intro h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 h
    rw [map_smul, LinearMap.smul_apply, weil_self, smul_zero]

/-- For `v ≠ 0` every value is attained by `e₂(v, ·)`; the complement may be fractional. -/
theorem exists_weil_eq {v : Fin 2 → K} (hv : v ≠ 0) (c : K) : ∃ x, weil v x = c := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv; funext i; fin_cases i <;> simp [h0, h1]
    refine ⟨![-c / v 1, 0], ?_⟩
    simp only [weil_apply, Matrix.cons_val_zero, Matrix.cons_val_one, h0]
    field_simp
    ring
  · refine ⟨![0, c / v 0], ?_⟩
    simp only [weil_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring

theorem mulVec_mulVec_of_sq {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1) (x : Fin 2 → K) :
    J *ᵥ (J *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, hJ2, Matrix.one_mulVec]

/-- The cross pairing between the finite and singular planes at a new inert prime
(manuscript lines 4888-4890): `β(x,y) = ε ⟨x, J y⟩ = ε e₂(x, J y)`. -/
def crossPairing (ε : K) (J : Matrix (Fin 2) (Fin 2) K) : LinearMap.BilinForm K (Fin 2 → K) :=
  ε • weil.compl₂ J.mulVecLin

@[simp] theorem crossPairing_apply (ε : K) (J : Matrix (Fin 2) (Fin 2) K) (x y : Fin 2 → K) :
    crossPairing ε J x y = ε * weil x (J *ᵥ y) := by
  simp [crossPairing]

/-- The cross pairing is perfect when `ε ≠ 0` and `J² = 1`. `PROVED`. -/
theorem crossPairing_isPerfPair {ε : K} (hε : ε ≠ 0) {J : Matrix (Fin 2) (Fin 2) K}
    (hJ2 : J * J = 1) : (crossPairing ε J).IsPerfPair := by
  refine LinearMap.IsPerfPair.of_injective ?_ ?_
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    apply eq_zero_of_weil_left
    intro y
    have := LinearMap.congr_fun hx (J *ᵥ y)
    simp only [crossPairing_apply, mulVec_mulVec_of_sq hJ2, LinearMap.zero_apply,
      mul_eq_zero, hε, false_or] at this
    exact this
  · refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    have hJy : J *ᵥ y = 0 := by
      apply eq_zero_of_weil_right
      intro x
      have := LinearMap.congr_fun hy x
      simp only [LinearMap.flip_apply, crossPairing_apply, LinearMap.zero_apply,
        mul_eq_zero, hε, false_or] at this
      exact this
    rw [← mulVec_mulVec_of_sq hJ2 y, hJy, Matrix.mulVec_zero]

/-- The local pairing on `F_v ⊕ S_v = T × T` at a new inert prime. -/
abbrev switchPairing (ε σ : K) (J : Matrix (Fin 2) (Fin 2) K) :
    LinearMap.BilinForm K ((Fin 2 → K) × (Fin 2 → K)) :=
  planePairing (crossPairing ε J) σ

theorem switchPairing_nondegenerate {ε σ : K} (hε : ε ≠ 0) (hσ : σ ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1) :
    (switchPairing ε σ J).Nondegenerate := by
  have := crossPairing_isPerfPair hε hJ2
  exact planePairing_nondegenerate (crossPairing ε J)
    (LinearMap.IsPerfPair.bijective_left _).injective
    (LinearMap.IsPerfPair.bijective_right _).injective hσ

/-- **Orthogonality of the two localized vectors** (manuscript lines 4896-4897):
`(v,0) ⊥ (0, J v)` since `β(v, J v) = ε e₂(v, J² v) = ε e₂(v, v) = 0`; hence the span of the two
vectors is totally isotropic, as it must be to lie in a self-annihilating `U`. `PROVED`. -/
theorem switch_pair_orthogonal (ε σ : K) {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    (v : Fin 2 → K) :
    switchPairing ε σ J (v, 0) (0, J *ᵥ v) = 0 ∧
    Submodule.span K {((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, J *ᵥ v)} ≤
      (switchPairing ε σ J).orthogonal
        (Submodule.span K {((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, J *ᵥ v)}) := by
  have key : ∀ a b c d : K,
      switchPairing ε σ J (c • v, d • (J *ᵥ v)) (a • v, b • (J *ᵥ v)) = 0 := by
    intro a b c d
    simp only [planePairing_apply, crossPairing_apply,
      mulVec_mulVec_of_sq hJ2, map_smul, LinearMap.smul_apply, weil_self, smul_zero, mul_zero,
      add_zero]
  refine ⟨by simpa using key 0 1 1 0, ?_⟩
  intro z hz
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hz
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hn
  simpa using key a b c d

/-- **A self-annihilating subspace of `F_v ⊕ S_v` has dimension two** (manuscript lines
4894-4897: the relaxed image is Lagrangian, of dimension 2 in the 4-dimensional `F_v ⊕ S_v` with
its nondegenerate pairing). `PROVED`. -/
theorem lagrangian_finrank_eq_two {ε σ : K} (hε : ε ≠ 0) (hσ : σ ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    (U : Submodule K ((Fin 2 → K) × (Fin 2 → K)))
    (hU : (switchPairing ε σ J).orthogonal U = U) : finrank K U = 2 := by
  have h := LinearMap.BilinForm.finrank_orthogonal (switchPairing_nondegenerate hε hσ hJ2) U
  rw [hU, Module.finrank_prod, Module.finrank_fin_fun] at h
  have hle : finrank K U ≤ 2 + 2 := by
    have := Submodule.finrank_le U
    rwa [Module.finrank_prod, Module.finrank_fin_fun] at this
  omega

/-- **The relaxed localization image is spanned by `(v,0)` and `(0,Jv)`** (manuscript lines
4893-4898): "The transported duality and localization identities identify the relaxed
localization image with the kernel of its dual localization map, hence with its exact annihilator
[Nekovář, Sections 6.3.3-6.3.4]. This image contains `(v,0)` and `(0,Jv)`, so these span it."
`PROVED` from the hypothesis `U = U^⊥`; that hypothesis is the cited duality (`GLUE` input,
Nekovář 6.3.3-6.3.4), not proved here. -/
theorem relaxed_image_eq_span {ε σ : K} (hε : ε ≠ 0) (hσ : σ ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1) {v : Fin 2 → K} (hv : v ≠ 0)
    (U : Submodule K ((Fin 2 → K) × (Fin 2 → K)))
    (hU : (switchPairing ε σ J).orthogonal U = U)
    (hvU : ((v, 0) : (Fin 2 → K) × (Fin 2 → K)) ∈ U) (hJvU : ((0, J *ᵥ v) : _) ∈ U) :
    U = Submodule.span K {((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, J *ᵥ v)} := by
  have hJv : J *ᵥ v ≠ 0 := by
    intro h; apply hv; rw [← mulVec_mulVec_of_sq hJ2 v, h, Matrix.mulVec_zero]
  have hli : LinearIndependent K
      ![((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, J *ᵥ v)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg Prod.fst hst
    have h2 := congrArg Prod.snd hst
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero, add_zero,
      zero_add, Prod.fst_zero, Prod.snd_zero] at h1 h2
    exact ⟨(smul_eq_zero.1 h1).resolve_right hv, (smul_eq_zero.1 h2).resolve_right hJv⟩
  have hspan_le : Submodule.span K {((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, J *ᵥ v)} ≤ U := by
    rw [Submodule.span_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hvU
    · exact hJvU
  have hrank : finrank K (Submodule.span K
      {((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, J *ᵥ v)}) = 2 := by
    have := finrank_span_eq_card hli
    rw [Matrix.range_cons_cons_empty] at this
    simpa using this
  exact (Submodule.eq_of_le_of_finrank_eq hspan_le
    (by rw [hrank, lagrangian_finrank_eq_two hε hσ hJ2 U hU])).symm

/-- The span of `(v,0)` and `(0,Jv)` is its own orthogonal (it is Lagrangian). This shows that the
hypothesis `U = U^⊥` of `relaxed_image_eq_span` is satisfiable. `PROVED`. -/
theorem span_pair_orthogonal_eq {ε σ : K} (hε : ε ≠ 0) (hσ : σ ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1) {v : Fin 2 → K} (hv : v ≠ 0) :
    (switchPairing ε σ J).orthogonal
        (Submodule.span K {((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, J *ᵥ v)}) =
      Submodule.span K {((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, J *ᵥ v)} := by
  have hJv : J *ᵥ v ≠ 0 := by
    intro h; apply hv; rw [← mulVec_mulVec_of_sq hJ2 v, h, Matrix.mulVec_zero]
  have hli : LinearIndependent K
      ![((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, J *ᵥ v)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg Prod.fst hst
    have h2 := congrArg Prod.snd hst
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_zero, add_zero,
      zero_add, Prod.fst_zero, Prod.snd_zero] at h1 h2
    exact ⟨(smul_eq_zero.1 h1).resolve_right hv, (smul_eq_zero.1 h2).resolve_right hJv⟩
  have hrank : finrank K (Submodule.span K
      {((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, J *ᵥ v)}) = 2 := by
    have := finrank_span_eq_card hli
    rw [Matrix.range_cons_cons_empty] at this
    simpa using this
  refine (Submodule.eq_of_le_of_finrank_eq (switch_pair_orthogonal ε σ hJ2 v).2 ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal (switchPairing_nondegenerate hε hσ hJ2),
    hrank, Module.finrank_prod, Module.finrank_fin_fun]

/-- The singular part of the relaxed image: `U ∩ S_v = K (0, J v)`. `PROVED`. -/
theorem relaxed_image_inf_singPlane {ε σ : K} (hε : ε ≠ 0) (hσ : σ ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1) {v : Fin 2 → K} (hv : v ≠ 0)
    (U : Submodule K ((Fin 2 → K) × (Fin 2 → K)))
    (hU : (switchPairing ε σ J).orthogonal U = U)
    (hvU : ((v, 0) : (Fin 2 → K) × (Fin 2 → K)) ∈ U) (hJvU : ((0, J *ᵥ v) : _) ∈ U) :
    U ⊓ singPlane K (Fin 2 → K) (Fin 2 → K) = K ∙ ((0, J *ᵥ v) : (Fin 2 → K) × (Fin 2 → K)) := by
  have hUeq := relaxed_image_eq_span hε hσ hJ2 hv U hU hvU hJvU
  ext z
  rw [Submodule.mem_inf, mem_singPlane, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨hzU, hz1⟩
    rw [hUeq] at hzU
    obtain ⟨a, c, rfl⟩ := Submodule.mem_span_pair.1 hzU
    have ha : a = 0 := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero] at hz1
      exact (smul_eq_zero.1 hz1).resolve_right hv
    exact ⟨c, by rw [ha, zero_smul, zero_add]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨U.smul_mem c hJvU, by simp⟩

/-- **The new generic `H¹` is spanned by the derivative** (manuscript lines 4892-4898):
"The strict `H^1` vanishes. ... This image contains `(v,0)` and `(0,Jv)`, so these span it.
Hence the new generic `H^1` is spanned by `B`."
Dimension bookkeeping with the exact sequence `0 → K₀ → V' → U ∩ S_v → 0` of the cone triangle
`C_str → C_S → S_v[-1] →` (lines 4877-4882), where `K₀ = H¹(C_str) = 0` (strict `H¹` vanishes),
`V' = H¹(C_S)` is the new generic `H¹`, and `U` is the relaxed localization image. Conclusion:
`dim V' = 1` and every nonzero `B ∈ V'` spans it.
`PROVED` from the hypotheses; `U = U^⊥` is the cited duality (`GLUE`, Nekovář 6.3.3-6.3.4), and the
exact sequence is the cone-triangle sequence (stated as hypotheses, as asked). -/
theorem switch_new_H1_spanned {ε σ : K} (hε : ε ≠ 0) (hσ : σ ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1) {v : Fin 2 → K} (hv : v ≠ 0)
    (U : Submodule K ((Fin 2 → K) × (Fin 2 → K)))
    (hU : (switchPairing ε σ J).orthogonal U = U)
    (hvU : ((v, 0) : (Fin 2 → K) × (Fin 2 → K)) ∈ U) (hJvU : ((0, J *ᵥ v) : _) ∈ U)
    {K₀ V' : Type*} [AddCommGroup K₀] [Module K K₀] [AddCommGroup V'] [Module K V']
    [Subsingleton K₀] (i : K₀ →ₗ[K] V') (p : V' →ₗ[K] (Fin 2 → K) × (Fin 2 → K))
    (hexact : LinearMap.range i = LinearMap.ker p)
    (hp : LinearMap.range p = U ⊓ singPlane K (Fin 2 → K) (Fin 2 → K))
    {B : V'} (hB : B ≠ 0) :
    finrank K V' = 1 ∧ Submodule.span K {B} = ⊤ := by
  have hi0 : LinearMap.range i = ⊥ := by
    rw [LinearMap.range_eq_bot]
    ext z
    rw [Subsingleton.elim z 0, map_zero, LinearMap.zero_apply]
  have hinj : Function.Injective p := by
    rw [← LinearMap.ker_eq_bot, ← hexact, hi0]
  have hJv : J *ᵥ v ≠ 0 := by
    intro h; apply hv; rw [← mulVec_mulVec_of_sq hJ2 v, h, Matrix.mulVec_zero]
  have hdim : finrank K V' = 1 := by
    rw [← LinearMap.finrank_range_of_inj hinj, hp,
      relaxed_image_inf_singPlane hε hσ hJ2 hv U hU hvU hJvU]
    exact finrank_span_singleton fun h => hJv (congrArg Prod.snd h)
  refine ⟨hdim, ?_⟩
  have : FiniteDimensional K V' := Module.finite_of_finrank_pos (by rw [hdim]; exact one_pos)
  exact Submodule.eq_top_of_finrank_eq (by rw [finrank_span_singleton hB, hdim])

/-- **The switch with the actual localization maps** (manuscript lines 4891-4898). Here
`R = H¹(C_rel)`, `f, s : R → T` are the finite and singular localizations at the new prime,
the old generic `H¹ = H¹(C_F) = ker s` is spanned by the actual old class `A` with `f(A) = v ≠ 0`,
and the derivative `B` satisfies `f(B) = 0`, `s(B) = Jv` ((4.2)). If the relaxed localization
image `U = im (f, s)` equals its exact annihilator (the cited duality, `GLUE`), then:
the strict `H¹ = ker (f, s)` vanishes, `U` is spanned by `(v,0)` and `(0,Jv)`, and the new generic
`H¹ = H¹(C_S) = ker f` is spanned by `B`. `PROVED`. -/
theorem switch_new_H1_spanned_of_loc {R : Type*} [AddCommGroup R] [Module K R]
    {ε σ : K} (hε : ε ≠ 0) (hσ : σ ≠ 0) {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    {v : Fin 2 → K} (hv : v ≠ 0) (f s : R →ₗ[K] (Fin 2 → K)) (A B : R)
    (hA : LinearMap.ker s = K ∙ A) (hfA : f A = v) (hfB : f B = 0) (hsB : s B = J *ᵥ v)
    (hU : (switchPairing ε σ J).orthogonal (LinearMap.range (f.prod s)) =
      LinearMap.range (f.prod s)) :
    LinearMap.ker (f.prod s) = ⊥ ∧
    LinearMap.range (f.prod s) =
      Submodule.span K {((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, J *ᵥ v)} ∧
    LinearMap.ker f = K ∙ B := by
  have hsA : s A = 0 := by
    have : A ∈ LinearMap.ker s := by rw [hA]; exact Submodule.mem_span_singleton_self A
    exact this
  have hstrict : LinearMap.ker (f.prod s) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hfx : f x = 0 := congrArg Prod.fst hx
    have hxs : x ∈ LinearMap.ker s := congrArg Prod.snd hx
    rw [hA, Submodule.mem_span_singleton] at hxs
    obtain ⟨c, rfl⟩ := hxs
    have hc : c = 0 := by
      rw [map_smul, hfA] at hfx
      exact (smul_eq_zero.1 hfx).resolve_right hv
    rw [hc, zero_smul]; exact Submodule.zero_mem _
  have hvU : ((v, 0) : (Fin 2 → K) × (Fin 2 → K)) ∈ LinearMap.range (f.prod s) :=
    ⟨A, by simp [hfA, hsA]⟩
  have hJvU : ((0, J *ᵥ v) : (Fin 2 → K) × (Fin 2 → K)) ∈ LinearMap.range (f.prod s) :=
    ⟨B, by simp [hfB, hsB]⟩
  have hspan := relaxed_image_eq_span hε hσ hJ2 hv _ hU hvU hJvU
  refine ⟨hstrict, hspan, ?_⟩
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hx
    have hmem : ((0, s x) : (Fin 2 → K) × (Fin 2 → K)) ∈ LinearMap.range (f.prod s) :=
      ⟨x, by simp [hx]⟩
    rw [hspan] at hmem
    obtain ⟨a, c, hac⟩ := Submodule.mem_span_pair.1 hmem
    have ha : a = 0 := by
      have := congrArg Prod.fst hac
      simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero] at this
      exact (smul_eq_zero.1 this).resolve_right hv
    have hsx : s x = c • (J *ᵥ v) := by
      have := congrArg Prod.snd hac
      simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add, ha] at this
      exact this.symm
    refine ⟨c, ?_⟩
    have hker : x - c • B ∈ LinearMap.ker (f.prod s) := by
      rw [LinearMap.mem_ker]
      refine Prod.ext ?_ ?_
      · show f (x - c • B) = 0
        rw [map_sub, map_smul, hx, hfB, smul_zero, sub_zero]
      · show s (x - c • B) = 0
        rw [map_sub, map_smul, hsx, hsB, sub_self]
    rw [hstrict, Submodule.mem_bot, sub_eq_zero] at hker
    exact hker.symm
  · rintro ⟨c, rfl⟩
    rw [map_smul, hfB, smul_zero]

end Switch

/-! ## Part 3. The determinant comparison: equal valuations of the two coordinates (gap B2-a) -/

section Coordinates

variable {K : Type*} [Field K] {R : Type*} [AddCommGroup R] [Module K R]

/-- The boundary map `F_v ⊕ S_v → H²(C_str)`, with `H²(C_str)` modelled as `H¹(C_rel)^∨ =
Module.Dual K R`: it is dual to the localization `loc = (f, s) : R → F_v ⊕ S_v` under the local
pairing, `∂ z = (c ↦ ⟨z, loc c⟩)`, i.e. `∂ = loc^∨ ∘ ⟨·,·⟩`.
`GLUE` (modelling input): the identification `H²(C_str) ≅ H¹(C_rel)^∨` and the description of the
connecting maps as duals of localization are the strict/relaxed duality of Nekovář, Sections
6.3.3-6.3.4 (strict and relaxed are orthogonal by `derivative_conditions_orthogonal`). -/
def bdry (ε σ : K) (J : Matrix (Fin 2) (Fin 2) K) (f s : R →ₗ[K] (Fin 2 → K)) :
    (Fin 2 → K) × (Fin 2 → K) →ₗ[K] Module.Dual K R :=
  (f.prod s).dualMap ∘ₗ switchPairing ε σ J

/-- The finite connecting map `∂_F : F_v → H²(C_str)` of the triangle
`C_str → C_F → F_v[-1] →`. -/
def bdryF (ε σ : K) (J : Matrix (Fin 2) (Fin 2) K) (f s : R →ₗ[K] (Fin 2 → K)) :
    (Fin 2 → K) →ₗ[K] Module.Dual K R :=
  bdry ε σ J f s ∘ₗ LinearMap.inl K (Fin 2 → K) (Fin 2 → K)

/-- The singular connecting map `∂_S : S_v → H²(C_str)` of the triangle
`C_str → C_S → S_v[-1] →`. -/
def bdryS (ε σ : K) (J : Matrix (Fin 2) (Fin 2) K) (f s : R →ₗ[K] (Fin 2 → K)) :
    (Fin 2 → K) →ₗ[K] Module.Dual K R :=
  bdry ε σ J f s ∘ₗ LinearMap.inr K (Fin 2 → K) (Fin 2 → K)

/-- `∂_F x = (c ↦ β(x, s c))`. -/
theorem bdryF_apply (ε σ : K) (J : Matrix (Fin 2) (Fin 2) K) (f s : R →ₗ[K] (Fin 2 → K))
    (x : Fin 2 → K) (c : R) : bdryF ε σ J f s x c = crossPairing ε J x (s c) := by
  simp [bdryF, bdry]

/-- `∂_S y = (c ↦ σ β(f c, y))`. -/
theorem bdryS_apply (ε σ : K) (J : Matrix (Fin 2) (Fin 2) K) (f s : R →ₗ[K] (Fin 2 → K))
    (y : Fin 2 → K) (c : R) : bdryS ε σ J f s y c = σ * crossPairing ε J (f c) y := by
  simp [bdryS, bdry]

/-- The integral volume form `vol = μ e₂` on a plane; the integral normalization ("unit
volume") is the condition `ν μ = 0` imposed in `switch_equal_valuation`. -/
def vol (μ : K) : LinearMap.BilinForm K (Fin 2 → K) := μ • weil

theorem vol_apply (μ : K) (x y : Fin 2 → K) : vol μ x y = μ * weil x y := by
  simp [vol]

/-- The class-functional coordinate of the finite determinant sequence
`0 → ⟨A⟩ → F_v → H²(C_str) → H²(C_F) → 0` at the complement `(x, w)`:
`u_F = vol_F(f A, x) · λ_A(w) / ω(∂_F x, w)`, where `λ_A = ` evaluation at `A` (the paired
functional transported from the actual class `A`) and `ω` is the common strict volume form
on `H²(C_str)`. Admissible complements are those with `ω(∂_F x, w) ≠ 0`. -/
def coordF (ε σ : K) (J : Matrix (Fin 2) (Fin 2) K) (f s : R →ₗ[K] (Fin 2 → K))
    (ω : LinearMap.BilinForm K (Module.Dual K R)) (μF : K) (A : R) (x : Fin 2 → K)
    (w : Module.Dual K R) : K :=
  vol μF (f A) x * Module.Dual.eval K R A w / ω (bdryF ε σ J f s x) w

/-- The class-functional coordinate of the singular determinant sequence
`0 → ⟨B⟩ → S_v → H²(C_str) → H²(C_S) → 0` at the complement `(y, w')`:
`u_S = vol_S(s B, y) · λ_B(w') / ω(∂_S y, w')`. -/
def coordS (ε σ : K) (J : Matrix (Fin 2) (Fin 2) K) (f s : R →ₗ[K] (Fin 2 → K))
    (ω : LinearMap.BilinForm K (Module.Dual K R)) (μS : K) (B : R) (y : Fin 2 → K)
    (w' : Module.Dual K R) : K :=
  vol μS (s B) y * Module.Dual.eval K R B w' / ω (bdryS ε σ J f s y) w'

variable (b : Basis (Fin 2) K R)

/-- In the dual basis `A*, B*` of `H²(C_str) = ⟨A, B⟩^∨`: `∂_F x = ε e₂(x, v) B*`
(gap B2-a: "`F_v → H²(C_str)` sends `x ↦ ε⟨x,v⟩B*`"). -/
theorem bdryF_eq {ε σ : K} {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hsA : s (b 0) = 0) (hsB : s (b 1) = J *ᵥ v)
    (x : Fin 2 → K) : bdryF ε σ J f s x = (ε * weil x v) • b.dualBasis 1 := by
  refine b.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · simp [bdryF_apply, hsA]
  · rw [bdryF_apply, hsB, crossPairing_apply, mulVec_mulVec_of_sq hJ2]
    simp

/-- `∂_S y = σ ε e₂(v, J y) A*` (gap B2-a: "`S_v → H²(C_str)` sends `y ↦ ε⟨v,Jy⟩A*`"). -/
theorem bdryS_eq {ε σ : K} {J : Matrix (Fin 2) (Fin 2) K}
    {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hfA : f (b 0) = v) (hfB : f (b 1) = 0)
    (y : Fin 2 → K) : bdryS ε σ J f s y = (σ * (ε * weil v (J *ᵥ y))) • b.dualBasis 0 := by
  refine b.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · simp [bdryS_apply, hfA]
  · simp [bdryS_apply, hfB]

/-- An alternating form on the plane `H²(C_str)` is a multiple of the dual-basis determinant. -/
theorem alt_expand {ω : LinearMap.BilinForm K (Module.Dual K R)} (hω : LinearMap.IsAlt ω)
    (w₁ w₂ : Module.Dual K R) :
    ω w₁ w₂ = (w₁ (b 0) * w₂ (b 1) - w₁ (b 1) * w₂ (b 0)) *
      ω (b.dualBasis 0) (b.dualBasis 1) := by
  have hexp : ∀ w : Module.Dual K R, w = w (b 0) • b.dualBasis 0 + w (b 1) • b.dualBasis 1 := by
    intro w
    refine b.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;> simp
  have hanti : ω (b.dualBasis 1) (b.dualBasis 0) = -ω (b.dualBasis 0) (b.dualBasis 1) := by
    have h := hω.self_eq_zero (b.dualBasis 0 + b.dualBasis 1)
    simp only [map_add, LinearMap.add_apply, hω.self_eq_zero, zero_add, add_zero] at h
    linear_combination h
  conv_lhs => rw [hexp w₁, hexp w₂]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hω.self_eq_zero, hanti]
  ring

/-- A nonzero alternating form on `H²(C_str)` has `ω(A*, B*) ≠ 0`. -/
theorem alt_basis_ne_zero {ω : LinearMap.BilinForm K (Module.Dual K R)} (hω : LinearMap.IsAlt ω)
    (hω0 : ω ≠ 0) : ω (b.dualBasis 0) (b.dualBasis 1) ≠ 0 := by
  intro h
  apply hω0
  refine LinearMap.ext fun w₁ => LinearMap.ext fun w₂ => ?_
  rw [alt_expand b hω, h, mul_zero]
  rfl

/-- `ω(∂_F x, w) = ε e₂(v, x) λ_A(w) ω(A*, B*)`. -/
theorem omega_bdryF {ε σ : K} {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hsA : s (b 0) = 0) (hsB : s (b 1) = J *ᵥ v)
    {ω : LinearMap.BilinForm K (Module.Dual K R)} (hω : LinearMap.IsAlt ω)
    (x : Fin 2 → K) (w : Module.Dual K R) :
    ω (bdryF ε σ J f s x) w = ε * weil v x * w (b 0) * ω (b.dualBasis 0) (b.dualBasis 1) := by
  rw [bdryF_eq b hJ2 hsA hsB, map_smul, LinearMap.smul_apply, alt_expand b hω, smul_eq_mul]
  simp only [Basis.dualBasis_apply_self, zero_ne_one, ↓reduceIte, zero_mul, one_mul, zero_sub]
  have hsw := weil_swap v x
  linear_combination (-(ε * w (b 0) * ω (b.dualBasis 0) (b.dualBasis 1))) * hsw

/-- `ω(∂_S y, w') = σ ε e₂(v, J y) λ_B(w') ω(A*, B*)`. -/
theorem omega_bdryS {ε σ : K} {J : Matrix (Fin 2) (Fin 2) K}
    {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hfA : f (b 0) = v) (hfB : f (b 1) = 0)
    {ω : LinearMap.BilinForm K (Module.Dual K R)} (hω : LinearMap.IsAlt ω)
    (y : Fin 2 → K) (w' : Module.Dual K R) :
    ω (bdryS ε σ J f s y) w' =
      σ * ε * weil v (J *ᵥ y) * w' (b 1) * ω (b.dualBasis 0) (b.dualBasis 1) := by
  rw [bdryS_eq b hfA hfB, map_smul, LinearMap.smul_apply, alt_expand b hω, smul_eq_mul]
  simp only [Basis.dualBasis_apply_self, one_ne_zero, ↓reduceIte, zero_mul, one_mul, sub_zero]
  ring

/-- `e₂(J v, y) = -e₂(v, J y)` (from `det J = -1`, `J² = 1`). -/
theorem weil_J_left {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1) (hJdet : J.det = -1)
    (v y : Fin 2 → K) : weil (J *ᵥ v) y = -weil v (J *ᵥ y) := by
  have h := weil_mulVec J v (J *ᵥ y)
  rw [mulVec_mulVec_of_sq hJ2, hJdet] at h
  rw [h]; ring

/-- The finite coordinate in closed form: `u_F = μ_F / (ε ω(A*, B*))` for every admissible
complement. It does not involve `v` at all. -/
theorem coordF_eq {ε σ : K} {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hfA : f (b 0) = v) (hsA : s (b 0) = 0)
    (hsB : s (b 1) = J *ᵥ v) {ω : LinearMap.BilinForm K (Module.Dual K R)}
    (hω : LinearMap.IsAlt ω) (μF : K) {x : Fin 2 → K} {w : Module.Dual K R}
    (hxw : ω (bdryF ε σ J f s x) w ≠ 0) :
    coordF ε σ J f s ω μF (b 0) x w = μF / (ε * ω (b.dualBasis 0) (b.dualBasis 1)) := by
  have hden := omega_bdryF (ε := ε) (σ := σ) (f := f) b hJ2 hsA hsB hω x w
  rw [hden] at hxw
  have h3 : ω (b.dualBasis 0) (b.dualBasis 1) ≠ 0 := right_ne_zero_of_mul hxw
  have h2 : w (b 0) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hxw)
  have h1 : weil v x ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hxw))
  have h0 : ε ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hxw))
  unfold coordF
  rw [hden, vol_apply, hfA, Module.Dual.eval_apply]
  field_simp

/-- The singular coordinate in closed form: `u_S = -μ_S / (σ ε ω(A*, B*))`. -/
theorem coordS_eq {ε σ : K} {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    (hJdet : J.det = -1) {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hfA : f (b 0) = v)
    (hfB : f (b 1) = 0) (hsB : s (b 1) = J *ᵥ v) {ω : LinearMap.BilinForm K (Module.Dual K R)}
    (hω : LinearMap.IsAlt ω) (μS : K) {y : Fin 2 → K} {w' : Module.Dual K R}
    (hyw : ω (bdryS ε σ J f s y) w' ≠ 0) :
    coordS ε σ J f s ω μS (b 1) y w' = -μS / (σ * (ε * ω (b.dualBasis 0) (b.dualBasis 1))) := by
  have hden := omega_bdryS (ε := ε) (σ := σ) (J := J) (s := s) b hfA hfB hω y w'
  rw [hden] at hyw
  have h4 : ω (b.dualBasis 0) (b.dualBasis 1) ≠ 0 := right_ne_zero_of_mul hyw
  have h3 : w' (b 1) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hyw)
  have h2 : weil v (J *ᵥ y) ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hyw))
  have h1 : ε ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hyw)))
  have h0 : σ ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hyw)))
  unfold coordS
  rw [hden, vol_apply, hsB, Module.Dual.eval_apply,
    weil_J_left hJ2 hJdet]
  field_simp

/-- Admissibility of a finite complement `(x, w)` unpacked: `ω(∂_F x, w) ≠ 0` iff
`ε ≠ 0`, `v ∧ x ≠ 0` (so `(v, x)` is a basis of `F_v`), `λ_A(w) ≠ 0` and `ω(A*, B*) ≠ 0`. -/
theorem admissibleF_iff {ε σ : K} {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hsA : s (b 0) = 0) (hsB : s (b 1) = J *ᵥ v)
    {ω : LinearMap.BilinForm K (Module.Dual K R)} (hω : LinearMap.IsAlt ω)
    (x : Fin 2 → K) (w : Module.Dual K R) :
    ω (bdryF ε σ J f s x) w ≠ 0 ↔ ε ≠ 0 ∧ weil v x ≠ 0 ∧ w (b 0) ≠ 0 ∧
      ω (b.dualBasis 0) (b.dualBasis 1) ≠ 0 := by
  rw [omega_bdryF (ε := ε) (σ := σ) (f := f) b hJ2 hsA hsB hω x w]
  simp only [ne_eq, mul_eq_zero, not_or]
  tauto

/-- Admissibility of a singular complement `(y, w')` unpacked. -/
theorem admissibleS_iff {ε σ : K} {J : Matrix (Fin 2) (Fin 2) K}
    {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hfA : f (b 0) = v) (hfB : f (b 1) = 0)
    {ω : LinearMap.BilinForm K (Module.Dual K R)} (hω : LinearMap.IsAlt ω)
    (y : Fin 2 → K) (w' : Module.Dual K R) :
    ω (bdryS ε σ J f s y) w' ≠ 0 ↔ σ ≠ 0 ∧ ε ≠ 0 ∧ weil v (J *ᵥ y) ≠ 0 ∧ w' (b 1) ≠ 0 ∧
      ω (b.dualBasis 0) (b.dualBasis 1) ≠ 0 := by
  rw [omega_bdryS (ε := ε) (σ := σ) (J := J) (s := s) b hfA hfB hω y w']
  simp only [ne_eq, mul_eq_zero, not_or]
  tauto

/-- **Exactness of the finite determinant sequence at `F_v`** (manuscript lines 4903-4905):
`ker ∂_F = f(⟨A⟩) = K v`. `PROVED`. -/
theorem ker_bdryF {ε σ : K} (hε : ε ≠ 0) {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hv : v ≠ 0) (hfA : f (b 0) = v)
    (hsA : s (b 0) = 0) (hsB : s (b 1) = J *ᵥ v) :
    LinearMap.ker (bdryF ε σ J f s) = (K ∙ b 0).map f ∧ (K ∙ b 0).map f = K ∙ v := by
  have himg : (K ∙ b 0).map f = K ∙ v := by
    rw [Submodule.map_span, Set.image_singleton, hfA]
  refine ⟨?_, himg⟩
  rw [himg]
  ext x
  rw [LinearMap.mem_ker, bdryF_eq b hJ2 hsA hsB, smul_eq_zero, ← weil_eq_zero_iff hv x,
    or_iff_left (b.dualBasis.ne_zero 1), mul_eq_zero, or_iff_right hε]

/-- **Exactness of the finite determinant sequence at `H²(C_str)`** (manuscript lines 4903-4905):
the image of `∂_F` is the kernel of the restriction `H²(C_str) = R^∨ → ⟨A⟩^∨ ≅ H²(C_F)`, namely the
annihilator of `A`. In particular `λ_A` (evaluation at `A`) vanishes on `im ∂_F`, so it is a
functional on `H²(C_F)`. `PROVED`. -/
theorem range_bdryF {ε σ : K} (hε : ε ≠ 0) {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hv : v ≠ 0)
    (hsA : s (b 0) = 0) (hsB : s (b 1) = J *ᵥ v) :
    LinearMap.range (bdryF ε σ J f s) = LinearMap.ker (K ∙ b 0).subtype.dualMap ∧
    LinearMap.ker (K ∙ b 0).subtype.dualMap = (K ∙ b 0).dualAnnihilator := by
  have hker : LinearMap.ker (K ∙ b 0).subtype.dualMap = (K ∙ b 0).dualAnnihilator := by
    rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range, Submodule.range_subtype]
  refine ⟨?_, hker⟩
  rw [hker]
  ext w
  rw [LinearMap.mem_range, Submodule.mem_dualAnnihilator]
  constructor
  · rintro ⟨x, rfl⟩ a ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    rw [bdryF_eq b hJ2 hsA hsB]
    simp
  · intro h
    have hw0 : w (b 0) = 0 := h _ (Submodule.mem_span_singleton_self _)
    obtain ⟨x, hx⟩ := exists_weil_eq hv (-(w (b 1)) / ε)
    have hx' : weil x v = w (b 1) / ε := by rw [weil_swap v x, hx]; ring
    refine ⟨x, ?_⟩
    rw [bdryF_eq b hJ2 hsA hsB]
    refine b.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp [hw0]
    · simp only [LinearMap.smul_apply, Basis.dualBasis_apply_self, ↓reduceIte, smul_eq_mul,
        mul_one, hx']
      field_simp

/-- **Exactness of the singular determinant sequence at `S_v`**: `ker ∂_S = s(⟨B⟩) = K (J v)`.
`PROVED`. -/
theorem ker_bdryS {ε σ : K} (hε : ε ≠ 0) (hσ : σ ≠ 0) {J : Matrix (Fin 2) (Fin 2) K}
    (hJ2 : J * J = 1) (hJdet : J.det = -1) {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K}
    (hv : v ≠ 0) (hfA : f (b 0) = v) (hfB : f (b 1) = 0) (hsB : s (b 1) = J *ᵥ v) :
    LinearMap.ker (bdryS ε σ J f s) = (K ∙ b 1).map s ∧ (K ∙ b 1).map s = K ∙ (J *ᵥ v) := by
  have hJv : J *ᵥ v ≠ 0 := by
    intro h; apply hv; rw [← mulVec_mulVec_of_sq hJ2 v, h, Matrix.mulVec_zero]
  have himg : (K ∙ b 1).map s = K ∙ (J *ᵥ v) := by
    rw [Submodule.map_span, Set.image_singleton, hsB]
  refine ⟨?_, himg⟩
  rw [himg]
  ext y
  have h : weil v (J *ᵥ y) = weil y (J *ᵥ v) := by
    rw [weil_swap (J *ᵥ v) y, weil_J_left hJ2 hJdet]; ring
  rw [LinearMap.mem_ker, bdryS_eq b hfA hfB, smul_eq_zero, ← weil_eq_zero_iff hJv y,
    or_iff_left (b.dualBasis.ne_zero 0), mul_eq_zero, or_iff_right hσ, mul_eq_zero,
    or_iff_right hε, h]

/-- **Exactness of the singular determinant sequence at `H²(C_str)`**: the image of `∂_S` is the
kernel of the restriction `R^∨ → ⟨B⟩^∨ ≅ H²(C_S)`, the annihilator of `B`; `λ_B` descends to
`H²(C_S)`. `PROVED`. -/
theorem range_bdryS {ε σ : K} (hε : ε ≠ 0) (hσ : σ ≠ 0) {J : Matrix (Fin 2) (Fin 2) K}
    (hJ2 : J * J = 1) (hJdet : J.det = -1) {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K}
    (hv : v ≠ 0) (hfA : f (b 0) = v) (hfB : f (b 1) = 0) :
    LinearMap.range (bdryS ε σ J f s) = LinearMap.ker (K ∙ b 1).subtype.dualMap ∧
    LinearMap.ker (K ∙ b 1).subtype.dualMap = (K ∙ b 1).dualAnnihilator := by
  have hJv : J *ᵥ v ≠ 0 := by
    intro h; apply hv; rw [← mulVec_mulVec_of_sq hJ2 v, h, Matrix.mulVec_zero]
  have hker : LinearMap.ker (K ∙ b 1).subtype.dualMap = (K ∙ b 1).dualAnnihilator := by
    rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range, Submodule.range_subtype]
  refine ⟨?_, hker⟩
  rw [hker]
  ext w
  rw [LinearMap.mem_range, Submodule.mem_dualAnnihilator]
  constructor
  · rintro ⟨y, rfl⟩ a ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
    rw [bdryS_eq b hfA hfB]
    simp
  · intro h
    have hw1 : w (b 1) = 0 := h _ (Submodule.mem_span_singleton_self _)
    obtain ⟨y, hy⟩ := exists_weil_eq hJv (-(w (b 0)) / (σ * ε))
    have hy' : weil v (J *ᵥ y) = w (b 0) / (σ * ε) := by
      have := weil_J_left hJ2 hJdet v y
      rw [hy] at this
      linear_combination this
    refine ⟨y, ?_⟩
    rw [bdryS_eq b hfA hfB]
    refine b.ext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · simp only [LinearMap.smul_apply, Basis.dualBasis_apply_self, ↓reduceIte, smul_eq_mul,
        mul_one, hy']
      field_simp
    · simp [hw1]

/-- **(i) Independence of the finite complement** (manuscript lines 4900-4905, gap B2-a): the
class-functional coordinate `u_F = vol_F(v, x) λ_A(w) / ω(∂_F x, w)` does not depend on the
admissible complement `(x, w)`. `PROVED`. -/
theorem switch_coord_indep_F {ε σ : K} {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hfA : f (b 0) = v) (hsA : s (b 0) = 0)
    (hsB : s (b 1) = J *ᵥ v) {ω : LinearMap.BilinForm K (Module.Dual K R)}
    (hω : LinearMap.IsAlt ω) (μF : K) {x x' : Fin 2 → K} {w w' : Module.Dual K R}
    (h : ω (bdryF ε σ J f s x) w ≠ 0) (h' : ω (bdryF ε σ J f s x') w' ≠ 0) :
    coordF ε σ J f s ω μF (b 0) x w = coordF ε σ J f s ω μF (b 0) x' w' := by
  rw [coordF_eq b hJ2 hfA hsA hsB hω μF h, coordF_eq b hJ2 hfA hsA hsB hω μF h']

/-- **(i) Independence of the singular complement**: `u_S = vol_S(Jv, y) λ_B(w') / ω(∂_S y, w')`
does not depend on the admissible complement `(y, w')`. `PROVED`. -/
theorem switch_coord_indep_S {ε σ : K} {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1)
    (hJdet : J.det = -1) {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hfA : f (b 0) = v)
    (hfB : f (b 1) = 0) (hsB : s (b 1) = J *ᵥ v) {ω : LinearMap.BilinForm K (Module.Dual K R)}
    (hω : LinearMap.IsAlt ω) (μS : K) {y y' : Fin 2 → K} {w w' : Module.Dual K R}
    (h : ω (bdryS ε σ J f s y) w ≠ 0) (h' : ω (bdryS ε σ J f s y') w' ≠ 0) :
    coordS ε σ J f s ω μS (b 1) y w = coordS ε σ J f s ω μS (b 1) y' w' := by
  rw [coordS_eq b hJ2 hJdet hfA hfB hsB hω μS h, coordS_eq b hJ2 hJdet hfA hfB hsB hω μS h']

/-- **(ii) Existence of admissible finite complements** (manuscript line 4901: "In the fraction
field choose `x` with `v∧x` of unit volume"): for every `v ≠ 0` there is `x` with
`vol_F(v, x) = 1` and `w` with `ω(∂_F x, w) ≠ 0`. The vector `x` lives in `K²` (it is fractional
in general, see `switch_integral_complement_not_unit`). `PROVED`. -/
theorem switch_exists_admissible_F {ε σ : K} (hε : ε ≠ 0) {J : Matrix (Fin 2) (Fin 2) K}
    (hJ2 : J * J = 1) {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hv : v ≠ 0)
    (hfA : f (b 0) = v) (hsA : s (b 0) = 0) (hsB : s (b 1) = J *ᵥ v)
    {ω : LinearMap.BilinForm K (Module.Dual K R)} (hω : LinearMap.IsAlt ω) (hω0 : ω ≠ 0)
    {μF : K} (hμF : μF ≠ 0) :
    ∃ x w, vol μF (f (b 0)) x = 1 ∧ ω (bdryF ε σ J f s x) w ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_weil_eq hv μF⁻¹
  refine ⟨x, b.dualBasis 0, ?_, ?_⟩
  · rw [vol_apply, hfA, hx, mul_inv_cancel₀ hμF]
  · rw [admissibleF_iff b hJ2 hsA hsB hω]
    exact ⟨hε, by rw [hx]; exact inv_ne_zero hμF, by simp, alt_basis_ne_zero b hω hω0⟩

/-- **(ii) Existence of admissible singular complements** (manuscript line 4902: "and similarly
`y` with `Jv∧y` of unit volume"). `PROVED`. -/
theorem switch_exists_admissible_S {ε σ : K} (hε : ε ≠ 0) (hσ : σ ≠ 0)
    {J : Matrix (Fin 2) (Fin 2) K} (hJ2 : J * J = 1) (hJdet : J.det = -1)
    {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K} (hv : v ≠ 0)
    (hfA : f (b 0) = v) (hfB : f (b 1) = 0) (hsB : s (b 1) = J *ᵥ v)
    {ω : LinearMap.BilinForm K (Module.Dual K R)} (hω : LinearMap.IsAlt ω) (hω0 : ω ≠ 0)
    {μS : K} (hμS : μS ≠ 0) :
    ∃ y w', vol μS (s (b 1)) y = 1 ∧ ω (bdryS ε σ J f s y) w' ≠ 0 := by
  have hJv : J *ᵥ v ≠ 0 := by
    intro h; apply hv; rw [← mulVec_mulVec_of_sq hJ2 v, h, Matrix.mulVec_zero]
  obtain ⟨y, hy⟩ := exists_weil_eq hJv μS⁻¹
  refine ⟨y, b.dualBasis 1, ?_, ?_⟩
  · rw [vol_apply, hsB, hy, mul_inv_cancel₀ hμS]
  · rw [admissibleS_iff b hfA hfB hω]
    refine ⟨hσ, hε, ?_, by simp, alt_basis_ne_zero b hω hω0⟩
    intro h0
    have := weil_J_left hJ2 hJdet v y
    rw [hy, h0, neg_zero] at this
    exact inv_ne_zero hμS this

/-- **(iii) The exact relation between the two class-functional coordinates** (manuscript lines
4903-4905, gap B2-a filled): for all admissible complements,
`u_S = -σ (μ_S / μ_F) u_F`.
Here `H²(C_str) = ⟨A, B⟩^∨` (`GLUE`: Nekovář 6.3.3-6.3.4) with dual basis `A*, B*`;
`∂_F x = ε e₂(x, v) B*`, `∂_S y = σ ε e₂(v, J y) A*`, `λ_A = A**`, `λ_B = B**`, so
`u_F = μ_F / (ε ω(A*,B*))` and `u_S = -μ_S / (σ ε ω(A*,B*))`: "The finite and singular determinant
exact sequences have the same strict factor". The symmetry uses `s(B) = J f(A)` exactly ((4.2)),
`J² = 1` and `det J = -1`; with the manuscript's symmetric pairing (`σ = 1`) the sign is `-1`.
`PROVED`. -/
theorem switch_coord_relation {ε σ : K} (hσ : σ * σ = 1) {J : Matrix (Fin 2) (Fin 2) K}
    (hJ2 : J * J = 1) (hJdet : J.det = -1) {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K}
    (hfA : f (b 0) = v) (hsA : s (b 0) = 0) (hfB : f (b 1) = 0) (hsB : s (b 1) = J *ᵥ v)
    {ω : LinearMap.BilinForm K (Module.Dual K R)} (hω : LinearMap.IsAlt ω)
    {μF μS : K} (hμF : μF ≠ 0) {x y : Fin 2 → K} {w w' : Module.Dual K R}
    (hxw : ω (bdryF ε σ J f s x) w ≠ 0) (hyw : ω (bdryS ε σ J f s y) w' ≠ 0) :
    coordS ε σ J f s ω μS (b 1) y w' = -σ * (μS / μF) * coordF ε σ J f s ω μF (b 0) x w := by
  obtain ⟨hε, -, -, hΩ⟩ := (admissibleF_iff b hJ2 hsA hsB hω x w).1 hxw
  have hσ0 : σ ≠ 0 := left_ne_zero_of_mul_eq_one hσ
  rw [coordS_eq b hJ2 hJdet hfA hfB hsB hω μS hyw, coordF_eq b hJ2 hfA hsA hsB hω μF hxw]
  field_simp
  linear_combination μS * hσ

/-- A sign `σ` with `σ² = 1` is a unit for every valuation. -/
theorem addValuation_eq_zero_of_mul_self_eq_one (ν : AddValuation K (WithTop ℤ)) {σ : K}
    (hσ : σ * σ = 1) : ν σ = 0 := by
  rcases mul_self_eq_one_iff.1 hσ with rfl | rfl
  · exact ν.map_one
  · rw [ν.map_neg, ν.map_one]

/-- **(iv) Equal valuations of the two class-functional determinant coordinates**
(manuscript lines 4849-4851 and 4900-4906, gap B2-a): "the two class-functional determinant
coordinates have equal valuations, even when `v` is not primitive in the local integral lattice."
For every additive valuation `ν` of the fraction/test field with unit volume normalizations
`ν μ_F = ν μ_S = 0`, and for all admissible complements, `ν u_F = ν u_S`.
There is no hypothesis on `v` beyond `v ≠ 0` (implied by admissibility): `v` may be divisible.
There is no hypothesis on `ν ε` or on the common strict factor `ω(A*, B*)` either: "All strict
torsion remains in that common factor", which cancels. The complements `x, y` are taken in the
fraction field. Requiring `x` integral would be wrong when `v` is divisible: if `v = π v₀` with
`ν π > 0` and `v₀` integral, every integral `x` has `ν (vol_F(v, x)) ≥ ν π > 0`
(`switch_integral_complement_not_unit`), so no integral `x` gives `v ∧ x` of unit volume, and the
unit-volume complement is necessarily fractional (`switch_unit_complement_fractional`).
`PROVED`. -/
theorem switch_equal_valuation {ε σ : K} (hσ : σ * σ = 1) {J : Matrix (Fin 2) (Fin 2) K}
    (hJ2 : J * J = 1) (hJdet : J.det = -1) {f s : R →ₗ[K] (Fin 2 → K)} {v : Fin 2 → K}
    (hfA : f (b 0) = v) (hsA : s (b 0) = 0) (hfB : f (b 1) = 0) (hsB : s (b 1) = J *ᵥ v)
    {ω : LinearMap.BilinForm K (Module.Dual K R)} (hω : LinearMap.IsAlt ω)
    (ν : AddValuation K (WithTop ℤ)) {μF μS : K} (hνF : ν μF = 0) (hνS : ν μS = 0)
    {x y : Fin 2 → K} {w w' : Module.Dual K R}
    (hxw : ω (bdryF ε σ J f s x) w ≠ 0) (hyw : ω (bdryS ε σ J f s y) w' ≠ 0) :
    ν (coordF ε σ J f s ω μF (b 0) x w) = ν (coordS ε σ J f s ω μS (b 1) y w') := by
  have hμF : μF ≠ 0 := by
    intro h; rw [h, ν.map_zero] at hνF; exact WithTop.top_ne_zero hνF
  have hνσ := addValuation_eq_zero_of_mul_self_eq_one ν hσ
  have hu : ν (-σ * (μS / μF)) = 0 := by
    have h1 : -σ * (μS / μF) * μF = -σ * μS := by field_simp
    have h2 := congrArg ν h1
    rw [ν.map_mul (-σ * (μS / μF)) μF, hνF, add_zero, ν.map_mul (-σ) μS, ν.map_neg, hνσ, hνS,
      add_zero] at h2
    exact h2
  rw [switch_coord_relation b hσ hJ2 hJdet hfA hsA hfB hsB hω hμF hxw hyw, ν.map_mul, hu,
    zero_add]

end Coordinates

section Integrality

variable {K : Type*} [Field K]

/-- **Why the complement must be fractional** (manuscript line 4906: "Requiring `x` integral would
be wrong when `v` is divisible"). If `v = π v₀` is divisible (`ν π > 0`, `v₀` integral) and the
volume form is integral with unit normalization (`ν μ = 0`), then every integral `x`
(`ν (x i) ≥ 0`) has `ν (vol(v, x)) ≥ ν π > 0`: the volume of `v ∧ x` is never a unit.
`PROVED`. -/
theorem switch_integral_complement_not_unit (ν : AddValuation K (WithTop ℤ)) {μ : K}
    (hμ : ν μ = 0) {π : K} (hπ : 0 < ν π) {v₀ : Fin 2 → K} (hv₀ : ∀ i, 0 ≤ ν (v₀ i))
    {x : Fin 2 → K} (hx : ∀ i, 0 ≤ ν (x i)) : 0 < ν (vol μ (π • v₀) x) := by
  rw [vol_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, ν.map_mul, ν.map_mul, hμ, zero_add]
  have h0 : 0 ≤ ν (weil v₀ x) := by
    rw [weil_apply]
    refine le_trans (le_min ?_ ?_) (ν.map_sub _ _)
    · rw [ν.map_mul]; exact add_nonneg (hv₀ 0) (hx 1)
    · rw [ν.map_mul]; exact add_nonneg (hv₀ 1) (hx 0)
  exact add_pos_of_pos_of_nonneg hπ h0

/-- Consequently a unit-volume complement of a divisible `v` is not integral. `PROVED`. -/
theorem switch_unit_complement_fractional (ν : AddValuation K (WithTop ℤ)) {μ : K}
    (hμ : ν μ = 0) {π : K} (hπ : 0 < ν π) {v₀ : Fin 2 → K} (hv₀ : ∀ i, 0 ≤ ν (v₀ i))
    {x : Fin 2 → K} (hx1 : vol μ (π • v₀) x = 1) : ∃ i, ν (x i) < 0 := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have := switch_integral_complement_not_unit ν hμ hπ hv₀ h
  rw [hx1, ν.map_one] at this
  exact lt_irrefl _ this

end Integrality

section NonVacuity

/-! ### Non-vacuity: the hypotheses of Parts 2 and 3 are jointly satisfiable -/

variable {K : Type*} [Field K]

variable (K) in
/-- A sample involution: `J₀ = diag(1, -1)`, with `J₀² = 1` and `det J₀ = -1`. -/
def switchJ0 : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, -1]

theorem switchJ0_sq : switchJ0 K * switchJ0 K = 1 := by
  rw [Matrix.one_fin_two]
  simp [switchJ0]

theorem switchJ0_det : (switchJ0 K).det = -1 := by
  simp [switchJ0, Matrix.det_fin_two_of]

variable {R : Type*} [AddCommGroup R] [Module K R]

/-- A sample nonzero alternating volume form on `H²(C_str) = R^∨`: the determinant in the dual
basis. -/
def dualVol (b : Basis (Fin 2) K R) : LinearMap.BilinForm K (Module.Dual K R) :=
  weil.compl₁₂ b.dualBasis.equivFun.toLinearMap b.dualBasis.equivFun.toLinearMap

theorem dualVol_isAlt (b : Basis (Fin 2) K R) : LinearMap.IsAlt (dualVol b) :=
  fun w => by simp [dualVol, weil_self]

theorem dualVol_basis (b : Basis (Fin 2) K R) :
    dualVol b (b.dualBasis 0) (b.dualBasis 1) = 1 := by
  simp [dualVol, weil_apply]

theorem dualVol_ne_zero (b : Basis (Fin 2) K R) : dualVol b ≠ 0 := by
  intro h
  have := dualVol_basis b
  rw [h] at this
  simp at this

/-- Non-vacuity of Part 3: for every field `K`, every `v ≠ 0` (primitive or not) and every
valuation `ν`, the data `R = K²` with its standard basis `A, B`, `f = (A ↦ v, B ↦ 0)`,
`s = (A ↦ 0, B ↦ J₀ v)`, `ε = σ = μ_F = μ_S = 1`, `ω = dualVol` satisfy all hypotheses of
`switch_equal_valuation`, with admissible complements. -/
example (ν : AddValuation K (WithTop ℤ)) {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ (x y : Fin 2 → K) (w w' : Module.Dual K (Fin 2 → K)),
      dualVol (Pi.basisFun K (Fin 2)) (bdryF 1 1 (switchJ0 K)
        ((Pi.basisFun K (Fin 2)).constr K ![v, 0])
        ((Pi.basisFun K (Fin 2)).constr K ![0, switchJ0 K *ᵥ v]) x) w ≠ 0 ∧
      dualVol (Pi.basisFun K (Fin 2)) (bdryS 1 1 (switchJ0 K)
        ((Pi.basisFun K (Fin 2)).constr K ![v, 0])
        ((Pi.basisFun K (Fin 2)).constr K ![0, switchJ0 K *ᵥ v]) y) w' ≠ 0 ∧
      ν (coordF 1 1 (switchJ0 K) ((Pi.basisFun K (Fin 2)).constr K ![v, 0])
        ((Pi.basisFun K (Fin 2)).constr K ![0, switchJ0 K *ᵥ v])
        (dualVol (Pi.basisFun K (Fin 2))) 1 (Pi.basisFun K (Fin 2) 0) x w) =
      ν (coordS 1 1 (switchJ0 K) ((Pi.basisFun K (Fin 2)).constr K ![v, 0])
        ((Pi.basisFun K (Fin 2)).constr K ![0, switchJ0 K *ᵥ v])
        (dualVol (Pi.basisFun K (Fin 2))) 1 (Pi.basisFun K (Fin 2) 1) y w') := by
  set b := Pi.basisFun K (Fin 2)
  have hfA : b.constr K ![v, 0] (b 0) = v := by rw [Basis.constr_basis]; rfl
  have hfB : b.constr K ![v, 0] (b 1) = 0 := by rw [Basis.constr_basis]; rfl
  have hsA : b.constr K ![0, switchJ0 K *ᵥ v] (b 0) = 0 := by rw [Basis.constr_basis]; rfl
  have hsB : b.constr K ![0, switchJ0 K *ᵥ v] (b 1) = switchJ0 K *ᵥ v := by
    rw [Basis.constr_basis]; rfl
  obtain ⟨x, w, -, hxw⟩ := switch_exists_admissible_F (σ := 1) b one_ne_zero switchJ0_sq hv
    hfA hsA hsB (dualVol_isAlt b) (dualVol_ne_zero b) one_ne_zero
  obtain ⟨y, w', -, hyw⟩ := switch_exists_admissible_S b one_ne_zero one_ne_zero switchJ0_sq
    switchJ0_det hv hfA hfB hsB (dualVol_isAlt b) (dualVol_ne_zero b) (μS := (1 : K)) one_ne_zero
  exact ⟨x, y, w, w', hxw, hyw, switch_equal_valuation b (mul_one 1) switchJ0_sq switchJ0_det
    hfA hsA hfB hsB (dualVol_isAlt b) ν ν.map_one ν.map_one hxw hyw⟩

/-- Non-vacuity of `switch_new_H1_spanned`: with `U = ⟨(v,0), (0,J₀v)⟩` (self-annihilating by
`span_pair_orthogonal_eq`), `V' = U ∩ S_v`, `K₀ = 0`, the hypotheses hold and `V'` is spanned by
`(0, J₀ v)`. -/
example {v : Fin 2 → K} (hv : v ≠ 0) :
    finrank K (Submodule.span K {((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, switchJ0 K *ᵥ v)} ⊓
      singPlane K (Fin 2 → K) (Fin 2 → K) : Submodule K ((Fin 2 → K) × (Fin 2 → K))) = 1 := by
  set U := Submodule.span K {((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, switchJ0 K *ᵥ v)}
  set V := U ⊓ singPlane K (Fin 2 → K) (Fin 2 → K)
  have hU : (switchPairing (1 : K) 1 (switchJ0 K)).orthogonal U = U :=
    span_pair_orthogonal_eq one_ne_zero one_ne_zero switchJ0_sq hv
  have hvU : ((v, 0) : (Fin 2 → K) × (Fin 2 → K)) ∈ U :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hJvU : ((0, switchJ0 K *ᵥ v) : (Fin 2 → K) × (Fin 2 → K)) ∈ U :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hJv : switchJ0 K *ᵥ v ≠ 0 := by
    intro h; apply hv; rw [← mulVec_mulVec_of_sq switchJ0_sq v, h, Matrix.mulVec_zero]
  have hBV : ((0, switchJ0 K *ᵥ v) : (Fin 2 → K) × (Fin 2 → K)) ∈ V :=
    ⟨hJvU, mem_singPlane.2 rfl⟩
  have hB : (⟨_, hBV⟩ : V) ≠ 0 := by
    intro h
    apply hJv
    have := congrArg (fun z : V => (z : (Fin 2 → K) × (Fin 2 → K)).2) h
    simpa using this
  exact (switch_new_H1_spanned one_ne_zero one_ne_zero switchJ0_sq hv U hU hvU hJvU
    (0 : Unit →ₗ[K] V) V.subtype
    (by rw [LinearMap.range_zero, Submodule.ker_subtype]) (Submodule.range_subtype V) hB).1

/-- Non-vacuity of `switch_new_H1_spanned_of_loc`: on `R = K²` with its standard basis `A, B`,
`f = (A ↦ v, B ↦ 0)` and `s = (A ↦ 0, B ↦ J₀ v)` satisfy all hypotheses (in particular the old
generic `H¹ = ker s` is spanned by `A`, and the relaxed image is self-annihilating). -/
example {v : Fin 2 → K} (hv : v ≠ 0) :
    LinearMap.ker ((Pi.basisFun K (Fin 2)).constr K ![v, 0]) =
      K ∙ (Pi.basisFun K (Fin 2) 1) := by
  set b := Pi.basisFun K (Fin 2)
  set f := b.constr K ![v, 0]
  set s := b.constr K ![0, switchJ0 K *ᵥ v]
  have hJv : switchJ0 K *ᵥ v ≠ 0 := by
    intro h; apply hv; rw [← mulVec_mulVec_of_sq switchJ0_sq v, h, Matrix.mulVec_zero]
  have hf : ∀ c, f c = c 0 • v := by
    intro c; simp [f, b, Basis.constr_apply_fintype, Fin.sum_univ_two]
  have hs : ∀ c, s c = c 1 • (switchJ0 K *ᵥ v) := by
    intro c; simp [s, b, Basis.constr_apply_fintype, Fin.sum_univ_two]
  have hA : LinearMap.ker s = K ∙ b 0 := by
    ext c
    rw [LinearMap.mem_ker, hs, smul_eq_zero, or_iff_left hJv, Submodule.mem_span_singleton]
    constructor
    · intro hc
      refine ⟨c 0, funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩ <;> simp [b, hc]
    · rintro ⟨a, rfl⟩
      simp [b]
  have hrange : LinearMap.range (f.prod s) =
      Submodule.span K {((v, 0) : (Fin 2 → K) × (Fin 2 → K)), (0, switchJ0 K *ᵥ v)} := by
    ext z
    rw [LinearMap.mem_range, Submodule.mem_span_pair]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨c 0, c 1, ?_⟩
      ext i <;> simp [hf, hs]
    · rintro ⟨a, d, rfl⟩
      refine ⟨![a, d], ?_⟩
      ext i <;> simp [hf, hs]
  have hU : (switchPairing (1 : K) 1 (switchJ0 K)).orthogonal (LinearMap.range (f.prod s)) =
      LinearMap.range (f.prod s) := by
    rw [hrange]; exact span_pair_orthogonal_eq one_ne_zero one_ne_zero switchJ0_sq hv
  have hfA : f (b 0) = v := by rw [hf]; simp [b]
  have hfB : f (b 1) = 0 := by rw [hf]; simp [b]
  have hsB : s (b 1) = switchJ0 K *ᵥ v := by rw [hs]; simp [b]
  exact (switch_new_H1_spanned_of_loc one_ne_zero one_ne_zero switchJ0_sq hv f s (b 0) (b 1)
    hA hfA hfB hsB hU).2.2

end NonVacuity

end

end ZInQ.Manuscript.RC.Uniform

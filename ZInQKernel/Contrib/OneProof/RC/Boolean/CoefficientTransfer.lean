import ZInQKernel.Contrib.OneProof.RC.Boolean.MissingAddress
import ZInQKernel.Contrib.OneProof.RC.Boolean.Convolution

/-!
# Lane RC1-boolean, part 6: finite coefficient transfer and the final contradiction

Proposition `ex:limits-coefficient-transfer` (`diophantine_zq.tex` 5647–5664, proof 5665–5739;
restated in Appendix G, 10901–10924), assembled from parts 1–5.

The statement takes as hypotheses exactly what the proof receives:
* from Proposition `ex:limits-fixed-field-clearing`, (5.9) (tex 5487–5645): elements
  `f, d ∈ 𝒪[G]` in the group basis with `f_x ũ_x = d_x` at every sign character, `f_0 ∈ Λ`,
  `c = v₂ f_0(0) ≤ c_det`, and the pole bound: for every `M` and every sign character `x`, all
  coefficients `[t^i] f_x` with `i < −L_T(M)` are divisible by `2^M` (`FixedFieldClearing`);
* from the height-one argument (Proposition `ex:limits-uniform-lower-bound`, tex 4909–5205, as
  used at tex 5703–5704): `ũ_x ∈ Λ[1/2]` at every address (`InLambdaHalf`);
* for the contradiction, from (3.9), (3.4), (4.6) and the unit comparison (4.7) (tex 5729–5731):
  one bound `v₂ ũ_x(0) ≤ B` at every nonzero address, with `B` fixed before `b`;
* the choice (5.10) of `M` and `b` (`Choice510`), which refers only to `c_det`, `B`, `d_K`.

Elements of `𝒪` are recorded by their Laurent coefficients (see `Convolution.lean`). `v₂` is
Mathlib's `Padic.addValuation` on `ℚ₂` (with `v₂(0) = ⊤`) and `PadicInt.valuation` on `ℤ₂`.

Main results (kind PROVED):
* `coefficient_transfer_at`: the argument at one precision `M` and cutoff `L`;
* `coefficient_transfer`: some nonzero address `x` has `v₂(ũ_x(0) − ũ_0(0)) ≥ M − 2c > B`;
* `base_coordinate_ne_zero`, `coefficient_transfer_contradiction`: with the bound `B` at nonzero
  addresses, `ũ_0(0) ≠ 0`; so the conclusion `ũ_0(0) = 0` of Lemma `ex:arith-base-zero` under
  `L'(E/K,1) = 0` is contradicted (tex 5659–5661, 5732–5733);
* `base_coordinate_ne_zero_of_le`: the order of choices (`M`, then `b`, from `c_det, d_K, B` only);
* `FixedFieldClearing.of_addValuation_le`: (5.9) with `v₂ f_0(0) ≤ c_det` read in `ℤ ∪ {⊤}`.
Non-vacuity of the hypotheses: `coefficientTransfer_hypotheses_satisfiable` (`Examples.lean`).
-/

namespace ZInQ.Manuscript.RC.Boolean

open Finset

variable {b : ℕ} {G : Type*} [Fintype G]

/-- The constant coefficient `f_0(0) = [t^0] f_0` of `f` at the trivial character (the augmentation
of the group-basis coefficient `[t^0] f`). -/
noncomputable def fZeroConst (ℓ : G → Address b →+ ZMod 2) (f : G → ℤ → ℤ_[2]) : ℤ_[2] :=
  signEval ℓ (fun g => f g 0) 0

/-- **What (5.9) provides** (Proposition `ex:limits-fixed-field-clearing`, tex 5487–5507 and
5619–5645; kind: the output of lane RC7's proposition, recorded as a predicate). The data:
`f g i = [t^i] f_g` and `d g i = [t^i] d_g` are the Laurent coefficients of the group-basis
coefficients of `f = 2^a Δ^4` and `d = η Δ Q` in `𝒪[G]`, and `u x n = [t^n] ũ_x` are those of the
corrected coordinate at the address `x`. The sign evaluation at `x` of `[t^i] f` is
`[t^i] f_x = signEval ℓ (fun g => f g i) x`. -/
structure FixedFieldClearing (ℓ : G → Address b →+ ZMod 2) (f d : G → ℤ → ℤ_[2])
    (u : Address b → ℕ → ℚ_[2]) (cdet dK : ℕ) : Prop where
  /-- `f_x ũ_x = d_x` at every sign character, including `Δ_x = 0` (tex 5495–5496, 5619–5624):
  `[t^n] d_x = Σ_{k ≥ 0} [t^{n−k}] f_x · [t^k] ũ_x`. -/
  identity : ∀ (x : Address b) (n : ℤ),
    HasSum (fun k : ℕ => ((signEval ℓ (fun g => f g (n - k)) x : ℤ_[2]) : ℚ_[2]) * u x k)
      ((signEval ℓ (fun g => d g n) x : ℤ_[2]) : ℚ_[2])
  /-- `f_0 ∈ Λ`: no negative powers of `t` at the trivial character (tex 5497, 5625). -/
  f_zero_mem_Lambda : ∀ i : ℤ, i < 0 → signEval ℓ (fun g => f g i) 0 = 0
  /-- `c = v₂ f_0(0)` is finite (tex 5627). -/
  fZeroConst_ne_zero : fZeroConst ℓ f ≠ 0
  /-- `c = v₂ f_0(0) ≤ c_det` (5.9) (tex 5627). -/
  valuation_le_cdet : (fZeroConst ℓ f).valuation ≤ cdet
  /-- The pole bound (5.9): `L_T(M) = 16(d_K+5)M` bounds the negative Laurent support of every
  `f_x` modulo `2^M`, uniformly in the sign character (tex 5499–5503, 5630–5639). -/
  pole : ∀ (M : ℕ) (x : Address b) (i : ℤ), i < -(LT dK M : ℤ) →
    (2 : ℤ_[2]) ^ M ∣ signEval ℓ (fun g => f g i) x

/-- `v₂ f_0(0) ≤ c_det` written with `v₂ : ℚ₂ → ℤ ∪ {⊤}` (`v₂(0) = ⊤`, as lane RC0 states (5.9))
already gives `f_0(0) ≠ 0` and `c ≤ c_det`. -/
theorem ne_zero_and_valuation_le_of_addValuation_le {z : ℤ_[2]} {cdet : ℕ}
    (h : Padic.addValuation (z : ℚ_[2]) ≤ ((cdet : ℤ) : WithTop ℤ)) :
    z ≠ 0 ∧ z.valuation ≤ cdet := by
  have hz : z ≠ 0 := by
    rintro rfl
    simp at h
  refine ⟨hz, ?_⟩
  have hz' : (z : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.2 hz
  rw [Padic.addValuation.apply hz', WithTop.coe_le_coe, PadicInt.valuation_coe] at h
  exact_mod_cast h

/-- `FixedFieldClearing` from (5.9) with `v₂ f_0(0) ≤ c_det` stated through `v₂ : ℚ₂ → ℤ ∪ {⊤}`. -/
theorem FixedFieldClearing.of_addValuation_le {ℓ : G → Address b →+ ZMod 2}
    {f d : G → ℤ → ℤ_[2]} {u : Address b → ℕ → ℚ_[2]} {cdet dK : ℕ}
    (identity : ∀ (x : Address b) (n : ℤ),
      HasSum (fun k : ℕ => ((signEval ℓ (fun g => f g (n - k)) x : ℤ_[2]) : ℚ_[2]) * u x k)
        ((signEval ℓ (fun g => d g n) x : ℤ_[2]) : ℚ_[2]))
    (f_zero_mem_Lambda : ∀ i : ℤ, i < 0 → signEval ℓ (fun g => f g i) 0 = 0)
    (hv : Padic.addValuation (fZeroConst ℓ f : ℚ_[2]) ≤ ((cdet : ℤ) : WithTop ℤ))
    (pole : ∀ (M : ℕ) (x : Address b) (i : ℤ), i < -(LT dK M : ℤ) →
      (2 : ℤ_[2]) ^ M ∣ signEval ℓ (fun g => f g i) x) :
    FixedFieldClearing ℓ f d u cdet dK :=
  ⟨identity, f_zero_mem_Lambda, (ne_zero_and_valuation_le_of_addValuation_le hv).1,
    (ne_zero_and_valuation_le_of_addValuation_le hv).2, pole⟩

/-- **The coefficient transfer at one precision** (tex 5666–5726; kind PROVED). Fix the precision
`M` and a cutoff `L` with `(L + 2)(2^{M−1} − 1) < b`. Suppose `f_x ũ_x = d_x` at every address,
`ũ_x ∈ Λ[1/2]`, `f_0 ∈ Λ` with `c = v₂ f_0(0) < M`, and every `[t^i] f_x` with `i < −L` divisible
by `2^M`. Then some nonzero address has `v₂(ũ_x(0) − ũ_0(0)) ≥ M − 2c`. This is the whole argument
of the proof: the `L + 2` tested coefficients (the coefficients of `f` from `−L` through `0` and the
constant coefficient of `d`) agree with the base modulo `2^M` at some `x ≠ 0` (Boolean degree and
cube parity), and the convolution estimate (5.11) applies there. -/
theorem coefficient_transfer_at (ℓ : G → Address b →+ ZMod 2) {f d : G → ℤ → ℤ_[2]}
    {u : Address b → ℕ → ℚ_[2]} {L M c : ℕ}
    (identity : ∀ (x : Address b) (n : ℤ),
      HasSum (fun k : ℕ => ((signEval ℓ (fun g => f g (n - k)) x : ℤ_[2]) : ℚ_[2]) * u x k)
        ((signEval ℓ (fun g => d g n) x : ℤ_[2]) : ℚ_[2]))
    (hreg : ∀ x, InLambdaHalf (u x))
    (hΛ : ∀ i : ℤ, i < 0 → signEval ℓ (fun g => f g i) 0 = 0)
    (hne : fZeroConst ℓ f ≠ 0) (hc : (fZeroConst ℓ f).valuation = c) (hcM : c < M)
    (hpole : ∀ (x : Address b) (i : ℤ), i < -(L : ℤ) →
      (2 : ℤ_[2]) ^ M ∣ signEval ℓ (fun g => f g i) x)
    (hb : (L + 2) * (2 ^ (M - 1) - 1) < b) :
    ∃ x : Address b, x ≠ 0 ∧ ‖u x 0 - u 0 0‖ ≤ (2 : ℝ) ^ (2 * (c : ℤ) - M) := by
  -- the Boolean step: the tested coefficients agree with the base modulo `2^M` at some `x ≠ 0`
  obtain ⟨x, hx0, htf, htd⟩ := exists_address_of_tested ℓ f d L M hb
  refine ⟨x, hx0, ?_⟩
  -- negative coefficients of `f_x` vanish modulo `2^M`: the tested range, and the pole bound
  -- below the cutoff (so the convolution includes every negative coefficient)
  have hneg : ∀ i : ℤ, i < 0 → (2 : ℤ_[2]) ^ M ∣ signEval ℓ (fun g => f g i) x := by
    intro i hi
    by_cases hiL : -(L : ℤ) ≤ i
    · have h1 := htf i hiL hi.le
      rwa [hΛ i hi, sub_zero] at h1
    · exact hpole x i (lt_of_not_ge hiL)
  exact difference_estimate (F₀ := fun i => signEval ℓ (fun g => f g i) 0)
    (Fx := fun i => signEval ℓ (fun g => f g i) x) (U₀ := u 0) (Ux := u x)
    (D₀ := fun n => signEval ℓ (fun g => d g n) 0) (Dx := fun n => signEval ℓ (fun g => d g n) x)
    (hreg x) (identity 0 0) (identity x) hΛ hne hc hcM hneg (htf 0 (by simp) le_rfl) htd

/-- **Proposition `ex:limits-coefficient-transfer`: the address** (tex 5647–5658, proof
5665–5726; kind PROVED). For a binary family over `𝔽₂^b` with the fixed-field clearing data (5.9)
and `ũ_x ∈ Λ[1/2]` at every address, if `M, b` satisfy (5.10) then for some nonzero address `x`,
`v₂(ũ_x(0) − ũ_0(0)) ≥ M − 2c > B` with `c = v₂ f_0(0) ≤ c_det`. The convolution includes every
negative Laurent coefficient of `f_x`. -/
theorem coefficient_transfer (ℓ : G → Address b →+ ZMod 2) {f d : G → ℤ → ℤ_[2]}
    {u : Address b → ℕ → ℚ_[2]} {cdet dK M : ℕ} {B : ℤ}
    (h59 : FixedFieldClearing ℓ f d u cdet dK) (hreg : ∀ x, InLambdaHalf (u x))
    (h510 : Choice510 cdet B dK M b) :
    ∃ x : Address b, x ≠ 0 ∧
      ((((M : ℤ) - 2 * ((fZeroConst ℓ f).valuation : ℤ) : ℤ) : WithTop ℤ) ≤
        Padic.addValuation (u x 0 - u 0 0)) ∧
      B < (M : ℤ) - 2 * ((fZeroConst ℓ f).valuation : ℤ) := by
  have hcM : (fZeroConst ℓ f).valuation < M :=
    lt_of_le_of_lt h59.valuation_le_cdet h510.cdet_lt
  obtain ⟨x, hx0, hest⟩ := coefficient_transfer_at ℓ h59.identity hreg h59.f_zero_mem_Lambda
    h59.fZeroConst_ne_zero rfl hcM (h59.pole M) h510.degree_sum_lt
  refine ⟨x, hx0, ?_, ?_⟩
  · -- from the norm bound to the valuation bound
    by_cases hz : u x 0 - u 0 0 = 0
    · rw [hz, AddValuation.map_zero]
      exact le_top
    · rw [Padic.addValuation.apply hz, WithTop.coe_le_coe]
      rw [Padic.norm_eq_zpow_neg_valuation hz] at hest
      have h2 : (1 : ℝ) < (2 : ℝ) := by norm_num
      have h3 : (2 : ℝ) ^ (-(u x 0 - u 0 0).valuation) ≤
          (2 : ℝ) ^ (2 * ((fZeroConst ℓ f).valuation : ℤ) - (M : ℤ)) := by
        exact_mod_cast hest
      have := (zpow_le_zpow_iff_right₀ h2).mp h3
      omega
  · have h1 := h510.bound_lt
    have h2 : ((fZeroConst ℓ f).valuation : ℤ) ≤ cdet := by exact_mod_cast h59.valuation_le_cdet
    omega

/-- **The base coordinate is nonzero** (tex 5729–5733; kind PROVED). If moreover every nonzero
address has `v₂ ũ_x(0) ≤ B` (the bound supplied by (3.9), (3.4), (4.6) and (4.7), with `B` fixed
before `b`), then `ũ_0(0) ≠ 0`. -/
theorem base_coordinate_ne_zero (ℓ : G → Address b →+ ZMod 2) {f d : G → ℤ → ℤ_[2]}
    {u : Address b → ℕ → ℚ_[2]} {cdet dK M : ℕ} {B : ℤ}
    (h59 : FixedFieldClearing ℓ f d u cdet dK) (hreg : ∀ x, InLambdaHalf (u x))
    (h510 : Choice510 cdet B dK M b)
    (hB : ∀ x : Address b, x ≠ 0 → Padic.addValuation (u x 0) ≤ (B : WithTop ℤ)) :
    u 0 0 ≠ 0 := by
  intro hbase
  obtain ⟨x, hx0, hv, hMB⟩ := coefficient_transfer ℓ h59 hreg h510
  rw [hbase, sub_zero] at hv
  have h1 := (hB x hx0).trans' hv
  have h2 := WithTop.coe_le_coe.mp h1
  omega

/-- **The final contradiction** (tex 5659–5661 and 5732–5733; kind PROVED). Lemma
`ex:arith-base-zero` gives `ũ_0(0) = 0` if `L'(E/K,1) = 0`; together with the data above this is
contradictory. Hence `L'(E/K,1) ≠ 0` (the deduction of `ord_{s=1} L(E,s) = 1` from it, through
`L(E/K,s) = L(E,s) L(E^{(k)},s)` and `L(E^{(k)},1) ≠ 0`, is the skeleton's). -/
theorem coefficient_transfer_contradiction (ℓ : G → Address b →+ ZMod 2) {f d : G → ℤ → ℤ_[2]}
    {u : Address b → ℕ → ℚ_[2]} {cdet dK M : ℕ} {B : ℤ}
    (h59 : FixedFieldClearing ℓ f d u cdet dK) (hreg : ∀ x, InLambdaHalf (u x))
    (h510 : Choice510 cdet B dK M b)
    (hB : ∀ x : Address b, x ≠ 0 → Padic.addValuation (u x 0) ≤ (B : WithTop ℤ))
    (hbase : u 0 0 = 0) : False :=
  base_coordinate_ne_zero ℓ h59 hreg h510 hB hbase

/-- **The order of choices** (tex 5650–5653, 5688–5693, 10910–10912; kind PROVED). Given `c_det`,
`d_K` (fixed with `K`) and the bound `B` (fixed before `b`), there are `M` and `b₀` such that for
every `b ≥ b₀` and every binary family over `𝔽₂^b` with the clearing data (5.9) for `c_det, d_K`,
`ũ_x ∈ Λ[1/2]`, and `v₂ ũ_x(0) ≤ B` at every nonzero address, the base coordinate `ũ_0(0)` is
nonzero; `M` and `b₀` depend only on `c_det, d_K, B`. -/
theorem base_coordinate_ne_zero_of_le (cdet dK : ℕ) (B : ℤ) :
    ∃ M b₀ : ℕ, max (cdet : ℤ) (B + 2 * cdet) < M ∧ ∀ b : ℕ, b₀ ≤ b →
      ∀ (G : Type) [Fintype G] (ℓ : G → Address b →+ ZMod 2) (f d : G → ℤ → ℤ_[2])
        (u : Address b → ℕ → ℚ_[2]), FixedFieldClearing ℓ f d u cdet dK →
        (∀ x, InLambdaHalf (u x)) →
        (∀ x : Address b, x ≠ 0 → Padic.addValuation (u x 0) ≤ (B : WithTop ℤ)) →
        u 0 0 ≠ 0 := by
  obtain ⟨M, hM, hb⟩ := choice510_exists cdet B dK
  refine ⟨M, (LT dK M + 2) * (2 ^ M - 1) + 1, hM, fun b hb₀ G _ ℓ f d u h59 hreg hB => ?_⟩
  exact base_coordinate_ne_zero ℓ h59 hreg (hb b (by omega)) hB

end ZInQ.Manuscript.RC.Boolean

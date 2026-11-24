import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! Finite limits of a field of meromorphic germs at a complex parameter. -/

noncomputable section

namespace ShimuraPointDict

open Filter
open scoped Topology

/-- Germs here use a punctured neighbourhood, so they do not depend on a value at the parameter. -/
abbrev PuncturedGerm (z : ℂ) := Germ (𝓝[≠] z) ℂ

/-- A germ has a specified finite limit. -/
def HasValue {z : ℂ} (g : PuncturedGerm z) (c : ℂ) : Prop :=
  g.liftOn (fun f => Tendsto f (𝓝[≠] z) (𝓝 c)) (fun _ _ h => propext (tendsto_congr' h))

theorem hasValue_coe {z c : ℂ} {f : ℂ → ℂ} :
    HasValue (f : PuncturedGerm z) c ↔ Tendsto f (𝓝[≠] z) (𝓝 c) := Iff.rfl

theorem hasValue_unique {z c d : ℂ} {g : PuncturedGerm z}
    (hc : HasValue g c) (hd : HasValue g d) : c = d := by
  induction g using Germ.inductionOn with
  | h f => exact tendsto_nhds_unique (hasValue_coe.mp hc) (hasValue_coe.mp hd)

private theorem hasValue_const (z c : ℂ) : HasValue (Germ.const c : PuncturedGerm z) c :=
  tendsto_const_nhds

private theorem hasValue_add {z c d : ℂ} {f g : PuncturedGerm z}
    (hf : HasValue f c) (hg : HasValue g d) : HasValue (f + g) (c + d) := by
  induction f, g using Germ.inductionOn₂ with
  | h f g => exact (hasValue_coe.mp hf).add (hasValue_coe.mp hg)

private theorem hasValue_mul {z c d : ℂ} {f g : PuncturedGerm z}
    (hf : HasValue f c) (hg : HasValue g d) : HasValue (f * g) (c * d) := by
  induction f, g using Germ.inductionOn₂ with
  | h f g => exact (hasValue_coe.mp hf).mul (hasValue_coe.mp hg)

private theorem hasValue_neg {z c : ℂ} {f : PuncturedGerm z}
    (hf : HasValue f c) : HasValue (-f) (-c) := by
  induction f using Germ.inductionOn with
  | h f => exact (hasValue_coe.mp hf).neg

/-- A germ represented by an eventually nonzero function is a unit. -/
theorem isUnit_germ_of_eventually_ne_zero {z : ℂ} {f : ℂ → ℂ}
    (hf : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0) : IsUnit (f : PuncturedGerm z) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨((fun w => (f w)⁻¹) : PuncturedGerm z), Germ.coe_eq.mpr ?_⟩
  filter_upwards [hf] with w hw using mul_inv_cancel₀ hw

private theorem inverse_germ_eq {z : ℂ} {f : ℂ → ℂ} {g : PuncturedGerm z}
    (h : (f : PuncturedGerm z) * g = 1) :
    g = ((fun w => (f w)⁻¹) : PuncturedGerm z) := by
  induction g using Germ.inductionOn with
  | h k =>
    have h' := Germ.coe_eq.mp (show ((f * k : ℂ → ℂ) : PuncturedGerm z) = Germ.const 1 from h)
    apply Germ.coe_eq.mpr
    filter_upwards [h'] with w hw
    change f w * k w = 1 at hw
    exact inv_eq_of_mul_eq_one_left (mul_comm (f w) (k w) ▸ hw) |>.symm

section FieldGerms

variable {K : Type} [Field K] {z : ℂ} (φ : K →+* PuncturedGerm z)

/-- Rational functions with finite values form a subring. -/
def finiteSubring : Subring K where
  carrier := {g | ∃ c, HasValue (φ g) c}
  zero_mem' := ⟨0, by rw [map_zero]; exact hasValue_const z 0⟩
  one_mem' := ⟨1, by rw [map_one]; exact hasValue_const z 1⟩
  add_mem' := by rintro a b ⟨c, hc⟩ ⟨d, hd⟩; exact ⟨c + d, by rw [map_add]; exact hasValue_add hc hd⟩
  mul_mem' := by rintro a b ⟨c, hc⟩ ⟨d, hd⟩; exact ⟨c * d, by rw [map_mul]; exact hasValue_mul hc hd⟩
  neg_mem' := by rintro a ⟨c, hc⟩; exact ⟨-c, by rw [map_neg]; exact hasValue_neg hc⟩

/-- The inverse of a rational function with a pole has limit zero. -/
theorem hasValue_inv_of_not_mem {g : K}
    (hφ : ∀ g, ∃ f : ℂ → ℂ, (f : PuncturedGerm z) = φ g ∧ MeromorphicAt f z)
    (h : g ∉ finiteSubring φ) : HasValue (φ g⁻¹) 0 := by
  obtain ⟨f, hf, hfm⟩ := hφ g
  have ho : meromorphicOrderAt f z < 0 := lt_of_not_ge fun ho => by
    obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hfm ho
    exact h ⟨c, hf ▸ hasValue_coe.mpr hc⟩
  have hg : g ≠ 0 := fun hg => h (hg ▸ (finiteSubring φ).zero_mem)
  have he := inverse_germ_eq (g := φ g⁻¹) (by rw [hf, ← map_mul, mul_inv_cancel₀ hg, map_one])
  refine he.symm ▸ hasValue_coe.mpr (tendsto_zero_of_meromorphicOrderAt_pos ?_)
  change 0 < meromorphicOrderAt (f⁻¹) z
  rw [meromorphicOrderAt_inv]
  exact LinearOrderedAddCommGroupWithTop.neg_pos.mpr (Or.inl ho)

/-- If every image germ is meromorphic, the subring of finite values is a valuation subring. -/
def finiteValuationSubring
    (hφ : ∀ g, ∃ f : ℂ → ℂ, (f : PuncturedGerm z) = φ g ∧ MeromorphicAt f z) :
    ValuationSubring K :=
  ValuationSubring.ofSubring (finiteSubring φ) <| by
    intro g
    by_cases h : g ∈ finiteSubring φ
    · exact Or.inl h
    · exact Or.inr ⟨0, hasValue_inv_of_not_mem φ hφ h⟩

/-- Evaluation as a ring homomorphism on the subring of finite germs. -/
def finiteValue : finiteSubring φ →+* ℂ where
  toFun g := g.property.choose
  map_zero' := hasValue_unique (show HasValue (φ 0) _ from (Subtype.property (0 : finiteSubring φ)).choose_spec)
    (by rw [map_zero]; exact hasValue_const z 0)
  map_one' := hasValue_unique (show HasValue (φ 1) _ from (Subtype.property (1 : finiteSubring φ)).choose_spec)
    (by rw [map_one]; exact hasValue_const z 1)
  map_add' a b := hasValue_unique (Subtype.property (a + b)).choose_spec
    (by change HasValue (φ ((a : K) + b)) _; rw [map_add]
        exact hasValue_add a.property.choose_spec b.property.choose_spec)
  map_mul' a b := hasValue_unique (Subtype.property (a * b)).choose_spec
    (by change HasValue (φ ((a : K) * b)) _; rw [map_mul]
        exact hasValue_mul a.property.choose_spec b.property.choose_spec)

theorem finiteValue_spec (g : finiteSubring φ) : HasValue (φ g.val) (finiteValue φ g) :=
  g.property.choose_spec

end FieldGerms

#print axioms hasValue_coe
#print axioms hasValue_unique
#print axioms hasValue_const
#print axioms hasValue_add
#print axioms hasValue_mul
#print axioms hasValue_neg
#print axioms isUnit_germ_of_eventually_ne_zero
#print axioms inverse_germ_eq
#print axioms hasValue_inv_of_not_mem
#print axioms finiteValue_spec

end ShimuraPointDict

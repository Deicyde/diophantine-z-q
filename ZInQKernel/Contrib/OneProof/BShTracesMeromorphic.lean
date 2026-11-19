import ZInQKernel.Contrib.OneProof.ShimuraPointDictField
import Mathlib.Algebra.Field.IsField

/-! ON THE SPOT (provenance (c)): the meromorphic part of the punctured germ
ring is a field. Its finite-value subring is the valuation used for the trace. -/

noncomputable section

namespace BShTraces

open Filter ShimuraPointDict AlgebraicGeometry CategoryTheory LeafModCurves AfTateLam
open scoped Topology

/-- Punctured germs that admit meromorphic representatives. -/
def meromorphicSubring (z : ℂ) : Subring (PuncturedGerm z) where
  carrier := { g | ∃ f : ℂ → ℂ, (f : PuncturedGerm z) = g ∧ MeromorphicAt f z }
  zero_mem' := ⟨fun _ => 0, rfl, MeromorphicAt.const _ _⟩
  one_mem' := ⟨fun _ => 1, rfl, MeromorphicAt.const _ _⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨_, rfl, hf.add hg⟩
  mul_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨_, rfl, hf.mul hg⟩
  neg_mem' := by
    rintro _ ⟨f, rfl, hf⟩
    exact ⟨_, rfl, hf.neg⟩

abbrev MeromorphicGerm (z : ℂ) := meromorphicSubring z

private theorem meromorphic_isField (z : ℂ) : IsField (MeromorphicGerm z) where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    rintro ⟨g, f, rfl, hf⟩ hne
    have he : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
      refine hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h => hne ?_
      exact Subtype.ext (Germ.coe_eq.mpr h)
    refine ⟨⟨((fun w => (f w)⁻¹) : PuncturedGerm z), _, rfl, hf.inv⟩, Subtype.ext ?_⟩
    change ((fun w => f w * (f w)⁻¹) : PuncturedGerm z) = (fun _ : ℂ => (1 : ℂ))
    exact Germ.coe_eq.mpr (he.mono fun w hw => mul_inv_cancel₀ hw)

instance (z : ℂ) : Field (MeromorphicGerm z) := (meromorphic_isField z).toField

/-- The inclusion into the punctured germ ring. -/
abbrev meromorphicIncl (z : ℂ) : MeromorphicGerm z →+* PuncturedGerm z :=
  (meromorphicSubring z).subtype

/-- The finite limit condition on a meromorphic germ cuts out a valuation ring. -/
def meromorphicValuation (z : ℂ) : ValuationSubring (MeromorphicGerm z) :=
  finiteValuationSubring (meromorphicIncl z) fun g => g.property

variable {X : Over SpecQ} [IsIntegral X.left] {N : ℕ} {jX tX : X.left.functionField}

/-- The model's germ realization factors through the field of meromorphic germs. -/
def meromorphicFieldGerm (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : UpperHalfPlane) :
    X.left.functionField →+* MeromorphicGerm (τ : ℂ) :=
  (fieldGerm hN hG τ).codRestrict _ (fieldGerm_meromorphic hN hG τ)

open Polynomial X1Igusa.Weber in
/-- The model's two named generators are represented by the holomorphic
extensions of the analytic coordinates, including near exceptional parameters. -/
theorem fieldGerm_coordinates (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (τ : UpperHalfPlane) :
    fieldGerm hN hG τ jX = (Jf : PuncturedGerm (τ : ℂ)) ∧
    fieldGerm hN hG τ tX = (Wf N : PuncturedGerm (τ : ℂ)) := by
  have e (P : Polynomial (Polynomial ℤ)) :
      fieldGerm hN hG τ (algEval jX tX P) =
        ((fun z : ℂ => ez N z (AfTateOr.toQ P)) : PuncturedGerm (τ : ℂ)) := by
    simpa only [map_one, div_one] using
      fieldGerm_fraction hN hG τ P 1 (show algEval jX tX 1 ≠ 0 by simp)
  exact ⟨by simpa [algEval, ez, AfTateOr.toQ] using e (C Polynomial.X),
    by simpa [algEval, ez, AfTateOr.toQ] using e Polynomial.X⟩

open X1Igusa.Weber in
/-- The two exceptional values of the generic (j)-coordinate are excluded. -/
theorem generic_j_ne (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) :
    jX ≠ 0 ∧ jX ≠ 1728 := by
  have hj (τ : UpperHalfPlane) :
      HasValue (fieldGerm hN hG τ jX) (Jf (τ : ℂ)) := by
    rw [(fieldGerm_coordinates hN hG τ).1, hasValue_coe]
    have h : ContinuousAt Jf (τ : ℂ) :=
      (diffOn_Jf.differentiableAt (isOpen_Hs.mem_nhds τ.coe_im_pos)).continuousAt
    exact h.tendsto.mono_left nhdsWithin_le_nhds
  constructor
  · intro h
    have he := hj UpperHalfPlane.I
    rw [congrArg (fieldGerm hN hG UpperHalfPlane.I) h, map_zero, Jf_I] at he
    have hh : (0 : ℂ) = 1728 := hasValue_unique
      ( (hasValue_coe (f := fun _ => 0)).mpr tendsto_const_nhds) he
    norm_num at hh
  · intro h
    have he := hj τρ
    rw [congrArg (fieldGerm hN hG τρ) h, map_ofNat, Jf_ρ] at he
    have hh : (1728 : ℂ) = 0 := hasValue_unique
      ( (hasValue_coe (f := fun _ => 1728)).mpr tendsto_const_nhds) he
    norm_num at hh

#print axioms meromorphic_isField
#print axioms fieldGerm_coordinates
#print axioms generic_j_ne

end BShTraces

import ZInQKernel.Contrib.DifferentBound.Global
import Mathlib.RingTheory.Trace.Basic

/-!
# Exact absolute-different and prime invariants under a number-field isomorphism

The map of integer rings is the restriction of the actual rational algebra
isomorphism. Trace compatibility proves equivalence of the actual complementary
modules and hence of the actual absolute differents over Z. Ideal equivalence
preserves multiplicities, and the pinned ramification-index comparison identifies
the actual length-defined ramification indices. No different/model comparison,
Serre bound or Hilbert formula is assumed.
-/

namespace ZInQ.Contrib.DifferentBound

open NumberField

variable {L K : Type*} [Field L] [NumberField L] [Field K] [NumberField K]

/-- The actual number-field isomorphism restricted to integer rings, over the actual base Z. -/
def integersEquiv (e : L ≃ₐ[ℚ] K) : 𝓞 L ≃ₐ[ℤ] 𝓞 K :=
  (e.restrictScalars ℤ).mapIntegralClosure

/-- The restriction agrees with the original field isomorphism, integrally. -/
@[simp]
theorem integersEquiv_coe (e : L ≃ₐ[ℚ] K) (x : 𝓞 L) :
    ((integersEquiv e x : 𝓞 K) : K) = e (x : L) :=
  AlgEquiv.coe_mapIntegralClosure (e.restrictScalars ℤ) x

/-- Actual integral field elements are preserved in both directions. -/
theorem integer_one_mem_equiv (e : L ≃ₐ[ℚ] K) (x : L) :
    e x ∈ (1 : Submodule (𝓞 K) K) ↔ x ∈ (1 : Submodule (𝓞 L) L) := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hx
    refine Submodule.mem_one.mpr ⟨(integersEquiv e).symm a, ?_⟩
    apply e.injective
    rw [← integersEquiv_coe e, AlgEquiv.apply_symm_apply]
    exact ha
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hx
    exact Submodule.mem_one.mpr ⟨integersEquiv e a, integersEquiv_coe e a⟩

/-- The trace-dual of the actual integer ring maps into the trace-dual of the isomorphic one. -/
theorem traceDual_one_mem_forward (e : L ≃ₐ[ℚ] K) (x : L)
    (hx : x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 L) L)) :
    e x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K) := by
  rw [Submodule.mem_traceDual] at hx ⊢
  intro a ha
  have ha' : e.symm a ∈ (1 : Submodule (𝓞 L) L) :=
    (integer_one_mem_equiv e (e.symm a)).mp (by simpa only [AlgEquiv.apply_symm_apply] using ha)
  have h := hx (e.symm a) ha'
  have htrace : Algebra.traceForm ℚ K (e x) a = Algebra.traceForm ℚ L x (e.symm a) := by
    rw [Algebra.traceForm_apply, Algebra.traceForm_apply]
    calc
      Algebra.trace ℚ K (e x * a) = Algebra.trace ℚ K (e (x * e.symm a)) := by
        rw [map_mul e, AlgEquiv.apply_symm_apply]
      _ = Algebra.trace ℚ L (x * e.symm a) := Algebra.trace_eq_of_algEquiv e _
  exact htrace.symm ▸ h

/-- The trace-dual of the actual integer ring is preserved by the actual field isomorphism. -/
theorem traceDual_one_mem_equiv (e : L ≃ₐ[ℚ] K) (x : L) :
    e x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K) ↔
      x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 L) L) := by
  constructor
  · intro hx
    simpa only [AlgEquiv.symm_apply_apply] using traceDual_one_mem_forward e.symm (e x) hx
  · exact traceDual_one_mem_forward e x

/-- The actual different is the inverse of the actual complementary module, elementwise.
This is a consequence of Mathlib's coeSubmodule_differentIdeal, not an extra different axiom. -/
theorem mem_absoluteDifferent_iff_traceDual (d : 𝓞 L) :
    d ∈ differentIdeal ℤ (𝓞 L) ↔
      ∀ x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 L) L),
        x * (d : L) ∈ (1 : Submodule (𝓞 L) L) := by
  constructor
  · intro hd x hx
    have hmem : (d : L) ∈ 1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 L) L) := by
      rw [← coeSubmodule_differentIdeal ℤ ℚ]
      exact ⟨d, hd, rfl⟩
    rw [mul_comm]
    exact Submodule.mem_div_iff_forall_mul_mem.mp hmem x hx
  · intro hd
    have hmem : (d : L) ∈ IsLocalization.coeSubmodule L (differentIdeal ℤ (𝓞 L)) := by
      rw [coeSubmodule_differentIdeal ℤ ℚ]
      exact Submodule.mem_div_iff_forall_mul_mem.mpr fun x hx ↦ mul_comm x _ ▸ hd x hx
    obtain ⟨d', hd', heq⟩ := hmem
    exact (NumberField.RingOfIntegers.coe_injective heq) ▸ hd'

/-- Membership in the actual absolute different is preserved by the restricted isomorphism. -/
theorem absoluteDifferent_mem_equiv (e : L ≃ₐ[ℚ] K) (d : 𝓞 L) :
    integersEquiv e d ∈ differentIdeal ℤ (𝓞 K) ↔ d ∈ differentIdeal ℤ (𝓞 L) := by
  rw [mem_absoluteDifferent_iff_traceDual, mem_absoluteDifferent_iff_traceDual]
  constructor
  · intro hd x hx
    have h := hd (e x) ((traceDual_one_mem_equiv e x).mpr hx)
    rw [integersEquiv_coe, ← map_mul] at h
    exact (integer_one_mem_equiv e _).mp h
  · intro hd x hx
    have hx' : e.symm x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 L) L) :=
      (traceDual_one_mem_equiv e (e.symm x)).mp (by simpa only [AlgEquiv.apply_symm_apply] using hx)
    have h := (integer_one_mem_equiv e _).mpr (hd (e.symm x) hx')
    simpa only [map_mul, AlgEquiv.apply_symm_apply, integersEquiv_coe] using h

/-- Literal ideal transport of the actual absolute different, over Z rather than O(Q). -/
theorem map_absoluteDifferent_equiv (e : L ≃ₐ[ℚ] K) :
    (differentIdeal ℤ (𝓞 L)).map (integersEquiv e) = differentIdeal ℤ (𝓞 K) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro d hd
    exact (absoluteDifferent_mem_equiv e d).mpr hd
  · intro d hd
    have h : (integersEquiv e).symm d ∈ differentIdeal ℤ (𝓞 L) :=
      (absoluteDifferent_mem_equiv e _).mp (by simpa only [AlgEquiv.apply_symm_apply] using hd)
    simpa only [AlgEquiv.apply_symm_apply] using Ideal.mem_map_of_mem (integersEquiv e) h

/-- The actual ideal equivalence underlying the restricted integer-ring isomorphism. -/
def integersIdealEquiv (e : L ≃ₐ[ℚ] K) : Ideal (𝓞 L) ≃* Ideal (𝓞 K) :=
  { (integersEquiv e).toRingEquiv.idealComapOrderIso.symm.toEquiv with
    map_mul' := Ideal.map_mul (integersEquiv e) }

/-- Absolute different coefficients are transported by the same literal ideal map. -/
theorem multiplicity_absoluteDifferent_equiv (e : L ≃ₐ[ℚ] K) (P : Ideal (𝓞 L)) :
    multiplicity (P.map (integersEquiv e)) (differentIdeal ℤ (𝓞 K)) =
      multiplicity P (differentIdeal ℤ (𝓞 L)) := by
  have h : multiplicity (integersIdealEquiv e P)
      (integersIdealEquiv e (differentIdeal ℤ (𝓞 L))) =
      multiplicity P (differentIdeal ℤ (𝓞 L)) := multiplicity_map_eq (integersIdealEquiv e)
  change multiplicity (P.map (integersEquiv e))
    ((differentIdeal ℤ (𝓞 L)).map (integersEquiv e)) = _ at h
  rw [map_absoluteDifferent_equiv] at h
  exact h

/-- Multiplicity of every integer principal ideal is preserved by the restricted isomorphism. -/
theorem multiplicity_natCast_equiv (e : L ≃ₐ[ℚ] K) (P : Ideal (𝓞 L)) (n : ℕ) :
    multiplicity (P.map (integersEquiv e)) (Ideal.span {(n : 𝓞 K)}) =
      multiplicity P (Ideal.span {(n : 𝓞 L)}) := by
  have h : multiplicity (integersIdealEquiv e P)
      (integersIdealEquiv e (Ideal.span {(n : 𝓞 L)})) =
      multiplicity P (Ideal.span {(n : 𝓞 L)}) := multiplicity_map_eq (integersIdealEquiv e)
  change multiplicity (P.map (integersEquiv e))
    ((Ideal.span {(n : 𝓞 L)}).map (integersEquiv e)) = _ at h
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at h
  exact h

/-- The actual ramification indices over Z are invariant under the same integral isomorphism. -/
theorem ramificationIdx_integersEquiv (e : L ≃ₐ[ℚ] K)
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    (P.map (integersEquiv e)).ramificationIdx ℤ = P.ramificationIdx ℤ := by
  let q := P.under ℤ
  have hq : q ≠ ⊥ := by
    intro hq
    exact hP (Ideal.eq_bot_of_under_eq_bot hq)
  have : (P.map (integersEquiv e)).IsPrime :=
    Ideal.map_isPrime_of_surjective (integersEquiv e).surjective (by simp)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx q (P.map (integersEquiv e)) hq,
    ← Ideal.ramificationIdx'_eq_ramificationIdx q P hq,
    Ideal.ramificationIdx'_map_eq q P (integersEquiv e)]

#check @map_absoluteDifferent_equiv
#check @ramificationIdx_integersEquiv
#print axioms map_absoluteDifferent_equiv
#print axioms ramificationIdx_integersEquiv

end ZInQ.Contrib.DifferentBound

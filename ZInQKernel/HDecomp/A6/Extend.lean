import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-a6-alg/Extend.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-
glue-a6-alg: extension of valuation rings (Chevalley). For any field extension `L/K` and any
valuation subring `O` of `K` there is a valuation subring `w` of `L` with `w ∩ K = O`.
Derived from Mathlib's `IsLocalRing.exists_factor_valuationRing` (Stacks 00IA, via
`LocalSubring.exists_le_valuationSubring`).
-/

namespace GlueA6Alg

theorem exists_valuationSubring_comap_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (O : ValuationSubring K) :
    ∃ w : ValuationSubring L, w.comap (algebraMap K L) = O := by
  let f : O →+* L := (algebraMap K L).comp O.subtype
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨B, ?_⟩
  ext x
  rw [ValuationSubring.mem_comap]
  constructor
  · intro hx
    by_contra hxO
    have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
    have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
    apply hxO
    have hu : IsUnit ((f.codRestrict B.toSubring hB) ⟨x⁻¹, hinv⟩) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K L x, hx⟩, ?_⟩
      apply Subtype.ext
      simp only [f, RingHom.codRestrict_apply, RingHom.comp_apply, ValuationSubring.coe_subtype,
        Subring.coe_mul, Subring.coe_one, map_inv₀]
      exact inv_mul_cancel₀ ((map_ne_zero (algebraMap K L)).mpr hx0)
    obtain ⟨⟨u, v, huv, hvu⟩, hu'⟩ := hloc.map_nonunit _ hu
    have hv : (v : K) = x := by
      have h1 : ((u : K)) * (v : K) = 1 := congrArg Subtype.val huv
      have h2 : (u : K) = x⁻¹ := congrArg Subtype.val hu'
      rw [h2] at h1
      field_simp at h1
      exact h1
    exact hv ▸ v.2
  · intro hx
    exact hB ⟨x, hx⟩

/-- The form used by A6: a valuation subring of `K̄` over a given one of `K`. -/
theorem exists_valuationSubring_algebraicClosure (K : Type*) [Field K] (O : ValuationSubring K) :
    ∃ w : ValuationSubring (AlgebraicClosure K),
      w.comap (algebraMap K (AlgebraicClosure K)) = O :=
  exists_valuationSubring_comap_eq O

end GlueA6Alg


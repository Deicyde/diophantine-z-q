import ZInQKernel.Contrib.G1Adelic.FiniteAdele

/-!
# G1-adelic over Mathlib's `𝔸ᶠ[ℤ, ℚ]`: `ℤ̂`, `ℤ̂^×`, `𝒪̂ = 𝒪 ⊗ ℤ̂` and `N/𝔸ᶠ^×K₀`
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum GlueVigneras
open scoped RestrictedProduct Quaternion

namespace G1Adelic.FA

/-- `ℤ̂` is the image of Mathlib's structure map `∏_v ℤ_v → 𝔸ᶠ[ℤ, ℚ]`. -/
theorem ZhatAF_eq_range_structureMap :
    ZhatAF = Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum ℤ =>
      v.adicCompletion ℚ) (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
      Filter.cofinite) := by
  rw [RestrictedProduct.range_structureMap]
  rfl

/-- `ℤ̂` as a subring of `𝔸ᶠ[ℤ, ℚ]`. -/
noncomputable def ZhatSubAF : Subring AF where
  carrier := ZhatAF
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem _
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem _
  neg_mem' ha v := neg_mem (ha v)

theorem qcoord_algebraMap {R : Type*} [CommRing R] (a : R) :
    qcoord (algebraMap R ℍ[R, 2, 0, -3] a) = ![a, 0, 0, 0] := by
  funext k; fin_cases k <;> simp [qcoord, QuaternionAlgebra.algebraMap_eq]

theorem algebraMap_mem_OhatAF_iff (a : AF) : algebraMap AF HA a ∈ OhatAF ↔ a ∈ ZhatAF := by
  simp only [OhatAF, Set.mem_ofPred_eq, qcoord_algebraMap]
  constructor
  · intro h; simpa using h 0
  · intro h k
    fin_cases k
    · simpa using h
    all_goals exact ZhatSubAF.zero_mem

/-- `ℤ̂^×`, as central scalars of `(B ⊗ 𝔸ᶠ)^×`. -/
noncomputable def ZintAF : Subgroup HAˣ :=
  ZhatSubAF.toSubmonoid.units.map (Units.map (algebraMap AF HA : AF →* HA))

/-- **`𝔸ᶠ^× ∩ K₀ = ℤ̂^×`** over Mathlib's finite adeles. -/
theorem ZAF_inf_K0AF : ZAF ⊓ K0AF = ZintAF := by
  ext x
  simp only [Subgroup.mem_inf, ZAF, ZintAF, MonoidHom.mem_range, Subgroup.mem_map, K0AF,
    Submonoid.mem_units_iff]
  constructor
  · rintro ⟨⟨a, rfl⟩, h1, h2⟩
    refine ⟨a, ⟨?_, ?_⟩, rfl⟩
    · exact (algebraMap_mem_OhatAF_iff _).mp h1
    · rw [← map_inv] at h2
      exact (algebraMap_mem_OhatAF_iff _).mp h2
  · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨a, rfl⟩, (algebraMap_mem_OhatAF_iff _).mpr h1, ?_⟩
    rw [← map_inv]
    exact (algebraMap_mem_OhatAF_iff _).mpr h2

/-- **A3's count with `ℤ̂^×` named, over Mathlib's `𝔸ᶠ[ℤ, ℚ]`:**
`|Γ'| = [N : 𝔸ᶠ^× K₃] = [N : 𝔸ᶠ^× K₀] · [K₀ : ℤ̂^× K₃] = 4 · 36 = 144`. -/
theorem gamma_count_Zint_AF :
    (ZAF ⊔ K3AF).relIndex NAF = (ZAF ⊔ K0AF).relIndex NAF * (ZintAF ⊔ K3AF).relIndex K0AF ∧
      (ZAF ⊔ K0AF).relIndex NAF = 4 ∧ (ZintAF ⊔ K3AF).relIndex K0AF = 36 := by
  rw [← ZAF_inf_K0AF, gamma_order_AF, relIndex_eq_four_AF, relIndex_K3_AF]
  exact ⟨rfl, rfl, rfl⟩

/-! ### `𝒪̂` is the `ℤ̂`-span of the basis of `𝒪` -/

/-- N5's `ℤ`-basis `1, i, (1 + j)/2, (i + ij)/2` of the maximal order `𝒪 ⊆ B = ℍ[ℚ, 2, 0, -3]`. -/
noncomputable def eQ : Fin 4 → ℍ[ℚ, 2, 0, -3] :=
  ![1, ⟨0, 1, 0, 0⟩, ⟨1 / 2, 0, 1 / 2, 0⟩, ⟨0, 1 / 2, 0, 1 / 2⟩]

/-- The basis of `𝒪` in `B ⊗ 𝔸ᶠ`. -/
noncomputable def eAF (k : Fin 4) : HA := qmap (algebraMap ℚ AF) (eQ k)

theorem half_mul_two : algebraMap ℚ AF (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap ℚ AF) 2, ← map_mul]; norm_num

theorem sum_qcoord (x : HA) : ∑ k, qcoord x k • eAF k = x := by
  have h := half_mul_two
  simp only [Fin.sum_univ_four, eAF, eQ, qcoord]
  ext <;> simp <;> trace_state <;> sorry

theorem qcoord_sum (a : Fin 4 → AF) : qcoord (∑ k, a k • eAF k) = a := by
  have h := half_mul_two
  funext k
  simp only [Fin.sum_univ_four, eAF, eQ]
  fin_cases k <;> simp [qcoord] <;> trace_state <;> sorry

/-- **`𝒪̂ = 𝒪 ⊗ ℤ̂`**: `OhatAF` is the set of `ℤ̂`-combinations of N5's basis of `𝒪`. -/
theorem OhatAF_eq_span :
    OhatAF = {x | ∃ a : Fin 4 → AF, (∀ k, a k ∈ ZhatAF) ∧ x = ∑ k, a k • eAF k} := by
  ext x
  constructor
  · intro hx
    exact ⟨qcoord x, hx, (sum_qcoord x).symm⟩
  · rintro ⟨a, ha, rfl⟩ k
    rw [qcoord_sum]; exact ha k

end G1Adelic.FA

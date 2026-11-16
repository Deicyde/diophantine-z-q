import ZInQKernel.Contrib.OneProof.ShimuraMainCMPrinted

noncomputable section
set_option linter.all false

namespace MainCMPolar

open NumberField IsDedekindDomain QMRecPrinted ShimuraCFT RayClassCFT
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E]

/-! ### `𝔞̂` -/

theorem one_tmul_mem_latHat {𝔞 : AddSubgroup E} {x : E} (hx : x ∈ 𝔞) : (1 : AQ) ⊗ₜ[ℚ] x ∈ latHat 𝔞 :=
  AddSubgroup.subset_closure ⟨1, ZhatS.one_mem, x, hx, rfl⟩

theorem latHat_mono {𝔞 𝔟 : AddSubgroup E} (h : 𝔞 ≤ 𝔟) : latHat 𝔞 ≤ latHat 𝔟 :=
  AddSubgroup.closure_mono fun _ ⟨c, hc, x, hx, e⟩ => ⟨c, hc, x, h hx, e⟩

theorem natCast_mul_tmul (m : ℕ) (b : AQ) (x : E) :
    ((m : AQ) * b) ⊗ₜ[ℚ] x = b ⊗ₜ[ℚ] ((m : E) * x) := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.smul_tmul]

theorem intCast_tmul (n : ℤ) (x : E) : ((n : AQ)) ⊗ₜ[ℚ] x = (1 : AQ) ⊗ₜ[ℚ] ((n : E) * x) := by
  rw [← zsmul_eq_mul, ← mul_one (n : AQ), ← zsmul_eq_mul, TensorProduct.smul_tmul]

/-- **`𝔞̂ = 𝔞 + 𝔟̂` for `m𝔞 ⊆ 𝔟`** (approximation of `ℤ̂` by `ℤ` modulo `m`). -/
theorem latHat_decomp {𝔞 𝔟 : AddSubgroup E} {m : ℕ} (hm : 0 < m) (hab : ∀ x ∈ 𝔞, (m : E) * x ∈ 𝔟)
    {w : AQ ⊗[ℚ] E} (hw : w ∈ latHat 𝔞) : ∃ a ∈ 𝔞, w - (1 : AQ) ⊗ₜ[ℚ] a ∈ latHat 𝔟 := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hw
    obtain ⟨n, b, hb, hcb⟩ := exists_int_approx hc m hm
    refine ⟨(n : E) * x, ?_, ?_⟩
    · rw [← zsmul_eq_mul]; exact AddSubgroup.zsmul_mem _ hx n
    · rw [hcb, TensorProduct.add_tmul, intCast_tmul, natCast_mul_tmul, add_sub_cancel_left]
      exact AddSubgroup.subset_closure ⟨b, hb, _, hab x hx, rfl⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, hau⟩ := hu
    obtain ⟨b, hb, hbv⟩ := hv
    refine ⟨a + b, add_mem ha hb, ?_⟩
    have e : u + v - (1 : AQ) ⊗ₜ[ℚ] (a + b) = (u - 1 ⊗ₜ a) + (v - 1 ⊗ₜ b) := by
      rw [TensorProduct.tmul_add]; abel
    rw [e]; exact add_mem hau hbv
  | neg u _ hu =>
    obtain ⟨a, ha, hau⟩ := hu
    refine ⟨-a, neg_mem ha, ?_⟩
    have e : -u - (1 : AQ) ⊗ₜ[ℚ] (-a) = -(u - 1 ⊗ₜ a) := by
      rw [TensorProduct.tmul_neg]; abel
    rw [e]; exact neg_mem hau

/-- **Density** of `E` in `𝔸_f ⊗ E` modulo `𝔟̂`, for `𝔟` containing a multiple of every element. -/
theorem exists_approx_latHat {𝔟 : AddSubgroup E} (hb : ∀ e : E, ∃ k : ℕ, 0 < k ∧ (k : E) * e ∈ 𝔟)
    (w : AQ ⊗[ℚ] E) : ∃ x : E, w - (1 : AQ) ⊗ₜ[ℚ] x ∈ latHat 𝔟 := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a e =>
    obtain ⟨d, hd, hda⟩ := exists_den a
    obtain ⟨k, hk, hke⟩ := hb e
    obtain ⟨n, b, hbz, hab⟩ := exists_int_approx hda (d * k) (Nat.mul_pos hd hk)
    refine ⟨((n : ℚ) / d) • e, ?_⟩
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have ha : a = algebraMap ℚ AQ ((n : ℚ) / d) + (k : AQ) * b := by
      have h1 : (d : AQ) * a = (d : AQ) * (algebraMap ℚ AQ ((n : ℚ) / d) + (k : AQ) * b) := by
        rw [hab, mul_add, ← mul_assoc, ← Nat.cast_mul, ← map_natCast (algebraMap ℚ AQ) d, ← map_mul,
          mul_div_cancel₀ _ hd0, map_intCast]
      have hu : algebraMap ℚ AQ (d : ℚ)⁻¹ * (d : AQ) = 1 := by
        rw [← map_natCast (algebraMap ℚ AQ), ← map_mul, inv_mul_cancel₀ hd0, map_one]
      calc a = algebraMap ℚ AQ (d : ℚ)⁻¹ * ((d : AQ) * a) := by rw [← mul_assoc, hu, one_mul]
        _ = _ := by rw [h1, ← mul_assoc, hu, one_mul]
    rw [ha, TensorProduct.add_tmul, natCast_mul_tmul, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, add_sub_cancel_left]
    exact AddSubgroup.subset_closure ⟨b, hbz, _, hke, rfl⟩
  | add u v hu hv =>
    obtain ⟨x, hx⟩ := hu
    obtain ⟨y, hy⟩ := hv
    refine ⟨x + y, ?_⟩
    have e : u + v - (1 : AQ) ⊗ₜ[ℚ] (x + y) = (u - 1 ⊗ₜ x) + (v - 1 ⊗ₜ y) := by
      rw [TensorProduct.tmul_add]; abel
    rw [e]; exact add_mem hx hy

end MainCMPolar
#print axioms MainCMPolar.exists_approx_latHat
#print axioms MainCMPolar.latHat_decomp

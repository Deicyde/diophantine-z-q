import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Density

/-!
# Rational radicals for quadratic characters

Tex 9748–9750. An anti-invariant in the fixed field of the character's
kernel gives a rational squareclass (on-the-spot, provenance (c)).
This step does not yet constrain the prime support of the radicand.
-/

namespace ZInQ.Manuscript.RC.TraceLimits

open ZInQ.Contrib.ChebFD.C10

/-- Every quadratic character of `G_ℚ` with open kernel is the action on the
square root of a squarefree integer. -/
theorem squarefree_radical_of_open_ker (χ : GQ →* Multiplicative (ZMod 2))
    (hopen : IsOpen (χ.ker : Set GQ)) :
    ∃ (d : ℤ) (s : Qbar), Squarefree d ∧ s ^ 2 = (d : Qbar) ∧
      ∀ g : GQ, χ g = 1 ↔ g s = s := by
  classical
  by_cases htriv : ∀ g, χ g = 1
  · exact ⟨1, 1, by simp, by simp, fun g => iff_of_true (htriv g) (map_one g)⟩
  push Not at htriv
  obtain ⟨τ, hτ⟩ := htriv
  let H : ClosedSubgroup GQ := ⟨χ.ker, χ.ker.isClosed_of_isOpen hopen⟩
  let E : IntermediateField ℚ Qbar := IntermediateField.fixedField χ.ker
  have hfix : E.fixingSubgroup = χ.ker := InfiniteGalois.fixingSubgroup_fixedField H
  have hτfix : τ ∉ E.fixingSubgroup := by
    rw [hfix, MonoidHom.mem_ker]
    exact hτ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτfix
  push Not at hτfix
  obtain ⟨x, hx, hτx⟩ := hτfix
  let y := x - τ x
  have hy : y ≠ 0 := sub_ne_zero.mpr hτx.symm
  have hk (g : GQ) (hg : χ g = 1) : g x = x := by
    change x ∈ IntermediateField.fixedField χ.ker at hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact hx g (MonoidHom.mem_ker.2 hg)
  have hval : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by decide
  have hsq : ∀ a : Multiplicative (ZMod 2), a * a = 1 := by decide
  have hy₁ (g : GQ) (hg : χ g = 1) : g y = y := by
    have e := hk (τ⁻¹ * g * τ) (by simp [map_mul, hg])
    have e' := congrArg (fun z : Qbar => τ z) e
    have hgg : g (τ x) = τ x := by
      simpa only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] using e'
    rw [show y = x - τ x from rfl, map_sub, hk g hg, hgg]
  have hy₂ (g : GQ) (hg : χ g ≠ 1) : g y = -y := by
    have c := hval (χ g) (χ τ) hg hτ
    have e := congrArg (fun z : Qbar => τ z) (hk (τ⁻¹ * g) (by simp [map_mul, c]))
    have e' : g x = τ x := by
      simpa only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] using e
    have f := hk (g * τ) (by rw [map_mul, c, hsq])
    change g (τ x) = x at f
    rw [show y = x - τ x from rfl, map_sub, e', f, neg_sub]
  obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) (y ^ 2)).2
    (fun g => by
      by_cases h : χ g = 1
      · rw [map_pow, hy₁ g h]
      · rw [map_pow, hy₂ g h]; ring)
  have hden : (r.den : Qbar) ≠ 0 := by exact_mod_cast r.den_ne_zero
  let z := (r.den : Qbar) * y
  have hz : z ≠ 0 := mul_ne_zero hden hy
  have hr' : (r.num : Qbar) / (r.den : Qbar) = y ^ 2 := by
    rw [← Rat.cast_def]
    exact (eq_ratCast (algebraMap ℚ Qbar) r).symm.trans hr
  have hzsq : z ^ 2 = ((r.num * (r.den : ℤ) : ℤ) : Qbar) := by
    dsimp [z]
    push_cast
    rw [mul_pow, ← hr']
    field_simp
  obtain ⟨e, d, hed, hd⟩ := exists_sq_mul_squarefree (r.num * (r.den : ℤ))
  have hed' : (e : Qbar) ^ 2 * (d : Qbar) = z ^ 2 := by
    have h := congrArg (fun a : ℤ => (a : Qbar)) hed
    push_cast at h
    exact h.trans (by simpa only [Int.cast_mul, Int.cast_natCast] using hzsq.symm)
  have he : (e : Qbar) ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 2 ≠ 0), zero_mul, eq_comm, pow_eq_zero_iff (by decide : 2 ≠ 0)] at hed'
    exact hz hed'
  let s := z / (e : Qbar)
  refine ⟨d, s, hd, ?_, fun g => ?_⟩
  · change (z / (e : Qbar)) ^ 2 = (d : Qbar)
    rw [div_pow, div_eq_iff (pow_ne_zero _ he), mul_comm, hed']
  · have Hs : g s = s ↔ g y = y := by
      simp only [s, z, map_div₀, map_mul, map_natCast, map_intCast,
        div_left_inj' he, mul_right_inj' hden]
    rw [Hs]
    refine ⟨hy₁ g, fun hg => ?_⟩
    by_contra hc
    have hyy : y = -y := hg.symm.trans (hy₂ g hc)
    have h : y + y = 0 := by nth_rewrite 2 [hyy]; exact add_neg_cancel y
    have hh : (2 : Qbar) * y = 0 := by rwa [two_mul]
    exact hy ((mul_eq_zero.mp hh).resolve_left (by norm_num))

#print axioms squarefree_radical_of_open_ker

end ZInQ.Manuscript.RC.TraceLimits

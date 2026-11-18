import ZInQKernel.Contrib.OneProof.RC.Eichler.ClassSet

/-! On-the-spot (c), tex 8467–8468 and 9067–9071: the units of a left order are precisely
the stabilizer of the corresponding right ideal. All the multipliers realizing a fixed
isomorphism class are a torsor for this stabilizer. -/

namespace ZInQ.Manuscript.RC.Eichler.RightIdeal

variable {a b : ℚ} {R : Order a b}

/-- The ambient units from the left order are exactly the units fixing the lattice. -/
theorem mem_G_iff_translate (ha : a < 0) (hb : b < 0) (I : RightIdeal R)
    (u : (B a b)ˣ) : u ∈ (I.leftOrder ha hb).G ↔ I.translate u = I := by
  constructor
  · rintro ⟨v, rfl⟩
    apply RightIdeal.ext
    ext x
    rw [mem_translate]
    constructor
    · intro hx
      have hv := v.val.prop _ hx
      change (((I.leftOrder ha hb).unitsHom v : (B a b)ˣ) : B a b) *
        ((↑((I.leftOrder ha hb).unitsHom v)⁻¹ : B a b) * x) ∈ I.lattice at hv
      simpa only [← mul_assoc, Units.mul_inv, one_mul] using hv
    · intro hx
      exact v.inv.prop _ hx
  · intro h
    have hf : (u : B a b) ∈ I.leftRing := by
      intro x hx
      rw [← h, mem_translate]
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using hx
    have hg : (↑u⁻¹ : B a b) ∈ I.leftRing := by
      intro x hx
      have hx' : x ∈ (I.translate u).lattice := by simpa only [h] using hx
      exact (mem_translate u I x).mp hx'
    let v : (I.leftOrder ha hb).ringˣ := {
      val := ⟨(u : B a b), hf⟩
      inv := ⟨(↑u⁻¹ : B a b), hg⟩
      val_inv := Subtype.ext (Units.mul_inv u)
      inv_val := Subtype.ext (Units.inv_mul u) }
    exact ⟨v, Units.ext rfl⟩

/-- Once one multiplier from `I` to `J` is fixed, all multipliers are a copy of
the unit group of the left order of `I`. -/
def multiplierEquiv (ha : a < 0) (hb : b < 0) {I J : RightIdeal R}
    (u : (B a b)ˣ) (hu : I.translate u = J) :
    {v : (B a b)ˣ // I.translate v = J} ≃ (I.leftOrder ha hb).G where
  toFun v := ⟨u⁻¹ * v.val, (mem_G_iff_translate ha hb I _).mpr (by
    rw [translate_mul, v.prop, ← hu, ← translate_mul, inv_mul_cancel, translate_one])⟩
  invFun v := ⟨u * v.val, by
    rw [translate_mul, (mem_G_iff_translate ha hb I _).mp v.prop, hu]⟩
  left_inv v := Subtype.ext (by simp [← mul_assoc])
  right_inv v := Subtype.ext (by simp [← mul_assoc])

end ZInQ.Manuscript.RC.Eichler.RightIdeal

/-! Axiom audit -/

#print axioms ZInQ.Manuscript.RC.Eichler.RightIdeal.mem_G_iff_translate
#print axioms ZInQ.Manuscript.RC.Eichler.RightIdeal.multiplierEquiv

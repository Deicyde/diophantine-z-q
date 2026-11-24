import ZInQKernel.Contrib.OneProof.BShTracesLattices

/-! ON THE SPOT (provenance (c)): the nonzero prime torsion segments
partition into the horizontal line and the triangular lines. -/

noncomputable section

namespace BShTraces

open PeriodPair T5Glue UpperHalfPlane AfTateLam

private theorem period_coords_inj (L : PeriodPair) {a b c d : ℤ}
    (h : (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = (c : ℂ) * L.ω₁ + (d : ℂ) * L.ω₂) :
    (a,b) = (c,d) := by
  apply L.latticeEquivProd.symm.injective
  apply Subtype.ext
  simpa only [latticeEquiv_symm_apply] using h

/-- Each nonzero class killed by (p) is in exactly one prime superlattice.
Use `none` for the horizontal prime branch and `some i` for the branch
at `(τ+i)/p`. -/
theorem prime_torsion_lattice_unique {p : ℕ} (hp : p.Prime) (τ : ℍ) (w : ℂ)
    (hw : w ∉ (pp τ).lattice) (hn : (p : ℂ) * w ∈ (pp τ).lattice) :
    ∃! i : Option (Fin p), w ∈ (i.elim (horizontal p hp.pos τ)
      (fun i => pp (shiftDiv p i τ))).lattice := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp hn
  have hab' : (a : ℂ) + (b : ℂ) * (τ : ℂ) = (p : ℂ) * w := by simpa [pp] using hab
  have hco {c d : ℤ} (he : (c : ℂ) + (d : ℂ) * (τ : ℂ) = (p : ℂ) * w) :
      (c,d) = (a,b) :=
    period_coords_inj (pp τ) (by simpa [pp] using he.trans hab'.symm)
  have hH : w ∈ (horizontal p hp.pos τ).lattice ↔ (p : ℤ) ∣ b := by
    rw [PeriodPair.mem_lattice, (horizontal_periods _ _ _).1, (horizontal_periods _ _ _).2]
    constructor
    · rintro ⟨c,d,hcd⟩
      have he := congrArg ((p : ℂ) * ·) hcd
      have h' : (c : ℂ) + (((p : ℤ) * d : ℤ) : ℂ) * (τ : ℂ) = (p : ℂ) * w := by
        push_cast
        rw [← he]
        field_simp
      exact ⟨d, (congrArg Prod.snd (hco h')).symm⟩
    · rintro ⟨d,hd⟩
      refine ⟨a,d, mul_left_cancel₀ hp' ?_⟩
      rw [← hab', hd]
      push_cast
      field_simp
  have hT (i : Fin p) : w ∈ (pp (shiftDiv p i τ)).lattice ↔
      (p : ℤ) ∣ (a - b * (i.val : ℤ)) := by
    rw [PeriodPair.mem_lattice]
    change (∃ c d : ℤ, (c : ℂ) * 1 + (d : ℂ) * (↑(shiftDiv p i τ) : ℂ) = w) ↔ _
    rw [HeckePin.coe_shiftDiv _ _ hp.pos]
    constructor
    · rintro ⟨c,d,hcd⟩
      have he := congrArg ((p : ℂ) * ·) hcd
      have h' : (((p : ℤ) * c + d * (i.val : ℤ) : ℤ) : ℂ) + (d : ℂ) * (τ : ℂ) =
          (p : ℂ) * w := by
        push_cast
        rw [← he]
        field_simp
        ring
      have h₁ := congrArg Prod.fst (hco h')
      have h₂ := congrArg Prod.snd (hco h')
      refine ⟨c, ?_⟩
      change (p : ℤ) * c + d * (i.val : ℤ) = a at h₁
      change d = b at h₂
      rw [← h₁, h₂]
      ring
    · rintro ⟨c,hc⟩
      have ha : a = (p : ℤ) * c + b * (i.val : ℤ) := sub_eq_iff_eq_add.mp hc
      refine ⟨c,b, mul_left_cancel₀ hp' ?_⟩
      rw [← hab', ha]
      push_cast
      field_simp
      ring
  have hne : ¬ ((a : ZMod p) = 0 ∧ (b : ZMod p) = 0) := by
    rintro ⟨ha,hb⟩
    obtain ⟨c,hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha
    obtain ⟨d,hd⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb
    apply hw
    rw [PeriodPair.mem_lattice]
    refine ⟨c,d, mul_left_cancel₀ hp' ?_⟩
    rw [← hab', hc, hd]
    simp only [pp, mul_one, Int.cast_mul, Int.cast_natCast]
    ring
  have hhm : w ∈ (horizontal p hp.pos τ).lattice ↔ (b : ZMod p) = 0 :=
    hH.trans (ZMod.intCast_zmod_eq_zero_iff_dvd b p).symm
  have htm (i : Fin p) : w ∈ (pp (shiftDiv p i τ)).lattice ↔
      (a : ZMod p) = (b : ZMod p) * (i.val : ZMod p) := by
    rw [hT, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero
  by_cases h0 : (b : ZMod p) = 0
  · refine ⟨none, hhm.mpr h0, ?_⟩
    rintro (_ | i) hi
    · rfl
    · have ha := (htm i).mp hi
      simp only [h0, zero_mul] at ha
      exact (hne ⟨ha,h0⟩).elim
  · let t := (a : ZMod p) / (b : ZMod p)
    let i : Fin p := ⟨t.val, ZMod.val_lt t⟩
    have hi : (i.val : ZMod p) = t := ZMod.natCast_zmod_val t
    refine ⟨some i, (htm i).mpr ?_, ?_⟩
    · rw [hi, mul_comm, div_mul_cancel₀ _ h0]
    rintro (_ | k) hk
    · exact (h0 (hhm.mp hk)).elim
    · congr 1
      apply Fin.ext
      have hk' := (htm k).mp hk
      have h : (k.val : ZMod p) = (i.val : ZMod p) := by
        rw [hi, eq_div_iff h0, mul_comm, ← hk']
      simpa only [ZMod.val_natCast_of_lt k.isLt, ZMod.val_natCast_of_lt i.isLt] using
        congrArg ZMod.val h

#print axioms period_coords_inj
#print axioms prime_torsion_lattice_unique

end BShTraces

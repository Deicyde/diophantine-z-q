import ZInQKernel.Contrib.OneProof.RC.CMField2.Multipliers
import ZInQKernel.Contrib.OneProof.RC.CMField2.PrimitiveNorms

/-! Primitive norm levels coincide with nontrivial diagonal roots (c). -/

noncomputable section

open ModularCurve Polynomial UpperHalfPlane

namespace ZInQ.Manuscript.RC.CMField2

private theorem int_coords_eq {z : ℂ} (hz : z.im ≠ 0) {a b c d : ℤ}
    (he : (a : ℂ) + (b : ℂ) * z = (c : ℂ) + (d : ℂ) * z) : a = c ∧ b = d := by
  have hi := congrArg Complex.im he
  simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
    zero_mul, add_zero, zero_add] at hi
  have hd : b = d := by
    exact_mod_cast (mul_right_cancel₀ hz hi : (b : ℝ) = (d : ℝ))
  subst d
  exact ⟨by exact_mod_cast (add_right_cancel he : (a : ℂ) = (c : ℂ)), rfl⟩

private theorem normSq_of_coords {z : ℂ} {t u : ℤ} (ht : (t : ℝ) = 2 * z.re)
    (hu : (u : ℝ) = Complex.normSq z) (a b : ℤ) :
    Complex.normSq ((a : ℂ) + (b : ℂ) * z) = ((a ^ 2 + t * a * b + u * b ^ 2 : ℤ) : ℝ) := by
  push_cast
  rw [ht, hu]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero,
    zero_add, add_zero]
  ring

private theorem scale_le_of_multiplier (L : PeriodPair) (v : ℂˣ)
    (hv : (v : ℂ) ∈ periodMultipliers L) : (L.scale v).lattice ≤ L.lattice := by
  intro x hx
  change x ∈ ((L.scale v).lattice : Set ℂ) at hx
  rw [lattice_scale] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact hv _ hw

private theorem scale_primitive_iff_gcd (L : PeriodPair) (z : periodMultipliers L)
    (hz : (z : ℂ).im ≠ 0)
    (hbas : ∀ w : periodMultipliers L, ∃ a b : ℤ, (w : ℂ) = (a : ℂ) + (b : ℂ) * z)
    (v : ℂˣ) (a b : ℤ) (hv : (v : ℂ) = (a : ℂ) + (b : ℂ) * z) :
    (∀ k : ℕ, 1 < k → ¬ ∀ x ∈ (L.scale v).lattice, ∃ y ∈ L.lattice, x = (k : ℤ) • y) ↔
      Int.gcd a b = 1 := by
  constructor
  · intro hp
    let k := Int.gcd a b
    have hk0 : k ≠ 0 := by
      intro hk
      obtain ⟨ha, hb⟩ := Int.gcd_eq_zero_iff.mp hk
      exact v.ne_zero (by simp [hv, ha, hb])
    by_contra h
    have hk1 : 1 < k := by change k ≠ 1 at h; omega
    obtain ⟨c, hc⟩ := Int.gcd_dvd_left a b
    obtain ⟨d, hd⟩ := Int.gcd_dvd_right a b
    let w : periodMultipliers L := (c : periodMultipliers L) + (d : periodMultipliers L) * z
    have hvw : (v : ℂ) = (k : ℂ) * (w : ℂ) := calc
      (v : ℂ) = (a : ℂ) + (b : ℂ) * z := hv
      _ = (((k : ℤ) * c : ℤ) : ℂ) + (((k : ℤ) * d : ℤ) : ℂ) * z :=
        congrArg₂ (fun a b : ℤ => (a : ℂ) + (b : ℂ) * z) hc hd
      _ = (k : ℂ) * (w : ℂ) := by push_cast [w]; ring
    apply hp k hk1
    intro x hx
    change x ∈ ((L.scale v).lattice : Set ℂ) at hx
    rw [lattice_scale] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨_, w.property y hy, ?_⟩
    change (v : ℂ) * y = (k : ℤ) • ((w : ℂ) * y)
    rw [hvw, mul_assoc, zsmul_eq_mul, Int.cast_natCast]
  · intro hg k hk hd
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    let q : ℂ := (v : ℂ) / (k : ℂ)
    have hq : q ∈ periodMultipliers L := by
      intro x hx
      have hvx : (v : ℂ) * x ∈ (L.scale v).lattice := by
        change _ ∈ ((L.scale v).lattice : Set ℂ)
        rw [lattice_scale]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, he⟩ := hd _ hvx
      have he' : q * x = y := by
        dsimp [q]
        rw [div_mul_eq_mul_div, div_eq_iff hk0]
        simpa only [zsmul_eq_mul, Int.cast_natCast, mul_comm y] using he
      rwa [he']
    obtain ⟨c, d, hqeq⟩ := hbas ⟨q, hq⟩
    have he : (a : ℂ) + (b : ℂ) * z = (((k : ℤ) * c : ℤ) : ℂ) + (((k : ℤ) * d : ℤ) : ℂ) * z := by
      push_cast
      have hh : (v : ℂ) = (k : ℂ) * q := by dsimp [q]; field_simp
      rw [← hv, hh, show q = (c : ℂ) + (d : ℂ) * z from hqeq]
      ring
    obtain ⟨ha, hb⟩ := int_coords_eq hz he
    have hdiv := Int.dvd_coe_gcd (show (k : ℤ) ∣ a from ⟨c, ha⟩) (show (k : ℤ) ∣ b from ⟨d, hb⟩)
    rw [hg] at hdiv
    exact (Nat.ne_of_gt hk) (Nat.dvd_one.mp (by exact_mod_cast hdiv))

private theorem diagonal_root_iff_ofTau (τ : ℍ) (m : ℕ) [NeZero m] (hm : 1 < m)
    (P : ModularPolynomialData m) (z : periodMultipliers (PeriodPair.ofTau τ))
    (hz : (z : ℂ).im ≠ 0) (t u : ℤ) (ht : (t : ℝ) = 2 * (z : ℂ).re)
    (hu : (u : ℝ) = Complex.normSq (z : ℂ))
    (hbas : ∀ w : periodMultipliers (PeriodPair.ofTau τ), ∃ a b : ℤ,
      (w : ℂ) = (a : ℂ) + (b : ℂ) * z) :
    let j := (PeriodPair.ofTau τ).jLattice
    (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) j)).IsRoot j ↔
      (m : ℤ) ∈ primitiveNormLevels t u := by
  let L := PeriodPair.ofTau τ
  change (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) L.jLattice)).IsRoot L.jLattice ↔ _
  constructor
  · intro hroot
    obtain ⟨M, hM, hidx, hc, hj⟩ := exists_cyclic_sublattice_of_modularPolynomial_root m P τ
      (X0Model.analyticJ τ) (by simpa only [L, PeriodPair.jLattice_ofTau, X0Model.analyticJ] using hroot)
    have hj' : L.jLattice = M.jLattice := (PeriodPair.jLattice_ofTau τ).trans hj.symm
    obtain ⟨v, hv⟩ := exists_homothetic_of_jLattice_eq L M hj'
    have hvsub : (L.scale v).lattice ≤ L.lattice := hv ▸ hM
    have hvmem : (v : ℂ) ∈ periodMultipliers L := by
      intro x hx
      apply hvsub
      change _ ∈ ((L.scale v).lattice : Set ℂ)
      rw [lattice_scale]
      exact ⟨x, hx, rfl⟩
    obtain ⟨a, b, hab⟩ := hbas ⟨v, hvmem⟩
    have hp := primitive_of_isAddCyclic_sublatticeQuotient L (L.scale v) hvsub
      (by
        have hs : (L.scale v).lattice.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup =
            M.lattice.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup := by rw [hv]
        exact (QuotientAddGroup.quotientAddEquivOfEq hs).isAddCyclic.mpr hc)
    have he := cast_sublatticeIndex_scale L v hvsub
    have hi : L.sublatticeIndex (L.scale v) = m := by unfold PeriodPair.sublatticeIndex; rwa [hv]
    rw [hi, show (v : ℂ) = (a : ℂ) + (b : ℂ) * z from hab, normSq_of_coords ht hu] at he
    exact ⟨by exact_mod_cast hm, a, b, (scale_primitive_iff_gcd L z hz hbas v a b hab).mp hp,
      by exact_mod_cast he.symm⟩
  · rintro ⟨_, a, b, hg, he⟩
    let α : periodMultipliers L := (a : periodMultipliers L) + (b : periodMultipliers L) * z
    have ha : (α : ℂ) = (a : ℂ) + (b : ℂ) * z := by simp [α]
    have hn : Complex.normSq (α : ℂ) = (m : ℝ) := by
      rw [ha, normSq_of_coords ht hu, he, Int.cast_natCast]
    have hα : (α : ℂ) ≠ 0 := by
      intro h
      have hm0 : (m : ℝ) = 0 := by simpa [h] using hn.symm
      exact (Nat.ne_of_gt (Nat.zero_lt_one.trans hm)) (by exact_mod_cast hm0)
    let v := Units.mk0 (α : ℂ) hα
    have hs := scale_le_of_multiplier L v α.property
    have hi : L.sublatticeIndex (L.scale v) = m := by
      exact_mod_cast (cast_sublatticeIndex_scale L v hs).trans hn
    have hc := isAddCyclic_sublatticeQuotient_of_primitive L (L.scale v) hs
      ((scale_primitive_iff_gcd L z hz hbas v a b ha).mpr hg)
    have h := ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic m P L (L.scale v) hs hi hc
    simpa only [Polynomial.IsRoot.def, jLattice_scale] using h

/-- The nontrivial specialized diagonal roots are exactly the primitive norm
levels of the embedded multiplier order. -/
theorem diagonal_root_iff_primitive_norm (L : PeriodPair) (m : ℕ) [NeZero m] (hm : 1 < m)
    (P : ModularPolynomialData m) (z : periodMultipliers L) (hz : (z : ℂ).im ≠ 0) (t u : ℤ)
    (ht : (t : ℝ) = 2 * (z : ℂ).re) (hu : (u : ℝ) = Complex.normSq (z : ℂ))
    (hbas : ∀ w : periodMultipliers L, ∃ a b : ℤ, (w : ℂ) = (a : ℂ) + (b : ℂ) * z) :
    (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) L.jLattice)).IsRoot L.jLattice ↔
      (m : ℤ) ∈ primitiveNormLevels t u := by
  obtain ⟨τ, hτ⟩ := exists_analyticJ_eq L.jLattice
  let M := PeriodPair.ofTau τ
  have hj : M.jLattice = L.jLattice := (PeriodPair.jLattice_ofTau τ).trans hτ
  have hS := periodMultipliers_eq_of_jLattice_eq M L hj
  let z' : periodMultipliers M := ⟨z, hS.symm ▸ z.property⟩
  have h := diagonal_root_iff_ofTau τ m hm P z' hz t u ht hu (fun w =>
    hbas ⟨w, hS ▸ w.property⟩)
  simpa only [M, hj] using h


end ZInQ.Manuscript.RC.CMField2

import ZInQKernel.Contrib.OneProof.RC.CMField2.CosetLattice
import ZInQKernel.Contrib.OneProof.RC.CMField2.Integrality

/-! A cyclic self-isogeny of nonsquare degree yields a nonreal multiplier. -/

noncomputable section

open Polynomial ModularCurve

namespace ZInQ.Manuscript.RC.CMField2

private theorem exists_invariant_scaling (a b c d : ℂ)
    (hL : a ^ 3 - 27 * b ^ 2 ≠ 0) (hM : c ^ 3 - 27 * d ^ 2 ≠ 0)
    (h : a ^ 3 * d ^ 2 = c ^ 3 * b ^ 2) :
    ∃ u : ℂˣ, (u : ℂ) ^ 4 * c = a ∧ (u : ℂ) ^ 6 * d = b := by
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by intro hd; simp [hc, hd] at hM
    have ha : a = 0 := by simpa [hc, hd] using h
    have hb : b ≠ 0 := by intro hb; simp [ha, hb] at hL
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (b / d) (by decide : 0 < 6)
    have hu0 : u ≠ 0 := by intro e; exact div_ne_zero hb hd (hu.symm.trans (by simp [e]))
    exact ⟨Units.mk0 u hu0, by simp [ha, hc], by simp [hu, hd]⟩
  have ha : a ≠ 0 := by
    intro ha
    have hb : b = 0 := by
      by_contra hb
      exact (mul_ne_zero (pow_ne_zero 3 hc) (pow_ne_zero 2 hb)) (by simpa [ha] using h.symm)
    simp [ha, hb] at hL
  by_cases hd : d = 0
  · have hb : b = 0 := by
      by_contra hb
      exact (mul_ne_zero (pow_ne_zero 3 hc) (pow_ne_zero 2 hb)) (by simpa [hd] using h.symm)
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (a / c) (by decide : 0 < 4)
    have hu0 : u ≠ 0 := by intro e; exact div_ne_zero ha hc (hu.symm.trans (by simp [e]))
    exact ⟨Units.mk0 u hu0, by simp [hu, hc], by simp [hd, hb]⟩
  have hb : b ≠ 0 := by intro hb; simp [hb, ha, hd] at h
  let A := a / c
  let B := b / d
  have hA : A ≠ 0 := div_ne_zero ha hc
  have hB : B ≠ 0 := div_ne_zero hb hd
  have hAB : A ^ 3 = B ^ 2 := by
    dsimp [A, B]
    rw [div_pow, div_pow, div_eq_div_iff (pow_ne_zero _ hc) (pow_ne_zero _ hd)]
    simpa only [mul_comm (c ^ 3)] using h
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (B / A) (by decide : 0 < 2)
  have hu0 : u ≠ 0 := by intro e; exact div_ne_zero hB hA (hu.symm.trans (by simp [e]))
  have hu4 : u ^ 4 = A := calc
    u ^ 4 = (u ^ 2) ^ 2 := by ring
    _ = A := by rw [hu, div_pow, ← hAB]; field_simp
  have hu6 : u ^ 6 = B := by
    rw [show u ^ 6 = u ^ 4 * u ^ 2 by ring, hu4, hu, mul_comm A, div_mul_cancel₀ _ hA]
  exact ⟨Units.mk0 u hu0, by simp [hu4, A, hc], by simp [hu6, B, hd]⟩

/-- Equal j-values give homothetic period lattices. Port of the private lemma at
60b162a0d07ad3a3e1eafbcc904fff2b2fbf3100,
ZInQKernel/Contrib/OneProof/RC/X0Model2/JOrbit.lean. -/
theorem exists_homothetic_of_jLattice_eq (L M : PeriodPair)
    (h : L.jLattice = M.jLattice) :
    ∃ u : ℂˣ, (L.scale u).lattice = M.lattice := by
  have hL := L.discriminant_ne_zero
  have hM := M.discriminant_ne_zero
  have hab : L.g₂ ^ 3 * M.g₃ ^ 2 = M.g₂ ^ 3 * L.g₃ ^ 2 := by
    rw [PeriodPair.jLattice, PeriodPair.jLattice, div_eq_div_iff hL hM] at h
    linear_combination (-1 / 46656 : ℂ) * h
  obtain ⟨u, h₂, h₃⟩ := exists_invariant_scaling L.g₂ L.g₃ M.g₂ M.g₃ hL hM hab
  refine ⟨u, X0Model2.lattice_eq_of_weierstrass_invariants _ _ ?_ ?_⟩
  · rw [P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair.g₂_scale, ← h₂,
      inv_mul_cancel_left₀ (pow_ne_zero _ u.ne_zero)]
  · rw [P2MW.S_PeriodPair_discriminant_ne_zero.PeriodPair.g₃_scale, ← h₃,
      inv_mul_cancel_left₀ (pow_ne_zero _ u.ne_zero)]

/-- A real multiplier of a complex period lattice is an integer. -/
theorem exists_int_eq_of_real_multiplier (L : PeriodPair) (z : ℂ) (hz : z.im = 0)
    (h : ∀ x ∈ L.lattice, z * x ∈ L.lattice) : ∃ n : ℤ, z = (n : ℂ) := by
  have hw : L.ω₁ ∈ L.lattice := Submodule.subset_span (by simp)
  obtain ⟨m, n, he⟩ := Submodule.mem_span_pair.mp (h L.ω₁ hw :
    z * L.ω₁ ∈ Submodule.span ℤ ({L.ω₁, L.ω₂} : Set ℂ))
  have hC : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hz)
  have hlin : ((m : ℝ) - z.re) • L.ω₁ + (n : ℝ) • L.ω₂ = 0 := by
    rw [hC] at he
    rw [sub_smul, sub_add_eq_add_sub, sub_eq_zero]
    rw [Complex.real_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    simpa only [zsmul_eq_mul] using he
  obtain ⟨hm, _⟩ := LinearIndependent.pair_iff.mp L.indep _ _ hlin
  exact ⟨m, hC.trans (by rw [← sub_eq_zero.mp hm]; norm_cast)⟩

/-- At a root on a nonsquare diagonal, the same period lattice admits a
nonreal multiplier with cyclic quotient of the specified degree. -/
theorem conjugate_has_nonreal_multiplier_of_root {F : Type*} [Field F] (x : F)
    (e f : F →+* ℂ) (N : ℕ) [NeZero N] (P : ModularPolynomialData N)
    (hNsq : ¬ IsSquare N)
    (hroot : (P.Φ.map (eval₂RingHom (Int.castRingHom ℂ) (e x))).IsRoot (e x)) :
    ∃ τ : UpperHalfPlane, X0Model.analyticJ τ = f x ∧
      let L := PeriodPair.ofTau τ
      ∃ u : ℂˣ, (u : ℂ).im ≠ 0 ∧ (L.scale u).lattice ≤ L.lattice ∧
        L.sublatticeIndex (L.scale u) = N ∧ IsAddCyclic (L.sublatticeQuotient (L.scale u)) := by
  obtain ⟨τ, hτ, M, hM, hidx, hcyc, hj⟩ := conjugate_has_cyclic_self_of_root x e f N P hroot
  let L := PeriodPair.ofTau τ
  obtain ⟨u, hu⟩ := exists_homothetic_of_jLattice_eq L M hj.symm
  have hsub : (L.scale u).lattice ≤ L.lattice := hu ▸ hM
  have hi : L.sublatticeIndex (L.scale u) = N := by
    unfold PeriodPair.sublatticeIndex
    rw [hu]
    exact hidx
  have hq : IsAddCyclic (L.sublatticeQuotient (L.scale u)) := by
    have hs : (L.scale u).lattice.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup =
        M.lattice.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup := by rw [hu]
    exact (QuotientAddGroup.quotientAddEquivOfEq hs).isAddCyclic.mpr hcyc
  refine ⟨τ, hτ, u, ?_, hsub, hi, hq⟩
  intro him
  have hmul : ∀ x ∈ L.lattice, (u : ℂ) * x ∈ L.lattice := by
    intro y hy
    apply hsub
    change _ ∈ ((L.scale u).lattice : Set ℂ)
    rw [lattice_scale]
    exact ⟨y, hy, rfl⟩
  obtain ⟨n, hn⟩ := exists_int_eq_of_real_multiplier L (u : ℂ) him hmul
  have hnorm := cast_sublatticeIndex_scale L u hsub
  rw [hi, hn, Complex.normSq_apply] at hnorm
  norm_num at hnorm
  apply hNsq
  refine ⟨n.natAbs, ?_⟩
  exact_mod_cast (show (N : ℝ) = (n.natAbs : ℝ) * (n.natAbs : ℝ) by
    rw [Nat.cast_natAbs, Int.cast_abs, ← pow_two, sq_abs, pow_two, hnorm])


end ZInQ.Manuscript.RC.CMField2

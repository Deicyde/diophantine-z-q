import ZInQKernel.Contrib.OneProof.RC.CMField2.ScalarWitness

/-! A multiplier ring with a nonreal scalar has a normalized integral basis.
On-the-spot calculation (c). -/

noncomputable section

open Module

namespace ZInQ.Manuscript.RC.CMField2

/-- Complex scalars preserving the integral lattice. -/
def periodMultipliers (L : PeriodPair) : Subring ℂ where
  carrier := {z | ∀ w ∈ L.lattice, z * w ∈ L.lattice}
  add_mem' := by
    intro x y hx hy w hw
    rw [add_mul]
    exact L.lattice.add_mem (hx w hw) (hy w hw)
  mul_mem' := by
    intro x y hx hy w hw
    rw [mul_assoc]
    exact hx _ (hy w hw)
  neg_mem' := by
    intro x hx w hw
    rw [neg_mul]
    exact L.lattice.neg_mem (hx _ hw)
  zero_mem' := by simp
  one_mem' := by simp

private theorem omega_one_mem (L : PeriodPair) : L.ω₁ ∈ L.lattice :=
  L.latticeBasis_zero ▸ (L.latticeBasis 0).property

private def secondCoord (L : PeriodPair) : periodMultipliers L →ₗ[ℤ] ℤ :=
  let e : periodMultipliers L →ₗ[ℤ] L.lattice :=
    { toFun := fun z => ⟨z * L.ω₁, z.property _ (omega_one_mem L)⟩
      map_add' := by intro x y; apply Subtype.ext; simp [add_mul]
      map_smul' := by intro n x; apply Subtype.ext; simp [zsmul_eq_mul, mul_assoc] }
  (L.latticeBasis.coord 1).comp e

private theorem exists_int_of_secondCoord_eq_zero (L : PeriodPair) (z : periodMultipliers L)
    (hz : secondCoord L z = 0) : ∃ a : ℤ, (z : ℂ) = a := by
  let x : L.lattice := ⟨z * L.ω₁, z.property _ (omega_one_mem L)⟩
  have hs := congrArg (fun w : L.lattice => (w : ℂ)) (L.latticeBasis.sum_repr x).symm
  rw [Fin.sum_univ_two] at hs
  change L.latticeBasis.repr x 1 = 0 at hz
  simp only [hz, zero_smul, add_zero, Submodule.coe_smul, PeriodPair.latticeBasis_zero,
    zsmul_eq_mul] at hs
  exact ⟨L.latticeBasis.repr x 0, (mul_right_cancel₀
    (L.indep.ne_zero (0 : Fin 2)) hs)⟩

/-- A nonreal multiplier yields a generator modulo the rational integers;
the argument uses the second coordinate of evaluation at the first period. -/
theorem exists_multiplier_basis_one (L : PeriodPair) (z : periodMultipliers L)
    (hz : (z : ℂ).im ≠ 0) :
    ∃ η : periodMultipliers L, (η : ℂ).im ≠ 0 ∧
      ∀ w : periodMultipliers L, ∃ a b : ℤ, (w : ℂ) = (a : ℂ) + (b : ℂ) * η := by
  let e := secondCoord L
  let J : Ideal ℤ := LinearMap.range e
  let g := Submodule.IsPrincipal.generator J
  obtain ⟨η, hη⟩ : ∃ η, e η = g := Submodule.IsPrincipal.generator_mem J
  have hg : g ≠ 0 := by
    intro h0
    have h := (Submodule.IsPrincipal.mem_iff_generator_dvd J).mp
      (LinearMap.mem_range_self e z : e z ∈ J)
    rw [show Submodule.IsPrincipal.generator J = g from rfl, h0, zero_dvd_iff] at h
    obtain ⟨a, ha⟩ := exists_int_of_secondCoord_eq_zero L z h
    exact hz (ha ▸ Complex.intCast_im a)
  have hηi : (η : ℂ).im ≠ 0 := by
    intro hi
    obtain ⟨a, ha⟩ := exists_int_eq_of_real_multiplier L (η : ℂ) hi η.property
    have he : η = (a : periodMultipliers L) := Subtype.ext ha
    have hone : e 1 = 0 := by
      let x : L.lattice := ⟨(1 : ℂ) * L.ω₁, by simpa only [one_mul] using omega_one_mem L⟩
      change L.latticeBasis.coord 1 x = 0
      have h : x = L.latticeBasis 0 := by
        apply Subtype.ext; simp [x]
      rw [h]
      simp
    have ha0 : e η = 0 := by
      rw [he, ← zsmul_one a, map_smul, hone, smul_zero]
    exact hg (hη.symm.trans ha0)
  refine ⟨η, hηi, fun w => ?_⟩
  obtain ⟨b, hb⟩ : g ∣ e w := (Submodule.IsPrincipal.mem_iff_generator_dvd J).mp
    (LinearMap.mem_range_self e w : e w ∈ J)
  have hw : e (w - b • η) = 0 := by
    rw [map_sub, map_smul, hη, hb, zsmul_eq_mul]
    change g * b - b * g = 0
    ring
  obtain ⟨a, ha⟩ := exists_int_of_secondCoord_eq_zero L (w - b • η) hw
  refine ⟨a, b, ?_⟩
  change (w : ℂ) - b • (η : ℂ) = (a : ℂ) at ha
  rw [zsmul_eq_mul] at ha
  exact sub_eq_iff_eq_add.mp ha

private theorem integral_trace_norm_of_multiplier (L : PeriodPair) (z : periodMultipliers L)
    (hz : (z : ℂ) ≠ 0) (hz1 : (1 + z : periodMultipliers L) ≠ 0) :
    ∃ t u : ℤ, (t : ℝ) = 2 * (z : ℂ).re ∧ (u : ℝ) = Complex.normSq (z : ℂ) := by
  have hidx (w : periodMultipliers L) (hw : (w : ℂ) ≠ 0) :
      ∃ n : ℕ, (n : ℝ) = Complex.normSq (w : ℂ) := by
    let v : ℂˣ := Units.mk0 (w : ℂ) hw
    have hsub : (L.scale v).lattice ≤ L.lattice := by
      intro x hx
      change x ∈ ((L.scale v).lattice : Set ℂ) at hx
      rw [lattice_scale] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact w.property _ hy
    exact ⟨_, cast_sublatticeIndex_scale L v hsub⟩
  obtain ⟨u, hu⟩ := hidx z hz
  obtain ⟨v, hv⟩ := hidx (1 + z) (fun he => hz1 (Subtype.ext he))
  refine ⟨(v : ℤ) - u - 1, u, ?_, by exact_mod_cast hu⟩
  change (v : ℝ) = Complex.normSq (1 + (z : ℂ)) at hv
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, zero_add] at hv hu
  push_cast
  nlinarith

/-- A normalized basis for the complex multiplier order: the generator has
integral trace 0 or 1, positive integral norm and nonzero imaginary part. -/
theorem exists_normalized_multiplier (L : PeriodPair) (z : periodMultipliers L)
    (hz : (z : ℂ).im ≠ 0) :
    ∃ (η : periodMultipliers L) (t u : ℤ),
      (η : ℂ).im ≠ 0 ∧ (t = 0 ∨ t = 1) ∧ 1 ≤ u ∧
      (t : ℝ) = 2 * (η : ℂ).re ∧ (u : ℝ) = Complex.normSq (η : ℂ) ∧
      ∀ w : periodMultipliers L, ∃ a b : ℤ, (w : ℂ) = (a : ℂ) + (b : ℂ) * η := by
  obtain ⟨ξ, hξ, hbas⟩ := exists_multiplier_basis_one L z hz
  obtain ⟨T, _, hT, _⟩ := integral_trace_norm_of_multiplier L ξ
    (by intro h; exact hξ (by rw [h, Complex.zero_im]))
    (by intro h; have he := congrArg (fun x : periodMultipliers L => (x : ℂ).im) h
        exact hξ (by simpa using he))
  let q := T / 2
  let η : periodMultipliers L := ξ - (q : periodMultipliers L)
  have hi : (η : ℂ).im ≠ 0 := by simpa [η, Complex.sub_im] using hξ
  obtain ⟨t, u, ht, hu⟩ := integral_trace_norm_of_multiplier L η
    (by intro he; exact hi (by rw [he, Complex.zero_im]))
    (by intro he; have h := congrArg (fun x : periodMultipliers L => (x : ℂ).im) he
        exact hi (by simpa using h))
  have hte : t = T - 2 * q := by
    have h : (η : ℂ).re = (ξ : ℂ).re - (q : ℝ) := by simp [η, Complex.sub_re]
    exact_mod_cast (show (t : ℝ) = (T : ℝ) - 2 * (q : ℝ) by rw [ht, hT, h]; ring)
  have ht0 : t = 0 ∨ t = 1 := by dsimp [q] at hte; omega
  have hu1 : 1 ≤ u := by
    have h : 0 < (u : ℝ) := hu ▸ Complex.normSq_pos.mpr (by intro h; exact hi (by simp [h]))
    exact (Int.add_one_le_iff.mpr (by exact_mod_cast h : 0 < u))
  refine ⟨η, t, u, hi, ht0, hu1, ht, hu, fun w => ?_⟩
  obtain ⟨a, b, h⟩ := hbas w
  refine ⟨a + b * q, b, ?_⟩
  rw [h]
  push_cast [η]
  ring

/-- Homothety preserves the multiplier subring, including its embedding in ℂ. -/
theorem periodMultipliers_scale (L : PeriodPair) (v : ℂˣ) :
    periodMultipliers (L.scale v) = periodMultipliers L := by
  ext z
  change (∀ w ∈ (L.scale v).lattice, z * w ∈ (L.scale v).lattice) ↔
    ∀ w ∈ L.lattice, z * w ∈ L.lattice
  simp only [← SetLike.mem_coe, lattice_scale, Set.mem_image]
  constructor
  · intro h w hw
    obtain ⟨y, hy, he⟩ := h _ ⟨w, hw, rfl⟩
    exact (mul_left_cancel₀ v.ne_zero (show (v : ℂ) * y = (v : ℂ) * (z * w) by
      rw [he]; ring) : y = z * w) ▸ hy
  · rintro h _ ⟨w, hw, rfl⟩
    exact ⟨z * w, h _ hw, by ring⟩

/-- Equal complex j-values have equal embedded multiplier subrings. -/
theorem periodMultipliers_eq_of_jLattice_eq (L M : PeriodPair) (h : L.jLattice = M.jLattice) :
    periodMultipliers L = periodMultipliers M := by
  obtain ⟨v, hv⟩ := exists_homothetic_of_jLattice_eq L M h
  rw [← periodMultipliers_scale L v]
  ext z
  change (∀ w ∈ (L.scale v).lattice, z * w ∈ (L.scale v).lattice) ↔
    ∀ w ∈ M.lattice, z * w ∈ M.lattice
  rw [hv]


end ZInQ.Manuscript.RC.CMField2

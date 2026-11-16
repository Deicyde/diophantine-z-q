import ZInQKernel.Contrib.OneProof.RayClassShimura

set_option linter.all false

noncomputable section

namespace DCY3Used

open LeafQM ShimuraCFT RayClassCFT IsDedekindDomain NumberField Complex

abbrev K4 : Type := ShimuraGlue.Ray.K4

instance : IsTotallyComplex K4 := isTotallyComplex_of_root y4_rel (by norm_num)

/-- `β = i + j ∈ 𝒪`, `β² = −1`. -/
def beta : B := ⟨0, 1, 1, 0⟩

theorem inO_beta : InO beta := ⟨![-1, 1, 2, 0], by ext <;> simp [beta, ofInt] <;> norm_num⟩

theorem beta_sq : beta * beta + (0 : ℚ) • beta + algebraMap ℚ B 1 = 0 := by
  ext <;> simp [beta] <;> norm_num

/-- `τ₀ = √2 + i`, the fixed point of `ι(β)` in `ℍ`. -/
def tau0 : UpperHalfPlane := ⟨(Real.sqrt 2 : ℂ) + I, by simp⟩

theorem heig0 : Matrix.mulVec ((BPAnalytic.QM.iota beta).map (algebraMap ℝ ℂ)) ![(tau0 : ℂ), 1] =
    I • ![(tau0 : ℂ), 1] := by
  have h := ZInQ.Contrib.TYZGenus.Shimura.sqrt_mul_self_C 2
  push_cast at h
  ext i
  fin_cases i
  · simp [BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, tau0, beta]
    linear_combination h - Complex.I_sq
  · simp [BPAnalytic.QM.iota, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, tau0, beta]

theorem y4_ne : ∀ r : ℚ, y4 ≠ r := not_rat_of_disc y4_rel (by norm_num)

/-- `q : ℚ(i) → B`, `i ↦ β`. -/
def q4 : K4 →ₐ[ℚ] B := liftQuad finrank_K4 y4_ne y4_rel beta beta_sq

theorem hl0 : I * I + (0 : ℚ) • I + algebraMap ℚ ℂ 1 = 0 :=
  eig_rel (v := ![(tau0 : ℂ), 1]) (by simp) heig0 beta_sq

/-- The reflex embedding `κ₀ : ℚ(i) → ℂ`, `i ↦ i`. -/
def kappa0 : K4 →+* ℂ := (liftQuad finrank_K4 y4_ne y4_rel I hl0).toRingHom

theorem q4_integral : ∀ x : 𝓞 K4, InO (q4 x) := by
  intro x
  obtain ⟨a, b, hab⟩ := ringOfIntegersGen_K4 x
  have e : (x : K4) = ((a : ℚ) : K4) + ((b : ℚ) : K4) * y4 := by rw [hab]; push_cast; ring
  rw [e, q4, liftQuad_apply]
  have e2 : algebraMap ℚ LeafQM.B (a : ℚ) + (b : ℚ) • beta = (a : LeafQM.B) + (b : LeafQM.B) * beta := by
    rw [Algebra.smul_def]; simp
  rw [e2]
  exact inO_int_comb inO_beta a b

theorem isCMPoint0 : IsCMPoint q4 kappa0 tau0 := by
  intro a
  obtain ⟨r, s, rfl⟩ := exists_rat_repr finrank_K4 y4_ne a
  show Matrix.mulVec (iotaC _) _ = _
  rw [kappa0, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, q4, liftQuad_apply, liftQuad_apply, map_add,
    AlgHom.commutes, map_smul, Matrix.add_mulVec, Matrix.smul_mulVec, show Matrix.mulVec (iotaC beta)
      ![(tau0 : ℂ), 1] = I • ![(tau0 : ℂ), 1] from heig0]
  ext i
  fin_cases i <;>
    simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal, Algebra.smul_def] <;> ring

/-- `c = 1 + i`. -/
def c4 : K4 := ((1 : ℚ) : K4) + ((1 : ℚ) : K4) * y4

theorem q4_c4 : q4 c4 = ofInt ![0, 1, 2, 0] := by
  rw [c4, q4, liftQuad_apply]
  ext <;> simp [beta, ofInt, Algebra.smul_def] <;> norm_num

end DCY3Used

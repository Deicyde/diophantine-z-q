import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.PairJ
import ZInQKernel.Contrib.OneProof.RC.ModelLevels.GeneratorOrbits
import ZInQKernel.Contrib.OneProof.RC.X0Model.Expansion
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_jLattice_ofTau

/-! # The cyclic pair of an actual upper half-plane parameter -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric3

open ModelGeneric2 UpperHalfPlane
open ZInQ.Manuscript.RC

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

variable {N : ℕ} [NeZero N]

private theorem nsmul_div_mem_periodLattice (τ : UpperHalfPlane) (m : ℕ) :
    m • (1 / (N : ℂ)) ∈ (PeriodPair.ofTau τ).lattice ↔ N ∣ m := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hreal : ((m : ℂ) / (N : ℂ)).im = 0 := by
    rw [← Complex.ofReal_natCast m, ← Complex.ofReal_natCast N, ← Complex.ofReal_div]
    exact Complex.ofReal_im _
  rw [PeriodPair.ofTau_lattice, Submodule.mem_span_pair, nsmul_eq_mul, mul_one_div]
  constructor
  · rintro ⟨a, b, h⟩
    have him := congrArg Complex.im h
    rw [hreal] at him
    simp only [zsmul_eq_mul, Complex.add_im, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, add_zero, Complex.one_im, mul_zero] at him
    have ha : a = 0 := by
      exact_mod_cast (mul_eq_zero.mp him).resolve_right τ.im_pos.ne'
    subst a
    simp only [zero_smul, zero_add, zsmul_eq_mul, mul_one] at h
    have hb : (b : ℤ) * (N : ℤ) = (m : ℤ) := by
      exact_mod_cast (eq_div_iff hN).mp h
    exact Int.natCast_dvd_natCast.mp ⟨b, by simpa [mul_comm] using hb.symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨0, b, ?_⟩
    simp only [zero_smul, zero_add, zsmul_eq_mul, mul_one, Int.cast_natCast, Nat.cast_mul]
    exact (eq_div_iff hN).2 (mul_comm _ _)

private noncomputable def latticeGenerator (τ : UpperHalfPlane) :
    Generators (PeriodPair.ofTau τ).weierstrassCurve.toAffine.Point N := by
  let L := PeriodPair.ofTau τ
  let h := L.discriminant_ne_zero
  let u : ℂ →+ L.weierstrassCurve.toAffine.Point :=
    { toFun := L.toPoint h
      map_zero' := L.toPoint_zero h
      map_add' := (L.isUniformization_toPoint h).1 }
  let z : ℂ := 1 / (N : ℂ)
  refine ⟨u z, Nat.dvd_antisymm ?_ ?_⟩
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    rw [← map_nsmul]
    exact L.toPoint_of_mem h ((nsmul_div_mem_periodLattice τ N).2 dvd_rfl)
  · apply (nsmul_div_mem_periodLattice τ (addOrderOf (u z))).1
    apply (L.isUniformization_toPoint h).2.2
    change u (addOrderOf (u z) • z) = 0
    rw [map_nsmul, addOrderOf_nsmul_eq_zero]

/-- The genuine analytic cyclic pair, using the Weierstrass equation of the
period lattice and the image of 1/N under its uniformization. -/
noncomputable def analyticCyclicPair (τ : UpperHalfPlane) : PairClasses ℂ N :=
  let L := PeriodPair.ofTau τ
  Quot.mk _ ⟨L.weierstrassCurve, ⟨isUnit_iff_ne_zero.mpr
    L.discriminant_ne_zero.weierstrassCurve_Δ_ne_zero⟩, subgroupOfGenerator (latticeGenerator τ)⟩

/-- The source j-invariant of the genuine analytic pair is the j-value of
the upper half-plane parameter. -/
theorem analyticCyclicPair_j (τ : UpperHalfPlane) :
    pairJ (analyticCyclicPair (N := N) τ) = X0Model.analyticJ τ := by
  let L := PeriodPair.ofTau τ
  rw [analyticCyclicPair, pairJ_mk, WeierstrassCurve.j,
    Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', mul_comm, ← div_eq_mul_inv]
  change L.weierstrassCurve.c₄ ^ 3 / L.weierstrassCurve.Δ = _
  rw [← L.jLattice_eq_c₄_pow_three_div_Δ]
  exact PeriodPair.jLattice_ofTau τ

#print axioms nsmul_div_mem_periodLattice
#print axioms latticeGenerator
#print axioms analyticCyclicPair
#print axioms analyticCyclicPair_j

end WeierstrassCurve.ModelLevels.ModelGeneric3

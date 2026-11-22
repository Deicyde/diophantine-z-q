import ZInQKernel.Contrib.OneProof.EndomorphismTraceForm
import ZInQKernel.Contrib.OneProof.TateSemisimplicity

/-! # Reduction of Faltings semisimplicity to splitting algebraic morphisms up to isogeny -/

noncomputable section
open PkgI3.AbVar
open scoped CategoryTheory.MonObj TensorProduct nonZeroDivisors

namespace ZInQ.Contrib.TateFiniteApproximation

private theorem exists_rat_tmul {M : Type*} [AddCommGroup M] (x : ℚ ⊗[ℤ] M) :
    ∃ (a : ℚ) (w : M), a ≠ 0 ∧ x = a ⊗ₜ[ℤ] w := by
  obtain ⟨⟨w, s⟩, hs⟩ := IsLocalizedModule.surj ℤ⁰ (TensorProduct.mk ℤ ℚ M 1) x
  let d : ℚ := algebraMap ℤ ℚ s.1
  have hd : d ≠ 0 := (map_ne_zero_iff _ Int.cast_injective).mpr (nonZeroDivisors.coe_ne_zero s)
  have he : d • x = (1 : ℚ) ⊗ₜ[ℤ] w := by
    change (s.1 : ℤ) • x = 1 ⊗ₜ[ℤ] w at hs
    simpa only [d, IsScalarTower.algebraMap_smul] using hs
  refine ⟨d⁻¹, w, inv_ne_zero hd, ?_⟩
  calc
    x = d⁻¹ • (d • x) := by rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
    _ = d⁻¹ ⊗ₜ[ℤ] w := by rw [he, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- An integral inner inverse up to a positive integer makes every scalar
extension of the endomorphism algebra to a characteristic-zero field semisimple. -/
theorem semisimple_of_integral_splitting {R : Type*} [Ring R] [Module.Finite ℤ R]
    (E : Type*) [Field E] [CharZero E]
    (h : ∀ f : R, ∃ (g : R) (n : ℕ), 0 < n ∧ f * g * f = n • f) :
    IsSemisimpleRing (E ⊗[ℤ] R) := by
  have hi (x : ℚ ⊗[ℤ] R) : ∃ y, x * y * x = x := by
    obtain ⟨a, f, ha, rfl⟩ := exists_rat_tmul x
    obtain ⟨g, n, hn, hg⟩ := h f
    have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    refine ⟨((a * n)⁻¹) ⊗ₜ[ℤ] g, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, hg,
      TensorProduct.tmul_smul (R' := ℕ), TensorProduct.smul_tmul']
    congr 1
    rw [nsmul_eq_mul, mul_inv]
    field_simp
  let e : (E ⊗[ℚ] (ℚ ⊗[ℤ] R)) ≃ₐ[E] E ⊗[ℤ] R :=
    AlgEquiv.symm <| AlgEquiv.ofLinearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ E E R).symm
      (by simp [Algebra.TensorProduct.one_def])
      (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ => by simp))
  have := semisimple_baseChange_of_innerInverse ℚ (ℚ ⊗[ℤ] R) E hi
  exact RingHom.isSemisimpleRing_of_surjective (R := E ⊗[ℚ] (ℚ ⊗[ℤ] R))
    (S := E ⊗[ℤ] R) e.toRingEquiv.toRingHom (fun b => ⟨e.symm b, e.apply_symm_apply b⟩)

/-- Only an inner inverse up to an integer for each genuine algebraic
endomorphism is needed in addition to the stable height and isogeny bound. -/
theorem faltingsSemisimple_at_of_geometric_splitting {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (g : ℕ) (height : ℝ) (hdim : A.dim = (g : WithBot ℕ∞))
    (hheight : ZInQ.SemistabAssembly.IsAnStableHeightSS A height)
    (hsplit : ∀ f : End A, ∃ (g : End A) (n : ℕ), 0 < n ∧ f * g * f = n • f) :
    (A.galRep ℓ).IsSemisimpleRepresentation := by
  have h := OneProof.HomFreeC.homFreeFiniteNF uniformizationLeafAll_proof
    CloudB3W16Torsion.mumfordTorsionAlgClosed_proof K A A
  let := h.2.1
  let := semisimple_of_integral_splitting ℚ_[ℓ] hsplit
  exact faltingsSemisimple_at_of_endomorphism_algebra ℓ A hGR g height hdim hheight

/-- For a simple abelian variety the ordinary isogeny quasi-inverse supplies
the splitting for each nonzero endomorphism. -/
theorem faltingsSemisimple_at_of_simple {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) (hA : PkgI3.EndDivision A) (ℓ : ℕ) [Fact ℓ.Prime]
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (g : ℕ) (height : ℝ) (hdim : A.dim = (g : WithBot ℕ∞))
    (hheight : ZInQ.SemistabAssembly.IsAnStableHeightSS A height) :
    (A.galRep ℓ).IsSemisimpleRepresentation := by
  apply faltingsSemisimple_at_of_geometric_splitting A ℓ hGR g height hdim hheight
  intro f
  by_cases h0 : f = 0
  · exact ⟨0, 1, by decide, by simp [h0]⟩
  obtain ⟨n, hn, r, _, hr⟩ := MilneQuasiInverse.milneIsogenyQuasiInverse_proof K A A f (hA f h0)
  have hfr : f*r = (n : End A) := by
    have he : f*r = ((n : ℤ) : End A) := Hom.ext' hr
    simpa using he
  exact ⟨r, n, hn, by rw [hfr, nsmul_eq_mul]⟩

end ZInQ.Contrib.TateFiniteApproximation

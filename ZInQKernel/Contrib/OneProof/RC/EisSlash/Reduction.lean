import ZInQKernel.Contrib.OneProof.RC.EisSlash.Characters

/-! Transfer the lattice transformation and its cusp bounds to the
explicit character-pair function of tex 9647–9654, 9762–9764 and 9862–9864.
The transfer is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisSlash

open Matrix Matrix.SpecialLinearGroup ModularForm UpperHalfPlane CongruenceSubgroup
open O12Eisenstein O12EisConst EisForm
open scoped MatrixGroups ModularForm

variable {D : Type*} [Field D] {p : ℕ} [Fact p.Prime]

/-- Weight-two Lipschitz normalization: factor two for the two signs of the
nonzero first coordinate, and the Gauss factor for the second character. -/
def orderedScale {m : ℕ} [NeZero m] (b : DirichletCharacter ℂ m) : ℂ :=
  (2 / (m : ℂ)^2) * ((-2 * Real.pi * Complex.I)^2 * gaussSum b⁻¹ ZMod.stdAddChar)

theorem orderedScale_ne_zero {m : ℕ} [NeZero m] (b : DirichletCharacter ℂ m)
    (hb : b.IsPrimitive) : orderedScale b ≠ 0 := by
  have hprim : b⁻¹.IsPrimitive := by
    simpa [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv] using hb
  have hg : gaussSum b⁻¹ ZMod.stdAddChar ≠ 0 := by
    intro h
    have he : ZMod.dft (⇑(b⁻¹)) = 0 := by
      funext r
      rw [hprim.fourierTransform_eq_inv_mul_gaussSum, h, mul_zero, Pi.zero_apply]
    have hzero : (⇑(b⁻¹) : ZMod m → ℂ) = 0 :=
      ZMod.dft.injective (he.trans ZMod.dft.map_zero.symm)
    simpa using congrFun hzero 1
  exact mul_ne_zero (div_ne_zero (by norm_num) (pow_ne_zero _ (by exact_mod_cast NeZero.ne m)))
    (mul_ne_zero (pow_ne_zero _ (by simp [Real.pi_ne_zero])) hg)

/-- The scalar for the actual Fourier order. -/
def pairScale (E : CharacterPair D p) (c : D →+* ℂ) : ℂ :=
  if E.twistUnramified then orderedScale (E.unram.ringHomComp c)
  else orderedScale (E.ramified.ringHomComp c)

theorem pairScale_ne_zero (E : CharacterPair D p) (c : D →+* ℂ)
    (hu : E.unram.IsPrimitive) (hr : E.ramified.IsPrimitive) : pairScale E c ≠ 0 := by
  unfold pairScale
  split
  · exact orderedScale_ne_zero _ (primitive_ringHomComp _ c hu)
  · exact orderedScale_ne_zero _ (primitive_ringHomComp _ c hr)

/-- The normalization identity: the concrete finite weighted
lattice sum has the prescribed Fourier series up to the indicated scalar.
The constant at the cusp at infinity is free. -/
def PairGridFourier (E : CharacterPair D p) (c : D →+* ℂ) : Prop :=
  ∃ C : ℂ, gridCombination (pairLevel E) (pairWeight E c) = pairScale E c • pairSeries E c C

/-- Transfer both analytic checks for the same constant from the finite
lattice expression; the identity itself mentions neither check. -/
theorem pair_checks_of_grid_eq (E : CharacterPair D p) (c : D →+* ℂ)
    (hu : E.unram.IsPrimitive) (hr : E.ramified.IsPrimitive) (C : ℂ)
    (h : gridCombination (pairLevel E) (pairWeight E c) = pairScale E c • pairSeries E c C) :
    PairSlashLaw E c C ∧ PairOtherCusps E c C := by
  have hn := pairScale_ne_zero E c hu hr
  let F := gridCombination (pairLevel E) (pairWeight E c)
  have hF : pairSeries E c C = (pairScale E c)⁻¹ • F := by
    change pairSeries E c C = (pairScale E c)⁻¹ • gridCombination (pairLevel E) (pairWeight E c)
    rw [h, smul_smul, inv_mul_cancel₀ hn, one_smul]
  constructor
  · intro g
    rw [hF]
    change ((pairScale E c)⁻¹ • F) ∣[(2 : ℤ)] g.val = _
    rw [SL_smul_slash, gridCombination_slash_scalar (pairLevel E) (pairWeight E c) g.val _
      (pairWeight_pullback E c g), smul_smul, smul_smul, mul_comm]
  · intro x _ hx
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff'] at hx
    obtain ⟨g, rfl⟩ := hx
    rw [OnePoint.IsBoundedAt.smul_iff, OnePoint.isBoundedAt_infty_iff]
    change IsBoundedAtImInfty (pairSeries E c C ∣[(2 : ℤ)] g)
    rw [hF, SL_smul_slash]
    apply (boundedAtImInftySubalgebra ℂ).smul_mem
    exact gridCombination_bounded_slash (pairLevel E) (pairWeight E c) g

/-- The finite sum normalization would close the original modularity stop. -/
theorem missingModularity_of_gridFourier (E : CharacterPair D p) (c : D →+* ℂ)
    (hu : E.unram.IsPrimitive) (hr : E.ramified.IsPrimitive) (h : PairGridFourier E c) :
    MissingModularity E c := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, pair_checks_of_grid_eq E c hu hr C hC⟩

/-- The normalized positive divisor sums give the exact constituent form
once the finite lattice expression is identified. -/
theorem baseForm_of_gridFourier (E : CharacterPair D p) (c : D →+* ℂ)
    (hu : E.unram.IsPrimitive) (hr : E.ramified.IsPrimitive) (h : PairGridFourier E c) :
    Nonempty (BaseForm E c) := by
  obtain ⟨C, hs, hc⟩ := missingModularity_of_gridFourier E c hu hr h
  exact baseForm_of_modularity E c hu hr C hs hc


end ZInQ.Manuscript.RC.EisSlash

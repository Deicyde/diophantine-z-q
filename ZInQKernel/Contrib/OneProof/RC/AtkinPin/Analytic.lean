import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Sign
import ZInQKernel.Contrib.CloudB3RC53.Prints.CST
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Primitive

/-! The scaled Eichler primitive and its Atkin–Lehner transform.
The argument for tex 2943–2946 on the upper half-plane is on-the-spot (c). -/

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Manifold TauCeti.ExactDivisor
open Complex UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open ZInQ.Contrib.CloudB3RC53.CST

namespace ZInQ.Manuscript.RC.AtkinPin

variable {N Q : ℕ} [NeZero N]

/-- The Möbius transformation used by the normalized operator. -/
def atkinGL (hQ : Q ∥ N) : GL (Fin 2) ℝ :=
  TauCeti.atkinLehnerGL hQ.pos (TauCeti.isAtkinLehnerMatrix_atkinLehnerMatrix hQ)

/-- The weight-two slash by this representative has the pinned eigenvalue. -/
theorem slash_eq_signUnit_smul (f : HeckeRing.GL2.Newform N 2) (hχ : f.χ = 1)
    (hQ : Q ∥ N) :
    (⇑(f.toCuspFormGamma0 hχ) ∣[(2 : ℤ)] atkinGL hQ) =
      ((signUnit f hχ hQ : ℤ) : ℂ) • ⇑(f.toCuspFormGamma0 hχ) := by
  rw [signUnit_cast]
  have h := congrArg (fun g : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2 => ⇑g)
    (f.normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_atkinLehnerSign_smul hχ hQ)
  simpa [atkinGL, hQ.coe_normalizedAtkinLehnerOperatorCusp, TauCeti.atkinLehnerNormalizer] using h

private theorem hasDerivAt_eichlerPotential
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2) (τ : ℍ) :
    HasDerivAt (eichlerPotential f ∘ ofComplex)
      ((2 * (Real.pi : ℂ) * Complex.I) * f τ) (τ : ℂ) := by
  have hΓ := TauCeti.one_mem_strictPeriods_Gamma0_map N
  have hh : (0 : ℝ) < 1 := one_pos
  have hE := TauCeti.mdifferentiable_eichlerIntegral hh
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) 1
  have hd := (UpperHalfPlane.mdifferentiableAt_iff.mp (hE τ)).hasDerivAt
  change HasDerivAt (eichlerPotential f ∘ ofComplex)
    (deriv (eichlerPotential f ∘ ofComplex) (τ : ℂ)) (τ : ℂ) at hd
  have h := congrFun
    (TauCeti.CuspFormClass.iterate_normalizedDerivOfComplex_eichlerIntegral f hh hΓ 0) τ
  change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * deriv (eichlerPotential f ∘ ofComplex) (τ : ℂ) = f τ at h
  rw [← h, ← mul_assoc, mul_inv_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]
  exact hd

/-- The scaled primitive transforms by an integer sign and a single
constant. This equality is already true in `ℂ`, before passing to periods. -/
theorem scaled_eichler_transform (f : HeckeRing.GL2.Newform N 2) (hχ : f.χ = 1)
    (hQ : Q ∥ N) (κ : ℂ) (base : ℍ) :
    ∀ τ : ℍ,
      κ * eichlerPotential (f.toCuspFormGamma0 hχ) (atkinGL hQ • τ) =
        ((signUnit f hχ hQ : ℤ) : ℂ) * (κ * eichlerPotential (f.toCuspFormGamma0 hχ) τ) +
          (κ * eichlerPotential (f.toCuspFormGamma0 hχ) (atkinGL hQ • base) -
            ((signUnit f hχ hQ : ℤ) : ℂ) *
              (κ * eichlerPotential (f.toCuspFormGamma0 hχ) base)) := by
  let F := f.toCuspFormGamma0 hχ
  let e : ℂ := ((signUnit f hχ hQ : ℤ) : ℂ)
  let b : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let g := atkinGL hQ
  let u : ℂ → ℂ := fun z => eichlerPotential F (g • ofComplex z)
  let v : ℂ → ℂ := fun z => e * eichlerPotential F (ofComplex z)
  have hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det :=
    TauCeti.val_det_atkinLehnerGL_pos hQ.pos _
  have hu (z : ℍ) : HasDerivAt u (e * (b * F z)) (z : ℂ) := by
    have h := TauCeti.hasDerivAt_comp_smul (F := fun z => b * F z)
      (Φ := eichlerPotential F ∘ ofComplex) (hasDerivAt_eichlerPotential F) hg z
    have he := congrFun (slash_eq_signUnit_smul f hχ hQ) z
    have he' : (⇑F ∣[(2 : ℤ)] g) z = e * F z := he
    rw [ModularForm.slash_apply_of_det_pos 2 hg] at he' h
    simp only [Function.comp_apply, ofComplex_apply] at h
    exact h.congr_deriv (by linear_combination b * he')
  have hv (z : ℍ) : HasDerivAt v (e * (b * F z)) (z : ℂ) :=
    (hasDerivAt_eichlerPotential F z).const_mul e
  let c := u (base : ℂ) - v (base : ℂ)
  have hc (z : ℍ) : HasDerivAt (fun x => v x + c) (e * (b * F z)) (z : ℂ) :=
    (hv z).add_const c
  have heq : Set.EqOn u (fun x => v x + c) {z : ℂ | 0 < z.im} :=
    isOpen_upperHalfPlaneSet.eqOn_of_deriv_eq (convex_halfSpace_im_gt 0).isPreconnected
      (fun z hz => (hu ⟨z, hz⟩).differentiableAt.differentiableWithinAt)
      (fun z hz => (hc ⟨z, hz⟩).differentiableAt.differentiableWithinAt)
      (fun z hz => ((hu ⟨z, hz⟩).deriv).trans (hc ⟨z, hz⟩).deriv.symm)
      base.im_pos (by dsimp [c]; ring)
  intro τ
  have ht := congrArg (κ * ·) (heq τ.im_pos)
  simpa only [u, v, c, g, F, e, ofComplex_apply, mul_add, mul_sub, mul_left_comm κ] using ht

/-- The transformation on the actual period quotient of the lattice.
The translate here is the class of the difference computed at `base`. -/
theorem periodClass_transform (f : HeckeRing.GL2.Newform N 2) (hχ : f.χ = 1)
    (hQ : Q ∥ N) (Lat : PeriodPair) (κ : ℂ) (base τ : ℍ) :
    let ζ := fun z : ℍ => κ * eichlerPotential (f.toCuspFormGamma0 hχ) z
    let mk := QuotientAddGroup.mk' Lat.lattice.toAddSubgroup
    mk (ζ (atkinGL hQ • τ)) =
      (signUnit f hχ hQ : ℤ) • mk (ζ τ) +
        (mk (ζ (atkinGL hQ • base)) - (signUnit f hχ hQ : ℤ) • mk (ζ base)) := by
  dsimp only
  have h := scaled_eichler_transform f hχ hQ κ base τ
  rw [← zsmul_eq_mul, ← zsmul_eq_mul] at h
  simpa only [map_add, map_sub, map_zsmul] using
    congrArg (QuotientAddGroup.mk' Lat.lattice.toAddSubgroup) h


end ZInQ.Manuscript.RC.AtkinPin

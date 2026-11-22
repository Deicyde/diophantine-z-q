import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.AffineSpaceRigidity

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace ZInQ.ToricOrthogonality

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) {h : Polynomial k}

/-- The structure map of the principal open of the affine line defined by `h`. -/
abbrev affineLineOpenMap (h : Polynomial k) : Spec (.of (Localization.Away h)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away h)))

/-- Over a nonempty affine chart, every unit on the product with an open of the
affine line splits as a unit from each factor. -/
theorem exists_unit_factorization (hh : h ≠ 0) {U : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty)
    (u : Γ(pullback f (affineLineOpenMap h), (pullback.fst f (affineLineOpenMap h)) ⁻¹ᵁ U)ˣ) :
    ∃ (c : Γ(X, U)ˣ) (w : Γ(Spec (.of (Localization.Away h)), ⊤)ˣ),
      u.val = (pullback.fst f (affineLineOpenMap h)).app U c.val *
        (pullback.snd f (affineLineOpenMap h)).appLE ⊤
        (pullback.fst f (affineLineOpenMap h) ⁻¹ᵁ U) le_top w.val := by
  let : Nonempty U := hne.to_subtype
  have := IsIntegral.component_integral (X := X) U
  let : Algebra k Γ(X, U) :=
    ((f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  obtain ⟨e, e₁, e₂⟩ :=
    exists_ringEquiv_tensor_app_preimage_fst (baseAlgebra := Localization.Away h) f hU
  obtain ⟨c, w, hcw⟩ := TensorProduct.exists_units_eq_tmul
    (baseField := k) Γ(X, U) hh (Units.map e.symm.toMulEquiv.toMonoidHom u)
  refine ⟨c, Units.map (Scheme.ΓSpecIso (.of (Localization.Away h))).inv.hom.toMonoidHom w, ?_⟩
  have hc : e.symm u.val = (c.val ⊗ₜ[k] w.val) := hcw
  rw [← e.apply_symm_apply u.val, hc,
    show (c.val ⊗ₜ[k] w.val) = (c.val ⊗ₜ[k] (1 : Localization.Away h)) * (1 ⊗ₜ[k] w.val) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, e₁, e₂]
  rfl

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.exists_unit_factorization

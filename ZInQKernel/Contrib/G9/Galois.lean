import ZInQKernel.Contrib.G9.I4Layer
import ZInQKernel.Contrib.G9.Descent

/-!
# G9: the image of `G_F` in `G_{ℚ_p}`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

For a finite Galois extension `F/ℚ_p`, pkg-I4's map `gfToGqp p F : G_F → G_{ℚ_p}` (Mathlib's
`Field.absoluteGaloisGroup.map`, restriction along a chosen embedding `ℚ̄_p → F̄`) has image the
kernel of the restriction `G_{ℚ_p} → Gal(F'/ℚ_p)`, where `F' ⊆ ℚ̄_p` is a copy of `F`
(`range_gfToGqp`). `F'` is finite Galois over `ℚ_p` with `[F':ℚ_p] = [F:ℚ_p]`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open PkgI4 Module

noncomputable section

section Galois

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- An element of `G_F` as an automorphism of `F̄`. -/
abbrev galF (σ : Field.absoluteGaloisGroup F) : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := σ

/-- `gfToGqp` is restriction along an embedding `g : ℚ̄_p → F̄` over `ℚ_p`. -/
theorem exists_emb_gfToGqp : ∃ g : PadicAlgCl p →+* AlgebraicClosure F,
    (∀ c : ℚ_[p], g (algebraMap ℚ_[p] (PadicAlgCl p) c) =
      algebraMap F (AlgebraicClosure F) (algebraMap ℚ_[p] F c)) ∧
    ∀ (σ : Field.absoluteGaloisGroup F) (x : PadicAlgCl p), g (gfToGqp p F σ x) = galF F σ (g x) := by
  let _i1 : Algebra ℚ_[p] F := (algebraMap ℚ_[p] F).toAlgebra
  let g0 : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] AlgebraicClosure F := IsAlgClosed.lift
  let _i2 : Algebra (AlgebraicClosure ℚ_[p]) (AlgebraicClosure F) := g0.toAlgebra
  refine ⟨g0.toRingHom, fun c => g0.commutes c, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars ℚ_[p] σ)
    (AlgebraicClosure ℚ_[p]) x

/-- The embedding `ℚ̄_p → F̄` behind `gfToGqp`. -/
def embF : PadicAlgCl p →+* AlgebraicClosure F := (exists_emb_gfToGqp p F).choose

theorem embF_algebraMap (c : ℚ_[p]) : embF p F (algebraMap ℚ_[p] (PadicAlgCl p) c) =
    algebraMap F (AlgebraicClosure F) (algebraMap ℚ_[p] F c) :=
  (exists_emb_gfToGqp p F).choose_spec.1 c

theorem embF_gfToGqp (σ : Field.absoluteGaloisGroup F) (x : PadicAlgCl p) :
    embF p F (gfToGqp p F σ x) = galF F σ (embF p F x) :=
  (exists_emb_gfToGqp p F).choose_spec.2 σ x

theorem embF_bijective : Function.Bijective (embF p F) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  intro y
  have : Algebra.IsIntegral ℚ_[p] (AlgebraicClosure F) :=
    Algebra.IsIntegral.trans (R := ℚ_[p]) F
  have hy : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  apply RingHom.IsIntegralElem.of_comp (f := algebraMap ℚ_[p] (PadicAlgCl p))
  have hc : (embF p F).comp (algebraMap ℚ_[p] (PadicAlgCl p)) =
      algebraMap ℚ_[p] (AlgebraicClosure F) := by
    ext c
    rw [RingHom.comp_apply, embF_algebraMap, ← IsScalarTower.algebraMap_apply]
  rw [hc]
  exact hy

/-- `ℚ̄_p ≃ F̄`. -/
def embFEquiv : PadicAlgCl p ≃+* AlgebraicClosure F :=
  RingEquiv.ofBijective (embF p F) (embF_bijective p F)

theorem embFEquiv_apply (x : PadicAlgCl p) : embFEquiv p F x = embF p F x := rfl

/-- `F → ℚ̄_p`, `y ↦ g⁻¹(y)`. -/
def phiF : F →ₐ[ℚ_[p]] PadicAlgCl p where
  toRingHom := (embFEquiv p F).symm.toRingHom.comp (algebraMap F (AlgebraicClosure F))
  commutes' c := by
    apply (embFEquiv p F).injective
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_ofClass, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      Function.comp_apply, RingEquiv.apply_symm_apply, embFEquiv_apply, embF_algebraMap]

theorem embF_phiF (y : F) : embF p F (phiF p F y) = algebraMap F (AlgebraicClosure F) y := by
  rw [← embFEquiv_apply]
  exact (embFEquiv p F).apply_symm_apply _

/-- `F' ⊆ ℚ̄_p`, the copy of `F` with `G_F = G_{F'}` under `gfToGqp`. -/
def fieldF : IntermediateField ℚ_[p] (PadicAlgCl p) := (phiF p F).fieldRange

/-- `F ≃ F'`. -/
def equivFieldF : F ≃ₐ[ℚ_[p]] fieldF p F := (phiF p F).equivFieldRange

instance : FiniteDimensional ℚ_[p] (fieldF p F) :=
  LinearEquiv.finiteDimensional (equivFieldF p F).toLinearEquiv

theorem finrank_fieldF : finrank ℚ_[p] (fieldF p F) = finrank ℚ_[p] F :=
  (equivFieldF p F).toLinearEquiv.finrank_eq.symm

variable [IsGalois ℚ_[p] F]

instance : IsGalois ℚ_[p] (fieldF p F) := IsGalois.of_algEquiv (equivFieldF p F)

/-- The restriction `G_{ℚ_p} → Gal(F'/ℚ_p)`. -/
def gammaF : GQp p →* (fieldF p F ≃ₐ[ℚ_[p]] fieldF p F) :=
  AlgEquiv.restrictNormalHom (fieldF p F)

theorem gammaF_surjective : Function.Surjective (gammaF p F) :=
  AlgEquiv.restrictNormalHom_surjective (PadicAlgCl p)

theorem gammaF_apply_coe (τ : GQp p) (x : fieldF p F) :
    ((gammaF p F τ x : fieldF p F) : PadicAlgCl p) = τ (x : PadicAlgCl p) :=
  AlgEquiv.restrictNormal_commutes τ (fieldF p F) x

theorem mem_ker_gammaF (τ : GQp p) :
    τ ∈ (gammaF p F).ker ↔ ∀ y : F, τ (phiF p F y) = phiF p F y := by
  rw [gammaF, IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y
    exact h _ ⟨y, rfl⟩
  · rintro h _ ⟨y, rfl⟩
    exact h y

/-- **The image of `G_F` is `ker(G_{ℚ_p} → Gal(F'/ℚ_p))`.** -/
theorem range_gfToGqp : (gfToGqp p F).range = (gammaF p F).ker := by
  ext τ
  rw [MonoidHom.mem_range, mem_ker_gammaF]
  constructor
  · rintro ⟨σ, rfl⟩ y
    apply (embF_bijective p F).injective
    rw [embF_gfToGqp, embF_phiF]
    exact (galF F σ).commutes y
  · intro h
    -- `σ = g ∘ τ ∘ g⁻¹`, an `F`-automorphism of `F̄`
    let e := embFEquiv p F
    let σr : AlgebraicClosure F ≃+* AlgebraicClosure F :=
      (e.symm.trans τ.toRingEquiv).trans e
    have hσr : ∀ x, σr x = e (τ (e.symm x)) := fun _ => rfl
    let σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F :=
      { σr with
        commutes' := by
          intro y
          change σr (algebraMap F (AlgebraicClosure F) y) = _
          rw [hσr, ← embF_phiF p F y, ← embFEquiv_apply, RingEquiv.symm_apply_apply, h y,
            embFEquiv_apply, embF_phiF] }
    let σ' : Field.absoluteGaloisGroup F := σ
    refine ⟨σ', ?_⟩
    ext x
    apply (embF_bijective p F).injective
    rw [embF_gfToGqp p F σ' x]
    change σr (embF p F x) = embF p F (τ x)
    rw [hσr, ← embFEquiv_apply, RingEquiv.symm_apply_apply]
    rfl

end Galois

end

end ZInQ.Contrib.G9

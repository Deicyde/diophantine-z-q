import ZInQKernel.Contrib.OneProof.TatePrints.Rows
import ZInQKernel.Contrib.AbVarBC.Main

/-!
# `T_p` of an abelian variety from its `F̄`-points and from its `ℂ_p`-points

Let `F/ℚ_p` be finite. `ℂ_p` is an `F`-algebra through `F ≅ F' ⊆ ℚ̄_p ⊆ ℂ_p`, where `F'` is the
image of `F` under `phiF`. The map `κ : F̄ → ℂ_p` is the inverse of the embedding `embF : ℚ̄_p ≅ F̄`
(the embedding behind `gfToGqp`) followed by `ℚ̄_p ⊆ ℂ_p`. Since `[pⁿ]` is a finite morphism, every
`ℂ_p`-point of `A[pⁿ]` comes from `F̄`, so `P ↦ P ∘ Spec κ` identifies `T_p(A(F̄))` with
`T_p(A(ℂ_p))`. An element `σ ∈ G_F` acts on `ℂ_p` through `gfToGqp` and `cpAct`, the continuous
automorphism whose restriction `oAct` to `𝓞_ℂ_p` defines `bdrAct`; `κ` intertwines this action with
the action of `σ` on `F̄`, so the identification is `G_F`-equivariant.
-/

namespace DeRhamScholze.TatePrints

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- `ℂ_p` as an `F`-algebra: `F ≅ F' = fieldF p F ⊆ ℚ̄_p ⊆ ℂ_p`, through `phiF`. -/
@[instance_reducible] def cpAlgF : Algebra F ℂ_[p] :=
  ((algebraMap (PadicAlgCl p) ℂ_[p]).comp (phiF p F).toRingHom).toAlgebra

attribute [local instance low] cpAlgF

theorem cpAlgF_algebraMap (y : F) : algebraMap F ℂ_[p] y = iotaCp p F (equivFieldF p F y) := rfl

/-- `κ : F̄ → ℂ_p`: the inverse of `embF` (the embedding behind `gfToGqp`), then `ℚ̄_p ⊆ ℂ_p`. -/
def fbarToCp : AlgebraicClosure F →ₐ[F] ℂ_[p] :=
  { (algebraMap (PadicAlgCl p) ℂ_[p]).comp (embFEquiv p F).symm.toRingHom with
    commutes' := fun _ => rfl }

theorem fbarToCp_embF (x : PadicAlgCl p) : fbarToCp p F (embF p F x) = (x : ℂ_[p]) := by
  show algebraMap (PadicAlgCl p) ℂ_[p] ((embFEquiv p F).symm (embFEquiv p F x)) = _
  rw [RingEquiv.symm_apply_apply, PadicComplex.coe_eq]

theorem fbarToCp_galF (σ : Field.absoluteGaloisGroup F) (y : AlgebraicClosure F) :
    fbarToCp p F (galF F σ y) = cpAct p (gfToGqp p F σ) (fbarToCp p F y) := by
  obtain ⟨x, rfl⟩ := (embFEquiv p F).surjective y
  rw [embFEquiv_apply, ← embF_gfToGqp, fbarToCp_embF, fbarToCp_embF, cpAct_coe]

/-- `σ ∈ G_F` acting on `ℂ_p` by `cpAct (gfToGqp σ)`, as an `F`-algebra automorphism. -/
def cpGalF (σ : Field.absoluteGaloisGroup F) : ℂ_[p] ≃ₐ[F] ℂ_[p] where
  toFun := cpAct p (gfToGqp p F σ)
  invFun := cpAct p (gfToGqp p F σ)⁻¹
  left_inv := cpAct_inv_apply p (gfToGqp p F σ)
  right_inv z := by simpa using cpAct_inv_apply p (gfToGqp p F σ)⁻¹ z
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' r := by
    show cpAct p (gfToGqp p F σ) (iotaCp p F (equivFieldF p F r)) = iotaCp p F (equivFieldF p F r)
    exact DeRhamPrint.Direct.cpAct_iotaCp_gf p F σ _

theorem cpGalF_apply (σ : Field.absoluteGaloisGroup F) (z : ℂ_[p]) :
    cpGalF p F σ z = cpAct p (gfToGqp p F σ) z := rfl

theorem coe_oAct_gfToGqp (σ : Field.absoluteGaloisGroup F) (z : 𝓞_ℂ_[p]) :
    ((oAct p (gfToGqp p F σ) z : 𝓞_ℂ_[p]) : ℂ_[p]) = cpGalF p F σ (z : ℂ_[p]) := rfl

end

end DeRhamScholze.TatePrints

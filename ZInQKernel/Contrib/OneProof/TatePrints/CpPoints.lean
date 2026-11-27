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

/-- `A(F̄) → A(ℂ_p)`, `P ↦ P ∘ Spec κ`. -/
def ptFbarToCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    A.Pt (AlgebraicClosure F) →* A.Pt ℂ_[p] :=
  ZInQ.Contrib.AbVarBC.extPt (DeRhamPrint.toKer A) (fbarToCp p F)

theorem ptFbarToCp_injective (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    Function.Injective (ptFbarToCp p F A) :=
  ZInQ.Contrib.AbVarBC.extPt_injective (DeRhamPrint.toKer A) (fbarToCp p F)

theorem ptFbarToCp_galAct (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F)
    (σ : Field.absoluteGaloisGroup F) (P : A.Pt (AlgebraicClosure F)) :
    ptFbarToCp p F A (A.galAct σ P) = A.galAct (cpGalF p F σ) (ptFbarToCp p F A P) :=
  ZInQ.Contrib.AbVarBC.extPt_galAct (DeRhamPrint.toKer A) (fbarToCp p F) σ (cpGalF p F σ)
    (fun y => fbarToCp_galF p F σ y) P

theorem ptFbarToCp_torsion (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (n : ℕ) (q : A.Pt ℂ_[p])
    (hq : q ^ (p ^ n) = 1) : ∃ P, ptFbarToCp p F A P = q := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective
  have h : (((p ^ n : ℕ)) : ℤ) ≠ 0 := by
    exact_mod_cast (pow_pos (Fact.out : p.Prime).pos n).ne'
  exact T5Torsion.exists_extPt_eq (DeRhamPrint.toKer A) (fbarToCp p F) (p ^ n)
    (ZInQ.Contrib.AbVarBC.mulIsogeny F (DeRhamPrint.toKer A) _ h).1 q hq

theorem ptFbarToCp_tate_bijective (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    Function.Bijective
      (ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p) (MonoidHom.toAdditive (ptFbarToCp p F A))) :=
  ZInQ.Contrib.AbVarBC.tate_map_bijective_of_torsion _ (ptFbarToCp_injective p F A)
    fun n q hq => ptFbarToCp_torsion p F A n (Additive.toMul q) hq

theorem ptFbarToCp_tate_galT (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F)
    (σ : Field.absoluteGaloisGroup F) (x : A.T p) :
    ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p) (MonoidHom.toAdditive (ptFbarToCp p F A))
        (A.galT (ℓ := p) σ x) =
      ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p)
          (MonoidHom.toAdditive (A.galAct (cpGalF p F σ)))
        (ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p)
          (MonoidHom.toAdditive (ptFbarToCp p F A)) x) := by
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (ptFbarToCp_galAct p F A σ (Additive.toMul (x.1 n)))

/-- `T_p` from `F̄`-points equals `T_p` from `ℂ_p`-points, `G_F`-equivariantly, for the actions
the row uses. -/
theorem colmezTateFbarCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    -- (a) the `F`-structure of `ℂ_p` is `F ≅ F' ⊆ ℚ̄_p ⊆ ℂ_p`
    (∀ y : F, algebraMap F ℂ_[p] y = iotaCp p F (equivFieldF p F y)) ∧
    -- (b) `κ ∘ embF` is the inclusion `ℚ̄_p ⊆ ℂ_p`
    (∀ x : PadicAlgCl p, fbarToCp p F (embF p F x) = (x : ℂ_[p])) ∧
    -- (c) `κ ∘ σ = cpAct (gfToGqp σ) ∘ κ`
    (∀ (σ : Field.absoluteGaloisGroup F) (y : AlgebraicClosure F),
      fbarToCp p F (galF F σ y) = cpAct p (gfToGqp p F σ) (fbarToCp p F y)) ∧
    -- (d) on `𝓞_ℂ_p`, `cpGalF σ` is `oAct (gfToGqp σ)`, from which `bdrAct (gfToGqp σ)` is built
    (∀ (σ : Field.absoluteGaloisGroup F) (z : 𝓞_ℂ_[p]),
      ((oAct p (gfToGqp p F σ) z : 𝓞_ℂ_[p]) : ℂ_[p]) = cpGalF p F σ (z : ℂ_[p])) ∧
    -- (e) `G_F`-equivariance on points
    (∀ (σ : Field.absoluteGaloisGroup F) (P : A.Pt (AlgebraicClosure F)),
      ptFbarToCp p F A (A.galAct σ P) = A.galAct (cpGalF p F σ) (ptFbarToCp p F A P)) ∧
    -- (f) injective
    Function.Injective (ptFbarToCp p F A) ∧
    -- (g) onto the `pⁿ`-torsion, for every `n`
    (∀ (n : ℕ) (q : A.Pt ℂ_[p]), q ^ (p ^ n) = 1 → ∃ P, ptFbarToCp p F A P = q) ∧
    -- (h) bijective from the row's `A.T p` to `T_p(A(ℂ_p))`
    Function.Bijective
      (ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p) (MonoidHom.toAdditive (ptFbarToCp p F A))) ∧
    -- (i) `G_F`-equivariant on `T_p`
    (∀ (σ : Field.absoluteGaloisGroup F) (x : A.T p),
      ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p) (MonoidHom.toAdditive (ptFbarToCp p F A))
          (A.galT (ℓ := p) σ x) =
        ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p)
            (MonoidHom.toAdditive (A.galAct (cpGalF p F σ)))
          (ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p)
            (MonoidHom.toAdditive (ptFbarToCp p F A)) x)) :=
  ⟨cpAlgF_algebraMap p F, fbarToCp_embF p F, fbarToCp_galF p F, coe_oAct_gfToGqp p F,
    ptFbarToCp_galAct p F A, ptFbarToCp_injective p F A, ptFbarToCp_torsion p F A,
    ptFbarToCp_tate_bijective p F A, ptFbarToCp_tate_galT p F A⟩

/-- The `V_p` form, stated against the row's `A.galRep p`. -/
theorem colmezVpFbarCp (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    ∃ Ψ : A.V p ≃ₗ[ℚ_[p]]
        ℚ_[p] ⊗[ℤ_[p]] ZInQ.Contrib.G9.PkgI4.I3.Tate.T p (Additive (A.Pt ℂ_[p])),
      (∀ t : A.T p, Ψ ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] t) =
        (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]]
          ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p) (MonoidHom.toAdditive (ptFbarToCp p F A)) t) ∧
      ∀ (σ : Field.absoluteGaloisGroup F) (v : A.V p),
        Ψ (A.galRep p σ v) =
          (ZInQ.Contrib.G9.PkgI4.I3.Tate.map (ℓ := p)
            (MonoidHom.toAdditive (A.galAct (cpGalF p F σ)))).baseChange ℚ_[p] (Ψ v) := by
  let e := LinearEquiv.ofBijective _ (ptFbarToCp_tate_bijective p F A)
  refine ⟨e.baseChange ℤ_[p] ℚ_[p] _ _, fun t => ?_, fun σ v => ?_⟩
  · rw [LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
  · induction v using TensorProduct.inductionOn with
    | tmul a t =>
      change e.baseChange ℤ_[p] ℚ_[p] _ _ ((A.galT (ℓ := p) σ).baseChange ℚ_[p] (a ⊗ₜ t)) = _
      rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LinearMap.baseChange_tmul, LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply,
        ptFbarToCp_tate_galT p F A σ t]
    | add v₁ v₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]

end

end DeRhamScholze.TatePrints

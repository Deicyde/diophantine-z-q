import ZInQKernel.Contrib.OneProof.ColmezTiltIso.TpShape
import ZInQKernel.Contrib.OneProof.ColmezTorsionIso.Row

/-!
# The row `colmez1992DeRhamAbVar` on `T_p`, as printed

Colmez, Math. Ann. 292 (1992), Théorème 5.2 (ii), p. 639: "L'application périodes p-adique
(ω,u) → ∫_u ω de H¹_dR(X) × T_p(X) dans B⁺_dR [...] est non-dégénérée quand on étend les scalaires
à B_dR."

`Colmez1992DeRhamAbVarTp` is the row `Colmez1992DeRhamAbVarCp` (`T_p` built from the
`ℂ_p`-points) with the pairing stated on `T_p(X)` itself: `P ω : T_p →ₗ[ℤ_p] B_dR`, and
non-degeneracy on `B_dR ⊗_{ℤ_p} T_p`. `colmez1992DeRhamAbVarTp_iff_cp` proves it equivalent to the
`V_p` form (`ColmezTiltIso.Tp.shapeT_iff_shapeV`), and `colmez1992DeRhamAbVar_iff_tp` to the row as
stated.
-/

namespace DeRhamScholze.TatePrints.ColmezTp

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open ZInQ.Contrib.ColmezTorsionIso (TCp galTCp)
open ZInQ.Contrib.ColmezTiltIso.Tp (shapeT_iff_shapeV)
open scoped TensorProduct ZInQ.Contrib.ColmezTiltIso.Tp

/- `ℂ_p` is an `F`-algebra through `F → ℚ̄_p ⊂ ℂ_p`, as in `ColmezTorsionIso/Basic.lean`; the
group structure on `A(ℂ_p)`, hence the module structure on `TCp`, uses it. -/
attribute [local instance] ZInQ.Contrib.ColmezTorsionIso.algCp

/-- **Row R1 on `T_p`** (Colmez, Théorème 5.2 (i)-(ii), p. 639): the statement of
`Colmez1992DeRhamAbVarCp` with `P ω` a `ℤ_p`-linear map on `T_p(X) = lim A(ℂ_p)[pⁿ]` (`TCp`),
`G_F` acting through `galTCp`, and non-degeneracy after extending scalars from `ℤ_p` to `B_dR`
(`B_dR` a `ℤ_p`-algebra through `ℤ_p ⊂ ℚ_p`). -/
def Colmez1992DeRhamAbVarTp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (H : Type) (P : H → (TCp p A →ₗ[ℤ_[p]] BdR p)),
      (∀ ω u, P ω u ∈ filB p 0) ∧
      (∀ ω (σ : Field.absoluteGaloisGroup F) u,
        P ω (galTCp p A σ u) = bdrAct p (gfToGqp p F σ) (P ω u)) ∧
      (∀ x : BdR p ⊗[ℤ_[p]] TCp p A, (∀ ω, (P ω).liftBaseChange (BdR p) x = 0) → x = 0)

/-- **The `T_p` form and the `V_p` form of the row (on `ℂ_p`-points) are equivalent.** -/
theorem colmez1992DeRhamAbVarTp_iff_cp :
    Colmez1992DeRhamAbVarTp ↔ ColmezCp.Colmez1992DeRhamAbVarCp := by
  constructor
  · intro h p _ F _ _ _ A
    exact (shapeT_iff_shapeV (filB p 0) (galTCp p A)).1 (h p F A)
  · intro h p _ F _ _ _ A
    exact (shapeT_iff_shapeV (filB p 0) (galTCp p A)).2 (h p F A)

/-- **The row as stated is equivalent to its `T_p` form on `ℂ_p`-points.** -/
theorem colmez1992DeRhamAbVar_iff_tp : Colmez1992DeRhamAbVar ↔ Colmez1992DeRhamAbVarTp :=
  ColmezCp.colmez1992DeRhamAbVar_iff_cp.trans colmez1992DeRhamAbVarTp_iff_cp.symm

theorem colmez1992DeRhamAbVar_of_tp (h : Colmez1992DeRhamAbVarTp) : Colmez1992DeRhamAbVar :=
  colmez1992DeRhamAbVar_iff_tp.2 h

end DeRhamScholze.TatePrints.ColmezTp

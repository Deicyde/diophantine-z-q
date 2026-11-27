import ZInQKernel.Contrib.OneProof.ColmezTiltIso.Algebra
import ZInQKernel.Contrib.OneProof.ColmezTiltIso.RowTp

/-!
# The Colmez row over Colmez's own `B_dR`

`Colmez1992DeRhamAbVarPrinted` is the row `Colmez1992DeRhamAbVarTp` with every ring of the print in
Colmez's own construction: values in Colmez's `B⁺_dR = lim← W(R)[p^{-1}]/(Ker θ)^n`
(`ColmezBdRPlus`), the pairing into its fraction field `B_dR` (Colmez, p. 632: "Notons B_dR le corps
des fractions de B⁺_dR"), the Galois action `colmezBdRAct` built from the componentwise action on
`R`, and non-degeneracy after extending scalars from `ℤ_p` to that `B_dR`.

* `colmezBdREquiv_mem_filB_zero_iff`: `colmezBdREquiv` carries "comes from Colmez's `B⁺_dR`" to the
  tree's `filB p 0`.
* `colmez1992DeRhamAbVarPrinted_iff_tp`: the printed-ring row is equivalent to
  `Colmez1992DeRhamAbVarTp`, through the `ℤ_p`-algebra isomorphism `colmezBdRAlgEquiv`, the
  intertwining `colmezBdREquiv_act` and the lemma above; `colmez1992DeRhamAbVar_iff_printed`: and so
  to the row as stated.
-/

namespace DeRhamScholze.TatePrints.ColmezPrinted

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open ZInQ.Contrib.ColmezTorsionIso (TCp galTCp)
open ZInQ.Contrib.ColmezTiltIso
open scoped TensorProduct ZInQ.Contrib.ColmezTiltIso.Tp ZInQ.Contrib.ColmezTiltIso.Printed

/- `ℂ_p` is an `F`-algebra through `F → ℚ̄_p ⊂ ℂ_p`, as in `ColmezTorsionIso/Basic.lean`; the
group structure on `A(ℂ_p)`, hence the module structure on `TCp`, uses it. -/
attribute [local instance] ZInQ.Contrib.ColmezTorsionIso.algCp

/-- **`filB p 0` is Colmez's `B⁺_dR`**: `colmezBdREquiv p y ∈ Fil⁰ B_dR` iff `y` comes from
Colmez's `B⁺_dR`. -/
theorem colmezBdREquiv_mem_filB_zero_iff (p : ℕ) [Fact p.Prime]
    (y : FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p)) :
    colmezBdREquiv p y ∈ filB p 0 ↔
      ∃ b : ColmezBdRPlus 𝓞_ℂ_[p] p, algebraMap _ _ b = y := by
  constructor
  · rintro ⟨b, -, hb⟩
    refine ⟨colmezBdRPlusEquiv.symm b, (colmezBdREquiv p).injective ?_⟩
    rw [colmezBdREquiv_algebraMap, RingEquiv.apply_symm_apply]
    exact hb
  · rintro ⟨b, rfl⟩
    refine ⟨colmezBdRPlusEquiv b, ?_, ?_⟩
    · rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · rw [colmezBdREquiv_algebraMap]
      rfl

/-- **Row R1 over Colmez's own rings** (Colmez, Théorème 5.2 (i)-(ii), p. 639): `T_p(X)` from
`X(ℂ_p)` (`TCp`), the pairing `P ω : T_p(X) →ₗ[ℤ_p] B_dR` with `B_dR` the fraction field of Colmez's
`B⁺_dR` (`ColmezBdRPlus`), values in `B⁺_dR`, Galois compatibility for Colmez's action
`colmezBdRAct`, and non-degeneracy after extending scalars from `ℤ_p` to `B_dR` (`ℤ_p = W(F_p)`
acting through `W(R)`). Same weakenings as `Colmez1992DeRhamAbVarCp`: `H¹_dR(X)` is an existential
type, bilinearity in `ω`, the `Fil¹` clause and (iii) are dropped. -/
def Colmez1992DeRhamAbVarPrinted : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (H : Type) (P : H → (TCp p A →ₗ[ℤ_[p]] FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p))),
      (∀ ω u, ∃ b : ColmezBdRPlus 𝓞_ℂ_[p] p, algebraMap _ _ b = P ω u) ∧
      (∀ ω (σ : Field.absoluteGaloisGroup F) u,
        P ω (galTCp p A σ u) = colmezBdRAct p (gfToGqp p F σ) (P ω u)) ∧
      (∀ x : FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p) ⊗[ℤ_[p]] TCp p A,
        (∀ ω, (P ω).liftBaseChange (FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p)) x = 0) → x = 0)

/-- **The row over Colmez's rings is equivalent to `Colmez1992DeRhamAbVarTp`.** -/
theorem colmez1992DeRhamAbVarPrinted_iff_tp :
    Colmez1992DeRhamAbVarPrinted ↔ ColmezTp.Colmez1992DeRhamAbVarTp := by
  constructor
  · intro h p _ F _ _ _ A
    exact (shapeB_iff p (colmezBdRAlgEquiv p)
      (Q := fun y => ∃ b : ColmezBdRPlus 𝓞_ℂ_[p] p, algebraMap _ _ b = y)
      (Q' := fun x => x ∈ filB p 0) (fun y => colmezBdREquiv_mem_filB_zero_iff p y)
      (act := fun σ => colmezBdRAct p (gfToGqp p F σ))
      (act' := fun σ => bdrAct p (gfToGqp p F σ)) (fun σ y => colmezBdREquiv_act p _ y)
      (galTCp p A)).1 (h p F A)
  · intro h p _ F _ _ _ A
    exact (shapeB_iff p (colmezBdRAlgEquiv p)
      (Q := fun y => ∃ b : ColmezBdRPlus 𝓞_ℂ_[p] p, algebraMap _ _ b = y)
      (Q' := fun x => x ∈ filB p 0) (fun y => colmezBdREquiv_mem_filB_zero_iff p y)
      (act := fun σ => colmezBdRAct p (gfToGqp p F σ))
      (act' := fun σ => bdrAct p (gfToGqp p F σ)) (fun σ y => colmezBdREquiv_act p _ y)
      (galTCp p A)).2 (h p F A)

/-- **The row as stated is equivalent to the row over Colmez's own rings.** -/
theorem colmez1992DeRhamAbVar_iff_printed :
    Colmez1992DeRhamAbVar ↔ Colmez1992DeRhamAbVarPrinted :=
  ColmezTp.colmez1992DeRhamAbVar_iff_tp.trans colmez1992DeRhamAbVarPrinted_iff_tp.symm

theorem colmez1992DeRhamAbVar_of_printed (h : Colmez1992DeRhamAbVarPrinted) :
    Colmez1992DeRhamAbVar :=
  colmez1992DeRhamAbVar_iff_printed.2 h

end DeRhamScholze.TatePrints.ColmezPrinted

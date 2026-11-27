import ZInQKernel.Contrib.OneProof.TatePrints.Rows
import ZInQKernel.Contrib.OneProof.ColmezTorsionIso.Shape

/-!
# The row `colmez1992DeRhamAbVar` in Colmez's own terms

The row `DeRhamScholze.TatePrints.Colmez1992DeRhamAbVar` builds `T_p(A)` from the `F̄`-points of `A`
(`G9/I4Layer.lean`, `AbVar.T`); Colmez builds `T_p(X)` from `X(C_p)`. Here `Colmez1992DeRhamAbVarCp`
is the row with `T_p` built from the `ℂ_p`-points, and `colmez1992DeRhamAbVar_iff_cp` proves the two
rows equivalent through the `G_F`-equivariant isomorphism `ColmezTorsionIso.vCp`, which comes from
`A[pⁿ](F̄) ≅ A[pⁿ](ℂ_p)` (`ColmezTorsionIso.extCp_injective`, `extCp_surj_torsion`, `extCp_galAct`).
So the identification of the two Tate modules is a Lean theorem, and `colmez1992DeRhamAbVar_of_cp`
derives the row from the print in Colmez's own terms.
-/

namespace DeRhamScholze.TatePrints.ColmezCp

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open ZInQ.Contrib.ColmezTorsionIso (VCp galRepCp vCp vCp_galRep colmezShape_iff_cp)
open scoped TensorProduct

/-- **Row R1 in Colmez's own terms. Colmez, *Périodes p-adiques des variétés abéliennes*,
Math. Ann. 292 (1992), 629-644, Théorème 5.2 (i)-(ii), p. 639.**

Standing hypotheses, p. 629: "soit X une variété abélienne définie sur une extension finie K de
Q_p, et 𝒳 un modèle de X sur les entiers de K"; p. 638: "Dans la suite de cette section, X sera
une variété abélienne, 𝒳 un modèle propre de X sur O_K. [...] Par construction, 𝒳(O_{C_p})
s'identifie à X(C_p)"; p. 639: "Soit u=(…,u_n,…), où u_n ∈ 𝒳(O_{C_p}), un élément du module de
Tate T_p(X) de X." No reduction hypothesis. `B_dR` is Fontaine's (§2, p. 632).

Print, p. 639: "(ii) L'application périodes p-adique (ω,u) → ∫_u ω de H¹_dR(X) × T_p(X) dans
B⁺_dR ainsi définie est bilinéaire, commute à l'action de Galois [i.e. g(∫_u ω) = ∫_{g(u)} ω si
g ∈ Gal(K̄/K)], respecte les filtrations [...] et est non-dégénérée quand on étend les scalaires
à B_dR."

Lean form: the statement of `Colmez1992DeRhamAbVar` word for word (same weakenings: `H¹_dR(X)` an
existential type, bilinearity in `ω`, the `Fil¹` clause and (iii) dropped), except that `T_p(X)` is
built as in the print, from the `C_p`-points: `VCp p A = ℚ_p ⊗ lim A(ℂ_p)[pⁿ]`, and `g ∈ G_F` acts
on coordinates through its continuous action on `ℂ_p` (`galRepCp`, `g ↦ cpAct (gfToGqp g)`).
Colmez's `K` is `F` and his `X` is `A`; `ℂ_p` is an `F`-algebra through `F ≅ F' ⊆ ℚ̄_p ⊂ ℂ_p`, the
embedding behind `gfToGqp` (the model step reduces to `ColmezProperModel.ProperModelExists`,
proposed for a ruling by Jack or the maintainer: `ColmezTorsionIso/Basic.lean`). -/
def Colmez1992DeRhamAbVarCp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (H : Type) (P : H → (VCp p A →ₗ[ℚ_[p]] BdR p)),
      (∀ ω u, P ω u ∈ filB p 0) ∧
      (∀ ω (σ : Field.absoluteGaloisGroup F) u,
        P ω (galRepCp p A σ u) = bdrAct p (gfToGqp p F σ) (P ω u)) ∧
      (∀ x : BdR p ⊗[ℚ_[p]] VCp p A, (∀ ω, (P ω).liftBaseChange (BdR p) x = 0) → x = 0)

/-- **The identification of the `F̄`-points with the `ℂ_p`-points is a Lean theorem here:** the
row as stated (Tate module of the `F̄`-points) is equivalent to the row in Colmez's terms (Tate
module of the `ℂ_p`-points), through the `G_F`-equivariant isomorphism
`vCp : V_p(A) ≃ V_p(A_{ℂ_p})` (from `extCp_injective`, `extCp_surj_torsion`, `extCp_galAct`). -/
theorem colmez1992DeRhamAbVar_iff_cp : Colmez1992DeRhamAbVar ↔ Colmez1992DeRhamAbVarCp := by
  constructor
  · intro h p _ F _ _ _ A
    exact (colmezShape_iff_cp (fun b => b ∈ filB p 0) A).1 (h p F A)
  · intro h p _ F _ _ _ A
    exact (colmezShape_iff_cp (fun b => b ∈ filB p 0) A).2 (h p F A)

theorem colmez1992DeRhamAbVarCp_of_row (h : Colmez1992DeRhamAbVar) : Colmez1992DeRhamAbVarCp :=
  colmez1992DeRhamAbVar_iff_cp.1 h

theorem colmez1992DeRhamAbVar_of_cp (h : Colmez1992DeRhamAbVarCp) : Colmez1992DeRhamAbVar :=
  colmez1992DeRhamAbVar_iff_cp.2 h

end DeRhamScholze.TatePrints.ColmezCp

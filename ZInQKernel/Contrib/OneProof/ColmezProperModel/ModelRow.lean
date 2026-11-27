import ZInQKernel.Contrib.OneProof.ColmezProperModel.ModelTate
import ZInQKernel.Contrib.OneProof.ColmezTiltIso.RowPrinted

/-!
# The Colmez row with `T_p(X) = lim 𝒳(O_{C_p})[pⁿ]`

`Colmez1992DeRhamAbVarModel` is `Colmez1992DeRhamAbVarPrinted` (`ColmezTiltIso/RowPrinted.lean`)
with `T_p(X)` built as Colmez builds it (p. 639, "u=(…,u_n,…), où u_n ∈ 𝒳(O_{C_p})"), from the
points of a proper model `𝒳` of `A` over `O_F` (`TModel`, `galTModel`, `ModelTate.lean`), for every
such model.

* `colmez1992DeRhamAbVarModel_of_printed`: the printed row implies the model row, for every proper
  model (transport along `tModelEquiv`, `shape_transport`).
* `colmez1992DeRhamAbVarPrinted_of_model`: given `ProperModelExists`, the model row implies the
  printed row.
* `colmez1992DeRhamAbVar_iff_model`: given `ProperModelExists`, the row as stated is equivalent to
  the model row.
-/

namespace ZInQ.Contrib.ColmezProperModel

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open ZInQ.Contrib.ColmezTorsionIso (TCp galTCp)
open ZInQ.Contrib.ColmezTiltIso
open scoped TensorProduct ZInQ.Contrib.ColmezTiltIso.Tp ZInQ.Contrib.ColmezTiltIso.Printed

attribute [local instance] ZInQ.Contrib.ColmezTorsionIso.algCp

/-- **Row R1 with `T_p(X)` from a proper model** (Colmez, Théorème 5.2 (i)-(ii), p. 639, with the
standing hypothesis of p. 638): for every proper model `π : 𝒳 ⟶ Spec O_F` of `A` with generic
fibre `A`, the printed row holds with `T_p(X) = lim 𝒳(O_{C_p})[pⁿ]` and its geometric `G_F`-action.
Same weakenings as `Colmez1992DeRhamAbVarPrinted`. -/
def Colmez1992DeRhamAbVarModel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (𝒳 : Scheme)
    (π : 𝒳 ⟶ Spec (CommRingCat.of (OF p F))) [IsProper π]
    (e : pullback π (Spec.map (CommRingCat.ofHom (algebraMap (OF p F) F))) ≅ A.X.left)
    (he : e.hom ≫ A.X.hom = pullback.snd _ _),
    ∃ (H : Type)
      (P : H → (TModel A π e he →ₗ[ℤ_[p]] FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p))),
      (∀ ω u, ∃ b : ColmezBdRPlus 𝓞_ℂ_[p] p, algebraMap _ _ b = P ω u) ∧
      (∀ ω (σ : Field.absoluteGaloisGroup F) u,
        P ω (galTModel A π e he σ u) = colmezBdRAct p (gfToGqp p F σ) (P ω u)) ∧
      (∀ x : FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p) ⊗[ℤ_[p]] TModel A π e he,
        (∀ ω, (P ω).liftBaseChange (FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p)) x = 0) → x = 0)

/-- **The printed row gives the row on `𝒳(O_{C_p})`, for every proper model.** -/
theorem colmez1992DeRhamAbVarModel_of_printed
    (h : DeRhamScholze.TatePrints.ColmezPrinted.Colmez1992DeRhamAbVarPrinted) :
    Colmez1992DeRhamAbVarModel := by
  intro p _ F _ _ _ A 𝒳 π _ e he
  exact (shape_transport (tModelEquiv A π e he) (galTModel A π e he) (galTCp p A)
    (tModelEquiv_gal A π e he)
    (fun y => ∃ b : ColmezBdRPlus 𝓞_ℂ_[p] p, algebraMap _ _ b = y)
    (fun σ => colmezBdRAct p (gfToGqp p F σ))).1 (h p F A)

/-- **Given a proper model, the row on `𝒳(O_{C_p})` gives the printed row.** -/
theorem colmez1992DeRhamAbVarPrinted_of_model (hm : ProperModelExists)
    (h : Colmez1992DeRhamAbVarModel) :
    DeRhamScholze.TatePrints.ColmezPrinted.Colmez1992DeRhamAbVarPrinted := by
  intro p _ F _ _ _ A
  obtain ⟨𝒳, π, hπ, e, he⟩ := hm p F A
  haveI := hπ
  exact (shape_transport (tModelEquiv A π e he) (galTModel A π e he) (galTCp p A)
    (tModelEquiv_gal A π e he)
    (fun y => ∃ b : ColmezBdRPlus 𝓞_ℂ_[p] p, algebraMap _ _ b = y)
    (fun σ => colmezBdRAct p (gfToGqp p F σ))).2 (h p F A 𝒳 π e he)

/-- **Given a proper model, the row as stated is the row on `𝒳(O_{C_p})`.** -/
theorem colmez1992DeRhamAbVar_iff_model (hm : ProperModelExists) :
    DeRhamScholze.TatePrints.Colmez1992DeRhamAbVar ↔ Colmez1992DeRhamAbVarModel :=
  DeRhamScholze.TatePrints.ColmezPrinted.colmez1992DeRhamAbVar_iff_printed.trans
    ⟨colmez1992DeRhamAbVarModel_of_printed, colmez1992DeRhamAbVarPrinted_of_model hm⟩

end ZInQ.Contrib.ColmezProperModel

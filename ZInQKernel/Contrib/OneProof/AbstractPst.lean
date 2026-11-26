import ZInQKernel.Contrib.OneProof.AbstractBst
import ZInQKernel.Contrib.OneProof.PstTransport

/-! # Potential semistability over the abstract `B_st`

Fontaine's definition (Brinon–Conrad, CMI notes, §5.2, pp. 67–68, and Thm 9.3.5, p. 148):
`V` is potentially semistable when, for some finite `K/ℚ_p`, `V|_{G_K}` is semistable:
`dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`, for the abstract `B_st = B_cris[X]`
with its Galois action. Over the tree's abstract model `PanBergerSplit.Bst` this is
`IsPstAbstract`, and it is exactly the tree's `IsPstF` over the image `BstFOf`
(`isPstAbstract_iff`), through the equivariant isomorphism `bstEquiv`.
-/

noncomputable section

namespace HDec.PkgI4.AbstractPeriods

open BergerBst FontaineSt BmaxOne Module
open PanBergerSplit (stAct)
open _root_.ZInQ.Contrib.G9.BdrKer.Cp (xi)

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- The Galois action on the abstract `B_st`, as `ℚ_p`-algebra maps. -/
def stAlgHom (σ : GQp p) : PanBergerSplit.Bst p →ₐ[ℚ_[p]] PanBergerSplit.Bst p :=
  { stAct p σ with commutes' := PanBergerSplit.stAct_algebraMap p σ }

theorem stAlgHom_apply (σ : GQp p) (x : PanBergerSplit.Bst p) : stAlgHom p σ x = stAct p σ x := rfl

/-- **Fontaine's potential semistability over the abstract `B_st`**, in the dimension form:
`dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V` for some finite `K/ℚ_p` inside `ℚ̄_p`. -/
def IsPstAbstract (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    finrank (actFixed p (stAlgHom p) K.fixingSubgroup)
        (actPeriods p (stAlgHom p) K.fixingSubgroup ρ) = finrank ℚ_[p] (Fin n → E)

/-- **The abstract and the image definitions of potential semistability agree.** -/
theorem isPstAbstract_iff (ρ : GQp p →* GL (Fin n) E) :
    IsPstAbstract p ρ ↔ IsPstF p (eps0_spec p) (xi p) (theta_xi' p) ρ := by
  unfold IsPstAbstract IsPstF IsAdmissible
  refine exists_congr fun K => and_congr_right fun _ => ?_
  rw [finrank_actPeriods_eq p (stAlgHom p) _ (bstEquiv p) (fun σ s => by
    rw [bstEquiv_apply, bstEquiv_apply, stAlgHom_apply, bstEmb_stAct]) K.fixingSubgroup ρ]

end HDec.PkgI4.AbstractPeriods

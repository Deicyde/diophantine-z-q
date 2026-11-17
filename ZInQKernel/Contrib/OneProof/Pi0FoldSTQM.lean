import ZInQKernel.Contrib.OneProof.STQM

/-! # pi0-fold: st-qbar's `STQM` from the weak row `R1R2fpRepW`

`GapST.cm_point` and `GapST.stQM_of` (STQM.lean, task st-qbar) take the row `HDec.LeafAdopt.R1R2fpRep` and discard
its last clause `R1pi0Props` (`X₆` geometrically connected). pi0-fold removes the two added leaves that produced that
clause, so the chain now carries the weak row `HDec.LeafAdopt.R1R2fpRepW` (LPrefix: `R1R2fpRep` without
`R1pi0Props`). This file restates the two theorems on the weak row; the proofs are st-qbar's, with the destructuring
pattern one conjunct shorter. The chain's `stQM` (TailX, `addedLeaves6_of_open7`) uses `stQM_ofW`.
(pi0-prune's scratch/pi0-prune/STQMW.lean compiled the same change.)
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

namespace GapST
open _root_.LeafQM _root_.LeafQM.AV

section Main

open MonoidalCategory CartesianMonoidalCategory MonObj
open HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck

/-- **A CM point of `Y₃(ℂ)` comes from `Y₃(ℚ̄)`** (`cm_point` with the weak row; pi0-fold): a level-3 QM surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]`
or `ℤ[√−6]` is isomorphic to the base change of a level-3 QM surface over `ℚ̄`. -/
theorem cm_pointW (hRep : HDec.LeafAdopt.R1R2fpRepW) (hconn : HDec.TSHecke.Y3Connected)
    (hAL : HDec.HeckeRest.ALFixedPoints) (hT : PkgI2.TorsionStructure.{0})
    (hU : ZInQ.LeafPush2.UniformizationExists) (hC : HDec.HomUnify.HomLatticeCorr)
    (Q : QML3 ℂ) (hcm : HasCM4 Q.q ∨ HasCM3 Q.q ∨ HasCM24 Q.q) :
    ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ Nonempty (Q.Iso Q') := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5⟩ := hRep
  haveI : IsProper Y.hom := h1.1
  haveI : SmoothOfRelativeDimension 1 Y.hom := h1.2.1
  haveI : ConnectedSpace Y.left := HDec.TSHecke.connectedSpace_of_R1fp hconn h1
  haveI : IrreducibleSpace Y.left := HDec.TSHecke.irreducibleSpace_of_connected Y.hom h1.1 h1.2.1
  -- a `ℚ̄`-point without CM
  obtain ⟨x, hx⟩ := hs.1 (OnePoint.some 1)
  obtain ⟨y₁, hy₁⟩ := hs.2 x
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : QML3 Qbar, Φ Qbar y₁ = M3.mk P₀ :=
    ⟨(Φ Qbar y₁).out, (Quotient.out_eq _).symm⟩
  have hΨ : Ψ x = Quotient.mk _ P₀.forget := by rw [← hy₁]; exact h6.2.2.2.2.2 y₁ P₀ hP₀
  obtain ⟨-, h4, h3, h24⟩ := h2 x x P₀.forget P₀.forget hΨ hΨ
  have n4 : ¬ HasCM4 P₀.q := fun h => by
    have := h4.1 h; rw [hx] at this; exact one_ne_zero (OnePoint.coe_injective this)
  have n3 : ¬ HasCM3 P₀.q := fun h => by
    have := h3.1 h; rw [hx] at this; exact OnePoint.coe_ne_infty _ this
  have n24 : ¬ HasCM24 P₀.q := fun h => by
    have := h24.1 h; rw [hx] at this
    have h' := OnePoint.coe_injective this
    norm_num at h'
  -- the automorphism fixing the point of `Q`
  have key : ∃ k : Fin 4, Nonempty (QMIso Q.q (Q.q.twist (HDec.LeafQM.AV.Pin.Exact.rep k))) ∧
      ¬ Nonempty (QMIso (P₀.q.twist (HDec.LeafQM.AV.Pin.Exact.rep k)) P₀.q) := by
    rcases twist_of_cm hT hU hC Q.surface Q.q hcm with ⟨-, hθ⟩ | ⟨-, hθ⟩ | ⟨-, hθ⟩
    · exact ⟨1, hθ, fun h => n4 ((hAL P₀.A P₀.surface P₀.q).1 h)⟩
    · exact ⟨2, hθ, fun h => n3 ((hAL P₀.A P₀.surface P₀.q).2.1 h)⟩
    · exact ⟨3, hθ, fun h => n24 ((hAL P₀.A P₀.surface P₀.q).2.2 h)⟩
  obtain ⟨k, ⟨θ⟩, hk⟩ := key
  obtain ⟨u, hu⟩ := fixed_class hT Q _ θ
  obtain ⟨gα, hgα⟩ := hh.1 (HDec.LeafQM.AV.Pin.Exact.rep k)
  obtain ⟨gu, hgu⟩ := hh.2 u
  set y := (Φ ℂ).symm (M3.mk Q) with hy
  have hyQ : Φ ℂ y = M3.mk Q := Equiv.apply_symm_apply _ _
  have hfix : y ≫ (gα.hom ≫ gu.hom) = y := by
    apply (Φ ℂ).injective
    rw [← Category.assoc, hgu, hgα, hyQ, ← hu]
  set s₀ := (Φ Qbar).symm (M3.mk P₀) with hs₀
  have hmove : s₀ ≫ (gα.hom ≫ gu.hom) ≠ s₀ := by
    intro heq
    have h' := congrArg (Φ Qbar) heq
    rw [← Category.assoc, hgu, hgα, hs₀, Equiv.apply_symm_apply, M3.twist_mk] at h'
    change M3.mk ((P₀.twist _).rightMul u) = M3.mk P₀ at h'
    obtain ⟨i⟩ := Quotient.exact h'
    exact hk ⟨⟨i.φ, i.ψ, i.left, i.right, i.equivariant⟩⟩
  obtain ⟨ιe, y₀, hy₀⟩ := exists_qbar_factor Y y _ hfix s₀ hmove
  obtain ⟨P, hP⟩ : ∃ P : QML3 Qbar, Φ Qbar y₀ = M3.mk P :=
    ⟨(Φ Qbar y₀).out, (Quotient.out_eq _).symm⟩
  obtain ⟨Q', hQ', hBC⟩ := h1.2.2.2.1 Qbar ℂ ιe.toRatAlgHom y₀ P hP
  rw [hy₀, hyQ] at hQ'
  exact ⟨ιe, P, Q', hBC, Quotient.exact hQ'⟩

end Main

section Final

open MonoidalCategory CartesianMonoidalCategory MonObj
open HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck

/-- **`STQM`, proved** (task st-qbar; `stQM_of` with the weak row, pi0-fold). A QM abelian surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]` or
`ℤ[√−6]` is isomorphic to `A₀ ×_{ℚ̄,ιe} ℂ` for an abelian variety `A₀/ℚ̄`.

Hypotheses, all already in the bundles or proved on the base:
* `hRep` — research field `r1r2`, the weak row `LeafAdopt.R1R2fpRepW` (pi0-fold);
* `hconn` — added field `y3Connected` (`TSHecke.Y3Connected`);
* `hAL` — `HeckeRest.ALFixedPoints`, proved in the chain as `(qmRows_of7 t l).2.1` (TailX);
* `hT` — `PkgI2.TorsionStructure` (T5; textbook `t5`, from `mumfordTorsionAlgClosed`);
* `hU` — `ZInQ.LeafPush2.UniformizationExists` (T35; textbook `t35`, from `uniformizationLeafAll`);
* `hC` — `ZInQ.HomUnify.HomLatticeCorr` (textbook `homLatticeCorr`, from `uniformizationLeafAll`,
  `gagaMorphism`). -/
theorem stQM_ofW (hRep : HDec.LeafAdopt.R1R2fpRepW) (hconn : HDec.TSHecke.Y3Connected)
    (hAL : HDec.HeckeRest.ALFixedPoints) (hT : _root_.PkgI2.TorsionStructure.{0})
    (hU : _root_.ZInQ.LeafPush2.UniformizationExists) (hC : _root_.ZInQ.HomUnify.HomLatticeCorr) :
    HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.STQM := by
  intro A q hA hcm
  obtain ⟨e⟩ := exists_level3 hT hA q
  obtain ⟨ιe, P, Q', hBC, ⟨i⟩⟩ :=
    cm_pointW hRep hconn hAL hT hU (HDec.HSyn.homLatticeCorr_ofK5 hC) ⟨A, hA, q, e⟩ hcm
  obtain ⟨θ, θ', h1, h2⟩ := bc_iso ιe P Q' hBC
  refine ⟨ιe, P.A, PkgI3.AbVar.Hom.mk' (θ'.hom ≫ i.ψ.hom), PkgI3.AbVar.Hom.mk' (i.φ.hom ≫ θ.hom),
    ?_, ?_⟩
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% i.right, h2]
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h1, i.left]

end Final

end GapST

#print axioms GapST.stQM_ofW

import ZInQKernel.Contrib.OneProof.Y3RepresentedFibres
import ZInQKernel.Contrib.OneProof.Y3CMPeriodValues
import ZInQKernel.Contrib.OneProof.STQM
import ZInQKernel.Contrib.OneProof.X6AtkinLehnerIdeal
import ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used

/-! # Descending the fixed points of level-three twists -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid HDec
open HDec.HSyn.G0Split.FibreQM HDec.HSyn.G0Split.FibreQM.PeriodGlue
open HDec.HSyn.G0Split.FibreQM.PeriodMapH
open HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck
open HDec.QMSplit.Moduli RayClassCFT Y3Fix Y3RouteA

namespace Y3P1j

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

private abbrev alRep : Fin 4 → O ≃+* O := HDec.LeafQM.AV.Pin.Exact.rep

/-- The three Atkin–Lehner fixed-point implications on complex QM surfaces. -/
def ComplexALFixedPoints : Prop :=
  ∀ (P : QML3 ℂ),
    (Nonempty (QMIso (P.q.twist (alRep 1)) P.q) → HasCM4 P.q) ∧
    (Nonempty (QMIso (P.q.twist (alRep 2)) P.q) → HasCM3 P.q) ∧
    (Nonempty (QMIso (P.q.twist (alRep 3)) P.q) → HasCM24 P.q)

/-- A complex point of a distinguished CM type is a fixed point of a nonidentity
algebraic automorphism of the fine-moduli curve. Its level structure and QM pair
therefore descend to the algebraic closure of ℚ. -/
theorem cm_point_of_z30 (hI : Y3FullThreeRepZ30) (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint)
    (hAL : ComplexALFixedPoints) (hA : CMAnalytic) (hH : PkgI1.QMHauptmodul)
    (hT : PkgI2.TorsionStructure.{0}) (hU : ZInQ.LeafPush2.UniformizationExists)
    (hC : HDec.HomUnify.HomLatticeCorr)
    (Q : QML3 ℂ) (hcm : HasCM4 Q.q ∨ HasCM3 Q.q ∨ HasCM24 Q.q) :
    ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
      IsBaseChangeOf ιe P Q' ∧ Nonempty (Q.Iso Q') := by
  obtain ⟨Y, 𝒜, hp, hs, hUniv⟩ := y3RepresentableQ_of_z30 hI
  obtain ⟨Φ, hΦ, hΦfib⟩ := Y3Audit.exists_fineModuliAt_of_rep hT hp hs hUniv
  obtain ⟨Ψ, hB, hUnits⟩ := Y3Hodge.deligneH_of_print hD Y Φ hΦ
  haveI : IsProper Y.hom := hp
  haveI : SmoothOfRelativeDimension 1 Y.hom := hs
  haveI : ConnectedSpace Y.left := DCY3Used.connected_of_body (body_of_H hB)
  haveI : IrreducibleSpace Y.left := HDec.TSHecke.irreducibleSpace_of_connected Y.hom hp hs
  have hN := Y3Audit.isLocallyNoetherian_of_smooth_Q Y hs
  obtain ⟨f, hf⟩ := qmHauptmodul_iff.mp hH
  obtain ⟨τ, hτ⟩ := hf.2.2.2.1 (OnePoint.some 1)
  have h1 : (1 : ShimuraCFT.BAQˣ) ∈ OhatU := ⟨OhatQ_one, by simpa using OhatQ_one⟩
  obtain ⟨P₀, _, hP₀⟩ := units_of_H hUnits 1 h1 τ
  obtain ⟨v4, v3, v24⟩ := cm_period_values hf hA P₀ τ hP₀
  have n4 : ¬ HasCM4 P₀.q := fun h => by
    have hv := OnePoint.coe_injective (hτ.symm.trans (v4 h))
    norm_num at hv
  have n3 : ¬ HasCM3 P₀.q := fun h => OnePoint.coe_ne_infty _ (hτ.symm.trans (v3 h))
  have n24 : ¬ HasCM24 P₀.q := fun h => by
    have hv := OnePoint.coe_injective (hτ.symm.trans (v24 h))
    norm_num at hv
  obtain ⟨k, ⟨θ⟩, hk⟩ : ∃ k : Fin 4,
      Nonempty (QMIso Q.q (Q.q.twist (alRep k))) ∧
      ¬ Nonempty (QMIso (P₀.q.twist (alRep k)) P₀.q) := by
    rcases GapST.twist_of_cm hT hU hC Q.surface Q.q hcm with ⟨_, hθ⟩ | ⟨_, hθ⟩ | ⟨_, hθ⟩
    · exact ⟨1, hθ, fun h => n4 ((hAL P₀).1 h)⟩
    · exact ⟨2, hθ, fun h => n3 ((hAL P₀).2.1 h)⟩
    · exact ⟨3, hθ, fun h => n24 ((hAL P₀).2.2 h)⟩
  obtain ⟨u, ⟨i⟩⟩ := exists_remarkPoint_iso (Q.twist (alRep k)) Q θ.symm
  let g := (twistMarkAut hUniv hN k u).asIso.hom
  have act {K : Type} [Field K] [Algebra ℚ K] (z : fieldPt K ⟶ Y) (P : QML3 K)
      (hz : Φ K z = M3.mk P) : Φ K (z ≫ g) = M3.mk (remarkPoint (P.twist (alRep k)) u) :=
    (hΦfib K _ _).mpr (isFibreOf_twistMarkAut hUniv hN k u ((hΦfib K z P).mp hz))
  let y := (Φ ℂ).symm (M3.mk Q)
  have hy : Φ ℂ y = M3.mk Q := Equiv.apply_symm_apply _ _
  have hfix : y ≫ g = y := by
    apply (Φ ℂ).injective
    rw [act y Q hy, hy]
    exact Quotient.sound ⟨i⟩
  have hne : g ≠ 𝟙 Y := by
    intro hg
    let s := (Φ ℂ).symm (M3.mk P₀)
    have hs : Φ ℂ s = M3.mk P₀ := Equiv.apply_symm_apply _ _
    have h := act s P₀ hs
    rw [hg, Category.comp_id, hs] at h
    obtain ⟨j⟩ := Quotient.exact h.symm
    exact hk ⟨⟨j.φ, j.ψ, j.left, j.right, j.equivariant⟩⟩
  obtain ⟨s, hmove⟩ : ∃ s : fieldPt Qbar ⟶ Y, s ≫ g ≠ s := by
    by_contra! hall
    apply hne
    apply X6ALIdeal.hom_ext_qbar hp hs
    intro s
    rw [Category.comp_id]
    exact hall s
  obtain ⟨ιe, y₀, hy₀⟩ := GapST.exists_qbar_factor Y y g hfix s hmove
  obtain ⟨P, hP⟩ : ∃ P : QML3 Qbar, Φ Qbar y₀ = M3.mk P :=
    ⟨(Φ Qbar y₀).out, (Quotient.out_eq _).symm⟩
  obtain ⟨Q', hQ', hBC⟩ := hΦ.2.2.1 Qbar ℂ ιe.toRatAlgHom y₀ P hP
  rw [hy₀, hy] at hQ'
  exact ⟨ιe, P, Q', hBC, Quotient.exact hQ'⟩

end Y3P1j

#print axioms Y3P1j.cm_point_of_z30

import ZInQKernel.OneProof.H.TailZ35

/-!
# pi0-prune (1/3): the row `R1R2fpRepW` (`R1R2fpRep` without `R1pi0Props`), its destructurers and producers

`HDec.LeafAdopt.R1R2fpRep` (LPrefix) ends with the clause `R1pi0Props X` (`X₆` geometrically connected). On the
single proof that clause is produced from the two fields `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure`
and read by nobody (triage2, probe `scratch/triage2/Pi0Use.lean`). This file defines

* `LeafAdopt.R1R2fpRepW`: `R1R2fpRep` without its last conjunct, with `R1R2fpRepW_of_rep : R1R2fpRep → R1R2fpRepW`;
* the destructurers (`R1R2fp_of_repW`, `r1rec_of_repW`, `r5fp_of_repW`, `pairsLift_of_repW`, ...) and the consumers
  of the row that are not bundle maps, copied verbatim from the chain with `R1R2fpRep` replaced by `R1R2fpRepW`
  (each copy names its source file and lines at base 43513d87);
* the producers: `r1r2fpRep_of_printedW`, which takes the base witness from González–Rotger's leaf
  (`GonzalezRotgerX6`) instead of Deligne's `π₀` with `GeomConnOfAlgClosure`.

No `sorry`; standard axioms only.
-/

set_option linter.all false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HDec.LeafAdopt

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **`R1R2fpRep` without its last conjunct `R1pi0Props X`** (pi0-prune). The clause `R1pi0Props X` (`X₆`
geometrically connected) is never read on the single proof (triage2, `scratch/triage2/Pi0Use.lean`). -/
def R1R2fpRepW : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6PropsIff X Ψ π₆ ∧
      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ

/-- The row `R1R2fpRep` implies its weak form. -/
theorem R1R2fpRepW_of_rep (h : R1R2fpRep) : R1R2fpRepW := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5⟩

/-- `R1R2fp_of_rep` (LPrefix 5228-5231) with the weak row; the proof is unchanged. -/
theorem R1R2fp_of_repW (h : R1R2fpRepW) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, r2X6Props_of_iff h2, cmExists_of_iff h2 hs.1, hr, hs, h5⟩

end HDec.LeafAdopt

/-! ## Copied from `ZInQKernel/OneProof/H/TailC.lean` (base 43513d87) -/

namespace HDec
set_option maxHeartbeats 1000000
attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
section G0A2_a80_fqm
noncomputable section
namespace HSyn
open scoped MatrixGroups ModularForm
namespace G0Split
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
namespace FibreQM
open _root_.ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt) -- op-dedupe
open Complex
-- pi0-prune: copied from TailC.lean:8447-8458
/-- **Main result from the decomposition's bundle form of the leaf (`LeafAdopt.R1R2fpRepW`,
proved).** -/
theorem fibreQMPeriod_main_repW (h : LeafAdopt.R1R2fpRepW) (hM : Pin.MobiusGlue)
    (hH : PkgI1.QMHauptmodul) (hE : UniformizationExistsT35) (hR11 : T11aRiemannEnd)
    (hCN : QMClassNumberOne)
    (hR : R1bFamily (ownY (LeafAdopt.R1R2fp_of_repW h)) (ownΦ (LeafAdopt.R1R2fp_of_repW h))
      (ownπ (LeafAdopt.R1R2fp_of_repW h)))
    (hG : PeriodMapGlue (ownY (LeafAdopt.R1R2fp_of_repW h)) (ownΦ (LeafAdopt.R1R2fp_of_repW h))
      (ownπ (LeafAdopt.R1R2fp_of_repW h)))
    (hHU : HauptmodulUnique) (hD : QMDenZeroCM3) (hCP : CPtsTransport) :
    ThetaPt.FibreQMPeriod :=
  fibreQMPeriod_main _ hM hH hE hR11 hCN hR hG hHU hD hCP

end FibreQM
end G0Split
end HSyn
end
end G0A2_a80_fqm
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailI.lean` (base 43513d87) -/

namespace HDec
set_option maxHeartbeats 1000000
attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
section G0A2_d90_fold3
noncomputable section
namespace HSyn
open CategoryTheory AlgebraicGeometry G0Split
-- pi0-prune: copied from TailI.lean:71-86
/-- **Proposition TS for every admissible cover** (prop-ts, prop-ts-glue 3d41b3d5, ts-kummer, kummer-comp,
ts-hecke, hecke-rest; part c80): prop-ts's `propTSAll_of_bundle_meet` with `KummerMeetGlue` proved
(kummer-comp), `SpecNonMeeting` proved (prop-ts-glue), T2 proved (leaf-fold), `MobiusGlue` from T5
(image-plane), and `CoverModelOfHecke` from hecke-rest's eight inputs: the leaf candidates `Y3Connected`
(R1conn), `QMAutCard`, `SerreRigidity3`, `ALFixedPoints`, the leaf T5, and the glue `ChartProper`,
`ChartQuasiFinite`, `HeckeVertWitness`. -/
-- (leaf-fold4) hecke-rest now proves ChartProper and ChartQuasiFinite; hP, hQ are unused here.
theorem propTSAll_of_pieces3W (hR : LeafAdopt.R1R2fpRepW) (h5 : PkgI2.TorsionStructure.{0})
    (hconn : TSHecke.Y3Connected) (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3)
    (hW : HeckeRest.ALFixedPoints) (hP : HeckeRestCurve.ChartProper)
    (hQ : HeckeRestCurve.ChartQuasiFinite) (hV : HeckeRestNV.HeckeVertWitness) :
    G0ModField.PropTSAll :=
  PropTSRed.propTSAll_of_bundle_meet t2_proved (LeafAdopt.R1R2fp_of_repW hR) KummerComp.kummerMeetGlue
    PropTSGlue.specNonMeeting (mobiusGlue_of_t5' h5)
    (HeckeRestAll.coverModelOfHecke_of_heckeRest hconn (LeafAdopt.R1R2fp_of_repW hR)
      (ObjBridge.torsionStructure_iff.mpr h5) hA hS hW hV)

end HSyn
end
end G0A2_d90_fold3
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailK.lean` (base 43513d87) -/

namespace HDec
set_option maxHeartbeats 1000000
attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
section G0A2_d95_fold4
noncomputable section
namespace HSyn
open CategoryTheory AlgebraicGeometry G0Split
-- pi0-prune: copied from TailK.lean:69-94
/-- **`PeriodMapGlue` at the leaf's own triple from leaves** (period-map's `periodMapGlue_own` with
period-glue's pieces, as in period-glue's `fibreQMPeriod_periodGlue`; part c90). Inputs: R1fp, R1hecke, R2fp
(the bundle `R1R2fpRepW`), T5 (`TorsionStructure`), `T11aRiemannHom` (from `HomLatticeCorr`), the leaf
candidate `CMDescends`; `AutOInnerFinite` and Skolem–Noether are kernel theorems. -/
theorem periodMapGlue_of_leaves4W (h : LeafAdopt.R1R2fpRepW) (hT : PkgI2.TorsionStructure.{0})
    (hC : HomUnify.HomLatticeCorr) (hD : G0Split.FibreQM.PeriodMapH.CMDescends) :
    G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_repW h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_repW h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_repW h)) :=
  have hHom := t11aRiemannHom_of_corr4 hC
  have hPT := G0Split.FibreQM.PeriodGlue.piTwistC_of _ _ _
    (G0Split.FibreQM.own_spec (LeafAdopt.R1R2fp_of_repW h)).1
    (G0Split.FibreQM.own_spec (LeafAdopt.R1R2fp_of_repW h)).2.2
    (G0Split.FibreQM.PeriodGlue.twistOrbitFinite_of' _ _
      (G0Split.FibreQM.own_spec (LeafAdopt.R1R2fp_of_repW h)).2.1
      (ObjBridge.torsionStructure_iff.mpr hT) autOInnerFinite_proved4)
    (G0Split.FibreQM.PeriodGlue.fibreTransferC_proof _ _)
  G0Split.FibreQM.PeriodMapH.periodMapGlue_own _
    G0Split.FibreQM.PeriodGlue.baseChangeClassUnique_proof hPT
    (G0Split.FibreQM.PeriodGlue.qmTwistLattice_of' hHom leafSkolemNoether_proved4)
    (G0Split.FibreQM.PeriodMapH.piCMC_of _ _ _
      (G0Split.FibreQM.own_spec (LeafAdopt.R1R2fp_of_repW h)).1
      (G0Split.FibreQM.own_spec (LeafAdopt.R1R2fp_of_repW h)).2.2
      G0Split.FibreQM.PeriodGlue.baseChangeClassUnique_proof hPT hD)
    (G0Split.FibreQM.PeriodMapH.cmFixedHasCM_of
      (G0Split.FibreQM.PeriodGlue.t11aRiemannEnd_of_hom hHom))

end HSyn
end
end G0A2_d95_fold4
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailN.lean` (base 43513d87) -/

namespace HDec
set_option maxHeartbeats 1000000
attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
section G0A2_e90_fold5
noncomputable section
namespace HSyn
open CategoryTheory AlgebraicGeometry
-- pi0-prune: copied from TailN.lean:33-42
/-- **`HeckeVertWitness` from leaves and one glue Prop** (model-glue's `ModelGlue.heckeVertWitness_of_curveBijIso`,
part e10, with `SmoothFibreReduced` the kernel's theorem `ZInQ.SmoothFibre.smoothFibreReduced`): the leaf
`ShimuraGoodReduction` (a smooth proper model of `Y₃` over `ℤ_(p)` for `p > 324`), R1fp/R1hecke/R2fp (the bundle
field `r1r2`), T5, the textbook leaf `CurveBijIso` and the glue `ModelCoordinateResidue` (the tame quotient
`𝒴/Γ' ≅ P¹_{ℤ_(p)}`). -/
theorem heckeVertWitness_of_leaves5W (hL : VertWitness.ShimuraGoodReduction) (h : LeafAdopt.R1R2fpRepW)
    (hT : PkgI2.TorsionStructure.{0}) (hD : ModelGlue.ModelCoordinateResidue)
    (hC : ModelGlue.CurveBijIso) : HeckeRestNV.HeckeVertWitness :=
  ModelGlue.heckeVertWitness_of_curveBijIso hL (LeafAdopt.R1R2fp_of_repW h)
    (ObjBridge.torsionStructure_iff.mpr hT) hD hC

end HSyn
end
end G0A2_e90_fold5
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailO.lean` (base 43513d87) -/

set_option linter.all false
namespace HDec.HSyn.G0Split.FibreQM.PeriodMapH
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM
namespace LeafQCheck
section Glue2
-- pi0-prune: copied from TailO.lean:1176-1299
/-- **The descended data** (glue, proved). -/
theorem descend_mainW (hST : STQM) (hR : ZInQ.LeafPush2.T11b_Rigidity) (hTD : TorsionDescends)
    (hRep : LeafAdopt.R1R2fpRepW) (Q : QML3 ℂ) (hcm : HasCM4 Q.q ∨ HasCM3 Q.q ∨ HasCM24 Q.q) :
    ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ)
      (κ : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End P.A),
      IsBaseChangeOf ιe P Q' ∧ Nonempty (QMIso Q.q Q'.q) ∧ ∀ a, κ (Q.q.iota a) = P.q.iota a := by
  obtain ⟨ιe, A₀, e, e', h1, h2⟩ := hST Q.A Q.q Q.surface hcm
  let β := RingEquiv.ofBijective (endBCe ιe A₀) (endBCe_bijective ιe A₀ hR)
  let κ : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End A₀ := β.symm.toRingHom.comp (conjE e e' h1 h2)
  have hβκ : ∀ f, endBCe ιe A₀ (κ f) = conjE e e' h1 h2 f := fun f => β.apply_symm_apply _
  have κinj : Function.Injective κ := β.symm.injective.comp (conjE_injective e e' h1 h2)
  let q₀ : QMStr A₀ := ⟨κ.comp Q.q.iota, κinj.comp Q.q.injective⟩
  have hdim : A₀.dim = 2 := by
    have := dim_eq_of_iso e e' h1 h2
    rw [← Q.surface, ← this]
    exact (@PkgI3.AbVar.dim_baseChange Qbar _ A₀ ℂ _ ιe.toAlgebra).symm
  -- the level structure
  let v : (bcC ιe A₀).Pt ℂ := Additive.toMul (Q.e.eta 1) ≫ e'.hom
  have hv3 : v ^ 3 = 1 := by
    have h30 : Q.e.eta 3 = 0 := (Q.e.ker 3).2 ⟨1, by rw [_root_.mul_one]⟩
    have h3 : (Additive.toMul (Q.e.eta 1)) ^ 3 = 1 := by
      rw [← toMul_nsmul, ← map_nsmul, nsmul_eq_mul, _root_.mul_one]
      push_cast
      rw [h30]; rfl
    change (IsMonHom.monoidHom e'.hom _ (Additive.toMul (Q.e.eta 1))) ^ 3 = 1
    rw [← map_pow, h3, map_one]
  obtain ⟨v₀, hv₀, huniq⟩ := hTD ιe A₀ v 3 (by norm_num) hv3
  let η₀ : LeafQM.O →+ Additive (A₀.Pt Qbar) :=
    { toFun := fun a => qmAct q₀ Qbar a (Additive.ofMul v₀)
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun a b => by rw [map_add]; rfl }
  have hη₀ : ∀ a, Additive.toMul (η₀ a) = v₀ ≫ (q₀.iota a).hom := fun a => rfl
  have lin : ∀ a b : LeafQM.O, η₀ (a * b) = qmAct q₀ Qbar a (η₀ b) := fun a b => by
    change qmAct q₀ Qbar (a * b) _ = _
    rw [map_mul]; rfl
  have ker : ∀ a : LeafQM.O, η₀ a = 0 ↔ ∃ b : LeafQM.O, a = 3 * b := by
    intro a
    have hw : v ≫ (endBCe ιe A₀ (q₀.iota a)).hom = Additive.toMul (Q.e.eta a) ≫ e'.hom := by
      rw [show q₀.iota a = κ (Q.q.iota a) from rfl, hβκ, conjE_hom]
      have hl := Q.e.linear a 1
      rw [_root_.mul_one] at hl
      have : Additive.toMul (Q.e.eta a) = Additive.toMul (Q.e.eta 1) ≫ (Q.q.iota a).hom := by
        rw [hl]; rfl
      rw [this]
      simp only [v, Category.assoc]
      rw [reassoc_of% h2]
    have hcorr := endBCe_corr ιe A₀ (q₀.iota a) hv₀
    constructor
    · intro h0
      have h0' : v₀ ≫ (q₀.iota a).hom = 1 := by rw [← hη₀, h0]; rfl
      have h1' : v ≫ (endBCe ιe A₀ (q₀.iota a)).hom = 1 :=
        ptC_ext ιe A₀ (by rw [hcorr, h0', one_corr])
      rw [hw] at h1'
      have h3 : Additive.toMul (Q.e.eta a) = 1 := by
        have := congrArg (· ≫ e.hom) h1'
        simp only [Category.assoc, h2, Category.comp_id] at this
        rw [this, MonObj.one_comp]
      exact (Q.e.ker a).1 h3
    · intro hb
      have h3 : Q.e.eta a = 0 := (Q.e.ker a).2 hb
      have h1' : v ≫ (endBCe ιe A₀ (q₀.iota a)).hom = 1 := by
        rw [hw, show Additive.toMul (Q.e.eta a) = 1 from congrArg Additive.toMul h3, MonObj.one_comp]
      obtain ⟨_, _, hu1⟩ := hTD ιe A₀ 1 1 one_pos (one_pow _)
      have e1 := hu1 (v₀ ≫ (q₀.iota a).hom) (by rw [← h1']; exact hcorr)
      have e2 := hu1 1 (one_corr ιe A₀)
      have : Additive.toMul (η₀ a) = 1 := by rw [hη₀, e1, ← e2]
      exact congrArg Additive.ofMul this
  let P : QML3 Qbar := ⟨A₀, hdim, q₀, ⟨η₀, lin, ker⟩⟩
  -- the base change from R1fp's naturality
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, hR1, -⟩ := hRep
  obtain ⟨Q', -, hBC⟩ := hR1.2.2.2.1 Qbar ℂ ιe.toRatAlgHom ((Φ Qbar).symm (M3.mk P)) P (by simp)
  have hBC' : IsBaseChangeOf ιe P Q' := hBC
  refine ⟨ιe, P, Q', κ, hBC', ?_, fun a => rfl⟩
  obtain ⟨g', hg', hι', hl'⟩ := hBC'
  -- comparison `Q'.A ≅ A₀ ×_{ℚ̄} ℂ`
  let θ : Q'.A.X ⟶ (bcC ιe A₀).X :=
    Over.homMk ((bc_isPullback ιe A₀).lift g' Q'.A.X.hom hg'.w) ((bc_isPullback ιe A₀).lift_snd _ _ _)
  let θ' : (bcC ιe A₀).X ⟶ Q'.A.X :=
    Over.homMk (hg'.lift (fstC ιe A₀) (bcC ιe A₀).X.hom (bc_isPullback ιe A₀).w) (hg'.lift_snd _ _ _)
  have hθ : θ.left ≫ fstC ιe A₀ = g' := (bc_isPullback ιe A₀).lift_fst _ _ _
  have hθ' : θ'.left ≫ g' = fstC ιe A₀ := hg'.lift_fst _ _ _
  have hθθ' : θ ≫ θ' = 𝟙 _ := by
    ext1
    exact hg'.hom_ext (by rw [Over.comp_left, Category.assoc, hθ', hθ]; simp)
      (by rw [Over.comp_left, Category.assoc, Over.w θ', Over.w θ]; simp)
  have hθ'θ : θ' ≫ θ = 𝟙 _ := by
    ext1
    exact (bc_isPullback ιe A₀).hom_ext (by rw [Over.comp_left, Category.assoc, hθ, hθ']; simp)
      (by rw [Over.comp_left, Category.assoc, Over.w θ, Over.w θ']; simp)
  have hη : η[Q'.A.X] ≫ θ = η[(bcC ιe A₀).X] := by
    ext1
    refine (bc_isPullback ιe A₀).hom_ext ?_ ?_
    · rw [Over.comp_left, Category.assoc, hθ, PeriodGlue.eta_comp hl', eta_bc_fst]
    · rw [Over.comp_left, Category.assoc, Over.w θ, Over.w η[Q'.A.X], Over.w η[(bcC ιe A₀).X]]
  have hη' : η[(bcC ιe A₀).X] ≫ θ' = η[Q'.A.X] := by
    rw [← hη, Category.assoc, hθθ', Category.comp_id]
  haveI : IsMonHom θ :=
    _root_.HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral Q'.A.X (bcC ιe A₀).X θ hη
  haveI : IsMonHom θ' :=
    _root_.HDec.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral (bcC ιe A₀).X Q'.A.X θ' hη'
  let qC : QMStr (bcC ιe A₀) :=
    ⟨(endBCe ιe A₀).comp q₀.iota, (endBCe_bijective ιe A₀ hR).1.comp q₀.injective⟩
  let iso1 : QMIso Q.q qC :=
    { φ := e'
      ψ := e
      left := h2
      right := h1
      equivariant := fun a => by
        change _ = e'.hom ≫ (endBCe ιe A₀ (κ (Q.q.iota a))).hom
        rw [hβκ, conjE_hom, reassoc_of% h2] }
  let iso2 : QMIso Q'.q qC :=
    { φ := PkgI3.AbVar.Hom.mk' θ
      ψ := PkgI3.AbVar.Hom.mk' θ'
      left := by simpa using hθθ'
      right := by simpa using hθ'θ
      equivariant := fun a => by
        simp only [PkgI3.AbVar.Hom.hom_mk']
        ext1
        refine (bc_isPullback ιe A₀).hom_ext ?_ ?_
        · change ((Q'.q.iota a).hom.left ≫ θ.left) ≫ fstC ιe A₀ =
            (θ.left ≫ (endBCe ιe A₀ (q₀.iota a)).hom.left) ≫ fstC ιe A₀
          rw [Category.assoc, hθ, hι' a, Category.assoc, endBCe_fst, ← Category.assoc, hθ]
        · simp [Over.w] }
  exact ⟨iso1.trans iso2.symm⟩

-- pi0-prune: copied from TailO.lean:1301-1322
/-- **`CMDescends` from `STQM`, `T11b_Rigidity`, `TorsionDescends` and `R1R2fpRepW` (proved).** -/
theorem cmDescends_ofW (hST : STQM) (hR : ZInQ.LeafPush2.T11b_Rigidity) (hTD : TorsionDescends)
    (hRep : LeafAdopt.R1R2fpRepW) : CMDescends := by
  intro Q
  have com_of : ∀ (P : QML3 Qbar) (κ : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End P.A),
      (∀ a, κ (Q.q.iota a) = P.q.iota a) → ∀ φ ∈ com Q.q, κ φ ∈ com P.q := by
    intro P κ hκ φ hφ
    rw [com, Subring.mem_centralizer_iff] at hφ ⊢
    rintro _ ⟨a, rfl⟩
    rw [← hκ, ← map_mul, ← map_mul, hφ _ ⟨a, rfl⟩]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨ιe, P, Q', κ, hBC, hiso, hκ⟩ := descend_mainW hST hR hTD hRep Q (Or.inl h)
    obtain ⟨φ, hφ, hφ2⟩ := h
    exact ⟨ιe, P, Q', hBC, ⟨κ φ, com_of P κ hκ φ hφ, by rw [← map_mul, hφ2, map_neg, map_one]⟩, hiso⟩
  · obtain ⟨ιe, P, Q', κ, hBC, hiso, hκ⟩ := descend_mainW hST hR hTD hRep Q (Or.inr (Or.inl h))
    obtain ⟨φ, hφ, hφ2⟩ := h
    exact ⟨ιe, P, Q', hBC, ⟨κ φ, com_of P κ hκ φ hφ, by
      rw [← map_mul, ← map_sub, ← map_one κ, ← map_add, hφ2, map_zero]⟩, hiso⟩
  · obtain ⟨ιe, P, Q', κ, hBC, hiso, hκ⟩ := descend_mainW hST hR hTD hRep Q (Or.inr (Or.inr h))
    obtain ⟨φ, hφ, hφ2⟩ := h
    exact ⟨ιe, P, Q', hBC, ⟨κ φ, com_of P κ hκ φ hφ, by rw [← map_mul, hφ2, map_neg, map_ofNat]⟩,
      hiso⟩

end Glue2
end LeafQCheck
end HDec.HSyn.G0Split.FibreQM.PeriodMapH

/-! ## Copied from `ZInQKernel/OneProof/H/TailU.lean` (base 43513d87) -/

section QMSplit_ModuliSplit
set_option linter.all false
noncomputable section
namespace HDec.QMSplit.Moduli
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
-- pi0-prune: copied from TailU.lean:1965-1973
/-- **Row H-20 from the split** (the research field `r1b` of C4''). -/
theorem r1b_ofW (hS : ShimuraFamily) (hT : R1bTransport) :
    ∀ h : LeafAdopt.R1R2fpRepW,
      HSyn.G0Split.FibreQM.R1bFamily (HSyn.G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_repW h))
        (HSyn.G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_repW h))
        (HSyn.G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_repW h)) := by
  intro h
  obtain ⟨Y, Φ, h1, hall⟩ := hS
  exact hT Y Φ _ _ h1 (HSyn.G0Split.FibreQM.own_spec _).1 hall _

-- pi0-prune: copied from TailU.lean:1990-1993
/-- **Row H-43 from the bundle leaf `r1r2` (H-1) and the conic glue.** -/
theorem x6ConicModel_ofW (hR : LeafAdopt.R1R2fpRepW) (hC : ConicOfWitness) : X6Kummer.X6ConicModel := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h⟩ := LeafAdopt.R1R2fp_of_repW hR
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h, hC Y Φ X Ψ fY π₆ h⟩

-- pi0-prune: copied from TailU.lean:2272-2278
/-- **Row H-20 from the leaf candidate `ShimuraFamily` alone** (`R1bTransport` discharged). -/
theorem r1b_of'W (hS : ShimuraFamily) :
    ∀ h : LeafAdopt.R1R2fpRepW,
      HSyn.G0Split.FibreQM.R1bFamily (HSyn.G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_repW h))
        (HSyn.G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_repW h))
        (HSyn.G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_repW h)) :=
  r1b_ofW hS r1bTransport_proof

end HDec.QMSplit.Moduli
end -- noncomputable section
end QMSplit_ModuliSplit

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ5.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
open CategoryTheory AlgebraicGeometry Limits
-- pi0-prune: copied from TailZ5.lean:258-265 (pattern: one conjunct fewer)
/-- **`R1rec` from `R1R2fpRepW`**: the object `P` is the object at a point `y` of the fine witness (`Φ` is a
bijection), the witness's reciprocity clause makes `ℚ(y)` unramified above 5, and `fieldOfModuli3 P ⊆ ℚ(y)`. -/
theorem r1rec_of_repW (h : LeafAdopt.R1R2fpRepW) : LeafQM.AV.R1rec := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, -, -, -, hrec, -, -⟩ := h
  intro P hcm
  have hy : Φ _ ((Φ _).symm (LeafQM.AV.M3.mk P)) = LeafQM.AV.M3.mk P := Equiv.apply_symm_apply _ _
  exact _root_.ZInQ.LeafFold9.unramifiedAbove5_mono (_root_.ZInQ.LeafFold9.fieldOfModuli3_le h1 _ P hy)
    (hrec _ P hy hcm)

-- pi0-prune: copied from TailZ5.lean:267-277 (pattern: one conjunct fewer)
/-- **`R5fp` from `R1R2fpRepW`**: the pair `P` is the pair at a point `x` of the coarse witness (`Ψ` is a
bijection), the witness's González–Rotger clause is about `ℚ(x)`, and `ℚ(x)` is the field of moduli of `P`. -/
theorem r5fp_of_repW (h : LeafAdopt.R1R2fpRepW) : LeafQM.AV.R5fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, h6, -, -, -, h5⟩ := h
  intro k _ _ _ hk R hR hc P hP
  have hx : Ψ (Ψ.symm (Quotient.mk _ P)) = Quotient.mk _ P := Equiv.apply_symm_apply _ _
  obtain ⟨h5a, h5b⟩ := h5 k hk R hR hc _ P hx hP
  have e := _root_.ZInQ.LeafFold9.residueImage_eq_fieldOfModuliPair h6 _ P hx
  refine ⟨?_, fun hne => (h5b hne).map fun φ => (IntermediateField.equivOfEq e).toAlgHom.comp φ⟩
  rw [← h5a]
  exact (IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq.symm

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ20.lean` (base 43513d87) -/

set_option linter.all false
noncomputable section
set_option autoImplicit false
set_option linter.all false
open CategoryTheory AlgebraicGeometry Limits
noncomputable section
namespace HDec.QMSplit.Moduli
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
-- pi0-prune: copied from TailZ20.lean:1030-1032 (pattern: one conjunct fewer)
theorem pairsLift_of_repW (h : LeafAdopt.R1R2fpRepW) : PairsLift := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, h6, -, -, hs, -⟩ := h
  exact pairsLift_of_witness h6 hs.2

-- pi0-prune: copied from TailZ20.lean:1062-1065
/-- `CoarseFactor` from the bundle leaf `R1R2fpRepW` (the hypothesis of qm-glue's
`x6ConicModel_of_canonical'`) and the AG glue. -/
theorem coarseFactor_of_repW (hR : LeafAdopt.R1R2fpRepW) (hF : FactorThroughSurj) : CoarseFactor :=
  coarseFactor_of (pairsLift_of_repW hR) hF

end HDec.QMSplit.Moduli
namespace HDec.QMSplit.Moduli
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
-- pi0-prune: copied from TailZ20.lean:1084-1086
/-- **`CoarseFactor` from `R1R2fpRepW`.** -/
theorem coarseFactor_of_rep'W (hR : LeafAdopt.R1R2fpRepW) : CoarseFactor :=
  coarseFactor_of_repW hR factorThroughSurj_proof

end HDec.QMSplit.Moduli
set_option linter.all false
noncomputable section
set_option linter.all false
noncomputable section
set_option linter.all false
noncomputable section
set_option linter.all false
noncomputable section
set_option linter.all false
noncomputable section
namespace HDec.QMSplit.Moduli
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
-- pi0-prune: copied from TailZ20.lean:1910-1915
/-- **Row H-43 (`x6ConicModel`) from `r1r2`, Elkies' model `ElkiesConicX6` and `MobiusGlue`** (the kernel
proves `MobiusGlue` from T5: `LeafQM.AV.CurveGlue.mobiusGlue_of_T5`). -/
theorem x6ConicModel_of_elkiesW (hR : LeafAdopt.R1R2fpRepW) (hC : ElkiesConicX6) (hM : Pin.MobiusGlue) :
    X6Kummer.X6ConicModel :=
  x6ConicModel_ofW hR (conicOfWitness_of_elkies hC
    (coarseCompare_of (coarseFactor_of_rep'W hR) CurveSplit.curveBijIso) (hauptmodulUniqueX6S_of hM))

end HDec.QMSplit.Moduli
namespace HDec.QMSplit.Moduli
-- pi0-prune: copied from TailZ20.lean:1921-1925
/-- **Row H-43 with `MobiusGlue` discharged from T5** (`PkgI2.TorsionStructure`, the bundle's T5 form; the
kernel's `LeafQM.AV.CurveGlue.mobiusGlue_of_t5`, image-plane). -/
theorem x6ConicModel_of_elkies_t5W (hR : LeafAdopt.R1R2fpRepW) (hC : ElkiesConicX6)
    (hT : PkgI2.TorsionStructure.{0}) : X6Kummer.X6ConicModel :=
  x6ConicModel_of_elkiesW hR hC (LeafQM.AV.CurveGlue.mobiusGlue_of_t5 hT)

end HDec.QMSplit.Moduli

/-! ## The producers of the weak row (pi0-prune)

The chain's `r1r2fpRep_of` (TailU 1914), `coarseX6OfFine_of`, `canonicalCoarseX6_of`, `r1r2fpRep_of_split{,5,6}`,
`r1r2fpRep_of_printed{,_t5}` (TailZ20) with the clause `R1pi0Props` removed from the intermediate statements
`CoarseX6OfFine`, `CanonicalCoarseX6`, `GeomConnX6`; the base witness `(Y, Φ, X, Ψ, fY)` with `R1fpProps ∧ X6Props`
now comes from `GonzalezRotgerX6` (González–Rotger 2006 Thm 5.12 on the canonical `X₆`, already an input of
`r1r2fpRep_of_printed`) instead of `geomConnX6_of hD hE`. -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- `CoarseX6OfFine` (TailU) without the clause `R1pi0Props X`. -/
def CoarseX6OfFineW : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → R1heckeProps Y Φ →
    ∃ (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
      (fY : Y ⟶ X), X6Props Y Φ X Ψ fY ∧ (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x)

theorem coarseX6OfFineW_of (h : CoarseX6OfFine) : CoarseX6OfFineW := by
  intro Y Φ h1 hh
  obtain ⟨X, Ψ, fY, h6, hs, -⟩ := h Y Φ h1 hh
  exact ⟨X, Ψ, fY, h6, hs⟩

/-- `r1r2fpRep_of` (TailU 1914-1921) for the weak row; the proof without the clause `R1pi0Props`. -/
theorem r1r2fpRep_ofW (hE : CanonicalModelY3) (hH : HeckeOfFine) (hX : CoarseX6OfFineW)
    (hP : HauptmodulOfX6) (hR : ReciprocityOfFine) (h5 : ResidueOfX6) : LeafAdopt.R1R2fpRepW := by
  obtain ⟨Y, Φ, h1⟩ := hE
  have hh := hH Y Φ h1
  obtain ⟨X, Ψ, fY, h6, hsurj⟩ := hX Y Φ h1 hh
  obtain ⟨π₆, h2, ht⟩ := hP Y Φ X Ψ fY h1 h6
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hR Y Φ h1, ⟨ht, hsurj⟩, h5 Y Φ X Ψ fY h1 h6⟩

/-- `r1r2fpRep_of'` (TailU 2267-2270) for the weak row. -/
theorem r1r2fpRep_of'W (hE : CanonicalModelY3) (hX : CoarseX6OfFineW) (hP : HauptmodulOfX6)
    (hR : ReciprocityOfFine) (h5 : ResidueOfX6) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_ofW hE heckeOfFine_proof hX hP hR h5

/-- `CanonicalCoarseX6` (TailZ20 185) without the clause `R1pi0Props X`. -/
def CanonicalCoarseX6W : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x)

theorem canonicalCoarseX6W_of (h : CanonicalCoarseX6) : CanonicalCoarseX6W := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, hs, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6, hs⟩

/-- `coarseX6OfFine_of` (TailZ20 212-219) for the weak forms. -/
theorem coarseX6OfFine_ofW (hC : CanonicalCoarseX6W) : CoarseX6OfFineW := by
  intro Y Φ h1 _
  obtain ⟨Y₀, Φ₀, X, Ψ, fY₀, h1₀, h6₀, hsurj⟩ := hC
  obtain ⟨g, hg⟩ := compare_iso h1₀ h1
  refine ⟨X, Ψ, g.hom ≫ fY₀, x6Props_transport g hg h6₀, fun x => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hsurj x
  exact ⟨y₀ ≫ g.inv, by rw [Category.assoc, Iso.inv_hom_id_assoc, hy₀]⟩

/-- `canonicalModelY3_of_coarse` (TailZ20 1723-1726) for the weak form. -/
theorem canonicalModelY3_of_coarseW (hC : CanonicalCoarseX6W) : CanonicalModelY3 := by
  obtain ⟨Y, Φ, -, -, -, h1, -⟩ := hC
  exact ⟨Y, Φ, h1⟩

/-- `pairsLift_of_canonical` (TailZ20 1026-1028) for the weak form. -/
theorem pairsLift_of_canonicalW (h : CanonicalCoarseX6W) : PairsLift := by
  obtain ⟨Y, Φ, X, Ψ, fY, -, h6, hs⟩ := h
  exact pairsLift_of_witness h6 hs

/-- `coarseCompare_of_canonical` (TailZ20 1089-1090, through `coarseFactor_of_canonical'`) for the weak form. -/
theorem coarseCompare_of_canonicalW (hC : CanonicalCoarseX6W) : CoarseCompare :=
  coarseCompare_of (coarseFactor_of (pairsLift_of_canonicalW hC) factorThroughSurj_proof) CurveSplit.curveBijIso

/-- `r1r2fpRep_of_split` (TailZ20 1749-1753) for the weak forms. -/
theorem r1r2fpRep_of_splitW (hC : CanonicalCoarseX6W) (hB : BabaGranathX6) (hR : LeafQM.AV.R1rec)
    (h5 : LeafQM.AV.R5fp) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_of'W (canonicalModelY3_of_coarseW hC) (coarseX6OfFine_ofW hC)
    (hauptmodulOfX6_of hB (coarseCompare_of_canonicalW hC)) (reciprocityOfFine_of_r1rec hR)
    (residueOfX6_of_r5fp h5)

/-- `GeomConnX6` (TailZ20 1770) without the clause `R1pi0Props X`: the base witness of the moduli clause lists. -/
def GeomConnX6W : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY

theorem geomConnX6W_of (h : GeomConnX6) : GeomConnX6W := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6⟩

/-- **The base witness from González–Rotger's leaf** (no Deligne, no `GeomConnOfAlgClosure`). -/
theorem geomConnX6W_of_gr (hG : GonzalezRotgerX6) : GeomConnX6W := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, -⟩ := hG
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6⟩

/-- `canonicalCoarseX6_of` (TailZ20 1776-1784) for the weak forms. -/
theorem canonicalCoarseX6_ofW (hG : GeomConnX6W) (hL : PairsLift) : CanonicalCoarseX6W := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6⟩ := hG
  refine ⟨Y, Φ, X, Ψ, fY, h1, h6, fun x => ?_⟩
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep (Ψ x)
  obtain ⟨P, hP⟩ := hL Q
  obtain ⟨y, hy⟩ := (Φ Qbar).surjective (M3.mk P)
  refine ⟨y, Ψ.injective ?_⟩
  rw [h6.2.2.2.2.2 y P hy, hP, hQ]

/-- `r1r2fpRep_of_split5` (TailZ20 1789-1791) for the weak forms. -/
theorem r1r2fpRep_of_split5W (hG : GeomConnX6W) (hL : PairsLift) (hB : BabaGranathX6)
    (hR : LeafQM.AV.R1rec) (h5 : LeafQM.AV.R5fp) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_of_splitW (canonicalCoarseX6_ofW hG hL) hB hR h5

/-- `r1r2fpRep_of_split6` (TailZ20 1820-1823) for the weak forms. -/
theorem r1r2fpRep_of_split6W (hG : GeomConnX6W) (hL : PairsLift) (hB : BabaGranathX6')
    (hR : LeafQM.AV.R1rec) (h5 : LeafQM.AV.R5fp) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_of_split5W hG hL (babaGranathX6_of hB) hR h5

/-- **`r1r2fpRep_of_printed` (TailZ20 1855-1859) without `hD` and `hE`**: the base witness from `hG`. -/
theorem r1r2fpRep_of_printedW (hL : PairsLift) (hB : BabaGranathX6') (hR : ReciprocityCanonical)
    (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRepW := by
  refine r1r2fpRep_of_split6W (geomConnX6W_of_gr hG) hL hB (r1rec_of_reciprocityCanonical hR) ?_
  obtain ⟨Y, Φ, X, Ψ, fY, -, h6, h5⟩ := hG
  exact ShimuraSplit.r5fp_of_point ⟨Y, Φ, X, Ψ, fY, h6, h5⟩

/-- `r1r2fpRep_of_printed_t5` (TailZ20 1937-1941) without `hD` and `hE`. -/
theorem r1r2fpRep_of_printed_t5W (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathX6')
    (hR : ReciprocityCanonical) (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_of_printedW (pairsLift_of_t5 hT) hB hR hG

/-- **The row `r1r2` (weak form) from published-form leaves**: `r1r2_of_published` (TailZ21 1420-1433) without
`hD : ShimuraGlue.DeligneComponentsX6Printed` and `hE : GeomConnOfAlgClosure`. Every hypothesis is a hypothesis of
`r1r2_of_published`: T5 (`PkgI2.TorsionStructure`), Baba–Granath (`BabaGranathRational`), the ray-class consequence
`RayClassCM` and González–Rotger Thm 5.12 (`GonzalezRotgerX6`). -/
theorem r1r2_of_publishedW (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathRational)
    (hR : ShimuraGlue.Ray.RayClassCM) (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_of_printed_t5W hT (babaGranathX6'_of_rational' hB) (ShimuraGlue.Ray.reciprocityCanonical_of_rayClass hR) hG

/-- `x6ConicModel_of_published` (TailZ21 1435-1441) without `hD` and `hE`. -/
theorem x6ConicModel_of_publishedW (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathRational)
    (hR : ShimuraGlue.Ray.RayClassCM) (hG : GonzalezRotgerX6) (hC : ElkiesEquationsX6) :
    X6Kummer.X6ConicModel :=
  x6ConicModel_of_elkies_t5W (r1r2_of_publishedW hT hB hR hG) (elkiesConicX6_of_equations hC) hT

/-- `X6Leaves` (TailZ21 1444-1451) without `deligneX6P` and `geomConn`. -/
structure X6LeavesW : Prop where
  t5 : PkgI2.TorsionStructure.{0}
  babaGranathR : BabaGranathRational
  rayClass : ShimuraGlue.Ray.RayClassCM
  gonzalezRotger : GonzalezRotgerX6
  elkiesEq : ElkiesEquationsX6

/-- `x6Rows_of_leaves` (TailZ21 1453-1456) for the weak row, without the two leaves. -/
theorem x6Rows_of_leavesW (L : X6LeavesW) : LeafAdopt.R1R2fpRepW ∧ X6Kummer.X6ConicModel :=
  ⟨r1r2_of_publishedW L.t5 L.babaGranathR L.rayClass L.gonzalezRotger,
    x6ConicModel_of_publishedW L.t5 L.babaGranathR L.rayClass L.gonzalezRotger L.elkiesEq⟩

end HDec.QMSplit.Moduli

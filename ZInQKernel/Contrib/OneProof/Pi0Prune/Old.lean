import ZInQKernel.Contrib.OneProof.Pi0Prune.Base

/-!
# pi0-prune (2/3): the old bundle generations with the weak row

The six bundle structures that carry the row (`ResearchLeaves3` (TailD), `OpenResearchLeaves2` (TailE), `5` (TailN),
`7` (TailX), `8` (TailZ4), `9` (TailZ9)) copied verbatim with `r1r2 : LeafAdopt.R1R2fpRepW` (and `r1b : ∀ h :
LeafAdopt.R1R2fpRepW, …` with `R1R2fp_of_repW`), suffix `W`; and every declaration of the single proof whose type
mentions them, copied verbatim with the same renaming (each copy names its source file and lines at base 43513d87).
No `sorry`; standard axioms only.
-/

set_option linter.all false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Copied from `ZInQKernel/OneProof/H/TailD.lean` (base 43513d87) -/

namespace HDec
set_option maxHeartbeats 1000000
attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
section G0A2_z80_leaves3
noncomputable section
namespace HSyn
open scoped MatrixGroups ModularForm
-- pi0-prune: copied from TailD.lean:35-82 (structure, docstring omitted)
structure ResearchLeaves3W : Prop where
  /-- R1 (a), (c), (d), `π₀(X₆) = 1` (rv-blueprints Q4), R1 at level one, R2 with biconditional CM
  clauses (Q5) and R5 on points of `X₆`, on one `Y₃`, `X₆` (leaf-qm-fp, repaired by leaf-adopt).
  Premise (rv-qm-polar Lemma P): for a QM pair `(A, ι)` in characteristic 0 there is exactly one
  principal polarization whose Rosati involution is `x ↦ μ⁻¹x̄μ` on `ι(𝒪)` (`μ = 2j + ij`, the
  type fixed by the PEL datum); see the definition. Checked by model reviews (rv-qm-polar), no
  human review. -/
  r1r2 : LeafAdopt.R1R2fpRepW
  -- (g0-assemble2) `r1an : R01b_ComplexUniformization` (an `opaque` placeholder) removed: unused;
  -- its concrete family form is `GluePieces3.r1bFamily` (fibre-qm-period).
  /-- R1(d), Shimura reciprocity, object form (leaf-qm-fp; premise Lemma P, rv-qm-polar). -/
  r1rec : LeafQM.AV.R1rec
  r4 : PkgI1.ThetaModularity
  /-- R5(ii), González–Rotger Thm 5.12, fields of moduli (= rv-blueprints' R5fpStrong, Q2;
  premise Lemma P, rv-qm-polar). -/
  r5 : LeafQM.AV.R5fp
  /-- R5(i), González–Rotger Prop. 5.6, `#CM(R) = 2^b h(R)` (premise Lemma P, rv-qm-polar). -/
  r5count : LeafQM.AV.R5fpCount
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r8 : PkgI2.GrothendieckMonodromy.{0}
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  r10 : PkgI4.DeRhamComparison
  /-- R11 (Berger) and R12 (Pan) enter through their joint consequence: Pan's theorem with "de Rham
  at `p`" in place of "potentially semistable at `p`" (pkg-I4). `B_st` is not needed by the glue.
  Both theorems remain separate leaves in the count. -/
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  r14 : EigenformRepExists
  r15 : DeligneSerreConseq
  /-- R16, Eichler–Shimura in `J₁(N)`, existential form for every `K_N` model (leaf-modcurves). -/
  r16 : LeafModCurves.R16_EichlerShimuraJ1'
  -- (g0-assemble2) `r17 : R17_Carayol` (an `opaque` placeholder) removed: unused; its concrete form
  -- is `GluePieces3.carayolR17` (`LadicCond.CarayolR17'`).
  /-- R18, Javanpeykar, over leaf-push2's stable Faltings height on `PkgI3.AbVar` (with H5). -/
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  /-- R19-R21 over def-faltings' `stableFaltingsHeight`. Its value is `⊤` (no metrized model) or
  the stable Faltings height in Faltings' normalization, so R19-R21 are true for the definition;
  they say something only together with `h5` (`StableHeightFinite`), which is where a defect of
  the definition would surface, as a false leaf (rv-leaves48, `RvLeaves48D`). -/
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r21 : ZInQ.DefFaltings.R21_Bost
  /-- R22, Pazuki's upper half, over all uniformizations and period matrices (leaf-push2). -/
  r22 : ZInQ.LeafPush2.R22_Pazuki
  /-- H5's finiteness half (rv-blueprints F2): the stable height is finite (g0-assemble2: the
  other half, `NeronModelMinimal`, is proved by h5-glue, `ZInQ.H5Glue.neronModelMinimal`). -/
  h5fin : ZInQ.DefFaltings.StableHeightFinite

-- pi0-prune: copied from TailD.lean:85-87
/-- H5 from its finiteness half and h5-glue's `NeronModelMinimal`. -/
theorem ResearchLeaves3W.h5 (r : ResearchLeaves3W) : LeafAdopt.H5 :=
  ⟨r.h5fin, ZInQ.H5Glue.neronModelMinimal⟩

end HSyn
namespace HSyn.G0RevIsog
-- pi0-prune: copied from TailD.lean:117-119
theorem reverseIsogeny_of_leaves3W (r : HSyn.ResearchLeaves3W) (hDimF : G0Split.DimFinite) :
    G0Split.ReverseIsogeny :=
  reverseIsogeny_of_exists (isogenyReverseExists_of_r19 r.r19 r.h5.1 hDimF)

end HSyn.G0RevIsog
namespace G0Galois
open _root_.PkgI4 (GaloisRep GaloisChar) -- op-dedupe
-- pi0-prune: copied from TailD.lean:128-141
theorem g8_g12_of_leaves3W (r : HSyn.ResearchLeaves3W) (t : HSyn.TextbookLeaves) (m : GaloisPieces)
    (h9 : G9GlueNoT23)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3 : G3Out A 5 T)
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β : PkgI4.GQ → PadicAlgCl 5)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7 : G7Out A 5 Tm c ε a β u) :
    ∃ r₅ : GaloisRep 5 2, G8Out A 5 (GlueDescent.rho Tm a β) r₅ ∧ G9Out r₅ ∧ G10Out r₅ ∧
      G11Out T r₅ ∧ G12Out r₅ :=
  g8_g12 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t11a t.t11b
    r.r11r12 r.r14 r.r13 r.r15 t.frobeniusDense HSyn.t19_proved t.t9 (g8Matrix_of_burnside m.burnside) h9 m.odd m.weight
    (g12Det_of m.r14det m.detTate m.finIndex (frobeniusDenseQ_of t.frobeniusDense))
    A T h2 h6 h3 Tm c ε a β u h7

end G0Galois
namespace HSyn.G0AssembleMod
open CategoryTheory AlgebraicGeometry
open G0ModField
-- pi0-prune: copied from TailD.lean:150-154
theorem newformLeaves_of3W (r : ResearchLeaves3W) (t : TextbookLeaves)
    (hCar : LadicCond.CarayolR17') : G0ModNewform.NewformLeaves :=
  ⟨C9Rhof.eigenformTwist_of_hsyn t.t24, t.t25, C9Rhof.eigenformRepExists_of_hsyn r.r14, r.r16,
    hCar, r.r9a, r.r9b, t.t26, C9Rhof.frobeniusDense_of_hsyn t.frobeniusDense,
    TSkolemKW.C10.brauerNesbittChar0'⟩

-- pi0-prune: copied from TailD.lean:156-181
theorem afterG7_of3W (r : ResearchLeaves3W) (t : TextbookLeaves) (m : G0Galois.GaloisPieces)
    (h9 : G0Galois.G9GlueNoT23)
    (hDF : G0ModNewform.DirichletOfFinite) (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hG36 : ModelG3G6) (hLink : LinkedTateData) : AfterG7 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨h6, h3₅, h3₃⟩ := hG36 Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  obtain ⟨Tm₅, c₅, ε₅, a₅, β₅, u₅, Tm₃, c₃, ε₃, a₃, β₃, u₃, h7₅, h7₃, hlink⟩ :=
    hLink Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  have h2 : G0Galois.G2Out L' (T u) :=
    galoisG2Out_of_g7Data resQRange u P L A ε N χ β L' hLL' hdata
  obtain ⟨r₅, h8₅, -, -, h11₅, h12⟩ :=
    G0Galois.g8_g12_of_leaves3W r t m h9 _ (T u) h2 h6 h3₅ Tm₅ c₅ ε₅ a₅ β₅ u₅ h7₅
  obtain ⟨r₃, h8₃, -, -, h11₃⟩ :=
    G0Galois.g8_g11 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t11a
      t.t11b (G0Galois.g8Matrix_of_burnside m.burnside) h9 m.odd _ (T u) h2 h6 3 h3₃
      Tm₃ c₃ ε₃ a₃ β₃ u₃ h7₃
  obtain ⟨i, ιC, ι5, hspec⟩ := G0ModNewform.g12Spec_of_galois hDF _ _ _ r₅ r₃ h8₅ h8₃ h12
  obtain ⟨ι3, h14, h15⟩ := hlink r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ :=
    G0ModNewform.modularConstituent_tail_G (newformLeaves_of3W r t hCar) t.t33 t.x1ModelExists
      hSw hL8 hAd _ u ⟨_, hspec ι3, h14, g15RamG_of_wild _ u h15 h11₅ h11₃⟩
  exact ⟨M, J, hM, hJ, hMle, (commonConstituent_copy' _ _).1 hCC⟩

end HSyn.G0AssembleMod
namespace HSyn
namespace G0Split
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
-- pi0-prune: copied from TailD.lean:192-196
theorem hom_of_common3W (r : ResearchLeaves3W) (t : TextbookLeaves) {K : Type} [Field K]
    [NumberField K] (A J : PkgI3.AbVar K) (h : CommonConstituent A J) :
    ∃ f : PkgI3.AbVar.Hom A J, f ≠ 0 := by
  obtain ⟨ℓ, _, E, _, _, U, U', e, hU, he⟩ := h
  exact PkgI3.E1_exists_hom_ne_zero r.r9a r.r9b t.t26 semisimpleBaseChange A J ℓ E U U' hU e he

end G0Split
open G0Split in
-- pi0-prune: copied from TailD.lean:201-253
theorem glueOutputs_of_leaves3W (r : ResearchLeaves3W) (t : TextbookLeaves) (gp : GluePieces)
    (h20 : R20Lower) : GlueAssembly.GlueOutputs ZInQ.Mult.S_mul := by
  obtain ⟨hDimF, hDim, hSimp, hPMH, hBC, hProdE, hRev, hThetaPt, hMod, hCopies⟩ := gp
  have hBelyi : X1BelyiOnModel := x1BelyiOnModel_of_belyiX1 t.belyiX1
  have hAdd : HeightAdditivity := heightAdditivity_of_h5neron t.t41 r.h5.2 hPMH
  have hR18 : R18_JavanpeykarConcrete := r18Concrete_of r.r18 hCopies
  have hR22 : R22_PazukiConcrete := r22Concrete_of r.r22 hCopies
  -- A4: the moduli data and an object over every value
  obtain ⟨Y, Φ, π, h1, h2, hfib⟩ :=
    LeafQM.AV.exists_fibre_object (LeafAdopt.R1R2fp_of_repW r.r1r2)
  intro u hu
  obtain ⟨y, P, hP, hy⟩ := hfib (OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)))
  -- G2-G16 (missing piece 10, `ModularConstituent`): the field `L'`, the model `A`, the level `N`, `J₁(N)`
  obtain ⟨L, emb, A, N, J, hiso, hN0, hJ1, hNQ, hdQ, hCC⟩ := hMod Y Φ π h1 h2 u hu y P hP hy
  have hFib : FibreOver Y Φ π u L A := ⟨emb, y, P, hP, hy, hiso⟩
  have hA2 : A.dim = 2 := model_dim hDim emb A P.A hiso P.surface
  -- H5: the stable height of `A` is real
  have hfin := r.h5.1
  have hx : ZInQ.DefFaltings.stableFaltingsHeight A = ZInQ.DefFaltings.faltingsHeight A :=
    (ZInQ.DefFaltings.faltingsHeight_coe hfin A).symm
  -- G19: the theta point (missing piece 9, `ThetaPointOfFibre`) and Pazuki (R22)
  obtain ⟨K', z, hF1, hPaz⟩ := thetaPazuki hR22 hThetaPt Y Φ π h1 h2 u hu L A hFib hA2 _ hx
  refine ⟨K', z, ZInQ.DefFaltings.faltingsHeight A, hF1, hPaz, Or.inl ?_⟩
  -- E1: a nonzero homomorphism `A → J₁(N)_{L'}`
  obtain ⟨f, hf⟩ := hom_of_common3W r t _ _ hCC
  -- G5-G6 (missing piece 4, `FibreSimple`): `A` simple; T8: Poincaré
  obtain ⟨Z, g, hisoZ⟩ := t.t8 L.K _ _ (hSimp Y Φ π h1 h2 u hu L A hFib) f hf
  -- G17 after Poincaré (`isogenousProduct`, from missing pieces 1, 7, 8): `A × Z`, the isogeny `J₁(N)_{L'} → A × Z`
  obtain ⟨Pr, φ, hφ, hPprod, hdims⟩ :=
    isogenousProduct hDimF hProdE hRev L.K _ _ _ f g hisoZ
  -- E2: `dim J₁(N) ≤ N²`
  obtain ⟨gJ, hgJ, hgN⟩ := dim_J1_le_of5 t34Le N hN0 J hJ1
  have hJLd : (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K).dim = (gJ : WithBot ℕ∞) :=
    (hDim ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)).trans hgJ
  have hALd : A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [hA2]; rfl
  obtain ⟨gZ, hZd, hsum⟩ := hdims 2 gJ hALd hJLd
  -- heights (H5; missing pieces 5, 6; R18 with missing pieces 2, 3)
  have hxJ : ZInQ.DefFaltings.stableFaltingsHeight
      (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) =
      ZInQ.DefFaltings.faltingsHeight ((LeafAdopt.abVarEquiv ℚ).symm J) := by
    rw [hBC ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)]
    exact (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hyP := (ZInQ.DefFaltings.faltingsHeight_coe hfin Pr).symm
  have hzZ := (ZInQ.DefFaltings.faltingsHeight_coe hfin ((LeafAdopt.abVarEquiv L.K).symm Z)).symm
  have hadd := hAdd L.K Pr A ((LeafAdopt.abVarEquiv L.K).symm Z) hPprod _ _ _ hx hzZ hyP
  have hJb := javanpeykarJ1_of_le hR18 hBelyi t34Le N hN0 J hJ1 gJ hgJ (by omega) _
    (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hgN' : (gJ : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  -- E3-E4 (proved from R19-R21)
  exact transfer_core r.r19 h20 r.r21 (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) Pr A
    ((LeafAdopt.abVarEquiv L.K).symm Z) gJ gZ hJLd hZd (by omega) (by omega) φ hφ _ _ _ _ hxJ hyP
    hzZ hadd hN1 hNQ hJb hgN' hdQ

-- pi0-prune: copied from TailD.lean:255-258
/-- **G0 with `ResearchLeaves3W`** (`sixContactMin_of_leaves` of Leaves.lean, copied). -/
theorem sixContactMin_of_leavesR3W (r : ResearchLeaves3W) (t : TextbookLeaves) (gp : GluePieces)
    (h20 : G0Split.R20Lower) : ZInQ.SixContactMin :=
  sixContactMin_of_glueOutputs (glueOutputs_of_leaves3W r t gp h20)

end HSyn
end
end G0A2_z80_leaves3
section G0A2_z90_bundle3
noncomputable section
namespace HSyn
open G0Split
-- pi0-prune: copied from TailD.lean:534-537
/-- fs5-nocm's `R1R2fpFull` is the leaf bundle's `R1R2fp` after pin-apply (same clauses). -/
theorem r1r2fpFull_ofW (r : ResearchLeaves3W) : FS5NoCM.R1R2fpFull := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h⟩ := LeafAdopt.R1R2fp_of_repW r.r1r2
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h⟩

end HSyn
end
end G0A2_z90_bundle3
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailE.lean` (base 43513d87) -/

namespace HDec
open _root_.ZInQ (Contrib.AbVarBC.G0FibreSimple.MulIsogeny Contrib.AbVarBC.MulRigidity.CotangentMulN Contrib.AbVarBC.MulRigidity.KerUnitOpen Contrib.AbVarBC.MulRigidity.KerUnitOpenOfCotangentSurj Contrib.AbVarBC.MulRigidity.MulEtale Contrib.AbVarBC.MulRigidity.MulUnramified Contrib.AbVarBC.MulRigidity.O0 Contrib.AbVarBC.MulRigidity.QuasiFiniteEndSurjective Contrib.AbVarBC.MulRigidity.charZero_residueField Contrib.AbVarBC.MulRigidity.cotangentMap Contrib.AbVarBC.MulRigidity.diagonal_isPullback Contrib.AbVarBC.MulRigidity.diffKer Contrib.AbVarBC.MulRigidity.formallyUnramified_of_kerUnit Contrib.AbVarBC.MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap Contrib.AbVarBC.MulRigidity.isOpenImmersion_of_section Contrib.AbVarBC.MulRigidity.isProper_left Contrib.AbVarBC.MulRigidity.kerUnit Contrib.AbVarBC.MulRigidity.kerUnitOpen_of_cotangent Contrib.AbVarBC.MulRigidity.kerUnitOpen_of_mulEtale Contrib.AbVarBC.MulRigidity.locallyQuasiFinite_of_formallyUnramified Contrib.AbVarBC.MulRigidity.map_origin Contrib.AbVarBC.MulRigidity.mulIsogeny_of_cotangent Contrib.AbVarBC.MulRigidity.mulIsogeny_of_kerUnitOpen Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulEtale Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified' Contrib.AbVarBC.MulRigidity.mulUnramified_of_kerUnitOpen Contrib.AbVarBC.MulRigidity.mulUnramified_of_mulEtale Contrib.AbVarBC.MulRigidity.ne_of_specializes_of_lqf Contrib.AbVarBC.MulRigidity.origin Contrib.AbVarBC.MulRigidity.quasiFiniteEndSurjective Contrib.AbVarBC.MulRigidity.stalkEndo Contrib.AbVarBC.MulRigidity.surjective_of_lqf_self) -- op-dedupe
open _root_.ZInQ.Contrib.AbVarBC (G0FibreSimple.MulIsogeny MulRigidity.CotangentMulN MulRigidity.KerUnitOpen MulRigidity.KerUnitOpenOfCotangentSurj MulRigidity.MulEtale MulRigidity.MulUnramified MulRigidity.O0 MulRigidity.QuasiFiniteEndSurjective MulRigidity.charZero_residueField MulRigidity.cotangentMap MulRigidity.diagonal_isPullback MulRigidity.diffKer MulRigidity.formallyUnramified_of_kerUnit MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap MulRigidity.isOpenImmersion_of_section MulRigidity.isProper_left MulRigidity.kerUnit MulRigidity.kerUnitOpen_of_cotangent MulRigidity.kerUnitOpen_of_mulEtale MulRigidity.locallyQuasiFinite_of_formallyUnramified MulRigidity.map_origin MulRigidity.mulIsogeny_of_cotangent MulRigidity.mulIsogeny_of_kerUnitOpen MulRigidity.mulIsogeny_of_mulEtale MulRigidity.mulIsogeny_of_mulUnramified MulRigidity.mulIsogeny_of_mulUnramified' MulRigidity.mulUnramified_of_kerUnitOpen MulRigidity.mulUnramified_of_mulEtale MulRigidity.ne_of_specializes_of_lqf MulRigidity.origin MulRigidity.quasiFiniteEndSurjective MulRigidity.stalkEndo MulRigidity.surjective_of_lqf_self) -- op-dedupe
open _root_.ZInQ.Contrib (AbVarBC.G0FibreSimple.MulIsogeny AbVarBC.MulRigidity.CotangentMulN AbVarBC.MulRigidity.KerUnitOpen AbVarBC.MulRigidity.KerUnitOpenOfCotangentSurj AbVarBC.MulRigidity.MulEtale AbVarBC.MulRigidity.MulUnramified AbVarBC.MulRigidity.O0 AbVarBC.MulRigidity.QuasiFiniteEndSurjective AbVarBC.MulRigidity.charZero_residueField AbVarBC.MulRigidity.cotangentMap AbVarBC.MulRigidity.diagonal_isPullback AbVarBC.MulRigidity.diffKer AbVarBC.MulRigidity.formallyUnramified_of_kerUnit AbVarBC.MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap AbVarBC.MulRigidity.isOpenImmersion_of_section AbVarBC.MulRigidity.isProper_left AbVarBC.MulRigidity.kerUnit AbVarBC.MulRigidity.kerUnitOpen_of_cotangent AbVarBC.MulRigidity.kerUnitOpen_of_mulEtale AbVarBC.MulRigidity.locallyQuasiFinite_of_formallyUnramified AbVarBC.MulRigidity.map_origin AbVarBC.MulRigidity.mulIsogeny_of_cotangent AbVarBC.MulRigidity.mulIsogeny_of_kerUnitOpen AbVarBC.MulRigidity.mulIsogeny_of_mulEtale AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified' AbVarBC.MulRigidity.mulUnramified_of_kerUnitOpen AbVarBC.MulRigidity.mulUnramified_of_mulEtale AbVarBC.MulRigidity.ne_of_specializes_of_lqf AbVarBC.MulRigidity.origin AbVarBC.MulRigidity.quasiFiniteEndSurjective AbVarBC.MulRigidity.stalkEndo AbVarBC.MulRigidity.surjective_of_lqf_self) -- op-dedupe
open _root_.ZInQ.Contrib.AbVarBC.MulRigidity (CotangentMulN KerUnitOpen KerUnitOpenOfCotangentSurj MulEtale MulUnramified O0 QuasiFiniteEndSurjective charZero_residueField cotangentMap diagonal_isPullback diffKer formallyUnramified_of_kerUnit isIsogenyMor_of_lqf_of_isOpenMap isOpenImmersion_of_section isProper_left kerUnit kerUnitOpen_of_cotangent kerUnitOpen_of_mulEtale locallyQuasiFinite_of_formallyUnramified map_origin mulIsogeny_of_cotangent mulIsogeny_of_kerUnitOpen mulIsogeny_of_mulEtale mulIsogeny_of_mulUnramified mulIsogeny_of_mulUnramified' mulUnramified_of_kerUnitOpen mulUnramified_of_mulEtale ne_of_specializes_of_lqf origin quasiFiniteEndSurjective stalkEndo surjective_of_lqf_self) -- op-dedupe
open _root_.ZInQ.Contrib.AbVarBC.G0FibreSimple (MulIsogeny) -- op-dedupe
set_option maxHeartbeats 1000000
attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
section G0A2_b20_fold
noncomputable section
namespace HSyn
open CategoryTheory AlgebraicGeometry G0Split
-- pi0-prune: copied from TailE.lean:6459-6490 (structure, docstring omitted)
structure OpenResearchLeaves2W : Prop where
  r1r2 : LeafAdopt.R1R2fpRepW
  /-- R1(b), concrete (family form), for the triple of the leaf bundle. -/
  r1b : ∀ h : LeafAdopt.R1R2fpRepW,
    G0Split.FibreQM.R1bFamily (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_repW h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_repW h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_repW h))
  r1rec : LeafQM.AV.R1rec
  r4 : PkgI1.ThetaModularity
  r5 : LeafQM.AV.R5fp
  r5count : LeafQM.AV.R5fpCount
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r8 : PkgI2.GrothendieckMonodromy.{0}
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  /-- R10 corrected (with multiplicity `0` off `{0, −1}`). -/
  r10 : PkgI4.DeRhamComparisonHT
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  /-- R14 corrected (with the determinant clause). -/
  r14 : G0Galois.R14Det
  r15 : DeligneSerreConseq
  r16 : LeafModCurves.R16_EichlerShimuraJ1'
  /-- R17, concrete (Carayol 1986, Thm (A)). -/
  r17 : LadicCond.CarayolR17'
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  /-- H5's finiteness half (its `NeronModelMinimal` half is proved, h5-glue). -/
  h5fin : ZInQ.DefFaltings.StableHeightFinite

-- pi0-prune: copied from TailE.lean:6569-6590
theorem researchLeaves3_of_open2W (r : OpenResearchLeaves2W) : ResearchLeaves3W where
  r1r2 := r.r1r2
  r1rec := r.r1rec
  r4 := r.r4
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r7a := r.r7a
  r8 := r.r8
  r9a := r.r9a
  r9b := r.r9b
  r10 := PkgI4.deRhamComparison_of_HT r.r10
  r11r12 := r.r11r12
  r13 := r.r13
  r14 := eigenformRepExists_of_r14Det r.r14
  r15 := r.r15
  r16 := r.r16
  r18 := r.r18
  r19 := r.r19
  r21 := r.r21
  r22 := r.r22
  h5fin := r.h5fin

end HSyn
end
end G0A2_b20_fold
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailK.lean` (base 43513d87) -/

namespace HDec
set_option maxHeartbeats 1000000
attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
section G0A2_d95_fold4
noncomputable section
namespace HSyn
open CategoryTheory AlgebraicGeometry G0Split
-- pi0-prune: copied from TailK.lean:282-342
/-- **Leaves.lean's `GluePieces` from leaf-fold4's open statements** (leaf-fold3's `gluePieces_of_open3`,
verbatim but for: the fields closed by leaf-fold4 replaced by their theorems above; T26 from T5
(`tateModuleFree_of_t5'`); `DetTate` from `detTate_of_leaves4`, i.e. without the leaf `DivisiblePoints`). -/
theorem gluePieces_of_open4W (r : OpenResearchLeaves2W) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeaves4) (g : OpenGlue4) (hYu : QMLattice.YuB6Alg) : GluePieces :=
  let t2 := textbookLeaves2_of_open3 (textbookLeaves3_of_open4 t)
  let r3 := researchLeaves3_of_open2W r
  let t3 := textbookLeaves_of_open2 t2
  have hMob : LeafQM.AV.Pin.MobiusGlue := mobiusGlue_of_t5' t.t5
  have hFS5 : G0FibreSimple.FibreComTrivial :=
    fibreComTrivial_of_full (FS5NoCM.fibreComTrivialFull_of_leaves'' (r1r2fpFull_ofW r3)
      hMob hYu t.t6 l.cmOptimalEmbedding (X6Kummer.x6KummerFibre_of_conic hMob l.x6ConicModel)
      r.r5count)
  have hFS : G0Split.FibreSimple :=
    G0FibreSimple.fibreSimple_of_leaves t3 hYu mulIsogeny_proved G0FibreSimple.rigidityHom
      ⟨G0FibreSimple.finiteDescends_proof, hFS5⟩
  { dimFinite := G0Split.dimFinite
    dimBaseChange := G0Split.dimBaseChange
    fibreSimple := hFS
    productModelHeight := ZInQ.ProductHeight.productModelHeight_of_splits productUnifSplits_proved
      (ZInQ.UnifDims.productMetrizationOfProductUnif_of_tangentDim t.t35 tangentDimAtOrigin_proved3)
    stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
      (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_glue4
        hodgeBCInjective_proved3 cotangentSpanBC_proved omegaBaseChange_proved3
        uniformizationLiftAnalytic_proved))
    productExists := G0Product.productExists
    reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3W r3 G0Split.dimFinite
    thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
      (G0Split.FibreQM.fibreQMPeriod_main_repW r.r1r2 hMob l.qmHauptmodul
        t.t35 t2.t11a l.qmClassNumberOne (r.r1b r.r1r2) (periodMapGlue_of_leaves4W r.r1r2 t.t5 t.homLatticeCorr l.cmDescends)
        hauptmodulUnique_proved4
        (qmDenZeroCM3_of_leaves4 r.r4 l.gammaStarGen l.valenceBoundGammaStar) cPtsTransport_proved3)
      l.thetaRatiosAlgebraic
    modularConstituent := modularConstituent_of_field t3
      (G0ModField.fibreCoverExists_of_propTSAll' t.t5
        (propTSAll_of_pieces3W r.r1r2 t.t5 l.y3Connected l.qmAutCard l.serreRigidity3 l.alFixedPoints
          chartProper_proved4 chartQuasiFinite_proved4 g.heckeVertWitness) unramifiedConjugates_proved)
      (G0ModField.KernelField.kernelFieldExists_of_split'' t.t6 r.r7a r.r6 t.t5 hYu
        hFS5 G0ModField.KernelField.oMaximal endTransport_proved conjIsogMaps_proved3)
      UnramTate.unramifiedSup_mf
      (G0AssembleMod.afterG7_of3W r3 t3
        ⟨burnsideAbsIrred_proved3, r.r14,
          g9Glue_of_deRhamComparisonHT r.r10,
          G0Galois.g10Glue_of_conjTwist
            (G0Galois.conjTwistNontrivial_of_leaves t.t5 (tateModuleFree_of_t5' t.t5) t.t35
              (HomUnify.homLinearLift_of_corr t.homLatticeCorr)),
          G0Galois.g12Weight_of_senTwist l.senTwist l.finiteImageHT,
          detTate_of_leaves4 l.t09SymmIsogenyExists l.isogenyQuasiInverse t.t5
            (tateModuleFree_of_t5' t.t5),
          G0AssembleMod.resQFiniteIndex⟩
        (g9GlueNoT23_of_deRhamComparisonHT r.r10)
        (G0ModNewform.dirichletOfFinite_of_t17 t17_proved) r.r17
        Swan.swanIndependent_proved Swan.swanIntegral_proved
        Swan.adaptedExists_proved
        (modelG3G6_of_leaves3 hFS r.r7a r.r6 t.t5)
        (G0AssembleMod.linkedTateData_of_local t.t7
          (linkedTateLocal_of_leaves3 r.r6 t.t5 (tateModuleFree_of_t5' t.t5)
            (abVarSpreadsOut_of_ega4 l.egaIV_8_8_2_ii l.egaIV_8_10_5_xii l.egaIV_17_7_8_ii)
            (properSmoothGenConnected_of_zariski4 l.zariskiConnectedness)
            t.t4 t.t3 hFS t.t6 hYu)))
    heightCopies := G0HeightCopies.heightCopiesAgree }

-- pi0-prune: copied from TailK.lean:344-355
/-- **G0 with only the open leaves and the open glue** (leaf-fold4; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from
* `OpenResearchLeaves2W`: 26 research-level fields (unchanged);
* `OpenTextbookLeaves4`: 19 textbook fields (T26 now from T5);
* `OpenAddedLeaves4`: 20 leaves (`DivisiblePoints` no longer needed);
* `OpenGlue4`: 1 glue Prop (`HeckeVertWitness`).
The table of every field is `docs/research/leaf-fold4.md` §2. -/
theorem sixContactMin_of_open4W (r : OpenResearchLeaves2W) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeaves4) (g : OpenGlue4) (h20 : G0Split.R20Lower) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_leavesR3W (researchLeaves3_of_open2W r)
    (textbookLeaves_of_open2 (textbookLeaves2_of_open3 (textbookLeaves3_of_open4 t)))
    (gluePieces_of_open4W r t l g hYu) h20

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
-- pi0-prune: copied from TailN.lean:66-97 (structure, docstring omitted)
structure OpenResearchLeaves5W : Prop where
  r1r2 : LeafAdopt.R1R2fpRepW
  /-- R1(b), concrete (family form), for the triple of the leaf bundle. -/
  r1b : ∀ h : LeafAdopt.R1R2fpRepW,
    G0Split.FibreQM.R1bFamily (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_repW h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_repW h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_repW h))
  r1rec : LeafQM.AV.R1rec
  r4 : PkgI1.ThetaModularity
  r5 : LeafQM.AV.R5fp
  r5count : LeafQM.AV.R5fpCount
  r6 : _root_.PkgI2.RaynaudCriterion.{0}
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r8 : _root_.PkgI2.GrothendieckMonodromy.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  /-- R10 corrected (with multiplicity `0` off `{0, −1}`). -/
  r10 : PkgI4.DeRhamComparisonHT
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  /-- R14 corrected (with the determinant clause). -/
  r14 : G0Galois.R14Det
  r15 : DeligneSerreConseq
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  /-- R17, concrete (Carayol 1986, Thm (A)). -/
  r17 : _root_.LadicCond.CarayolR17'
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  /-- H5's finiteness half (its `NeronModelMinimal` half is proved, h5-glue). -/
  h5fin : ZInQ.DefFaltings.StableHeightFinite

-- pi0-prune: copied from TailN.lean:99-123
/-- leaf-fold2's research bundle from leaf-fold5's. -/
theorem researchLeaves2_of_open5W (r : OpenResearchLeaves5W) : OpenResearchLeaves2W where
  r1r2 := r.r1r2
  r1b := r.r1b
  r1rec := r.r1rec
  r4 := r.r4
  r5 := r.r5
  r5count := r.r5count
  r6 := raynaudCriterion_ofK5 r.r6
  r7a := neronOggShafarevich_ofK5 r.r7a
  r8 := grothendieckMonodromy_ofK5 r.r8
  r9a := faltingsSemisimple_ofK5 r.r9a
  r9b := faltingsTate_ofK5 r.r9b
  r10 := r.r10
  r11r12 := r.r11r12
  r13 := r.r13
  r14 := r.r14
  r15 := r.r15
  r16 := eichlerShimuraJ1_ofK5 r.r16
  r17 := carayolR17_ofK5 r.r17
  r18 := r.r18
  r19 := r.r19
  r21 := r.r21
  r22 := r.r22
  h5fin := r.h5fin

end HSyn
end
end G0A2_e90_fold5
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailO.lean` (base 43513d87) -/

set_option linter.all false
noncomputable section
namespace HDec.HSyn
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
-- pi0-prune: copied from TailO.lean:2869-2873
/-- **`CMDescends` from Shimura–Taniyama** (leafq-check's `cmDescends_ofW`, with leaf-fold5's T11(b) and T5). -/
theorem cmDescends_of6W (r : OpenResearchLeaves5W) (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6) :
    G0Split.FibreQM.PeriodMapH.CMDescends :=
  G0Split.FibreQM.PeriodMapH.LeafQCheck.cmDescends_ofW l.stQM (t11b_of_exists5 t.t11bExists)
    (G0Split.FibreQM.PeriodMapH.LeafQCheck.torsionDescends_of_t5 (torsionStructure_ofK5 t.t5)) r.r1r2

-- pi0-prune: copied from TailO.lean:2875-2880
/-- **`QMHauptmodul` from `QMHauptmodulBase3`** (leafq-check's `base2_of_base3` and `qmHauptmodul_of_base2`:
R4, `GammaStarGen` (proved) and the valence bound (from the valence formula)). -/
theorem qmHauptmodul_of6W (r : OpenResearchLeaves5W) (l : OpenAddedLeaves6) : PkgI1.QMHauptmodul :=
  LeafQCheck.HM.qmHauptmodul_of_base2
    (LeafQCheck.HM.base2_of_base3 r.r4 LeafQCheck.gammaStarGen_proof
      (LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar) l.qmHauptmodulBase3)

-- pi0-prune: copied from TailO.lean:2882-2904
/-- leaf-fold4's added-leaves bundle from leaf-fold6's. -/
theorem addedLeaves4_of_open6W (r : OpenResearchLeaves5W) (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6) :
    OpenAddedLeaves4 where
  cmOptimalEmbedding := l.cmOptimalEmbedding
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodul := qmHauptmodul_of6W r l
  qmClassNumberOne := l.qmClassNumberOne
  senTwist := l.senTwist
  finiteImageHT := l.finiteImageHT
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  isogenyQuasiInverse := l.isogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := l.qmAutCard
  serreRigidity3 := serreRigidity3_of_T35_5 (uniformizationExists_ofK5 t.t35) (homLatticeCorr_ofK5 t.homLatticeCorr)
  alFixedPoints := l.alFixedPoints
  zariskiConnectedness := l.zariskiConnectedness
  cmDescends := cmDescends_of6W r t l
  gammaStarGen := LeafQCheck.gammaStarGen_proof
  valenceBoundGammaStar := LeafQCheck.VB.valenceBound_of_formula l.valenceFormulaGammaStar
  egaIV_8_8_2_ii := l.egaIV_8_8_2_ii
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := l.egaIV_17_7_8_ii

-- pi0-prune: copied from TailO.lean:2906-2911
/-- leaf-fold4's glue bundle from leaf-fold6's: `HeckeVertWitness` from leaves and `ModelCoordinateResidue`
(leaf-fold5's `heckeVertWitness_of_leaves5W`). -/
theorem glue4_of_open6W (r : OpenResearchLeaves5W) (t : OpenTextbookLeaves6) (l : OpenAddedLeaves6)
    (g : OpenGlue6) : OpenGlue4 where
  heckeVertWitness := heckeVertWitness_of_leaves5W l.shimuraGoodReduction r.r1r2 (torsionStructure_ofK5 t.t5)
    g.modelCoordinateResidue l.curveBijIso

-- pi0-prune: copied from TailO.lean:2913-2923
/-- **G0 with only the open leaves and the open glue** (leaf-fold6; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from
* `OpenResearchLeaves5W`: 26 research-level fields (leaf-fold5's bundle, unchanged; nine on the kernel's Props);
* `OpenTextbookLeaves6`: 21 textbook fields (T8 kept, on the kernel's Prop);
* `OpenAddedLeaves6`: 20 added leaves;
* `OpenGlue6`: 1 glue Prop (`ModelCoordinateResidue`).
The table of every field is `docs/research/leaf-fold6.md` §2. -/
theorem sixContactMin_of_open6W (r : OpenResearchLeaves5W) (t : OpenTextbookLeaves6)
    (l : OpenAddedLeaves6) (g : OpenGlue6) (h20 : G0Split.R20Lower) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open4W (researchLeaves2_of_open5W r) (textbookLeaves4_of_open6 t l) (addedLeaves4_of_open6W r t l)
    (glue4_of_open6W r t l g) h20 hYu

end HDec.HSyn
end

/-! ## Copied from `ZInQKernel/OneProof/H/TailX.lean` (base 43513d87) -/

namespace HDec
set_option maxHeartbeats 1000000
namespace HSyn
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
-- pi0-prune: copied from TailX.lean:71-108 (structure, docstring omitted)
structure OpenResearchLeaves7W : Prop where
  r1r2 : LeafAdopt.R1R2fpRepW
  /-- qm-split, H-20: Shimura 1967 Main Thm I on one fine witness, for every map `π : Y → P¹` (replaces `r1b`). -/
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  r1rec : LeafQM.AV.R1rec
  /-- qm-split, H-2: Igusa's `ψ₄` is a Siegel modular form of weight 4 (with `igusaChi10`, replaces `r4`). -/
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  /-- qm-split, H-2: Igusa's `χ₁₀` is a Siegel modular form of weight 10. -/
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r5 : LeafQM.AV.R5fp
  r5count : LeafQM.AV.R5fpCount
  r6 : _root_.PkgI2.RaynaudCriterion.{0}
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r8 : _root_.PkgI2.GrothendieckMonodromy.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  /-- hodge-split, H-8: the Hodge–Tate decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g` (Fontaine 1982; Tate 1967;
  Faltings 1988; with `deRhamH1AbVarT` and Tate's two theorems, replaces `r10`). -/
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  /-- hodge-split, H-8: `H¹_ét(A_F̄, ℚ_p) = Hom(V_p A, ℚ_p)` is de Rham (Faltings 1989; Tsuji 1999; Scholze 2013
  Cor. 1.8). -/
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  /-- hodge-split, H-10: Kato's theorem for newforms, transported to any semisimple attached `ρ` and dualized
  (replaces `r13`, which is the same for all normalized eigenforms; not a leaf: Kato's `V_f` is not definable). -/
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- hodge-split, H-22: Diamond–Shurman Thm 9.6.5 (`k ≥ 2`, Deligne; with `dsThm966`, replaces `r14`). -/
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  /-- hodge-split, H-22: Diamond–Shurman Thm 9.6.6 (`k = 1`, Deligne–Serre Thm 4.1). -/
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r15 : DeligneSerreConseq
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  h5fin : ZInQ.DefFaltings.StableHeightFinite

-- pi0-prune: copied from TailX.lean:189-215
/-- leaf-fold6's research bundle (`OpenResearchLeaves5W`) from leaf-fold7's. -/
theorem researchLeaves5_of_open7W (r : OpenResearchLeaves7W) (l : OpenAddedLeaves7) : OpenResearchLeaves5W where
  r1r2 := r.r1r2
  r1b := QMSplit.Moduli.r1b_of'W r.shimuraFamily
  r1rec := r.r1rec
  r4 := QMSplit.Theta.thetaModularity_of r.igusaPsi4 r.igusaChi10
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r7a := r.r7a
  r8 := r.r8
  r9a := r.r9a
  r9b := r.r9b
  r10 := HodgeLF7.r10 (_root_.ZInQ.Contrib.HodgeSplit.deRhamComparisonHT_of_leavesT r.hodgeTateDecompAbVar
    l.tateTwistInvariants l.axSenTate r.deRhamH1AbVarT)
  r11r12 := r.r11r12
  r13 := HodgeLF7.eigenformHT (_root_.ZInQ.Contrib.HodgeSplit.eigenformHT_of_kato_ds r.eigenformHTNew
    HodgeLF7.newformOfEigenformG9 r.dsThm965 r.dsThm966)
  r14 := HodgeLF7.r14Det (_root_.ZInQ.Contrib.HodgeSplit.r14Det_of_printed r.dsThm965 r.dsThm966)
  r15 := r.r15
  r16 := r.r16
  r17 := r.r17
  r18 := r.r18
  r19 := r.r19
  r21 := r.r21
  r22 := r.r22
  h5fin := r.h5fin

-- pi0-prune: copied from TailX.lean:244-268
/-- leaf-fold6's added bundle from leaf-fold7's. -/
theorem addedLeaves6_of_open7W (r : OpenResearchLeaves7W) (t : OpenTextbookLeaves7) (l : OpenAddedLeaves7) :
    OpenAddedLeaves6 where
  cmOptimalEmbedding := (qmRows_of7 t l).2.2
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodulBase3 := l.qmHauptmodulBase3
  qmClassNumberOne := QMSplit.CNO.qmClassNumberOne_proof
  senTwist := HodgeLF7.senTwist (_root_.ZInQ.Contrib.HodgeSplit.senTwist_of_tate l.tateTwistInvariants l.axSenTate)
  finiteImageHT :=
    HodgeLF7.finiteImageHT (_root_.ZInQ.Contrib.HodgeSplit.finiteImageHT_of_tate l.tateTwistInvariants l.axSenTate)
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  isogenyQuasiInverse := isogenyQuasiInverse_lf7 l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  qmAutCard := (qmRows_of7 t l).1
  alFixedPoints := (qmRows_of7 t l).2.1
  zariskiConnectedness := l.zariskiConnectedness
  stQM := stQM_lf7 l.shimuraTaniyamaQbar
  valenceFormulaGammaStar := l.valenceFormulaGammaStar
  egaIV_8_8_2_ii := l.egaIV_8_8_2_ii
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := l.egaIV_17_7_8_ii
  shimuraGoodReduction := CurveSplitGR.shimuraGoodReduction_of_noGuard (LeafAdopt.R1R2fp_of_repW r.r1r2)
    l.shimuraGoodReductionNoGuard
  curveBijIso := curveBijIso_lf7

-- pi0-prune: copied from TailX.lean:274-280
/-- **G0 with only the open leaves and the open glue** (leaf-fold7; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves7W` (29), `OpenTextbookLeaves7` (23), `OpenAddedLeaves7` (16)
and `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is `docs/research/leaf-fold7.md` §2. -/
theorem sixContactMin_of_open7W (r : OpenResearchLeaves7W) (t : OpenTextbookLeaves7) (l : OpenAddedLeaves7)
    (g : OpenGlue7) (h20 : G0Split.R20Lower) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open6W (researchLeaves5_of_open7W r l) (textbookLeaves6_of_open7 t l) (addedLeaves6_of_open7W r t l)
    (glue6_of_open7 g) h20 hYu

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ4.lean` (base 43513d87) -/

namespace HDec
set_option maxHeartbeats 1000000
namespace HSyn
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
-- pi0-prune: copied from TailZ4.lean:66-102 (structure, docstring omitted)
structure OpenResearchLeaves8W : Prop where
  r1r2 : LeafAdopt.R1R2fpRepW
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  r1rec : LeafQM.AV.R1rec
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r5 : LeafQM.AV.R5fp
  r5count : LeafQM.AV.R5fpCount
  r6 : _root_.PkgI2.RaynaudCriterion.{0}
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r8 : _root_.PkgI2.GrothendieckMonodromy.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r15 : DeligneSerreConseq
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, SS1: Grothendieck's semistable reduction theorem, global form (SGA 7 IX 3.6). -/
  semistableReductionThm : _root_.ZInQ.HeightSplit.SemistableReductionThm
  /-- height-split, SS2: base change of the identity component in the semistable case (SGA 7 IX 3.3). -/
  semistableNeronBaseChange : _root_.ZInQ.HeightSplit.SemistableNeronBaseChange
  /-- height-split, SS3: semistability persists under finite extension (SGA 7 IX 3.3). -/
  semistablePersists : _root_.ZInQ.HeightSplit.SemistablePersists
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.BostLowerBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14

-- pi0-prune: copied from TailZ4.lean:151-170
/-- **The five height rows other than R20** (sem-prune), from the fields `heightRows_of8` reads except
`faltingsLemma5BC`: the proofs of `ZInQ.HeightSplit.heightRows_of`'s other components. -/
theorem heightRowsNo20_of8W (r : OpenResearchLeaves8W) (t : OpenTextbookLeaves8) :
    _root_.ZInQ.LeafPush2.R18_Javanpeykar ∧ _root_.ZInQ.DefFaltings.R19_GaudronRemond ∧
      _root_.ZInQ.DefFaltings.R21_Bost ∧ _root_.ZInQ.LeafPush2.R22_Pazuki ∧
      _root_.ZInQ.DefFaltings.StableHeightFinite :=
  have hN1 := _root_.ZInQ.Contrib.NeronC.neronModelExists_of_extension t.neronSchemeExtensionExists
  have gl := _root_.ZInQ.HeightGlue.heightGlue_of_t35
    (_root_.AvSplit.Final.h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed)
  have hMet := _root_.ZInQ.HeightSplit.neronMetrizable_of gl.an3Exists gl.unifDim gl.metrize
  ⟨_root_.ZInQ.HeightSplit.r18_of_leaves r.javanpeykarBound hN1 r.semistableReductionThm
      r.semistableNeronBaseChange hMet,
    _root_.ZInQ.HeightSplit.r19_of_leaves r.gaudronRemondThm14 hN1 r.semistableReductionThm
      r.semistableNeronBaseChange,
    _root_.ZInQ.HeightSplit.r21_of_leaves' r.bostLowerBound hN1 r.semistableReductionThm
      r.semistableNeronBaseChange gl.an3Unique,
    _root_.ZInQ.HeightSplit.r22_of_upper r.pazukiCor13Upper hN1 r.semistableReductionThm
      r.semistableNeronBaseChange,
    _root_.ZInQ.HeightSplit.stableHeightFinite_of' hN1 r.semistableReductionThm r.semistableNeronBaseChange
      hMet gl.an3Unique⟩

-- pi0-prune: copied from TailZ4.lean:172-178
/-- **The lower half of R20** (sem-prune) from the lower half of `faltingsLemma5BC` and the fields
`heightRows_of8` uses for R20 (N1 from `neronSchemeExtensionExists`, SS1, SS2, SS3). -/
theorem r20Lower_of8W (r : OpenResearchLeaves8W) (t : OpenTextbookLeaves8)
    (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) : G0Split.R20Lower :=
  _root_.ZInQ.HeightSplit.r20Lower_of_leaves' hF5
    (_root_.ZInQ.Contrib.NeronC.neronModelExists_of_extension t.neronSchemeExtensionExists)
    r.semistableReductionThm r.semistableNeronBaseChange r.semistablePersists

-- pi0-prune: copied from TailZ4.lean:180-207
/-- leaf-fold7's research bundle from leaf-fold8's. -/
theorem researchLeaves7_of_open8W (r : OpenResearchLeaves8W) (t : OpenTextbookLeaves8) : OpenResearchLeaves7W where
  r1r2 := r.r1r2
  shimuraFamily := r.shimuraFamily
  r1rec := r.r1rec
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r7a := r.r7a
  r8 := r.r8
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  dsThm965 := r.dsThm965
  dsThm966 := r.dsThm966
  r15 := r.r15
  r16 := r.r16
  r17 := r.r17
  r18 := r18_lf8 (heightRowsNo20_of8W r t).1
  r19 := (heightRowsNo20_of8W r t).2.1
  r21 := (heightRowsNo20_of8W r t).2.2.1
  r22 := r22_lf8 (heightRowsNo20_of8W r t).2.2.2.1
  h5fin := (heightRowsNo20_of8W r t).2.2.2.2

-- pi0-prune: copied from TailZ4.lean:231-251
/-- leaf-fold7's added bundle from leaf-fold8's. -/
theorem addedLeaves7_of_open8W (r : OpenResearchLeaves8W) (l : OpenAddedLeaves8) : OpenAddedLeaves7 where
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmHauptmodulBase3 := LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of_leaves
    (QMSplit.Theta.thetaModularity_of r.igusaPsi4 r.igusaChi10) l.valenceFormulaCocompactEq l.shimizuCovolumeO1
    l.igusaCMValue24
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  zariskiConnectedness := _root_.ZariskiConn.ZariskiConnectedness_proof.{0}
  shimuraTaniyamaQbar := l.shimuraTaniyamaQbar
  valenceFormulaGammaStar :=
    LeafQCheck.HM.QMSplit.valenceFormulaGammaStar_of_leaves l.valenceFormulaCocompactEq l.shimizuCovolumeO1
  egaIV_8_8_2_ii := _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii_proof
  shimuraGoodReductionNoGuard := l.shimuraGoodReductionNoGuard

-- pi0-prune: copied from TailZ4.lean:253-260
/-- **G0 with only the open leaves and the open glue** (leaf-fold8; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves8W` (31), `OpenTextbookLeaves8` (20), `OpenAddedLeaves8` (14)
and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold8.md` §2. -/
theorem sixContactMin_of_open8W (r : OpenResearchLeaves8W) (t : OpenTextbookLeaves8) (l : OpenAddedLeaves8)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open7W (researchLeaves7_of_open8W r t) (textbookLeaves7_of_open8 t) (addedLeaves7_of_open8W r l) g
    (r20Lower_of8W r t hF5) hYu

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ9.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
open CategoryTheory AlgebraicGeometry Limits
-- pi0-prune: copied from TailZ9.lean:25-66 (structure, docstring omitted)
structure OpenResearchLeaves9W : Prop where
  r1r2 : LeafAdopt.R1R2fpRepW
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r6 : _root_.PkgI2.RaynaudCriterion.{0}
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, SS1: Grothendieck's semistable reduction theorem, global form (SGA 7 IX 3.6). -/
  semistableReductionThm : _root_.ZInQ.HeightSplit.SemistableReductionThm
  /-- height-split, SS2: base change of the identity component in the semistable case (SGA 7 IX 3.3). -/
  semistableNeronBaseChange : _root_.ZInQ.HeightSplit.SemistableNeronBaseChange
  /-- height-split, SS3: semistability persists under finite extension (SGA 7 IX 3.3). -/
  semistablePersists : _root_.ZInQ.HeightSplit.SemistablePersists
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.BostLowerBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Thm 3.6 over a DVR (semistable reduction after a finite extension, at every place
  above `O`). -/
  semistableReductionDVR : _root_.ReductSplit.SemistableReductionDVR
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest reading). -/
  semistableUnipotent : _root_.ReductSplit.SemistableUnipotent
  /-- reduct-split, r8: BLR §1.4 Thm 3 over a DVR (scheme form). -/
  neronSchemeModelExistsDVR : _root_.ReductSplit.NeronSchemeModelExistsDVR
  /-- shimura-split, r5count: González–Rotger 2006 Prop. 5.6 at `(D, N) = (6, 1)` on the points of one canonical
  coarse witness `X₆` (`#CM(R) = 2^{b(k)} h(R)`; the audit read Prop. 5.6). -/
  gonzalezRotgerCountX6 : _root_.ShimuraSplit.GonzalezRotgerCountX6

-- pi0-prune: copied from TailZ9.lean:88-118
/-- leaf-fold8's research bundle from leaf-fold9's. -/
theorem researchLeaves8_of_open9W (r : OpenResearchLeaves9W) (t : OpenTextbookLeaves9) : OpenResearchLeaves8W where
  r1r2 := r.r1r2
  shimuraFamily := r.shimuraFamily
  r1rec := r1rec_of_repW r.r1r2
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r5 := r5fp_of_repW r.r1r2
  r5count := _root_.ShimuraSplit.r5fpCount_of_points r.gonzalezRotgerCountX6
  r6 := r.r6
  r7a := r.r7a
  r8 := _root_.ReductSplit.grothendieckMonodromy_final' r.semistableReductionDVR r.semistableUnipotent
    r.neronSchemeModelExistsDVR t.mumfordTorsionAlgClosed
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  dsThm965 := r.dsThm965
  dsThm966 := r.dsThm966
  r15 := _root_.ModularSplit.deligneSerreConseq_of_ds r.dsThm966
  r16 := r.r16
  r17 := r.r17
  semistableReductionThm := r.semistableReductionThm
  semistableNeronBaseChange := r.semistableNeronBaseChange
  semistablePersists := r.semistablePersists
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14

-- pi0-prune: copied from TailZ9.lean:139-145
/-- **G0 with only the open leaves and the open glue** (leaf-fold9; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves9W` (30), `OpenTextbookLeaves9` (18), leaf-fold8's
`OpenAddedLeaves8` (14) and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold9.md` §2. -/
theorem sixContactMin_of_open9W (r : OpenResearchLeaves9W) (t : OpenTextbookLeaves9) (l : OpenAddedLeaves8)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open8W (researchLeaves8_of_open9W r t) (textbookLeaves8_of_open9 t) l g hF5 hYu

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ11.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ11.lean:51-57
/-- **G0 with only the open leaves and the open glue** (leaf-fold10; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from leaf-fold9's `OpenResearchLeaves9W` (30), `OpenTextbookLeaves10` (17),
leaf-fold8's `OpenAddedLeaves8` (14) and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every
field is `docs/research/leaf-fold10.md` §2. -/
theorem sixContactMin_of_open10W (r : OpenResearchLeaves9W) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves8)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open9W r (textbookLeaves9_of_open10 t) l g hF5 hYu

end HSyn
end HDec

/-! ## Copied from `ZInQKernel/OneProof/H/TailZ13.lean` (base 43513d87) -/

namespace HDec
namespace HSyn
-- pi0-prune: copied from TailZ13.lean:64-70
/-- **G0 with only the open leaves and the open glue** (leaf-fold10; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from leaf-fold9's `OpenResearchLeaves9W` (30), `OpenTextbookLeaves10` (17),
`OpenAddedLeaves9` (14) and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold10.md` §2. -/
theorem sixContactMin_of_open11W (r : OpenResearchLeaves9W) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves9)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=
  sixContactMin_of_open10W r t (addedLeaves8_of_open9 l) g hF5 hYu

end HSyn
end HDec

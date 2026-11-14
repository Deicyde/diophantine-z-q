import ZInQKernel.OneProof.H.TailF
import ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral
import ZInQKernel.Contrib.SpreadOut.NumberField
import ZInQKernel.Contrib.UnramRoots.Main

namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

section G0A3_z80_leaves3
/-! ## g0-assemble2: `ResearchLeaves3`, the research bundle without placeholders

`HSyn.ResearchLeaves` (Leaves.lean) has two fields whose types are `opaque` placeholders,
`r1an : R01b_ComplexUniformization` and `r17 : R17_Carayol`: no proof of them can exist, so the
bundle cannot be inhabited, and neither of them is used by any proof. `ResearchLeaves3` is the
same structure (field names, types and docstrings copied) without these two fields, and with
`h5 : LeafAdopt.H5 = StableHeightFinite ∧ NeronModelMinimal` replaced by its first half
`h5fin` (the second is proved by h5-glue, part a90). Their concrete replacements are fields of
`GluePieces3`: `carayolR17 : LadicCond.CarayolR17'` and `r1bFamily` (fibre-qm-period).

The seven consumers of `r : ResearchLeaves` on the route are copied below with `r : ResearchLeaves3`
(names suffixed `3`); their proofs are the originals', verbatim (they use `r` only through
fields, and `r.h5` is `ResearchLeaves3.h5` below). -/

noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

/-- **The research-level leaves, without placeholders** (g0-assemble2; see above). -/
structure ResearchLeaves3 : Prop where
  /-- R1 (a), (c), (d), `π₀(X₆) = 1` (rv-blueprints Q4), R1 at level one, R2 with biconditional CM
  clauses (Q5) and R5 on points of `X₆`, on one `Y₃`, `X₆` (leaf-qm-fp, repaired by leaf-adopt).
  Premise (rv-qm-polar Lemma P): for a QM pair `(A, ι)` in characteristic 0 there is exactly one
  principal polarization whose Rosati involution is `x ↦ μ⁻¹x̄μ` on `ι(𝒪)` (`μ = 2j + ij`, the
  type fixed by the PEL datum); see the definition. Checked by model reviews (rv-qm-polar), no
  human review. -/
  r1r2 : LeafAdopt.R1R2fpRep
  -- (g0-assemble2) `r1an : R01b_ComplexUniformization` (an `opaque` placeholder) removed: unused;
  -- its concrete family form is `GluePieces3.r1bFamily` (fibre-qm-period).
  /-- R1(d), Shimura reciprocity, object form (leaf-qm-fp; premise Lemma P, rv-qm-polar). -/
  r1rec : LeafQM.AV.R1rec
  /-- R3, Lin–Yang over `ℂ`, existential and polarization-free (leaf-push2; premise Lemma P). -/
  r3 : ZInQ.LeafPush2.R03_LinYang
  r4 : PkgI1.ThetaModularity
  /-- R5(ii), González–Rotger Thm 5.12, fields of moduli (= rv-blueprints' R5fpStrong, Q2;
  premise Lemma P, rv-qm-polar). -/
  r5 : LeafQM.AV.R5fp
  /-- R5(i), González–Rotger Prop. 5.6, `#CM(R) = 2^b h(R)` (premise Lemma P, rv-qm-polar). -/
  r5count : LeafQM.AV.R5fpCount
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
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
  r20 : ZInQ.DefFaltings.R20_FaltingsLemma5
  r21 : ZInQ.DefFaltings.R21_Bost
  /-- R22, Pazuki's upper half, over all uniformizations and period matrices (leaf-push2). -/
  r22 : ZInQ.LeafPush2.R22_Pazuki
  /-- H5's finiteness half (rv-blueprints F2): the stable height is finite (g0-assemble2: the
  other half, `NeronModelMinimal`, is proved by h5-glue, `ZInQ.H5Glue.neronModelMinimal`). -/
  h5fin : ZInQ.DefFaltings.StableHeightFinite


/-- H5 from its finiteness half and h5-glue's `NeronModelMinimal`. -/
theorem ResearchLeaves3.h5 (r : ResearchLeaves3) : LeafAdopt.H5 :=
  ⟨r.h5fin, ZInQ.H5Glue.neronModelMinimal⟩

/-- `ResearchLeaves3` is weaker than `ResearchLeaves`. -/
theorem researchLeaves3_of (r : ResearchLeaves) : ResearchLeaves3 :=
  { r1r2 := r.r1r2,
    r1rec := r.r1rec,
    r3 := r.r3,
    r4 := r.r4,
    r5 := r.r5,
    r5count := r.r5count,
    r6 := r.r6,
    r7a := r.r7a,
    r7b := r.r7b,
    r8 := r.r8,
    r9a := r.r9a,
    r9b := r.r9b,
    r10 := r.r10,
    r11r12 := r.r11r12,
    r13 := r.r13,
    r14 := r.r14,
    r15 := r.r15,
    r16 := r.r16,
    r18 := r.r18,
    r19 := r.r19,
    r20 := r.r20,
    r21 := r.r21,
    r22 := r.r22,
    h5fin := r.h5.1 }

end HSyn

namespace HSyn.G0RevIsog

theorem reverseIsogeny_of_leaves3 (r : HSyn.ResearchLeaves3) (hDimF : G0Split.DimFinite) :
    G0Split.ReverseIsogeny :=
  reverseIsogeny_of_exists (isogenyReverseExists_of_r19 r.r19 r.h5.1 hDimF)

end HSyn.G0RevIsog

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

theorem g8_g12_of_leaves3 (r : HSyn.ResearchLeaves3) (t : HSyn.TextbookLeaves) (m : GaloisPieces)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3 : G3Out A 5 T)
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β : PkgI4.GQ → PadicAlgCl 5)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7 : G7Out A 5 Tm c ε a β u) :
    ∃ r₅ : GaloisRep 5 2, G8Out A 5 (GlueDescent.rho Tm a β) r₅ ∧ G9Out r₅ ∧ G10Out r₅ ∧
      G11Out T r₅ ∧ G12Out r₅ :=
  g8_g12 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t23 t.t11a t.t11b
    r.r11r12 r.r14 r.r13 r.r15 t.frobeniusDense HSyn.t19_proved t.t9 (g8Matrix_of_burnside m.burnside) m.deRham m.odd m.weight
    (g12Det_of m.r14det m.detTate m.finIndex (frobeniusDenseQ_of t.frobeniusDense))
    A T h2 h6 h3 Tm c ε a β u h7

end G0Galois

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField

theorem newformLeaves_of3 (r : ResearchLeaves3) (t : TextbookLeaves)
    (hCar : LadicCond.CarayolR17') : G0ModNewform.NewformLeaves :=
  ⟨C9Rhof.eigenformTwist_of_hsyn t.t24, t.t25, C9Rhof.eigenformRepExists_of_hsyn r.r14, r.r16,
    hCar, r.r9a, r.r9b, t.t26, C9Rhof.frobeniusDense_of_hsyn t.frobeniusDense,
    TSkolemKW.C10.brauerNesbittChar0'⟩

theorem afterG7_of3 (r : ResearchLeaves3) (t : TextbookLeaves) (m : G0Galois.GaloisPieces)
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
    G0Galois.g8_g12_of_leaves3 r t m _ (T u) h2 h6 h3₅ Tm₅ c₅ ε₅ a₅ β₅ u₅ h7₅
  obtain ⟨r₃, h8₃, -, -, h11₃⟩ :=
    G0Galois.g8_g11 r.r9a r.r9b t.t26 t.t6 HSyn.G0Split.semisimpleBaseChange r.r10 t.t23 t.t11a
      t.t11b (G0Galois.g8Matrix_of_burnside m.burnside) m.deRham m.odd _ (T u) h2 h6 3 h3₃
      Tm₃ c₃ ε₃ a₃ β₃ u₃ h7₃
  obtain ⟨i, ιC, ι5, hspec⟩ := G0ModNewform.g12Spec_of_galois hDF _ _ _ r₅ r₃ h8₅ h8₃ h12
  obtain ⟨ι3, h14, h15⟩ := hlink r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ :=
    G0ModNewform.modularConstituent_tail_G (newformLeaves_of3 r t hCar) t.t33 t.x1ModelExists
      hSw hL8 hAd _ u ⟨_, hspec ι3, h14, g15RamG_of_wild _ u h15 h11₅ h11₃⟩
  exact ⟨M, J, hM, hJ, hMle, (commonConstituent_copy' _ _).1 hCC⟩

end HSyn.G0AssembleMod

namespace HSyn

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

theorem hom_of_common3 (r : ResearchLeaves3) (t : TextbookLeaves) {K : Type} [Field K]
    [NumberField K] (A J : PkgI3.AbVar K) (h : CommonConstituent A J) :
    ∃ f : PkgI3.AbVar.Hom A J, f ≠ 0 := by
  obtain ⟨ℓ, _, E, _, _, U, U', e, hU, he⟩ := h
  exact PkgI3.E1_exists_hom_ne_zero r.r9a r.r9b t.t26 semisimpleBaseChange A J ℓ E U U' hU e he

end G0Split

open G0Split in
theorem glueOutputs_of_leaves3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces) :
    GlueAssembly.GlueOutputs ZInQ.Mult.S_mul := by
  obtain ⟨hDimF, hDim, hSimp, hPMH, hBC, hProdE, hRev, hThetaPt, hMod, hCopies⟩ := gp
  have hBelyi : X1BelyiOnModel := x1BelyiOnModel_of_belyiX1 t.belyiX1
  have hAdd : HeightAdditivity := heightAdditivity_of_h5neron t.t41 r.h5.2 hPMH
  have hR18 : R18_JavanpeykarConcrete := r18Concrete_of r.r18 hCopies
  have hR22 : R22_PazukiConcrete := r22Concrete_of r.r22 hCopies
  -- A4: the moduli data and an object over every value
  obtain ⟨Y, Φ, π, h1, h2, hfib⟩ :=
    LeafQM.AV.exists_fibre_object (LeafAdopt.R1R2fp_of_rep r.r1r2)
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
  obtain ⟨f, hf⟩ := hom_of_common3 r t _ _ hCC
  -- G5-G6 (missing piece 4, `FibreSimple`): `A` simple; T8: Poincaré
  obtain ⟨Z, g, hisoZ⟩ := t.t8 L.K _ _ (hSimp Y Φ π h1 h2 u hu L A hFib) f hf
  -- G17 after Poincaré (`isogenousProduct`, from missing pieces 1, 7, 8): `A × Z`, the isogeny `J₁(N)_{L'} → A × Z`
  obtain ⟨Pr, φ, hφ, hPprod, hdims⟩ :=
    isogenousProduct hDimF hProdE hRev L.K _ _ _ f g hisoZ
  -- E2: `dim J₁(N) ≤ N²`
  obtain ⟨gJ, hgJ, hgN⟩ := LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1
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
  have hJb := javanpeykarJ1 hR18 hBelyi t.t34 N hN0 J hJ1 gJ hgJ (by omega) _
    (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hgN' : (gJ : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  -- E3-E4 (proved from R19-R21)
  exact transfer_core r.r19 r.r20 r.r21 (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) Pr A
    ((LeafAdopt.abVarEquiv L.K).symm Z) gJ gZ hJLd hZd (by omega) (by omega) φ hφ _ _ _ _ hxJ hyP
    hzZ hadd hN1 hNQ hJb hgN' hdQ

/-- **G0 with `ResearchLeaves3`** (`sixContactMin_of_leaves` of Leaves.lean, copied). -/
theorem sixContactMin_of_leavesR3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces) :
    ZInQ.SixContactMin :=
  sixContactMin_of_glueOutputs (glueOutputs_of_leaves3 r t gp)

end HSyn

end

end G0A3_z80_leaves3

section G0A3_z85_modelg3g6
/-! ## g0-assemble2: g0-assemble's `ModelG3G6` split
-- (g0-assemble3: `hD.2^11` → `hD.2^11.1` (1×), for G7Data's added last clause `[L:ℚ] ≤ D`)

`ModelG3G6` (part 87) asks, on G7's model `A_{L'}`: `G6Out` (`End` a division ring, and
noncommutative) and `G3Out` at `ℓ = 5, 3`. The division-ring half is NoCM on the model; it follows
from g0-split's piece `FibreSimple` (which `GluePieces3` already supplies through FS5), because
G7's model is a `FibreOver` of the fibre context (G7Data's last clause `IsModelOver`). What remains
is split into two smaller glue Props. -/

noncomputable section

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **Glue: `End(A_{L'})` is noncommutative** on G7's model (g0-assemble2). Elementary given the QM
structure of `IsQMModel` (`ι(𝒪) ⊆ End(PK.A)`, base change `End(PK.A) → End(A_{L'})`, unram-tate's
`endBaseChange`, and `[24] ≠ 0`); not formalized. No NoCM content. -/
def ModelNoncomm : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∃ x y : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')), x * y ≠ y * x

/-- **Glue G3 on G7's model** (g0-assemble2; the G3 half of `ModelG3G6`): inertia at primes outside
`T(u)` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A_{L'})`, `ℓ = 5, 3` (good reduction of the QM model away from
`T`, `QML3.goodReduction`, with Néron–Ogg–Shafarevich R7a). -/
def ModelG3 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 (T u) ∧
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 (T u)

/-- **`ModelG3G6` from `FibreSimple`, `ModelNoncomm` and `ModelG3`** (g0-assemble2). The
`EndDivision` clause of G6 is `FibreSimple` at the `FibreOver` given by G7Data's `IsModelOver`. -/
theorem modelG3G6_of (hFS : G0Split.FibreSimple) (hNC : ModelNoncomm) (hG3 : ModelG3) :
    ModelG3G6 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨h1, h2, hu, y, hy, hπ⟩ := hctx
  have hdiv := hFS Y Φ π h1 h2 u hu ⟨L'⟩
    ((LeafAdopt.abVarEquiv L').symm (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')))
    ⟨algebraMap L' Qbar, y, P, hy, hπ, hD.2.2.2.2.2.2.2.2.2.2.2.1⟩
  rw [Equiv.apply_symm_apply] at hdiv
  obtain ⟨g5, g3⟩ := hG3 Y Φ π u P ⟨h1, h2, hu, y, hy, hπ⟩ L A ε N χ β L' hLL' hD
  exact ⟨⟨hdiv, hNC Y Φ π u P ⟨h1, h2, hu, y, hy, hπ⟩ L A ε N χ β L' hLL' hD⟩, g5, g3⟩

end HSyn.G0AssembleMod

end

end G0A3_z85_modelg3g6

section G0A3_z86_noncomm
/-! ## g0-assemble2: `ModelNoncomm` proved from `MulIsogeny`
-- (g0-assemble3: `hD.2^11` → `hD.2^11.1` (1×), for G7Data's added last clause `[L:ℚ] ≤ D`)

On G7's model `A_{L'} = (PK.A)_{L'}` (`IsQMModel`), let `ψ : 𝒪 → End(A_{L'})` be `ι` followed by
unram-tate's base-change ring maps `endBC`. If `ψ(i)` and `ψ(j)` commuted, then `ij = -ji` would give
`2·ψ(j)ψ(i) = 0`, hence `12 = 2·ψ(j)²·ψ(i)² = 0` in `End(A_{L'})` (`i² = 2`, `j² = -3`). But
`[12]` is an isogeny (`MulIsogeny`), so `0 = [12]` would be surjective; it factors through
`Spec L'` (a point), so `A_{L'}` would be a point, while `dim A_{L'} = 2` (`model_dim`). -/

noncomputable section

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- An abelian variety of dimension `2` is not a point: the zero endomorphism (`1` in the
convolution monoid, `toUnit ≫ η`) is not surjective. -/
theorem not_surjective_zero_hom {K : Type} [Field K] (A : PkgI3.AbVar K) (hA : A.dim = 2) :
    ¬ Surjective ((0 : PkgI3.AbVar.End A).hom).left := by
  intro hs
  have hsub : Subsingleton A.X.left := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hs.surj a
    obtain ⟨b', rfl⟩ := hs.surj b
    have h0 : ((0 : PkgI3.AbVar.End A).hom) = toUnit A.X ≫ η[A.X] := rfl
    rw [h0, Over.comp_left, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    congr 1
    haveI : Subsingleton (PrimeSpectrum K) := inferInstance
    exact Subsingleton.elim (α := PrimeSpectrum K) _ _
  have hle := topologicalKrullDim_zero_of_discreteTopology A.X.left
  have h2 : topologicalKrullDim A.X.left = 2 := hA
  rw [h2] at hle
  exact absurd hle (by decide)

/-- **`ModelNoncomm` is proved** from g0-fibresimple's `MulIsogeny` (here from mul-rigidity's leaf
`MulEtale`) and g0-dim's proved `DimBaseChange`. -/
theorem modelNoncomm_of_mulIsogeny (hMul : G0FibreSimple.MulIsogeny) : ModelNoncomm := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  haveI : CharZero L' := charZero_of_injective_algebraMap (algebraMap ℚ L').injective
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 :=
    G0Split.model_dim G0Split.dimBaseChange (algebraMap L' Qbar)
      ((LeafAdopt.abVarEquiv L').symm (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')))
      P.A hD.2.2.2.2.2.2.2.2.2.2.2.1 P.surface
  obtain ⟨K, hKL, PK, -, rfl⟩ := hD.1
  set ψ : LeafQM.O →+* PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) :=
    (@UnramTate.endBC L _ _ L' _ (incAlg hLL')).comp
      ((@UnramTate.endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) with hψ
  refine ⟨ψ UnramTate.iO, ψ UnramTate.jO, fun h => ?_⟩
  set x := ψ UnramTate.jO
  set y := ψ UnramTate.iO
  have hy2 : y * y = 2 := by
    rw [← map_mul, UnramTate.iO_sq, map_add, map_one]; norm_num
  have hx2 : x * x = -3 := by
    rw [← map_mul, UnramTate.jO_sq, map_neg, map_add, map_add, map_one]; norm_num
  have hanti : y * x = -(x * y) := by
    rw [← map_mul, ← map_mul, UnramTate.iO_jO, map_neg]
  have hxy : x * y = -(x * y) := h.symm.trans hanti
  have h2 : (2 : PkgI3.AbVar.End _) * (x * y) = 0 := by
    rw [two_mul]; nth_rewrite 2 [hxy]; exact add_neg_cancel _
  have h3 : x * ((2 : PkgI3.AbVar.End _) * (x * y)) * y = 0 := by rw [h2, mul_zero, zero_mul]
  have h4 : x * ((2 : PkgI3.AbVar.End _) * (x * y)) * y = 2 * (x * x) * (y * y) := by
    noncomm_ring
  rw [h4, hx2, hy2] at h3
  have h12 : ((12 : ℤ) : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) = 0 := by
    have : (2 : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) * -3 * 2 =
        -((12 : ℤ) : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) := by
      push_cast; norm_num
    rw [this, neg_eq_zero] at h3
    exact h3
  have hiso := hMul L' (@PkgI3.AbVar.baseChange L _
    (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) 12 (by norm_num)
  rw [h12] at hiso
  exact not_surjective_zero_hom _ hdim hiso.2

end HSyn.G0AssembleMod

end

end G0A3_z86_noncomm

section G0A3_z90_bundle3
/-! ## g0-assemble2: `GluePieces` from `GluePieces3`

Task g0-assemble2, 2026-11-13. g0-assemble's `GluePieces2` (27 fields) with every wave-27 result
applied (parts a10-a80 above). Each field of `GluePieces3` is a named `def … : Prop` of a wave-26
or wave-27 task, copied verbatim in that task's part; kinds and sources are in
`docs/research/g0-assemble2.md` §2 (LEAF = published theorem, LEAF? = leaf candidate, GLUE = to be
proved by the project). -/

noncomputable section

namespace HSyn

open G0Split

/-- **The named Props left after waves 26-27** (g0-assemble2). -/
structure GluePieces3 : Prop where
  -- FibreSimple (FS1-FS5)
  /-- mul-rigidity, LEAF (Mumford §4 Appl. 2, §6; Milne Thm 8.2, char 0; UNVERIFIED locators):
  `[n]` is étale for `n ≠ 0`. -/
  mulEtale : MulRigidity.MulEtale
  /-- fs5-nocm N1b′, LEAF (Shimura's description of CM points; UNVERIFIED locator). -/
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  /-- fs5-nocm N2, GLUE (Kummer fibre of `X₆`). -/
  x6KummerFibre : FS5NoCM.X6KummerFibre
  /-- curve-facts C1b, GLUE (dimension theory of smooth curves). -/
  smoothStalkDimOne : LeafQM.AV.Pin.SmoothStalkDimOne
  /-- curve-facts C2K, LEAF (Hartshorne II.6.8, UNVERIFIED numbering). -/
  constOrOntoAlgClosed : LeafQM.AV.Pin.ConstOrOntoAlgClosed
  /-- curve-facts C3K, GLUE (textbook consequence). -/
  ratFactorAlgClosed : LeafQM.AV.Pin.RatFactorAlgClosed
  -- ProductModelHeight (P2)
  /-- product-height S-an, GLUE (elementary analysis). -/
  productUnifSplits : ZInQ.ProductHeight.ProductUnifSplits
  /-- product-height S-alg, GLUE (Hodge theory of a product). -/
  productMetrizationOfProductUnif : ZInQ.ProductHeight.ProductMetrizationOfProductUnif
  -- StableHeightBaseChange (H4a)
  /-- height-bc, GLUE. -/
  hodgeBCInjective : ZInQ.HeightBC.HodgeBCInjective
  /-- height-bc, GLUE. -/
  cotangentSpanBC : ZInQ.HeightBC.CotangentSpanBC
  /-- height-bc, GLUE. -/
  omegaBaseChange : ZInQ.HeightBC.OmegaBaseChange
  /-- height-bc, GLUE. -/
  uniformizationLiftAnalytic : ZInQ.HeightBC.UniformizationLiftAnalytic
  -- ThetaPointOfFibre
  /-- g0-thetapoint, LEAF? (Shimura 1976 / Mumford Tata II; UNVERIFIED). -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- fibre-qm-period, LEAF? (pkg-I1's composite leaf). -/
  qmHauptmodul : PkgI1.QMHauptmodul
  /-- fibre-qm-period, LEAF (Eichler class number one, lattice form). -/
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  /-- fibre-qm-period, LEAF (R1(b) in family form), for the triple of the leaf bundle. -/
  r1bFamily : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.R1bFamily (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- fibre-qm-period, GLUE, for the triple of the leaf bundle. -/
  periodMapGlue : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- fibre-qm-period, GLUE. -/
  hauptmodulUnique : G0Split.FibreQM.HauptmodulUnique
  /-- fibre-qm-period, LEAF? (Lin–Yang's divisor of `ψ₄`). -/
  qmDenZeroCM3 : G0Split.FibreQM.QMDenZeroCM3
  /-- fibre-qm-period, GLUE. -/
  cPtsTransport : G0Split.FibreQM.CPtsTransport
  -- ModularConstituent: G2 (fibre-cover), G4 (kernel-field)
  /-- fibre-cover, GLUE (Prop. TS for every admissible cover). -/
  propTSAll : G0ModField.PropTSAll
  /-- fibre-cover, GLUE (Neukirch; compositum of conjugates). -/
  unramifiedConjugates : G0ModField.UnramifiedConjugates
  /-- kernel-field 4a′, GLUE (pure algebra: `𝒪` is maximal). -/
  oMaximal : G0ModField.KernelField.OMaximal
  /-- kernel-field 4b, GLUE. -/
  endTransport : G0ModField.KernelField.EndTransport
  /-- kernel-field, GLUE (the conjugacy maps, geometric part). -/
  conjIsogMaps : G0ModField.KernelField.ConjIsogMaps
  -- ModularConstituent: G8-G12 (g0-mod-galois, g10-odd, conj-twist, g12-det)
  /-- g0-mod-galois, LEAF (Burnside). -/
  burnsideAbsIrred : G0Galois.BurnsideAbsIrred
  /-- g0-mod-galois, LEAF (R14 with its determinant clause). -/
  r14Det : G0Galois.R14Det
  /-- g9-derham F2, GLUE: base change of an abelian variety along a field embedding in
  characteristic 0, with `V_ℓ` Galois-compatible (Mumford §4, §6; EGA IV 4.1.4). -/
  g9AbVarBaseChange : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange
  /-- g9-derham F1, LEAF (the vanishing half of the Hodge–Tate decomposition of `V_p(A)`, Tate 1967,
  Faltings 1988; g9-derham recommends adding it to R10): HT multiplicities vanish off `{0, -1}`. -/
  g9R10Weights : ZInQ.Contrib.G9.G9Bridge.R10Weights
  /-- conj-twist N1-surj, GLUE. -/
  artinTorsionSurj : G0Galois.ArtinTorsionSurj
  /-- conj-twist N2, LEAF (Birkenhake–Lange Prop. 1.2.1, UNVERIFIED). -/
  homLinearLift : G0Galois.HomLinearLift
  /-- conj-twist N3a, GLUE. -/
  conjUniformization : G0Galois.ConjUniformization
  /-- g12-det, LEAF (Sen 1980). -/
  senTwist : G0Galois.SenTwist
  /-- g12-det, LEAF (Tate 1967, Ax–Sen–Tate). -/
  finiteImageHT : G0Galois.FiniteImageHT
  /-- weil-pairing (used by g12-det), LEAF (T9 restated; Mumford §§6, 8, 20, 23). -/
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  /-- weil-pairing, LEAF (Mumford §7-8). -/
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  /-- weil-pairing, LEAF (Mumford §4 Appl. 2). -/
  divisiblePoints : WeilPairing.DivisiblePoints
  -- ModularConstituent: G13-G16
  /-- R17 concretely, LEAF (Carayol 1986, Thm (A)). -/
  carayolR17 : LadicCond.CarayolR17'
  -- ModularConstituent: joint glue on G7's data (g0-assemble)
  /-- g0-assemble2, GLUE: G3 on G7's model (the remaining half of g0-assemble's `ModelG3G6`; its
  G6 half is proved from `FibreSimple` and `MulIsogeny`, parts z85, z86). -/
  modelG3 : G0AssembleMod.ModelG3
  /-- g0-assemble2 (from g14-trace, g15-ram), GLUE: linked Tate data with the Frobenius link and
  the local data (replaces g0-assemble's `LinkedTateData`). -/
  linkedTateLocal : G0AssembleMod.LinkedTateLocal

/-- fs5-nocm's `R1R2fpFull` is the leaf bundle's `R1R2fp` after pin-apply (same clauses). -/
theorem r1r2fpFull_of (r : ResearchLeaves3) : FS5NoCM.R1R2fpFull := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h⟩ := LeafAdopt.R1R2fp_of_rep r.r1r2
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h⟩

/-- fs5-nocm's `FibreComTrivialFull` is g0-fibresimple's `FibreComTrivial` over Leaves.lean after
pin-apply (`R1fpPropsFull` and `R1fpProps` have the same text). -/
theorem fibreComTrivial_of_full (h : FS5NoCM.FibreComTrivialFull) :
    G0FibreSimple.FibreComTrivial :=
  fun Y Φ π h1 => h Y Φ π h1

/-- `MobiusGlue` from the curve facts (curve-facts, mobius-glue) and T5. -/
theorem mobiusGlue_of_gp3 (t : TextbookLeaves) (gp : GluePieces3) : LeafQM.AV.Pin.MobiusGlue :=
  LeafQM.AV.Pin.mobiusGlue_of_curves'
    (LeafQM.AV.Pin.curveFacts_of_leaves gp.smoothStalkDimOne gp.constOrOntoAlgClosed
      gp.ratFactorAlgClosed).1
    (LeafQM.AV.Pin.curveFacts_of_leaves gp.smoothStalkDimOne gp.constOrOntoAlgClosed
      gp.ratFactorAlgClosed).2
    t.t5

/-- FS5 (NoCM on the fibre) from `GluePieces3` (fs5-nocm). -/
theorem fibreComTrivial_of_gp3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3) :
    G0FibreSimple.FibreComTrivial :=
  fibreComTrivial_of_full (FS5NoCM.fibreComTrivialFull_of_leaves'' (r1r2fpFull_of r)
    (mobiusGlue_of_gp3 t gp) t.t27 t.t6 gp.cmOptimalEmbedding gp.x6KummerFibre r.r5count)

/-- `FibreSimple` from `GluePieces3` (fs1-descend, mul-rigidity, fs5-nocm). -/
theorem fibreSimple_of_gp3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3) :
    G0Split.FibreSimple :=
  G0FibreSimple.fibreSimple_of_leaves t
    (MulRigidity.mulIsogeny_of_mulEtale gp.mulEtale) G0FibreSimple.rigidityHom
    ⟨G0FibreSimple.finiteDescends_proof, fibreComTrivial_of_gp3 r t gp⟩

/-- **`GluePieces` from `GluePieces3` and the leaf bundles** (g0-assemble2). -/
theorem gluePieces_of_gluePieces3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3) :
    GluePieces where
  dimFinite := G0Split.dimFinite
  dimBaseChange := G0Split.dimBaseChange
  fibreSimple := fibreSimple_of_gp3 r t gp
  productModelHeight := ZInQ.ProductHeight.productModelHeight_of_splits gp.productUnifSplits
    gp.productMetrizationOfProductUnif
  stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
    (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_glue4
      gp.hodgeBCInjective gp.cotangentSpanBC gp.omegaBaseChange gp.uniformizationLiftAnalytic))
  productExists := G0Product.productExists
  reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r G0Split.dimFinite
  thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
    (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 (mobiusGlue_of_gp3 t gp) gp.qmHauptmodul
      t.t35 t.t11a gp.qmClassNumberOne (gp.r1bFamily r.r1r2) (gp.periodMapGlue r.r1r2)
      gp.hauptmodulUnique gp.qmDenZeroCM3 gp.cPtsTransport)
    gp.thetaRatiosAlgebraic
  modularConstituent := modularConstituent_of_field t
    (G0ModField.fibreCoverExists_of_propTSAll' t.t5 gp.propTSAll gp.unramifiedConjugates)
    (G0ModField.KernelField.kernelFieldExists_of_split'' t.t6 r.r7a r.r6 t.t5 t.t27
      (fibreComTrivial_of_gp3 r t gp) gp.oMaximal gp.endTransport gp.conjIsogMaps)
    UnramTate.unramifiedSup_mf
    (G0AssembleMod.afterG7_of3 r t
      ⟨gp.burnsideAbsIrred, gp.r14Det,
        ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange gp.g9AbVarBaseChange gp.g9R10Weights,
        G0Galois.g10Glue_of_conjTwist (G0Galois.conjTwistNontrivial_main t.t26 t.t35
          gp.artinTorsionSurj gp.homLinearLift gp.conjUniformization),
        G0Galois.g12Weight_of_senTwist gp.senTwist gp.finiteImageHT,
        G0Galois.detTate_of_leaves gp.t09SymmIsogenyExists gp.isogenyQuasiInverse
          gp.divisiblePoints t.t26,
        G0AssembleMod.resQFiniteIndex⟩
      (G0ModNewform.dirichletOfFinite_of_t17 t.t17) gp.carayolR17
      Swan.swanIndependent_proved Swan.swanIntegral_proved
      Swan.adaptedExists_proved
      (G0AssembleMod.modelG3G6_of (fibreSimple_of_gp3 r t gp)
        (G0AssembleMod.modelNoncomm_of_mulIsogeny
          (MulRigidity.mulIsogeny_of_mulEtale gp.mulEtale)) gp.modelG3)
      (G0AssembleMod.linkedTateData_of_local t.t7 gp.linkedTateLocal))
  heightCopies := G0HeightCopies.heightCopiesAgree

/-- **G0 after waves 26-27** (g0-assemble2): the leaf bundles (`ResearchLeaves3`: no `opaque`
placeholder) and `GluePieces3` imply `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leavesR3 r t (gluePieces_of_gluePieces3 r t gp)

/-- The same with Leaves.lean's `ResearchLeaves` (which implies `ResearchLeaves3`). -/
theorem sixContactMin_of_leaves3' (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces3) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leaves3 (researchLeaves3_of r) t gp

end HSyn

end

#print axioms HSyn.gluePieces_of_gluePieces3
#print axioms HSyn.sixContactMin_of_leaves3
#print axioms HSyn.sixContactMin_of_leaves3'
#print axioms HSyn.researchLeaves3_of

end G0A3_z90_bundle3

section G0A3_z92_unifdims_tail
/-! ## g0-assemble3: unif-dims' Leaves-world closing theorem (`scratch/unif-dims/build_leaves.py`, the `tail` string,
verbatim), and its instance with infra-smooth-dim's `tangentDimAtOrigin` (part e25). -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings.HodgeLattice

/-- Integration check: Leaves.lean's glue piece 5 (`GluePieces.productModelHeight`) from
metrization's `AnalyticUniformizationOfDim` (which follows from T35 in the kernel world) and
hodge-lattice's `TangentDimAtOrigin`. -/
theorem productModelHeight_of_leaves (hU : ZInQ.Metrization.AnalyticUniformizationOfDim)
    (hT : TangentDimAtOrigin) : ZInQ.H5Neron.ProductModelHeight :=
  ZInQ.ProductHeight.productModelHeight_of_splits ZInQ.ProductUnif.productUnifSplits
    (ZInQ.ProductUnif.productMetrizationOfProductUnif_of_local
      (hodgeLatticeTheorem_of_tangent hT dimBaseChange)
      (productUnifDims_of_unifOfDim hU) ZInQ.Metrization2.productLocalStructure
      (productHodgeLattice_of productCotangent detLatticeProd
        (cotangentRank_of_tangentDim (tangentDim_of_abVar hT dimBaseChange)) hU))

/-- (g0-assemble3) product-height's S-alg `ProductMetrizationOfProductUnif` from the leaf
`AnalyticUniformizationOfDim` alone (`TangentDimAtOrigin` is infra-smooth-dim's theorem). -/
theorem productMetrizationOfProductUnif_of_unifOfDim
    (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.ProductHeight.ProductMetrizationOfProductUnif :=
  ZInQ.ProductUnif.productMetrizationOfProductUnif_of_local
    (hodgeLatticeTheorem_of_tangent tangentDimAtOrigin dimBaseChange)
    (productUnifDims_of_unifOfDim hU) ZInQ.Metrization2.productLocalStructure
    (productHodgeLattice_of productCotangent detLatticeProd
      (cotangentRank_of_tangentDim (tangentDim_of_abVar tangentDimAtOrigin dimBaseChange)) hU)

/-- (g0-assemble3) `ProductModelHeight` (the `GluePieces` field) from the leaf
`AnalyticUniformizationOfDim` alone. -/
theorem productModelHeight_of_unifOfDim (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.H5Neron.ProductModelHeight :=
  productModelHeight_of_leaves hU tangentDimAtOrigin

end ZInQ.UnifDims

end G0A3_z92_unifdims_tail

section G0A3_z93_linkedfrob
/-! ## assemble-port: linked-frob (LinkedFrob from N1-g1, ProperSmoothGenConnected, I2-Red, I2-NMP); see mk/mk_z93.py -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q


/-!
# g14-trace, second file: the linked Tate bridge at `ℓ = 3, 5`

Appended to a verbatim copy of `scratch/g0-mod-field/ModField.lean` (g0-mod-field's `G7Data`,
`TateBridge`, `GaloisCopy.G7Out`). `TateBridge` gives the `ℓ`-adic data at each `ℓ` separately
(`∀ ℓ, ∃ Tm c ε' a β' uu, G7Out …`), which does not determine the traces of `r₃` against `r₅`
(g14-trace §1, `g7Out_twist`). `TateBridge35` is the linked form at `ℓ = 3, 5` that
`G14Trace.g12Spec_g14_of_galois` consumes: one pair `a, β : G_ℚ → ℚ̄` mapped to `ℚ̄₅`, `ℚ̄₃` by
embeddings `j₅`, `j₃` (TateBridge's own docstring: "mapped into `ℚ̄_ℓ` by one embedding of the
number field they generate"), and the operators `Tm_ℓ` (from one points-level `m_σ`) in the
Frobenius link at Frobenius elements. No `sorry`, no `axiom`.
-/

noncomputable section

namespace G14Bridge

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField
open GlueC10Link (FrobCompare)

/-- (copy of `G14Trace.FrobTraceLink`, over `GaloisCopy.Vb`) **The Frobenius trace link (GLUE,
AV side; N5 L781-786).** Outside a finite set `S`, at every arithmetic Frobenius `τ` above `p`,
`N·Tm_ℓ(τ)` is conjugate to `V_ℓ(α')` for one endomorphism `α'` of an abelian variety over a
field of characteristic `p`, at `ℓ = 3` and `ℓ = 5` (kernel's `GlueC10Link.FrobCompare`). -/
def FrobTraceLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5) (GaloisCopy.Vb A 5))
    (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3) (GaloisCopy.Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
    PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p →
    ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k) (α : PkgI3.AbVar.End Ab)
      (N : ℕ), N ≠ 0 ∧ FrobCompare 3 (Tm3 τ) α N ∧ FrobCompare 5 (Tm5 τ) α N

/-- **The linked Tate bridge at `ℓ = 3, 5` (GLUE; replaces the `ℓ = 3, 5` instances of
`G0ModField.TateBridge`).** From G7's data, `dim A_{L'} = 2` and `rank End = 4`: one pair
`a, β : G_ℚ → ℚ̄` (N5's `a_σ` and `β(σ)`, algebraic), embeddings `j₅ : ℚ̄ → ℚ̄₅`, `j₃ : ℚ̄ → ℚ̄₃`, and
for `ℓ = 5, 3` the operators `Tm_ℓ` (`ℚ̄_ℓ ⊗ V_ℓ(m_σ)`), `c_ℓ`, `ε_ℓ` and matrix units with
`G7Out` for the scalars `j_ℓ ∘ a`, `j_ℓ ∘ β`, `FrobTraceLink` for `Tm₅`, `Tm₃`, and `β` an
algebraic form of `G7Data`'s `β` (`ιC ∘ βQ = β`; G15 needs this `β`). `aQ` is not tied to
`DescentDatum`'s `a` in the statement (`a_σ = deg(μ_σ)^{-1/4}`, N5 L647, is algebraic), nor `Tm_ℓ` to
its `m_σ`, as in `TateBridge`; for G14 only the common `aQ` and `FrobTraceLink` matter (a joint
twist at both `ℓ` keeps the system compatible). -/
def TateBridge35 : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5 ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3 ∧
      @FrobTraceLink L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3 ∧
      ∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)

instance fact_prime_five' : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_three' : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- `TateBridge35` contains the `ℓ = 5` and `ℓ = 3` conclusions of `TateBridge` (proved): it is a
strengthening at these two primes. -/
theorem tateBridge_five_three_of_35 (h : TateBridge35) (u : ℚ) (P : QML3 Qbar)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
    (∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β' : PkgI4.GQ → PadicAlgCl 5)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm c ε' a β' uu) ∧
    (∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3) (a β' : PkgI4.GQ → PadicAlgCl 3)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm c ε' a β' uu) := by
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, -, -⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  exact ⟨⟨Tm5, c5, ε5, _, _, u5, h5⟩, ⟨Tm3, c3, ε3, _, _, u3, h3⟩⟩

end G14Bridge

end



/-!
# frob-trace: `TateBridge35` and `FrobTraceLink` (g14-trace)

Appended (by `build.sh`) to verbatim copies of `scratch/unram-tate/TateBridge.lean` (which is
`scratch/g0-mod-field/ModField.lean` L1-1036 plus unram-tate's section `UnramTate`) and of
`scratch/g14-trace/part_bridge.lean` (`G14Bridge.FrobTraceLink`, `G14Bridge.TateBridge35`).

Main result: `FrobTrace.tateBridge35_of_algFrobRed (hT : PkgI3.TateModuleFree)
(hR : AlgFrobRed) : G14Bridge.TateBridge35`, through the chain of proved implications
`AlgFrobRed → AlgFrobOne → AlgFrobLink` and `tateBridge35_of_algFrobLink`. The operators are
unram-tate's `Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at `ℓ = 5, 3` (one points-level `m`, one `Θ`,
one `h`), the scalars are `aQ g = βQ g / γQ(hgh⁻¹)` and `βQ` with `ιC ∘ βQ = β` in `ℚ̄` (proved,
`scalarsQbar`), and the conjunct `FrobTraceLink` for these operators is derived from the glue
Prop `AlgFrobRed` (one reduction homomorphism `A(ℚ̄) → Ā(k̄)` intertwining `f = F ∘ - ∘ Spec(σ)`
with an endomorphism of the reduction, bijective on prime-to-`p` torsion).
No `sorry`, no `axiom`.
-/

noncomputable section

namespace FrobTrace

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

/-! ## The Tate functor on an additive equivalence -/

/-- `T_ℓ(Θ)` for an additive equivalence `Θ : M ≃+ N`, as a `ℤ_ℓ`-linear equivalence. -/
def tateMapEquiv (ℓ : ℕ) [Fact ℓ.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (Θ : M ≃+ N) : PkgI3.Tate.T ℓ M ≃ₗ[ℤ_[ℓ]] PkgI3.Tate.T ℓ N :=
  LinearEquiv.ofLinear (PkgI3.Tate.map (ℓ := ℓ) Θ.toAddMonoidHom)
    (PkgI3.Tate.map (ℓ := ℓ) Θ.symm.toAddMonoidHom)
    (LinearMap.ext fun x => Subtype.ext (funext fun n => Θ.apply_symm_apply (x.1 n)))
    (LinearMap.ext fun x => Subtype.ext (funext fun n => Θ.symm_apply_apply (x.1 n)))

/-- Conjugation commutes with base change. -/
theorem conj_baseChange {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (f : Module.End R M) :
    (e.baseChange R A M N).conj (f.baseChange A) = (e.conj f).baseChange A := by
  rw [LinearEquiv.conj_apply, LinearEquiv.conj_apply, ← LinearEquiv.baseChange_symm,
    LinearEquiv.coe_baseChange, LinearEquiv.coe_baseChange, LinearMap.baseChange_comp,
    LinearMap.baseChange_comp]

/-! ## The glue Prop: reduction of the algebraic maps `m_σ` modulo `p` -/

/-- **`AlgFrobLink` (GLUE, AV side; Glazer N5 L777-786; reduction of abelian varieties).** Let
`A` be an abelian variety over a finite Galois `L ⊆ ℚ̄` and `m_σ` (`σ ∈ G_ℚ`) additive maps of
`A(ℚ̄)` with three of `DescentDatum`'s clauses, copied verbatim: `m_σ` is the Galois action for
`σ ∈ G_L`; `m_{σk} = m_σ m_k`, `m_{kσ} = m_k m_σ` for `k ∈ G_L`; and `m_σ` is algebraic,
`m_σ(x) = F_σ ∘ x ∘ Spec(σ)` for a finite surjective morphism of schemes `F_σ : A → A`. Then there
is a finite set `S` of primes such that, for every arithmetic Frobenius `τ` at a place `v` above
`p ∉ S` and every `g ∈ G_ℚ` (`gτg⁻¹` is an arithmetic Frobenius at `g(v)`), there are an
abelian variety `Ā` over a field `k` of characteristic `p`, an endomorphism `α'` of `Ā` and
`N ≠ 0` such that for every prime `ℓ ≠ p` some `ℚ_ℓ`-isomorphism
`ℚ_ℓ ⊗ T_ℓ(A(ℚ̄)) ≅ V_ℓ(Ā)` carries `N · V_ℓ(m_{gτg⁻¹})` to `V_ℓ(α')`.

Why it is true (SPECULATIVE in its Lean details; `N = 1` works): by the first two clauses one
`F_{σ_s}` serves the whole coset `σ_s G_L`, so finitely many morphisms occur (this is the proved
step `algFrobLink_of_one`). Put `σ' = gτg⁻¹` and `w = g(v) ∩ L`, not `v ∩ L`: `σ'` lies in the
decomposition group of `g(v)`. Put in `S` the primes of bad reduction of `A` and the primes below
which some `F_{σ_s}` does not extend to the abelian scheme. For `p ∉ S`, `Ā` is the reduction of
`A` at `w` over `k = κ(w)`. On prime-to-`p` torsion, reduction is a bijection
`A(ℚ̄)[ℓⁿ] ≅ Ā(k̄)[ℓⁿ]` (leaf I2-Red, `PkgI2.ReductionTorsionBijective`, Serre–Tate 1968 §1).
Under it, `σ'` acting on coordinates becomes the `p`-power map of `k̄` (`IsArithFrob`), which on
`k̄`-points is the absolute Frobenius of `Ā`, and `F_{σ'}` becomes its reduction `F̄_{σ'}` (Néron
mapping property of the abelian scheme, leaf I2-NMP, `PkgI2.NeronMappingAbelianScheme`). So
`m_{σ'}` becomes `α' = F̄_{σ'} ∘ Fr_Ā`, a `k`-morphism
fixing `0`, hence an endomorphism of `Ā`, the same for every `ℓ ≠ p`. -/
def AlgFrobLink : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (m : GQ → (PtQ L A →+ PtQ L A)),
    (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) →
    (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) →
    (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ) →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p → ∀ g : PkgI4.GQ,
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
            ∃ Ψ : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (PtQ L A)) ≃ₗ[ℚ_[ℓ]] Ab.V ℓ,
              Ψ.conj ((N : ℚ_[ℓ]) •
                  (PkgI3.Tate.map (ℓ := ℓ) (m (g * τ * g⁻¹))).baseChange ℚ_[ℓ]) =
                (PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ]

/-- **`AlgFrobOne` (GLUE, AV side; Glazer N5 L777-786; reduction of one morphism modulo `p`).**
`AlgFrobLink` for a single morphism of schemes. Let `A` be an abelian variety over a finite Galois
`L ⊆ ℚ̄` and `F : A → A` a finite surjective morphism of schemes. There is a finite set `S` of
primes such that: for every arithmetic Frobenius `τ` at a place `v` above `p ∉ S`, every
`g ∈ G_ℚ`, and every additive map `f` of `A(ℚ̄)` of the form `f(x) = F ∘ x ∘ Spec(gτg⁻¹)`, there
are an abelian variety `Ā` over a field `k` of characteristic `p`, `α' ∈ End(Ā)` and `N ≠ 0`
such that for every prime `ℓ ≠ p` some `ℚ_ℓ`-isomorphism `ℚ_ℓ ⊗ T_ℓ(A(ℚ̄)) ≅ V_ℓ(Ā)` carries
`N · V_ℓ(f)` to `V_ℓ(α')`.

Why it is true (SPECULATIVE in its Lean details; `N = 1` works). If such an `f` exists, `F` lies
over `Spec(s)` with `s = (gτg⁻¹)⁻¹|_L`, which is in the decomposition group of `w = g(v) ∩ L`;
so `F` is an `L`-morphism `A → A^{(s)}`. Put in `S` the primes below which `A` has bad
reduction or this `L`-morphism does not extend to the abelian-scheme models (spreading out; one
condition: `s` is determined by `F`, since `Γ(A, 𝒪) = L`; `S` depends on `F` only). For `p ∉ S`,
`Ā` is the reduction of `A` at `w`, over `k = κ(w)`. Reduction is a bijection on prime-to-`p`
torsion (leaf I2-Red, `PkgI2.ReductionTorsionBijective`, Serre–Tate 1968 §1); under it,
`gτg⁻¹` acting on coordinates becomes the `p`-power map of `k̄`, i.e. the absolute Frobenius
`Fr_Ā` on `k̄`-points, and `F` becomes its reduction `F̄` (leaf I2-NMP,
`PkgI2.NeronMappingAbelianScheme`). So `f` becomes `F̄ ∘ Fr_Ā`, which lies over `Spec(id_k)`
and fixes `0` (`f` is additive), hence `α' := F̄ ∘ Fr_Ā ∈ End(Ā)` (rigidity, Mumford §4 Cor. 1,
UNVERIFIED locator), the same for every `ℓ ≠ p`. -/
def AlgFrobOne : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p → ∀ (g : PkgI4.GQ)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act (g * τ * g⁻¹) : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p →
            ∃ Ψ : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (PtQ L A)) ≃ₗ[ℚ_[ℓ]] Ab.V ℓ,
              Ψ.conj ((N : ℚ_[ℓ]) • (PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ]) =
                (PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ]

/-- **`AlgFrobLink` from `AlgFrobOne` (proved).** The maps `m_σ` take only finitely many shapes:
for each `s ∈ Gal(L/ℚ)` fix one `σ_s` restricting to `s`; then
`m_{σ_s k}(x) = F_{σ_s} ∘ x ∘ Spec(σ_s k)` for `k ∈ G_L` (second and first clauses), so one
morphism `F_{σ_s}` serves the whole coset, and `S` is the union of the `|Gal(L/ℚ)|` sets
`AlgFrobOne` gives for the `F_{σ_s}`. -/
theorem algFrobLink_of_one (hO : AlgFrobOne) : AlgFrobLink := by
  classical
  intro L _ _ A m hmL hmLL hFalg
  obtain ⟨F, hF⟩ := hFalg
  let res : GQ →* (L ≃ₐ[ℚ] L) := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L
  -- a representative of each restriction class
  let rep : (L ≃ₐ[ℚ] L) → GQ := fun s =>
    if h : ∃ σ : GQ, res σ = s then h.choose else 1
  have hrep : ∀ σ : GQ, res (rep (res σ)) = res σ := by
    intro σ
    have h : ∃ σ' : GQ, res σ' = res σ := ⟨σ, rfl⟩
    simp only [rep, h, dite_true]
    exact h.choose_spec
  choose Sf hSf using fun s : L ≃ₐ[ℚ] L => hO L A (F (rep s)) (hF (rep s)).1 (hF (rep s)).2.1
  refine ⟨Finset.univ.biUnion Sf, fun p hp hpS v τ hv hτ g => ?_⟩
  let σ' : GQ := g * τ * g⁻¹
  let σ0 : GQ := rep (res σ')
  have hpS0 : p ∉ Sf (res σ') := fun h' =>
    hpS (Finset.mem_biUnion.mpr ⟨res σ', Finset.mem_univ _, h'⟩)
  -- `k = σ0⁻¹ σ' ∈ G_L`
  have hk : σ0⁻¹ * σ' ∈ GQL L := by
    have h1 : res (σ0⁻¹ * σ') = 1 := by
      rw [map_mul, map_inv, hrep, inv_mul_cancel]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L _).mp h1 x hx
  have hσ' : σ' = σ0 * (σ0⁻¹ * σ') := by group
  have hf : ∀ x : PtQ L A, (Additive.toMul (m σ' x)).left =
      Spec.map (CommRingCat.ofHom ((act (g * τ * g⁻¹) : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (Additive.toMul x).left ≫ F σ0 := by
    intro x
    have hm : m σ' = (m σ0).comp (m (σ0⁻¹ * σ')) := by
      conv_lhs => rw [hσ']
      exact (hmLL σ0 _ hk).1
    have hmk := hmL (σ0⁻¹ * σ') (toLAut _ hk) (fun _ => rfl)
    rw [hm, AddMonoidHom.comp_apply, (hF σ0).2.2, hmk]
    show Spec.map (CommRingCat.ofHom ((act σ0 : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (PkgI3.AbVar.galHom (toLAut _ hk) ≫ Additive.toMul x).left ≫ F σ0 = _
    have hSpec : Spec.map (CommRingCat.ofHom ((act σ0 : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        Spec.map (CommRingCat.ofHom ((toLAut _ hk : Qbar ≃ₐ[L] Qbar) : Qbar →+* Qbar)) =
        Spec.map (CommRingCat.ofHom ((act (g * τ * g⁻¹) : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext y
      have h0 : σ0 * (σ0⁻¹ * σ') = σ' := by group
      exact congrArg (fun s : GQ => act s y) h0
    rw [← hSpec, Category.assoc]
    rfl
  exact hSf (res σ') p hp hpS0 v τ hv hτ g (m σ') hf

/-! ## `AlgFrobOne` from a reduction homomorphism on points -/

/-- `T_ℓ(r)` is bijective if `r` is injective on `ℓ`-power torsion and every `ℓⁿ`-torsion point
of the target has an `ℓⁿ`-torsion preimage. -/
theorem tateMap_bijective (ℓ : ℕ) [Fact ℓ.Prime] {M N : Type*} [AddCommGroup M]
    [AddCommGroup N] (r : M →+ N)
    (hinj : ∀ (n : ℕ) (x : M), (ℓ ^ n) • x = 0 → r x = 0 → x = 0)
    (hsurj : ∀ (n : ℕ) (y : N), (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ r x = y) :
    Function.Bijective (PkgI3.Tate.map (ℓ := ℓ) r) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Subtype.ext
    funext n
    exact hinj n (x.1 n) (PkgI3.Tate.pow_smul_eq_zero x.2 n)
      (congrFun (congrArg Subtype.val hx) n)
  · intro y
    choose X hX using fun n => hsurj n (y.1 n) (PkgI3.Tate.pow_smul_eq_zero y.2 n)
    have h0 : X 0 = 0 := by simpa using (hX 0).1
    have hs : ∀ n, ℓ • X (n + 1) = X n := by
      intro n
      have := hinj n (ℓ • X (n + 1) - X n) (by
          rw [smul_sub, smul_smul, ← pow_succ, (hX (n + 1)).1, (hX n).1, sub_zero])
        (by rw [map_sub, map_nsmul, (hX (n + 1)).2, (hX n).2, y.2.2 n, sub_self])
      exact sub_eq_zero.mp this
    exact ⟨⟨X, h0, hs⟩, Subtype.ext (funext fun n => (hX n).2)⟩

/-- **`AlgFrobRed` (GLUE, AV side; Glazer N5 L777-786; the reduction map).** `AlgFrobOne` with
the `ℓ`-adic isomorphisms replaced by one homomorphism on points: for `F`, `S`, `p ∉ S`, `τ`, `g`
and `f(x) = F ∘ x ∘ Spec(gτg⁻¹)` as in `AlgFrobOne`, there are an abelian variety `Ā` over a
field `k` of characteristic `p`, `α' ∈ End(Ā)`, `N ≠ 0` and a group homomorphism
`red : A(ℚ̄) → Ā(k̄)` with `red ∘ (N·f) = α' ∘ red`, injective on `ℓ`-power torsion and with
every `ℓⁿ`-torsion point of `Ā(k̄)` the image of an `ℓⁿ`-torsion point, for every prime `ℓ ≠ p`.

Why it is true (SPECULATIVE in its Lean details; `N = 1`). `S` as in `AlgFrobOne`. Let
`v' = g(v)`, at which `σ' = gτg⁻¹` is an arithmetic Frobenius, `w = v' ∩ L`, `𝒜` the abelian
scheme over `O_w`, `Ā` its special fibre over `k = κ(w)`. `red` is the reduction map
`A(ℚ̄) = 𝒜(O_{v'}) → Ā(κ(v'))` (valuative criterion of properness), followed by a `k`-isomorphism
`κ(v') ≅ k̄`. Since `σ'` preserves `O_{v'}` and `F` extends to `𝒜` (leaf I2-NMP), `f` lifts to
`𝒜(O_{v'})` and reduces to `x̄ ↦ F̄ ∘ x̄ ∘ Spec(Frob_p) = (F̄ ∘ Fr_Ā)(x̄)`, which is
`α' := F̄ ∘ Fr_Ā ∈ End(Ā)` (see `AlgFrobOne`). The torsion clauses are leaf I2-Red
(`PkgI2.ReductionTorsionBijective`, Serre–Tate 1968 §1) for `m = ℓⁿ`, prime to `p`. -/
def AlgFrobRed : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p → ∀ (g : PkgI4.GQ)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act (g * τ * g⁻¹) : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∃ red : PtQ L A →+ Additive (Ab.Pt (AlgebraicClosure k)),
            (∀ x, red (N • f x) =
              MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) α) (red x)) ∧
            ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ,
              (∀ x : PtQ L A, (ℓ ^ n) • x = 0 → red x = 0 → x = 0) ∧
              (∀ y, (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ red x = y)

/-- **`AlgFrobOne` from `AlgFrobRed` (proved):** `Ψ = ℚ_ℓ ⊗ T_ℓ(red)`. -/
theorem algFrobOne_of_red (hR : AlgFrobRed) : AlgFrobOne := by
  intro L _ _ A F hF1 hF2
  obtain ⟨S, hS⟩ := hR L A F hF1 hF2
  refine ⟨S, fun p hp hpS v τ hv hτ g f hf => ?_⟩
  obtain ⟨k, _, hk, Ab, α, N, hN, red, hred, hbij⟩ := hS p hp hpS v τ hv hτ g f hf
  refine ⟨k, _, hk, Ab, α, N, hN, fun ℓ _ hℓp => ?_⟩
  let Ψ0 := LinearEquiv.ofBijective (PkgI3.Tate.map (ℓ := ℓ) red)
    (tateMap_bijective ℓ red (fun n => (hbij ℓ (Fact.out) hℓp n).1)
      (fun n => (hbij ℓ (Fact.out) hℓp n).2))
  refine ⟨Ψ0.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _, ?_⟩
  have h1 : Ψ0.conj (N • PkgI3.Tate.map (ℓ := ℓ) f) = PkgI3.AbVar.homT (ℓ := ℓ) α := by
    apply LinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := Ψ0.surjective z
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    funext n
    show (PkgI3.Tate.map red ((N • PkgI3.Tate.map f) w)).1 n =
      (PkgI3.AbVar.homT (ℓ := ℓ) α (PkgI3.Tate.map red w)).1 n
    rw [LinearMap.smul_apply, map_nsmul]
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, PkgI3.Tate.map_apply, PkgI3.AbVar.homT]
    rw [← map_nsmul, hred]
  have h2 : (N : ℚ_[ℓ]) • (PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ] =
      (N • PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ] := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ] N (PkgI3.Tate.map (ℓ := ℓ) f), LinearMap.baseChange_smul,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h2, conj_baseChange, h1]

/-! ## From the points-level comparison to `FrobCompare` for `opV(Θ ∘ f ∘ Θ⁻¹)` -/

/-- The comparison for `f` on `V_ℓ(A(ℚ̄))` gives the kernel's `FrobCompare` for the transported
operator `opV(Θ ∘ f ∘ Θ⁻¹)` on `ℚ̄_ℓ ⊗ V_ℓ(A_{L'})`, for any additive bijection `Θ`. -/
theorem frobCompare_opV_conjE {L : IF} (A : PkgI3.AbVar L) {K : Type} [Field K]
    (A' : PkgI3.AbVar K) (Θ : PtQ L A ≃+ PtA A') (f : PtQ L A →+ PtQ L A)
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type} [Field k] (Ab : PkgI3.AbVar k)
    (α : PkgI3.AbVar.End Ab) (N : ℕ)
    (Ψ : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (PtQ L A)) ≃ₗ[ℚ_[ℓ]] Ab.V ℓ)
    (hΨ : Ψ.conj ((N : ℚ_[ℓ]) • (PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ]) =
      (PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ]) :
    GlueC10Link.FrobCompare ℓ (opV A' ℓ (conjE Θ f)) α N := by
  let e := tateMapEquiv ℓ Θ
  let Ψ' : A'.V ℓ ≃ₗ[ℚ_[ℓ]] Ab.V ℓ :=
    (e.symm.baseChange ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (PtA A')) (PkgI3.Tate.T ℓ (PtQ L A))).trans Ψ
  refine ⟨Ψ'.baseChange ℚ_[ℓ] (PadicAlgCl ℓ) (A'.V ℓ) (Ab.V ℓ), ?_⟩
  -- the `ℚ_ℓ`-level identity
  have h1 : Ψ'.conj ((N : ℚ_[ℓ]) •
      (PkgI3.Tate.map (ℓ := ℓ) (conjE Θ f)).baseChange ℚ_[ℓ]) =
      (PkgI3.AbVar.homT (ℓ := ℓ) α).baseChange ℚ_[ℓ] := by
    rw [← hΨ]
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.conj_apply_apply]
    show (e.symm.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _).trans Ψ _ = _
    rw [LinearEquiv.trans_apply]
    congr 1
    rw [LinearEquiv.symm_trans_apply]
    generalize Ψ.symm x = y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul q t =>
      rw [← LinearEquiv.baseChange_symm, LinearEquiv.symm_symm, LinearEquiv.baseChange_tmul,
        LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
        LinearMap.baseChange_tmul, map_smul, LinearEquiv.baseChange_tmul]
      congr 2
      apply Subtype.ext
      funext n
      show Θ.symm (Θ (f (Θ.symm (Θ (t.1 n))))) = f (t.1 n)
      rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    | add y z hy hz => simp only [map_add, hy, hz]
  -- base change to `ℚ̄_ℓ`
  have h2 : ((N : PadicAlgCl ℓ) • opV A' ℓ (conjE Θ f)) =
      (((N : ℚ_[ℓ]) • (PkgI3.Tate.map (ℓ := ℓ) (conjE Θ f)).baseChange ℚ_[ℓ])).baseChange
        (PadicAlgCl ℓ) := by
    rw [LinearMap.baseChange_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rfl
  rw [h2, conj_baseChange, h1]

/-! ## Rescaling the scalars of `G7Out` -/

/-- `G7Out` is preserved by multiplying `a` and `β` by one nonzero `φ` that is `1` on `G_K`
(with `ε` multiplied by `∂φ`); `ρ = β⁻¹ a T` does not change. -/
theorem g7Out_rescale {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β a₂ β₂ φ : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (GaloisCopy.Vb A ℓ))
    (hφ0 : ∀ g, φ g ≠ 0) (hφ1 : ∀ σ, φ (GaloisCopy.resQ K σ) = 1)
    (ha₂ : ∀ g, a₂ g = φ g * a g) (hβ₂ : ∀ g, β₂ g = φ g * β g)
    (h : GaloisCopy.G7Out A ℓ Tm c ε a β u) :
    GaloisCopy.G7Out A ℓ Tm c (fun g g₂ => ε g g₂ * (φ g * φ g₂ / φ (g * g₂))) a₂ β₂ u := by
  obtain ⟨hdim, hrk, hT, ha, hβ, hβ0, hres, hcomm, hcont⟩ := h
  have hrho : ∀ g, GlueDescent.rho Tm a₂ β₂ g = GlueDescent.rho Tm a β g := by
    intro g
    unfold GlueDescent.rho
    rw [ha₂, hβ₂]
    congr 1
    have h0 := hφ0 g
    have h1 := hβ0 g
    field_simp
  refine ⟨hdim, hrk, hT, fun g g₂ => ?_, fun g g₂ => ?_, fun g => ?_, fun σ => ?_, hcomm, ?_⟩
  · rw [ha₂, ha₂, ha₂]
    have h0 := hφ0 (g * g₂)
    have := ha g g₂
    calc φ g * a g * (φ g₂ * a g₂) * c g g₂ = φ g * φ g₂ * (a g * a g₂ * c g g₂) := by ring
      _ = φ g * φ g₂ * (ε g g₂ * a (g * g₂)) := by rw [this]
      _ = ε g g₂ * (φ g * φ g₂ / φ (g * g₂)) * (φ (g * g₂) * a (g * g₂)) := by
        field_simp
  · rw [hβ₂, hβ₂, hβ₂]
    have h0 := hφ0 (g * g₂)
    have := hβ g g₂
    calc φ g * β g * (φ g₂ * β g₂) = φ g * φ g₂ * (β g * β g₂) := by ring
      _ = φ g * φ g₂ * (ε g g₂ * β (g * g₂)) := by rw [this]
      _ = ε g g₂ * (φ g * φ g₂ / φ (g * g₂)) * (φ (g * g₂) * β (g * g₂)) := by
        field_simp
  · rw [hβ₂]; exact mul_ne_zero (hφ0 g) (hβ0 g)
  · obtain ⟨h1, h2, h3⟩ := hres σ
    exact ⟨h1, by rw [ha₂, hφ1, h2, _root_.one_mul], by rw [hβ₂, hφ1, h3, _root_.one_mul]⟩
  · intro f v
    have : (fun g => f (GlueDescent.rho Tm a₂ β₂ g v)) = fun g => f (GlueDescent.rho Tm a β g v) :=
      funext fun g => by rw [hrho]
    rw [this]
    exact hcont f v

/-! ## The scalars in `ℚ̄` -/

/-- **The scalar link (proved, no leaf).** From the data of B1/B2 (`a > 0` real, `c = n/d`,
`ε` a sign cocycle with `a_σ a_τ c(σ,τ) = ε(σ,τ) a_{στ}`, `∂β = ε`, `a = β = 1` on `G_{L'}`):
`γQ : G_ℚ → ℚ̄^×` with `∂γQ = c` and `γQ = 1` on `G_{L'}` (the algebraic form of `β/a`), and
`βQ : G_ℚ → ℚ̄` with `ιC ∘ βQ = β` for one embedding `ιC : ℚ̄ → ℂ`. The values of `β/a` and of `β`
are algebraic because their `r`-th powers lie in `ℚ`, resp. are `±1`, where `r` is the order of
`σ|_{L'}`. -/
theorem scalarsQbar (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (a : GQ → ℝ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ) (n d : GQ → GQ → ℤ)
    (hd : ∀ σ τ, d σ τ ≠ 0)
    (hna : ∀ σ τ, (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) =
      (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ))
    (hβe : ∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ))
    (hε2 : ∀ σ τ, ε σ τ ^ 2 = 1)
    (ha0 : ∀ σ, 0 < a σ)
    (hone : ∀ k ∈ GQL L', a k = 1 ∧ β k = 1) :
    ∃ (gamQ βQ : GQ → Qbar) (ιC : Qbar →ₐ[ℚ] ℂ), (∀ σ, gamQ σ ≠ 0) ∧
      (∀ σ τ, gamQ σ * gamQ τ = ((n σ τ : Qbar) / (d σ τ : Qbar)) * gamQ (σ * τ)) ∧
      (∀ k ∈ GQL L', gamQ k = 1) ∧ (∀ σ, ιC (βQ σ) = (β σ : ℂ)) := by
  let gC : GQ → ℂ := fun σ => (β σ : ℂ) / ((a σ : ℝ) : ℂ)
  let q : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have ha0' : ∀ σ, ((a σ : ℝ) : ℂ) ≠ 0 := fun σ => Complex.ofReal_ne_zero.mpr (ha0 σ).ne'
  have hq : ∀ σ τ, gC σ * gC τ = (q σ τ : ℂ) * gC (σ * τ) := by
    intro σ τ
    have h1 := hna σ τ
    have h2 : (β σ : ℂ) * β τ = ε σ τ * β (σ * τ) := by
      rw [← Units.val_mul, hβe σ τ, Units.val_mul]
    have hdC : (d σ τ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hd σ τ)
    have hε : (ε σ τ : ℂ) = (((a σ * a τ * ((n σ τ : ℝ) / d σ τ)) : ℝ) : ℂ) /
        ((a (σ * τ) : ℝ) : ℂ) := by
      rw [h1, mul_div_cancel_right₀ _ (ha0' _)]
    have hA := ha0' σ
    have hB := ha0' τ
    have hAB := ha0' (σ * τ)
    simp only [gC, q]
    rw [div_mul_div_comm, h2, hε]
    push_cast
    field_simp
  have hg1 : ∀ k ∈ GQL L', gC k = 1 := by
    intro k hk; simp only [gC]; rw [(hone k hk).1, (hone k hk).2]; simp
  have hg0 : ∀ σ, gC σ ≠ 0 := fun σ => div_ne_zero (Units.ne_zero _) (ha0' σ)
  have hpow : ∀ (σ : GQ) (k : ℕ), ∃ r : ℚ, gC σ ^ k = (r : ℂ) * gC (σ ^ k) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by rw [pow_zero, pow_zero, hg1 1 (one_mem _)]; simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * q (σ ^ k) σ, ?_⟩
      rw [pow_succ, hr, _root_.mul_assoc, hq, pow_succ]
      push_cast; ring
  have hfin : ∀ σ : GQ, ∃ r : ℕ, 0 < r ∧ σ ^ r ∈ GQL L' := by
    intro σ
    let σ' : Qbar ≃ₐ[ℚ] Qbar := σ
    let s := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' σ'
    have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
    refine ⟨orderOf s, hs.orderOf_pos, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' (σ' ^ orderOf s) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L' _).mp h1 x hx
  have halg : ∀ σ, IsIntegral ℚ (gC σ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨t, ht⟩ := hpow σ r
    rw [hg1 _ hr, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ r - Polynomial.C t, Polynomial.monic_X_pow_sub_C t hr0.ne', ?_⟩
    simp [Polynomial.eval₂_sub, ht]
  -- `β` is algebraic: `β(σ)^r = ±1`
  have hpowβ : ∀ (σ : GQ) (k : ℕ), ∃ e : ℂ, e ^ 2 = 1 ∧
      (β σ : ℂ) ^ k = e * (β (σ ^ k) : ℂ) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by norm_num, by rw [pow_zero, pow_zero, (hone 1 (one_mem _)).2]; simp⟩
    | succ k ih =>
      obtain ⟨e, he, hk⟩ := ih
      refine ⟨e * (ε (σ ^ k) σ : ℂ), ?_, ?_⟩
      · rw [mul_pow, he, _root_.one_mul, ← Units.val_pow_eq_pow_val, hε2, Units.val_one]
      · rw [pow_succ, hk, _root_.mul_assoc, ← Units.val_mul, hβe, Units.val_mul, pow_succ]
        ring
  have halgβ : ∀ σ, IsIntegral ℚ (β σ : ℂ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨e, he, ht⟩ := hpowβ σ r
    rw [(hone _ hr).2, Units.val_one, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ (r * 2) - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
    simp [Polynomial.eval₂_sub, pow_mul, ht, he]
  let F : IntermediateField ℚ ℂ :=
    IntermediateField.adjoin ℚ (Set.range gC ∪ Set.range (fun σ => (β σ : ℂ)))
  haveI : Algebra.IsAlgebraic ℚ F := IntermediateField.isAlgebraic_adjoin (by
    rintro x (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
    · exact halg σ
    · exact halgβ σ)
  let ψ : F →ₐ[ℚ] Qbar := IsAlgClosed.lift
  have hmem : ∀ σ, gC σ ∈ F := fun σ =>
    IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨σ, rfl⟩)
  have hmemβ : ∀ σ, (β σ : ℂ) ∈ F := fun σ =>
    IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨σ, rfl⟩)
  letI : Algebra F Qbar := ψ.toAlgebra
  haveI : IsScalarTower ℚ F Qbar := IsScalarTower.of_algebraMap_eq (fun x => (ψ.commutes x).symm)
  haveI : Algebra.IsAlgebraic F Qbar :=
    Algebra.IsAlgebraic.extendScalars (R := ℚ) (algebraMap ℚ F).injective
  let ιF : Qbar →ₐ[F] ℂ := IsAlgClosed.lift
  let ιC : Qbar →ₐ[ℚ] ℂ := ιF.restrictScalars ℚ
  have hιψ : ∀ x : F, ιC (ψ x) = x := fun x => ιF.commutes x
  refine ⟨fun σ => ψ ⟨gC σ, hmem σ⟩, fun σ => ψ ⟨β σ, hmemβ σ⟩, ιC, ?_, ?_, ?_, ?_⟩
  · intro σ h0
    apply hg0 σ
    have : (⟨gC σ, hmem σ⟩ : F) = 0 := ψ.toRingHom.injective (h0.trans (map_zero ψ).symm)
    exact congrArg Subtype.val this
  · intro σ τ
    have hF : (⟨gC σ, hmem σ⟩ : F) * ⟨gC τ, hmem τ⟩ =
        algebraMap ℚ F (q σ τ) * ⟨gC (σ * τ), hmem (σ * τ)⟩ := Subtype.ext (hq σ τ)
    show ψ _ * ψ _ = _ * ψ _
    rw [← map_mul, hF, map_mul, AlgHom.commutes]
    congr 1
    simp only [q, map_div₀, map_intCast]
  · intro k hk
    show ψ _ = 1
    rw [← map_one ψ]
    exact congrArg ψ (Subtype.ext (hg1 k hk))
  · intro σ
    exact hιψ ⟨β σ, hmemβ σ⟩

/-! ## The assembly -/

set_option maxHeartbeats 4000000 in
/-- **`TateBridge35` from the leaf I3.M0 (`TateModuleFree`) and the glue `AlgFrobLink`.**
`Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at `ℓ = 5, 3` (unram-tate's operators, built from the one
points-level descent datum `m` of `G7Data`), `aQ g = βQ g / γQ(hgh⁻¹)`, `βQ` with `ιC ∘ βQ = β`
(`scalarsQbar`), `j_ℓ = IsAlgClosed.lift`. `G7Out` at `ℓ` is unram-tate's construction with
`γ = j_ℓ ∘ γQ`, rescaled by `φ = j_ℓ(βQ)/j_ℓ(γQ(h·h⁻¹))` (`g7Out_rescale`). `FrobTraceLink`
comes from `AlgFrobLink` (applied to `m` with `g = h`) via `frobCompare_opV_conjE`, with
`S ∪ {3, 5}`. -/
theorem tateBridge35_of_algFrobLink (hT : PkgI3.TateModuleFree) (hF : AlgFrobLink) :
    G14Bridge.TateBridge35 := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD _hdim _hrank
  haveI hNF : NumberField L' := numberField_of_fd L'
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, -, hmc, hFalg⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(endBaseChange K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := tatePoints L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gamQ, βQ, ιC, hg0, hgc, hg1, hιβ⟩ := scalarsQbar L' a β ε n d hd hna hβe hεc.2.1 ha0
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  have hβQ0 : ∀ g, βQ g ≠ 0 := by
    intro g h0
    have := hιβ g
    rw [h0, map_zero] at this
    exact Units.ne_zero _ this.symm
  have hβQ1 : ∀ k, k ∈ GQL L' → βQ k = 1 := by
    intro k hk
    apply ιC.toRingHom.injective
    show ιC (βQ k) = ιC 1
    rw [hιβ, hβL' k hk, map_one, Units.val_one]
  have hC := tateCont_of_tateModuleFree hT
  have hR := resQEmbedding
  -- the operators and `G7Out` at one `ℓ`
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : Qbar →ₐ[ℚ] PadicAlgCl ℓ),
      ∃ (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ)
        (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
          (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
        @GaloisCopy.G7Out L' _ (numberField_of_fd L')
          (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _
          (fun g => opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
            (conjE Θ (m (h * g * h⁻¹)))) c ε'
          (fun g => j (βQ g / gamQ (h * g * h⁻¹))) (fun g => j (βQ g)) uu := by
    intro ℓ _ j
    let gam : GQ → PadicAlgCl ℓ := fun σ => j (gamQ σ)
    have hgam0 : ∀ σ, gam σ ≠ 0 := fun σ => (map_ne_zero j).mpr (hg0 σ)
    have hgamc : ∀ σ τ, gam σ * gam τ =
        ((n σ τ : PadicAlgCl ℓ) / (d σ τ : PadicAlgCl ℓ)) * gam (σ * τ) := by
      intro σ τ
      show j _ * j _ = _ * j _
      rw [← map_mul, hgc, map_mul, map_div₀, map_intCast, map_intCast]
    have hgam1 : ∀ k ∈ GQL L', gam k = 1 := by
      intro k hk; show j _ = 1; rw [hg1 k hk, map_one]
    -- (from here: unram-tate's `tateBridge_of_pieces`, with this `gam`)
    let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
    let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
    have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
      show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
      group
    let m' : GQ → AddMonoid.End (PtQ L A) := m
    let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
    let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
      ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
    let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => 1
    let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => gam (cj g)
    let QM : LeafQM.O →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      R.comp ((LeafQM.AV.endPt A Qbar).comp iot)
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : PadicAlgCl ℓ) (by norm_num : 0 < 2)
    have hI : QM iO * QM iO = (2 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, iO_sq, map_add, map_one, two_smul]
    have hJ : QM jO * QM jO = (-3 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, jO_sq, map_neg, map_add, map_add, map_one]
      module
    have hIJ : QM iO * QM jO = -(QM jO * QM iO) := by
      rw [← map_mul, iO_jO, map_neg, map_mul]
    obtain ⟨uu, huu⟩ := matrixUnits_of_quat s hs two_ne_zero three_ne_zero _ _ hI hJ hIJ
    have hcomm : ∀ (g : PkgI4.GQ) (o : LeafQM.O), Commute (Tm g) (QM o) := by
      intro g o
      apply Commute.map _ R
      exact hmEnd (cj g) (iot o)
    have hTm : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
      intro g g₂
      have h0 : d (cj g) (cj g₂) • (m' (cj g) * m' (cj g₂)) = n (cj g) (cj g₂) • m' (cj g * cj g₂) :=
        hnd (cj g) (cj g₂)
      have h1 := congrArg R h0
      rw [map_zsmul, map_zsmul, ← hcj] at h1
      have h1' : d (cj g) (cj g₂) • (Tm g * Tm g₂) = n (cj g) (cj g₂) • Tm (g * g₂) := by
        show d (cj g) (cj g₂) • (R (m' (cj g)) * R (m' (cj g₂))) = _
        rw [← map_mul]; exact h1
      have h2 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) • (Tm g * Tm g₂) =
          (n (cj g) (cj g₂) : PadicAlgCl ℓ) • Tm (g * g₂) :=
        (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
          (h1'.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
      have hd0 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
      show _ = ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) • _
      rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = c' g g₂ * a' (g * g₂) := by
      intro g g₂; simp only [a', _root_.one_mul, _root_.mul_one]
    have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
      intro g g₂; simp only [β', c']; rw [hcj]; exact hgamc _ _
    have hβ0 : ∀ g, β' g ≠ 0 := fun g => hgam0 _
    have hnorm : (L'.fixingSubgroup).Normal :=
      (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
    have hres : ∀ σ : Field.absoluteGaloisGroup L',
        cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
      intro σ
      have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
        rw [← resQRange L']; exact ⟨σ, rfl⟩
      exact hnorm.conj_mem _ this h
    have hres0 : ∀ σ : Field.absoluteGaloisGroup L',
        (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
      intro σ
      have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
        rw [← resQRange L']; exact ⟨σ, rfl⟩
      exact this
    have hTres : ∀ σ : Field.absoluteGaloisGroup L',
        Tm (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      have hτ := hres σ
      let σ' : Qbar ≃ₐ[L] Qbar :=
        AlgEquiv.ofRingEquiv (f := (act (cj (@GaloisCopy.resQ L' _ hNF σ))).toRingEquiv)
          (fun x => (mem_GQL.mp (hLL'G _ hτ)) x x.2)
      have hm := hmL (cj (@GaloisCopy.resQ L' _ hNF σ)) σ' (fun x => rfl)
      rw [tate_eq_opV]
      show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m' (cj _))) = _
      congr 1
      refine DFunLike.ext _ _ fun x => ?_
      show Θ (m (cj (@GaloisCopy.resQ L' _ hNF σ)) (Θ.symm x)) = _
      rw [hm]
      show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
      rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]
    have hrho1 : ∀ σ : Field.absoluteGaloisGroup L',
        GlueDescent.rho Tm a' β' (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      unfold GlueDescent.rho
      rw [hTres σ]
      simp only [β', a', hgam1 _ (hres σ), inv_one, _root_.mul_one, one_smul]
    have hG7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c' c' a' β' uu := by
      refine ⟨_hdim, _hrank, hTm, ha, hβ, hβ0, fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,
        fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩
      intro f v
      rw [continuous_iff_continuousAt]
      intro g₀
      let e₀ : Field.absoluteGaloisGroup L' → PkgI4.GQ := fun σ => g₀ * @GaloisCopy.resQ L' _ hNF σ
      have he₀ : Topology.IsOpenEmbedding e₀ :=
        (Homeomorph.mulLeft g₀).isOpenEmbedding.comp (hR L')
      have he₀1 : e₀ 1 = g₀ := by simp only [e₀, map_one, _root_.mul_one]
      have hcomp : (fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀ =
          fun σ => (f ∘ₗ GlueDescent.rho Tm a' β' g₀) (GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ v) := by
        funext σ
        simp only [Function.comp_apply, e₀, LinearMap.comp_apply]
        rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hTm ha hβ hβ0, hrho1, Module.End.mul_apply]
      have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
        rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
      rw [he₀.continuousAt_iff, he₀1] at hc
      exact hc
    -- rescale by `φ = j(βQ)/γ(h·h⁻¹)`
    let φ : PkgI4.GQ → PadicAlgCl ℓ := fun g => j (βQ g) / gam (cj g)
    have hφ0 : ∀ g, φ g ≠ 0 := fun g =>
      div_ne_zero ((map_ne_zero j).mpr (hβQ0 g)) (hgam0 _)
    have hφ1 : ∀ σ, φ (@GaloisCopy.resQ L' _ hNF σ) = 1 := by
      intro σ
      show j (βQ _) / gam (cj _) = 1
      rw [hβQ1 _ (hres0 σ), hgam1 _ (hres σ), map_one, div_one]
    refine ⟨c', _, uu, g7Out_rescale _ ℓ Tm c' c' a' β' _ _ φ uu hφ0 hφ1 (fun g => ?_)
      (fun g => ?_) hG7⟩
    · show j (βQ g / gamQ (cj g)) = j (βQ g) / j (gamQ (cj g)) * 1
      rw [map_div₀, _root_.mul_one]
    · show j (βQ g) = j (βQ g) / gam (cj g) * gam (cj g)
      rw [div_mul_cancel₀ _ (hgam0 _)]
  let j5 : Qbar →ₐ[ℚ] PadicAlgCl 5 := IsAlgClosed.lift
  let j3 : Qbar →ₐ[ℚ] PadicAlgCl 3 := IsAlgClosed.lift
  obtain ⟨c5, ε5, u5, h5⟩ := key 5 j5
  obtain ⟨c3, ε3, u3, h3⟩ := key 3 j3
  refine ⟨fun g => βQ g / gamQ (h * g * h⁻¹), βQ, j5, j3, _, c5, ε5, u5, _, c3, ε3, u3, h5, h3,
    ?_, ιC, hιβ⟩
  -- `FrobTraceLink` from `AlgFrobLink`
  obtain ⟨S, hS⟩ := hF L A m hmL hmLL hFalg
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS' : p ∉ S := fun h' => hpS (Finset.mem_union_left _ h')
  have hp3 : (3 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  have hp5 : (5 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  obtain ⟨k, _, hk, Ab, α, N', hN', hΨ⟩ := hS p hp hpS' v τ hv hτ h
  obtain ⟨Ψ3, hΨ3⟩ := hΨ 3 hp3
  obtain ⟨Ψ5, hΨ5⟩ := hΨ 5 hp5
  exact ⟨k, _, hk, Ab, α, N', hN',
    frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 3 Ab α N' Ψ3 hΨ3,
    frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 5 Ab α N' Ψ5 hΨ5⟩

/-- **Main result: `TateBridge35` from the leaf I3.M0 and the single-morphism glue
`AlgFrobOne`.** -/
theorem tateBridge35_of_algFrobOne (hT : PkgI3.TateModuleFree) (hO : AlgFrobOne) :
    G14Bridge.TateBridge35 :=
  tateBridge35_of_algFrobLink hT (algFrobLink_of_one hO)

/-- **Main result, finest form: `TateBridge35` from the leaf I3.M0 and the glue `AlgFrobRed`
(the reduction homomorphism on points).** -/
theorem tateBridge35_of_algFrobRed (hT : PkgI3.TateModuleFree) (hR : AlgFrobRed) :
    G14Bridge.TateBridge35 :=
  tateBridge35_of_algFrobOne hT (algFrobOne_of_red hR)

end FrobTrace

end


/-!
# alg-frob-red: reducing `FrobTrace.AlgFrobRed`

Appended (by `build.sh`) to verbatim copies of frob-trace's three source parts
(`src_part_tate_src.lean`, `src_part_bridge_src.lean`, `src_part_frob.lean`, i.e.
`scratch/frob-trace/FrobTrace.lean` without its first import line, which `build.sh` re-adds).

Main results (namespace `AlgFrobRedRed`):
* `algFrobRed_of_at : AlgFrobRedAt → FrobTrace.AlgFrobRed` (proved): the place `g(v)` and the
  Frobenius `gτg⁻¹` are absorbed (`liesOver_smul`, `isArithFrob_conj`).
* `algFrobRedAt_of_good : GoodRedCofinite → AlgFrobRedGood → AlgFrobRedAt` (proved): the finite
  set `S` is the set of primes of bad reduction (leaf `GoodRedCofinite`); what remains is local
  at one place of good reduction (`AlgFrobRedGood`).
No `sorry`, no `axiom`.
-/

noncomputable section

namespace AlgFrobRedRed

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate
open scoped Pointwise

/-! ## 1. Conjugating the place -/

/-- Nonunits move with the place: `z ∈ v.nonunits → g z ∈ (g • v).nonunits`. -/
theorem smul_mem_nonunits (g : PkgI4.GQ) {v : ValuationSubring PkgI4.Qbar} {z : PkgI4.Qbar}
    (hz : z ∈ v.nonunits) : g z ∈ (g • v).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hz ⊢
  rcases hz with hz | hz
  · left; rw [hz, map_zero]
  · right
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀,
      AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    exact hz

/-- `g(v)` lies over `p` if `v` does. -/
theorem liesOver_smul (g : PkgI4.GQ) {v : ValuationSubring PkgI4.Qbar} {p : ℕ}
    (hv : PkgI4.LiesOver v p) : PkgI4.LiesOver (g • v) p := by
  have := smul_mem_nonunits g hv
  rwa [map_natCast] at this

/-- `gτg⁻¹` is an arithmetic Frobenius at `g(v)` if `τ` is one at `v`. -/
theorem isArithFrob_conj (g : PkgI4.GQ) {τ : PkgI4.GQ} {v : ValuationSubring PkgI4.Qbar}
    {p : ℕ} (hτ : PkgI4.IsArithFrob τ v p) : PkgI4.IsArithFrob (g * τ * g⁻¹) (g • v) p := by
  obtain ⟨hD, hF⟩ := hτ
  refine ⟨?_, fun x hx => ?_⟩
  · rw [MulAction.mem_stabilizer_iff] at hD ⊢
    rw [mul_smul, mul_smul, inv_smul_smul, hD]
  · rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def] at hx
    have h := smul_mem_nonunits g (hF _ hx)
    have e1 : g (τ (g⁻¹ x)) = (g * τ * g⁻¹) x := rfl
    have e2 : g (g⁻¹ x) = x := by rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    rwa [map_sub, map_pow, e1, e2] at h

/-- **`AlgFrobRedAt` (GLUE, AV side; Glazer N5 L777-786; the reduction map at the place of the
Frobenius).** `FrobTrace.AlgFrobRed` with the Frobenius `σ` at the place `v` itself (no
conjugating `g`): for `A/L`, `F : A → A` finite surjective there is a finite `S` such that for
`p ∉ S`, `v ∣ p`, `σ` an arithmetic Frobenius at `v` and `f(x) = F ∘ x ∘ Spec(σ)` additive, there
are `Ā/k` (`char k = p`), `α' ∈ End(Ā)`, `N ≠ 0` and `red : A(ℚ̄) → Ā(k̄)` with
`red ∘ (N·f) = α' ∘ red`, injective on `ℓⁿ`-torsion and onto `Ā(k̄)[ℓⁿ]` from `A(ℚ̄)[ℓⁿ]` for every
prime `ℓ ≠ p`. -/
def AlgFrobRedAt : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob σ v p →
        ∀ (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∃ red : PtQ L A →+ Additive (Ab.Pt (AlgebraicClosure k)),
            (∀ x, red (N • f x) =
              MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) α) (red x)) ∧
            ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ,
              (∀ x : PtQ L A, (ℓ ^ n) • x = 0 → red x = 0 → x = 0) ∧
              (∀ y, (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ red x = y)

/-- **`AlgFrobRed` from `AlgFrobRedAt` (proved):** apply `AlgFrobRedAt` at the place `g(v)` to
the arithmetic Frobenius `gτg⁻¹` there. -/
theorem algFrobRed_of_at (h : AlgFrobRedAt) : FrobTrace.AlgFrobRed := by
  intro L _ _ A F hF1 hF2
  obtain ⟨S, hS⟩ := h L A F hF1 hF2
  exact ⟨S, fun p hp hpS v τ hv hτ g f hf =>
    hS p hp hpS (g • v) (g * τ * g⁻¹) (liesOver_smul g hv) (isArithFrob_conj g hτ) f hf⟩

/-! ## 2. Isolating the finite set: good reduction outside finitely many primes -/

/-- **`GoodRedCofinite` (LEAF candidate; good reduction almost everywhere).** An abelian variety
`A` over a number field `L ⊆ ℚ̄` has good reduction at every place of `L` above all but finitely
many primes `p`: there is a finite `S` with `A` having good reduction (I2's `HasGoodReduction`:
an abelian scheme over the valuation ring with generic fibre `≅ A`) at `v ∩ L` for every place
`v` of `ℚ̄` above `p ∉ S`. Source: spreading out, EGA IV₃ §8 (8.8.2, 8.10.5) and EGA IV₄ 17.7.8
for smoothness, with properness and geometric connectedness of fibres; in this form e.g.
Serre–Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968), §1, and
Milne, *Abelian varieties* (in Cornell–Silverman, *Arithmetic Geometry*, 1986), §20
(all locators UNVERIFIED). -/
def GoodRedCofinite : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L),
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
        PkgI2.HasGoodReduction (ObjBridge.toGrp A) (v.comap (algebraMap L PkgI4.Qbar))

/-- **`AlgFrobRedGood` (GLUE, AV side; Glazer N5 L777-786; the reduction map at one place of
good reduction).** `AlgFrobRedAt` at a single place `v ∣ p` at which `A` has good reduction
(`HasGoodReduction` at `v ∩ L`), with no finite set: for `σ` an arithmetic Frobenius at `v` and
`f(x) = F ∘ x ∘ Spec(σ)` additive (`F : A → A` finite surjective), there are `Ā/k`
(`char k = p`), `α' ∈ End(Ā)`, `N ≠ 0` and `red : A(ℚ̄) → Ā(k̄)` with `red ∘ (N·f) = α' ∘ red`,
injective on `ℓⁿ`-torsion and onto `Ā(k̄)[ℓⁿ]` from `A(ℚ̄)[ℓⁿ]` for every prime `ℓ ≠ p`.

Why it is true (SPECULATIVE in its Lean details; `N = 1`): `𝒜/O_w` (`w = v ∩ L`) the abelian
scheme, `Ā` its special fibre over `k = κ(w)`; `red` is `A(ℚ̄) = 𝒜(O_v) → Ā(κ(v)) ≅ Ā(k̄)`
(valuative criterion); `F` is an `L`-morphism `A → A^{(s)}`, `s = σ⁻¹|_L ∈ D(w)`, and `A^{(s)}`
has good reduction at `s(w) = w`, so `F` extends to `𝒜 → 𝒜^{(s)}` (leaf I2-NMP); `f` reduces to
`F̄ ∘ Fr_Ā`, a `k`-morphism fixing `0`, hence `α' ∈ End(Ā)` (rigidity); the torsion clauses are
leaf I2-Red. -/
def AlgFrobRedGood : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob σ v p →
        PkgI2.HasGoodReduction (ObjBridge.toGrp A) (v.comap (algebraMap L PkgI4.Qbar)) →
        ∀ (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k)
          (α : PkgI3.AbVar.End Ab) (N : ℕ), N ≠ 0 ∧
          ∃ red : PtQ L A →+ Additive (Ab.Pt (AlgebraicClosure k)),
            (∀ x, red (N • f x) =
              MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := AlgebraicClosure k) α) (red x)) ∧
            ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ,
              (∀ x : PtQ L A, (ℓ ^ n) • x = 0 → red x = 0 → x = 0) ∧
              (∀ y, (ℓ ^ n) • y = 0 → ∃ x, (ℓ ^ n) • x = 0 ∧ red x = y)

/-- **`AlgFrobRedAt` from the leaf `GoodRedCofinite` and the local glue `AlgFrobRedGood`
(proved):** `S` is the finite set of `GoodRedCofinite` for `A`. -/
theorem algFrobRedAt_of_good (hG : GoodRedCofinite) (hL : AlgFrobRedGood) : AlgFrobRedAt := by
  intro L _ _ A F hF1 hF2
  obtain ⟨S, hS⟩ := hG L A
  exact ⟨S, fun p hp hpS v σ hv hσ f hf =>
    hL L A F hF1 hF2 p hp v σ hv hσ (hS p hp hpS v hv) f hf⟩

/-- **`AlgFrobRed` from `GoodRedCofinite` and `AlgFrobRedGood` (proved).** -/
theorem algFrobRed_of_good (hG : GoodRedCofinite) (hL : AlgFrobRedGood) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_at (algFrobRedAt_of_good hG hL)

/-- **`TateBridge35` from I3.M0, `GoodRedCofinite` and `AlgFrobRedGood` (proved).** -/
theorem tateBridge35_of_good (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hL : AlgFrobRedGood) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_good hG hL)

/-! ## 3. The local glue: special fibre, reduction relation, Frobenius -/

/-- `O_w = v ∩ L`, the valuation ring of `L` below the place `v` of `ℚ̄`. -/
abbrev Ow (L : IF) (v : ValuationSubring PkgI4.Qbar) : ValuationSubring L :=
  v.comap (algebraMap L PkgI4.Qbar)

/-- The residue field `k = κ(w)` of `O_w`. -/
abbrev kw (L : IF) (v : ValuationSubring PkgI4.Qbar) : Type :=
  IsLocalRing.ResidueField (Ow L v)

/-- The special fibre `𝒜 ×_{O} κ(O)` of a group object over a local ring `O`, as a group object
over `Spec κ(O)` (base change along `Spec κ(O) → Spec O`). -/
def sf {O : Type} [CommRing O] [IsLocalRing O] (𝒜 : Grp (Over (Spec (.of O)))) :
    Grp (Over (Spec (.of (IsLocalRing.ResidueField O)))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))).mapGrp.obj 𝒜

/-- **`SmoothGeomConnIntegral` (LEAF candidate, textbook; Stacks Project / EGA IV₂).** A smooth,
quasi-compact, geometrically connected scheme over a field is geometrically integral (smooth ⇒
geometrically normal, EGA IV₂ 6.8.1 / 6.7.4 (UNVERIFIED); a connected, quasi-compact, locally
Noetherian normal scheme is integral, Stacks Tag 033M (UNVERIFIED); applied after every field
base change, which preserves smoothness and connectedness). -/
def SmoothGeomConnIntegral : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (.of k)),
    Smooth f → GeometricallyConnected f → QuasiCompact f → GeometricallyIntegral f

/-- The special fibre of an abelian scheme over a local ring is an abelian variety (I2's
`IsAbelianVariety`): properness, smoothness and geometric connectedness are stable under base
change (Mathlib), and geometric integrality is `SmoothGeomConnIntegral`. -/
theorem sf_isAbelianVariety (hS : SmoothGeomConnIntegral) {O : Type} [CommRing O]
    [IsLocalRing O] (𝒜 : Grp (Over (Spec (.of O)))) [h : PkgI2.IsAbelianScheme 𝒜] :
    PkgI2.IsAbelianVariety (sf 𝒜) := by
  haveI := h.proper; haveI := h.smooth; haveI := h.geomConnected
  have hp : IsProper (sf 𝒜).X.hom := by
    show IsProper (pullback.snd 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))))
    infer_instance
  have hs : Smooth (sf 𝒜).X.hom := by
    show Smooth (pullback.snd 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))))
    infer_instance
  have hc : GeometricallyConnected (sf 𝒜).X.hom := by
    show GeometricallyConnected
      (pullback.snd 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))))
    infer_instance
  exact ⟨hp, hs, hS _ _ _ hs hc inferInstance⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **The reduction relation.** For `A/L`, an abelian scheme `𝒜/O_w` with `e : 𝒜_L ≅ A`, and a
ring map `j : κ(v) → κ(w)‾`: the `κ(w)‾`-point `y` of the special fibre is the reduction of
`x ∈ A(ℚ̄)` (via `j`) if some `O_w`-morphism `x' : Spec O_v → 𝒜` restricts to `x` on the generic
point (through `e`; the clause of I2's `IsReductionOf`, copied) and `y` followed by the projection
to `𝒜` is `x'` on `Spec κ(v)`, read through `Spec j`. -/
def RedRel {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (x : PtQ L A) (y : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))) : Prop :=
  ∃ x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X,
    ((Additive.toMul x) ≫ (e.inv.hom.hom : A.X ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj 𝒜.X)).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))) =
      Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left ∧
    y.left ≫ pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v)))) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
        x'.left

/-- `char κ(w) = p` for `w = v ∩ L`, `v ∣ p`. -/
theorem charP_kw {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ} (hp : p.Prime)
    (hv : PkgI4.LiesOver v p) : CharP (kw L v) p := by
  have h1 : ((p : Ow L v) : L) ∈ (Ow L v).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hin
    rw [ValuationSubring.mem_comap, map_inv₀] at hin
    have he : (algebraMap L PkgI4.Qbar ((p : Ow L v) : L)) = (p : PkgI4.Qbar) := by simp
    rw [he] at hin
    have hv' := hv
    unfold PkgI4.LiesOver at hv'
    rw [ValuationSubring.mem_nonunits_iff_or] at hv'
    rcases hv' with h0 | h0
    · exact (Nat.cast_ne_zero.mpr hp.ne_zero) h0
    · exact h0 hin
  have h2 : (p : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    (ValuationSubring.coe_mem_nonunits_iff).mp h1
  have h3 : (p : kw L v) = 0 := by
    rw [← map_natCast (IsLocalRing.residue (Ow L v)), IsLocalRing.residue_eq_zero_iff]
    exact h2
  exact (CharP.charP_iff_prime_eq_zero hp).mpr h3

/-- `ℓⁿ` is a unit of `O_w` for a prime `ℓ ≠ p`. -/
theorem isUnit_cast_of_ne {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ} (hp : p.Prime)
    (hv : PkgI4.LiesOver v p) {ℓ : ℕ} (hℓ : ℓ.Prime) (hne : ℓ ≠ p) (n : ℕ) :
    IsUnit (((ℓ ^ n : ℕ)) : Ow L v) := by
  by_contra hnu
  have hm : ((ℓ ^ n : ℕ) : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have h0 : ((ℓ ^ n : ℕ) : kw L v) = 0 := by
    rw [← map_natCast (IsLocalRing.residue (Ow L v)), IsLocalRing.residue_eq_zero_iff]
    exact hm
  haveI := charP_kw (L := L) hp hv
  rw [CharP.cast_eq_zero_iff (kw L v) p] at h0
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow h0)).symm

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ReductionMapGood` (GLUE; valuative criterion of properness, Stacks Tag 0BX5 / EGA II 7.3.8
(UNVERIFIED locators)).** At a place `v ∣ p` and an abelian scheme `𝒜/O_w` (`w = v ∩ L`) with
`e : 𝒜_L ≅ A`: there are a ring isomorphism `j : κ(v) ≅ κ(w)‾` compatible with the maps from
`O_w` (`κ(v)` is an algebraic closure of `κ(w)`) and a group homomorphism
`red : A(ℚ̄) → Ā(κ(w)‾)` (`Ā` the special fibre `sf 𝒜`) with `RedRel x (red x)` for every `x`
(existence of the lift `x' : Spec O_v → 𝒜`, valuative criterion: `𝒜` proper, `O_v` a valuation
ring with fraction field `ℚ̄`), and the reduction is unique (uniqueness of the lift, `𝒜`
separated, plus the universal property of the fibre product). `red` is a homomorphism since
restriction `𝒜(O_v) → 𝒜(ℚ̄)` is a bijective homomorphism and reduction `𝒜(O_v) → 𝒜(κ(v))` is
one. No Frobenius, no torsion. -/
def ReductionMapGood : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) (p : ℕ), p.Prime →
    ∀ (v : ValuationSubring PkgI4.Qbar), PkgI4.LiesOver v p →
    ∀ (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
      (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
        ObjBridge.toGrp A),
    ∃ j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v), Function.Bijective j ∧
      (∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) ∧
      ∃ red : PtQ L A →+ Additive (PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))),
        (∀ x, RedRel v 𝒜 e j x (Additive.toMul (red x))) ∧
        (∀ x y y', RedRel v 𝒜 e j x y → RedRel v 𝒜 e j x y' → y = y')

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RedTorsionQbar` (GLUE: leaf I2-Red, `PkgI2.ReductionTorsionBijective` (Serre–Tate 1968,
§1), transported).** For `m ≥ 1` invertible in `O_w` and any ring isomorphism
`j : κ(v) ≅ κ(w)‾` compatible with the maps from `O_w`: reduction (`RedRel`) is a bijection
`A(ℚ̄)[m] → Ā(κ(w)‾)[m]`, in I2-Red's form (`∃!` both ways). This is I2-Red for the abelian scheme
`𝒜` over the DVR `O_w` (a valuation ring of the number field `L` with `p` a nonunit), read
through the `L`-isomorphism `ℚ̄ ≅ L‾` (`ℚ̄` is an algebraic closure of `L`), the universal
property of `sf 𝒜 = 𝒜 ×_{O_w} κ(w)` (points of `𝒜` over `κ(v)` = `κ(w)`-points of `sf 𝒜` over
`κ(v)`) and `j`. -/
def RedTorsionQbar : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) (p : ℕ), p.Prime →
    ∀ (v : ValuationSubring PkgI4.Qbar), PkgI4.LiesOver v p →
    ∀ (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
      (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
        ObjBridge.toGrp A)
      (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)), Function.Bijective j →
      (∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) →
      ∀ m : ℕ, 0 < m → IsUnit (m : Ow L v) →
        (∀ x : PtQ L A, m • x = 0 →
          ∃! y : Additive (PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))),
            m • y = 0 ∧ RedRel v 𝒜 e j x (Additive.toMul y)) ∧
        (∀ y : Additive (PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))), m • y = 0 →
          ∃! x : PtQ L A, m • x = 0 ∧ RedRel v 𝒜 e j x (Additive.toMul y))

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ReductionFrobGood` (GLUE, AV side; Glazer N5 L777-786; the Frobenius step).** At a place
`v ∣ p` with an abelian scheme `𝒜/O_w` and `e : 𝒜_L ≅ A`, `σ` an arithmetic Frobenius at `v`,
`F : A → A` finite surjective and `f(x) = F ∘ x ∘ Spec(σ)` additive: there is an endomorphism
`ᾱ` of the special fibre `Ā = sf 𝒜` (a morphism of group objects over `κ(w)`) such that for every
ring map `j : κ(v) → κ(w)‾`, if `y` is the reduction of `x` then `ᾱ ∘ y` is the reduction of
`f x`.

Why it is true (SPECULATIVE in its Lean details): `F` lies over `Spec(t)`, `t = σ⁻¹|_L ∈ D(w)`
(forced by `f(x)` being an `L`-point); `F` extends to `F̃ : 𝒜 → 𝒜` over `Spec(t|_{O_w})` (leaf
I2-NMP applied to `𝒜` and its base change along `t`); a lift of `f x` is
`Spec(σ|_{O_v}) ≫ x' ≫ F̃`; on `Spec κ(v)`, `σ` induces the `p`-power map (`IsArithFrob`), i.e.
the absolute Frobenius, which commutes with every morphism of schemes; so the reduction of
`f x` is `y ≫ Fr_Ā ≫ F̄` with `F̄` the base change of `F̃` (over `Spec(t̄) = Spec(Frob⁻¹)`), and
`ᾱ = Fr_Ā ≫ F̄` lies over `id_{κ(w)}` and fixes `0` (`f` is additive), hence is a homomorphism
(rigidity, Mumford, *Abelian varieties*, §4 Cor. 1, UNVERIFIED locator). -/
def ReductionFrobGood : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ),
        PkgI4.LiesOver v p → PkgI4.IsArithFrob σ v p →
        ∀ (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
          (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
            𝒜 ≅ ObjBridge.toGrp A)
          (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
            Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
              (Additive.toMul x).left ≫ F) →
        ∃ ab : sf 𝒜 ⟶ sf 𝒜,
          ∀ (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (x : PtQ L A)
            (y : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))),
            RedRel v 𝒜 e j x y → RedRel v 𝒜 e j (f x) (y ≫ ab.hom.hom)

set_option synthInstance.maxHeartbeats 400000 in
/-- **`AlgFrobRedGood` from `SmoothGeomConnIntegral`, `ReductionMapGood`, `RedTorsionQbar` and
`ReductionFrobGood` (proved).** `k = κ(w)`, `Ā = sf 𝒜` (an abelian variety by
`sf_isAbelianVariety`), `α' = ᾱ`, `N = 1`, `red` from `ReductionMapGood`; the intertwining is the
uniqueness of reductions, the torsion clauses are `RedTorsionQbar` at `m = ℓⁿ` (a unit of `O_w`,
`isUnit_cast_of_ne`). -/
theorem algFrobRedGood_of (hS : SmoothGeomConnIntegral) (h1 : ReductionMapGood)
    (h2 : RedTorsionQbar) (h3 : ReductionFrobGood) : AlgFrobRedGood := by
  intro L _ _ A F hF1 hF2 p hp v σ hv hσ hgood f hf
  obtain ⟨𝒜, h𝒜, ⟨e⟩⟩ := hgood
  haveI := h𝒜
  haveI hAV := sf_isAbelianVariety hS 𝒜
  obtain ⟨j, hjb, hjc, red, hred, huniq⟩ := h1 L A p hp v hv 𝒜 e
  obtain ⟨ab, hab⟩ := h3 L A F hF1 hF2 p hp v σ hv hσ 𝒜 e f hf
  refine ⟨kw L v, inferInstance, charP_kw hp hv, ObjBridge.ofGrp (sf 𝒜),
    ObjBridge.homOfGrp ab, 1, one_ne_zero, red, ?_, ?_⟩
  · intro x
    rw [one_smul]
    exact congrArg Additive.ofMul (huniq (f x) _ _ (hred (f x)) (hab j x _ (hred x)))
  · intro ℓ hℓ hne n
    have hu := isUnit_cast_of_ne (L := L) hp hv hℓ hne n
    obtain ⟨-, hB⟩ := h2 L A p hp v hv 𝒜 e j hjb hjc (ℓ ^ n) (pow_pos hℓ.pos n) hu
    refine ⟨fun x hx h0 => ?_, fun y hy => ?_⟩
    · have hx0 : RedRel v 𝒜 e j x (Additive.toMul 0) := h0 ▸ hred x
      have h00 : RedRel v 𝒜 e j 0 (Additive.toMul 0) := (map_zero red) ▸ hred 0
      exact (hB 0 (smul_zero _)).unique ⟨hx, hx0⟩ ⟨smul_zero _, h00⟩
    · obtain ⟨x, ⟨hx, hxr⟩, -⟩ := hB y hy
      exact ⟨x, hx, congrArg Additive.ofMul (huniq x _ _ (hred x) hxr)⟩

/-! ## 4. `ReductionMapGood` from the valuative criterion (Mathlib) and two smaller Props -/

set_option synthInstance.maxHeartbeats 400000 in
/-- `x ∈ A(ℚ̄)` as a `ℚ̄`-point of `𝒜_L` (through `e`). -/
def genPt {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) :
    PkgI3.AbVar.ptObj (K := L) PkgI4.Qbar ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj 𝒜.X :=
  (Additive.toMul x) ≫ (e.inv.hom.hom : A.X ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj 𝒜.X)

set_option synthInstance.maxHeartbeats 400000 in
/-- The generic point map `Spec ℚ̄ → 𝒜` of `x ∈ A(ℚ̄)` (through `e`), as in `RedRel`. -/
def genMap {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) : Spec (.of PkgI4.Qbar) ⟶ 𝒜.X.left :=
  (genPt v 𝒜 e x).left ≫
    pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))

set_option synthInstance.maxHeartbeats 400000 in
/-- The valuative square: `Spec ℚ̄ → 𝒜` over `Spec O_v → Spec O_w`. -/
theorem genMap_comm {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) :
    genMap v 𝒜 e x ≫ 𝒜.X.hom = Spec.map (CommRingCat.ofHom (algebraMap v PkgI4.Qbar)) ≫
      Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)) := by
  have key : ∀ (T : Scheme) (u : T ⟶ pullback 𝒜.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))),
      (u ≫ pullback.fst _ _) ≫ 𝒜.X.hom = (u ≫ pullback.snd _ _) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) := fun T u => by
    rw [Category.assoc, pullback.condition, Category.assoc]
  have hw : (genPt v 𝒜 e x).left ≫ pullback.snd 𝒜.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))) =
      Spec.map (CommRingCat.ofHom (algebraMap L PkgI4.Qbar)) := Over.w (genPt v 𝒜 e x)
  have h2 : ((genPt v 𝒜 e x).left ≫ pullback.snd _ _) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) =
      Spec.map (CommRingCat.ofHom (algebraMap L PkgI4.Qbar)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) :=
    congrArg (fun t => t ≫ Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))) hw
  have h3 : Spec.map (CommRingCat.ofHom (algebraMap L PkgI4.Qbar)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) =
      Spec.map (CommRingCat.ofHom (algebraMap v PkgI4.Qbar)) ≫
        Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  exact (key _ (genPt v 𝒜 e x).left).trans (h2.trans h3)

set_option synthInstance.maxHeartbeats 400000 in
/-- The valuative commutative square of `x`. -/
def vsq {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) : ValuativeCommSq 𝒜.X.hom where
  R := v
  K := PkgI4.Qbar
  i₁ := genMap v 𝒜 e x
  i₂ := Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))
  commSq := ⟨genMap_comm v 𝒜 e x⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **Existence of the lift** `x' : Spec O_v → 𝒜` (proved: valuative criterion for the proper
`𝒜 → Spec O_w`, Mathlib `UniversallyClosed.eq_valuativeCriterion`). -/
theorem exists_lift {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [h𝒜 : PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A) :
    ∃ x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X,
      genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left := by
  haveI := h𝒜.proper
  have h1 : (ValuativeCriterion.Existence ⊓ @QuasiCompact) 𝒜.X.hom := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
  obtain ⟨⟨l, hl1, hl2⟩⟩ := h1.1 (vsq v 𝒜 e x)
  exact ⟨Over.homMk l hl2, hl1.symm⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **Uniqueness of the lift** (proved: valuative criterion of separatedness, Mathlib
`IsSeparated.valuativeCriterion`). -/
theorem lift_unique {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [h𝒜 : PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A) (x : PtQ L A)
    (x₁ x₂ : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X)
    (h₁ : genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x₁.left)
    (h₂ : genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x₂.left) : x₁ = x₂ := by
  haveI := h𝒜.proper
  have hU := IsSeparated.valuativeCriterion 𝒜.X.hom (vsq v 𝒜 e x)
  have e1 : (⟨x₁.left, h₁.symm, Over.w x₁⟩ : (vsq v 𝒜 e x).commSq.LiftStruct) =
      ⟨x₂.left, h₂.symm, Over.w x₂⟩ := Subsingleton.elim _ _
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l e1)

set_option synthInstance.maxHeartbeats 400000 in
/-- Every `x` has a reduction, for `j` compatible with the maps from `O_w` (proved). -/
theorem exists_redRel {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (x : PtQ L A) : ∃ y, RedRel v 𝒜 e j x y := by
  obtain ⟨x', hx'⟩ := exists_lift v 𝒜 e x
  have hw : (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue v)) ≫ x'.left) ≫ 𝒜.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (kw L v) (AlgebraicClosure (kw L v)))) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))) := by
    rw [Category.assoc, Category.assoc, Over.w x']
    simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact hjc a
  refine ⟨Over.homMk (pullback.lift _ _ hw) (pullback.lift_snd _ _ hw), x', hx', ?_⟩
  exact pullback.lift_fst _ _ hw

set_option synthInstance.maxHeartbeats 400000 in
/-- Reductions are unique (proved: uniqueness of the lift and of maps into a fibre product). -/
theorem redRel_unique {L : IF} {A : PkgI3.AbVar L} (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (x : PtQ L A)
    (y y' : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))) :
    RedRel v 𝒜 e j x y → RedRel v 𝒜 e j x y' → y = y' := by
  rintro ⟨x₁, h₁, h₁'⟩ ⟨x₂, h₂, h₂'⟩
  obtain rfl := lift_unique v 𝒜 e x x₁ x₂ h₁ h₂
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h₁'.trans h₂'.symm
  · exact (Over.w y).trans (Over.w y').symm

/-- **`ResidueAlgClosure` (GLUE, standard commutative algebra).** For a place `v ∣ p` of `ℚ̄` and
`w = v ∩ L`, there is a ring isomorphism `j : κ(v) ≅ κ(w)‾` compatible with the maps from `O_w`:
`κ(v)` is algebraically closed (the residue field of a valuation ring of an algebraically closed
field) and algebraic over `κ(w)` (`ℚ̄/L` is algebraic), hence an algebraic closure of `κ(w)`
(Engler–Prestel, *Valued fields* (2005), Thm 3.2.11 and §3.2; Bourbaki, *Alg. Comm.* VI §8;
locators UNVERIFIED). -/
def ResidueAlgClosure : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (v : ValuationSubring PkgI4.Qbar) (p : ℕ), p.Prime →
    PkgI4.LiesOver v p →
    ∃ j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v), Function.Bijective j ∧
      (∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RedRelMul` (GLUE; reduction respects the group law).** If `y₁, y₂` are the reductions of
`x₁, x₂` then `y₁ y₂` is the reduction of `x₁ + x₂`: the product `x'₁ x'₂` of the lifts (in the
group `𝒜(O_v)`) lifts `x₁ + x₂` (restriction to the generic point and `e` respect the group
laws), and base change to the special fibre respects them too (`sf 𝒜` carries the base-changed
group law). -/
def RedRelMul : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L) (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (x₁ x₂ : PtQ L A)
    (y₁ y₂ : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))),
    RedRel v 𝒜 e j x₁ y₁ → RedRel v 𝒜 e j x₂ y₂ → RedRel v 𝒜 e j (x₁ + x₂) (y₁ * y₂)

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ReductionMapGood` from `ResidueAlgClosure` and `RedRelMul` (proved)**, with the valuative
criterion (existence and uniqueness of lifts) from Mathlib. -/
theorem reductionMapGood_of (hR : ResidueAlgClosure) (hM : RedRelMul) : ReductionMapGood := by
  intro L _ A p hp v hv 𝒜 _ e
  obtain ⟨j, hjb, hjc⟩ := hR L v p hp hv
  choose r hr using exists_redRel v 𝒜 e j hjc
  have hun := redRel_unique v 𝒜 e j
  let red : PtQ L A →+ Additive (PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v))) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (r x)) (fun a b => by
      show Additive.ofMul (r (a + b)) = Additive.ofMul (r a * r b)
      exact congrArg Additive.ofMul (hun _ _ _ (hr (a + b)) (hM L A v 𝒜 e j a b _ _ (hr a) (hr b))))
  exact ⟨j, hjb, hjc, red, fun x => hr x, hun⟩

/-- **`AlgFrobRed` from the leaves `GoodRedCofinite`, `SmoothGeomConnIntegral` and the glue
`ReductionMapGood`, `RedTorsionQbar`, `ReductionFrobGood` (proved).** -/
theorem algFrobRed_of_pieces (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (h1 : ReductionMapGood) (h2 : RedTorsionQbar) (h3 : ReductionFrobGood) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_good hG (algFrobRedGood_of hS h1 h2 h3)

/-- **`TateBridge35` from I3.M0 and the five pieces (proved).** -/
theorem tateBridge35_of_pieces (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (h1 : ReductionMapGood) (h2 : RedTorsionQbar)
    (h3 : ReductionFrobGood) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_pieces hG hS h1 h2 h3)

/-- **Main result: `AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the glue `ResidueAlgClosure`, `RedRelMul`, `RedTorsionQbar`,
`ReductionFrobGood` (proved).** The valuative criterion (existence and uniqueness of the lift
`Spec O_v → 𝒜`), the special fibre being an abelian variety (up to `SmoothGeomConnIntegral`), the
residue characteristic, the units `ℓⁿ` and the conjugation of the place are proved here. -/
theorem algFrobRed_of_split (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hR : ResidueAlgClosure) (hM : RedRelMul) (h2 : RedTorsionQbar) (h3 : ReductionFrobGood) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_pieces hG hS (reductionMapGood_of hR hM) h2 h3

/-- **`TateBridge35` from I3.M0 and the six pieces (proved).** -/
theorem tateBridge35_of_split (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hR : ResidueAlgClosure) (hM : RedRelMul)
    (h2 : RedTorsionQbar) (h3 : ReductionFrobGood) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_split hG hS hR hM h2 h3)

/-! ## 5. `ReductionFrobGood` from the extension of `F` and the twisted Frobenius -/

/-- `σ` restricted to `O_v`, for `σ` in the decomposition group of `v`. -/
def sigV {v : ValuationSubring PkgI4.Qbar} (σ : PkgI4.GQ) (hσ : σ ∈ v.decompositionSubgroup ℚ) :
    v →+* v where
  toFun y := ⟨σ y, by
    have h : σ • v = v := hσ
    have h2 := ValuationSubring.smul_mem_pointwise_smul σ (y : PkgI4.Qbar) v y.2
    rw [h, AlgEquiv.smul_def] at h2
    exact h2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' a b := Subtype.ext (map_mul σ _ _)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' a b := Subtype.ext (map_add σ _ _)

/-- An arithmetic Frobenius acts on `κ(v)` as `z ↦ z^p` (proved from `IsArithFrob`). -/
theorem residue_sigV {v : ValuationSubring PkgI4.Qbar} {σ : PkgI4.GQ} {p : ℕ}
    (hσ : PkgI4.IsArithFrob σ v p) (y : v) :
    IsLocalRing.residue v (sigV σ hσ.1 y) = IsLocalRing.residue v y ^ p := by
  rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  have h := hσ.2 y y.2
  simpa [sigV] using h

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FExtend` (GLUE; leaf I2-NMP, `PkgI2.NeronMappingAbelianScheme` (BLR, *Néron models*,
§1.2), applied to the conjugate model).** At a place `v ∣ p` with an abelian scheme `𝒜/O_w`,
`e : 𝒜_L ≅ A`, `σ` an arithmetic Frobenius at `v`, `F : A → A` finite surjective and
`f(x) = F ∘ x ∘ Spec(σ)` additive: there are a ring endomorphism `t` of `O_w` (it is
`σ⁻¹|_{O_w}`) and a morphism of schemes `F̃ : 𝒜 → 𝒜` over `Spec(t)` such that `t` induces
`Frob⁻¹` on `κ(w)` (`t(a)^p ≡ a`), `F̃` maps the unit section to itself (over `Spec t`), and
`F̃` extends `F`: whenever `x'` is the lift of `x`, `Spec(σ|_{O_v}) ≫ x' ≫ F̃` is a lift of `f x`.

Why it is true: `f(x) ∈ A(ℚ̄)` for all `x` forces `F` to lie over `Spec(σ⁻¹|_L)`, so `F` is an
`L`-morphism `A → A^{(t)}`; `A^{(t)}` is the generic fibre of the base change `𝒜^{(t)}` of `𝒜`
along `t|_{O_w}` (`σ ∈ D(v)`, so `t(O_w) = O_w`), and I2-NMP extends it to `𝒜 → 𝒜^{(t)}`, i.e.
`F̃`; the lift identity holds on the generic point, and `F̃` fixes `0` since `f(0) = 0` and `𝒜`
is separated over the integral `Spec O_w`. `t(a)^p ≡ a` since `σ` acts on `κ(v)` as `z ↦ z^p`. -/
def FExtend : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ) (_ : PkgI4.LiesOver v p)
        (hσ : PkgI4.IsArithFrob σ v p)
        (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
        (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
          𝒜 ≅ ObjBridge.toGrp A)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ (Ft : 𝒜.X.left ⟶ 𝒜.X.left) (t : Ow L v →+* Ow L v),
          Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ Spec.map (CommRingCat.ofHom t) ∧
          (∀ a, IsLocalRing.residue (Ow L v) (t a) ^ p = IsLocalRing.residue (Ow L v) a) ∧
          (η[𝒜.X]).left ≫ Ft = Spec.map (CommRingCat.ofHom t) ≫ (η[𝒜.X]).left ∧
          ∀ (x : PtQ L A)
            (x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X),
            genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left →
            ∃ x'' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X,
              genMap v 𝒜 e (f x) = Spec.map (CommRingCat.ofHom v.subtype) ≫ x''.left ∧
              x''.left = Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫ x'.left ≫ Ft

/-- **`FrobMorph` (GLUE; the absolute Frobenius of the special fibre twisted by `F̄`).** Let `O`
be a local ring with residue field `k` of characteristic `p`, `𝒜/O` an abelian scheme,
`t : O → O` a ring map inducing `Frob⁻¹` on `k` (`t(a)^p ≡ a`) and `F̃ : 𝒜 → 𝒜` a morphism over
`Spec(t)` fixing the unit section. Then there is a `k`-morphism `β` of the special fibre
`Ā = sf 𝒜` fixing `0` with `β ∘ y = F̃ ∘ y ∘ Spec(z ↦ z^p)` on `k̄`-points (after projecting to
`𝒜`).

Why it is true: `β = Fr_Ā ≫ F̄`, with `Fr_Ā` the absolute Frobenius of the `𝔽_p`-scheme `Ā`
(over `Fr_{Spec k} = Spec(z ↦ z^p)`) and `F̄ = F̃ ×_{Spec t} Spec(t̄)` the base change (over
`Spec t̄`, `t̄ = Frob⁻¹`); `β` lies over `Spec(t̄) ∘ Spec(Frob) = id`; on a point,
`y ≫ Fr_Ā = Fr_{Spec k̄} ≫ y` (naturality of the absolute Frobenius), and `Fr_Ā, F̄` fix `0`. The
absolute Frobenius of schemes is not in Mathlib 4.35. -/
def FrobMorph : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (p : ℕ), p.Prime →
    CharP (IsLocalRing.ResidueField O) p →
    ∀ (𝒜 : Grp (Over (Spec (.of O)))) [PkgI2.IsAbelianScheme 𝒜]
      (Ft : 𝒜.X.left ⟶ 𝒜.X.left) (t : O →+* O),
      Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ Spec.map (CommRingCat.ofHom t) →
      (∀ a, IsLocalRing.residue O (t a) ^ p = IsLocalRing.residue O a) →
      (η[𝒜.X]).left ≫ Ft = Spec.map (CommRingCat.ofHom t) ≫ (η[𝒜.X]).left →
      ∃ β : (sf 𝒜).X ⟶ (sf 𝒜).X, η[(sf 𝒜).X] ≫ β = η[(sf 𝒜).X] ∧
        ∀ (y : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (IsLocalRing.ResidueField O)))
          (φ : AlgebraicClosure (IsLocalRing.ResidueField O) →+*
            AlgebraicClosure (IsLocalRing.ResidueField O)),
          (∀ z, φ z = z ^ p) →
          (y ≫ β).left ≫
              pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) =
            Spec.map (CommRingCat.ofHom φ) ≫ y.left ≫
              pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) ≫ Ft

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ReductionFrobGood` from `SmoothGeomConnIntegral`, `FExtend` and `FrobMorph` (proved)**,
with rigidity (`G0FibreSimple.rigidityHom`, proved from Mathlib by mul-rigidity, copied
verbatim): `ᾱ = β` is a homomorphism because it fixes `0`; the reduction of `f x` is computed
from the lift `Spec(σ|_{O_v}) ≫ x' ≫ F̃` and `residue_sigV` (`σ` is `z ↦ z^p` on `κ(v)`, and
`j` commutes with `z ↦ z^p`). -/
theorem reductionFrobGood_of (hS : SmoothGeomConnIntegral) (hE : FExtend) (hFr : FrobMorph) :
    ReductionFrobGood := by
  intro L _ _ A F hF1 hF2 p hp v σ hv hσ 𝒜 _ e f hf
  obtain ⟨Ft, t, hover, hres, hzero, hlift⟩ := hE L A F hF1 hF2 p hp v σ hv hσ 𝒜 e f hf
  haveI := charP_kw (L := L) hp hv
  obtain ⟨β, hβ0, hβ⟩ := hFr (Ow L v) p hp inferInstance 𝒜 Ft t hover hres hzero
  haveI hAV := sf_isAbelianVariety hS 𝒜
  haveI hmon : IsMonHom β := G0FibreSimple.rigidityHom _ (ObjBridge.ofGrp (sf 𝒜))
    (ObjBridge.ofGrp (sf 𝒜)) β hβ0
  refine ⟨Grp.homMk β, fun j x y ⟨x', hx', hy⟩ => ?_⟩
  obtain ⟨x'', hx'', hx''eq⟩ := hlift x x' hx'
  refine ⟨x'', hx'', ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (AlgebraicClosure (kw L v)) p :=
    charP_of_injective_algebraMap (algebraMap (kw L v) _).injective p
  have h1 := hβ y (frobenius _ p) (fun z => rfl)
  have hring : Spec.map (CommRingCat.ofHom (frobenius (AlgebraicClosure (kw L v)) p)) ≫
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
        Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext z
    simp only [RingHom.comp_apply, residue_sigV hσ, map_pow, frobenius_def]
  have h3 := congrArg (fun m => Spec.map (CommRingCat.ofHom
    (frobenius (AlgebraicClosure (kw L v)) p)) ≫ m ≫ Ft) hy
  have h5 : Spec.map (CommRingCat.ofHom (frobenius (AlgebraicClosure (kw L v)) p)) ≫
      (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
        x'.left) ≫ Ft =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
        Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫ x'.left ≫ Ft := by
    have h4 := congrArg (fun m => m ≫ x'.left ≫ Ft) hring
    simp only [Category.assoc] at h4 ⊢
    exact h4
  have h2 := (congrArg (fun m => Spec.map (CommRingCat.ofHom
    (frobenius (AlgebraicClosure (kw L v)) p)) ≫ m) (Category.assoc y.left _ Ft).symm).trans
    (h3.trans h5)
  rw [hx''eq]
  exact h1.trans h2

/-! ## 6. `ResidueAlgClosure` from two statements on residue fields -/

/-- `O_w → O_v` is a local homomorphism (proved). -/
instance isLocalHom_toW (L : IF) (v : ValuationSubring PkgI4.Qbar) :
    IsLocalHom (PkgI2.toW (Ow L v) v rfl) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : ((a : Ow L v) : L) ∈ (Ow L v).nonunits :=
    ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hna)
  have h2 : ((PkgI2.toW (Ow L v) v rfl a : v) : PkgI4.Qbar) ∈ v.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at h1 ⊢
    show algebraMap L PkgI4.Qbar (a : L) = 0 ∨ (algebraMap L PkgI4.Qbar (a : L))⁻¹ ∉ v
    rcases h1 with h | h
    · left; rw [h, map_zero]
    · right; rw [← map_inv₀]; exact h
  exact (IsLocalRing.mem_maximalIdeal _).mp (ValuationSubring.coe_mem_nonunits_iff.mp h2) ha

/-- **`ResidueAlgClosed` (GLUE, standard: the residue field of a valuation ring of an
algebraically closed field is algebraically closed; e.g. Engler–Prestel, *Valued fields* (2005),
Thm 3.2.11 (locator UNVERIFIED)).** Proof idea: lift a monic polynomial to `O_v`, take a root in
`ℚ̄`; it is integral over `O_v`, hence in `O_v`; reduce. -/
def ResidueAlgClosed : Prop :=
  ∀ v : ValuationSubring PkgI4.Qbar, IsAlgClosed (IsLocalRing.ResidueField v)

/-- **`ResidueAlgebraic` (GLUE, standard: the residue extension of an algebraic extension of
valued fields is algebraic; Bourbaki, *Alg. Comm.* VI §8.1, Engler–Prestel Cor. 3.2.3 (locators
UNVERIFIED)).** `κ(v)` is algebraic over `κ(w)`, `w = v ∩ L`, for the map induced by
`O_w → O_v`. -/
def ResidueAlgebraic : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (v : ValuationSubring PkgI4.Qbar),
    @Algebra.IsAlgebraic (kw L v) (IsLocalRing.ResidueField v) _ _
      (IsLocalRing.ResidueField.map (PkgI2.toW (Ow L v) v rfl)).toAlgebra

/-- **`ResidueAlgClosed` holds (proved from Mathlib):** lift a monic irreducible `q` over `κ(v)`
to a monic `Q` over `O_v`, take a root `z ∈ ℚ̄` of `Q`; `z` is integral over the integrally closed
`O_v`, so `z ∈ O_v`, and its residue is a root of `q`. -/
theorem residueAlgClosed : ResidueAlgClosed := by
  intro v
  refine IsAlgClosed.of_exists_root _ (fun q hq hirr => ?_)
  obtain ⟨Q, hQmap, hQdeg, hQmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective q) hq
  have hinj : Function.Injective (algebraMap v PkgI4.Qbar) := IsFractionRing.injective v PkgI4.Qbar
  have hdeg : (Q.map (algebraMap v PkgI4.Qbar)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj]
    intro h
    have h1 : Q.natDegree = 0 := Polynomial.natDegree_eq_of_degree_eq_some h
    rw [hQdeg] at h1
    exact (Irreducible.natDegree_pos hirr).ne' h1
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  rw [Polynomial.IsRoot, Polynomial.eval_map] at hz
  have hint : IsIntegral v z := ⟨Q, hQmon, hz⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [Polynomial.eval₂_hom] at hz
  have h0 : Q.eval y = 0 := hinj (hz.trans (map_zero _).symm)
  refine ⟨IsLocalRing.residue v y, ?_⟩
  rw [← hQmap, Polynomial.eval_map, Polynomial.eval₂_hom, h0, map_zero]

/-- **`ResidueAlgebraic` holds (proved from Mathlib):** for `y ∈ O_v`, take `P ∈ L[X]`, `P ≠ 0`,
`P(y) = 0`, and divide by a coefficient of largest valuation for `O_w`: the result has
coefficients in `O_w` and a coefficient `1`, so its reduction is a nonzero polynomial over `κ(w)`
vanishing at the residue of `y`. -/
theorem residueAlgebraic : ResidueAlgebraic := by
  intro L _ v
  letI : Algebra (kw L v) (IsLocalRing.ResidueField v) :=
    (IsLocalRing.ResidueField.map (PkgI2.toW (Ow L v) v rfl)).toAlgebra
  refine ⟨fun z => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  have hyalg : IsAlgebraic L (y : PkgI4.Qbar) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (y : PkgI4.Qbar)).tower_top L
  obtain ⟨P, hP0, hPy⟩ := hyalg
  obtain ⟨i, hi, hmax⟩ := P.support.exists_max_image (fun n => (Ow L v).valuation (P.coeff n))
    (Polynomial.support_nonempty.mpr hP0)
  have hci : P.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hlift : P * Polynomial.C (P.coeff i)⁻¹ ∈ Polynomial.lifts (algebraMap (Ow L v) L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_mul_C]
    have hmem : P.coeff n * (P.coeff i)⁻¹ ∈ Ow L v := by
      rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
      by_cases hn : n ∈ P.support
      · exact mul_inv_le_one_of_le₀ (hmax n hn) zero_le'
      · rw [Polynomial.notMem_support_iff.mp hn, map_zero, zero_mul]
        exact zero_le'
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨Q, hQ⟩ := (Polynomial.mem_lifts _).mp hlift
  have hinjO : Function.Injective (algebraMap (Ow L v) L) := IsFractionRing.injective (Ow L v) L
  have hQi : Q.coeff i = 1 := by
    apply hinjO
    rw [← Polynomial.coeff_map, hQ, Polynomial.coeff_mul_C, mul_inv_cancel₀ hci, map_one]
  refine ⟨Q.map (IsLocalRing.residue (Ow L v)), ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun r => r.coeff i) h0
    simp only [Polynomial.coeff_map, hQi, map_one, Polynomial.coeff_zero] at h1
    exact one_ne_zero h1
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap (kw L v) (IsLocalRing.ResidueField v)).comp
        (IsLocalRing.residue (Ow L v)) =
        (IsLocalRing.residue v).comp (PkgI2.toW (Ow L v) v rfl) := by
      ext a
      exact IsLocalRing.ResidueField.map_residue _ a
    rw [hcomp, ← Polynomial.hom_eval₂]
    have hzero : Q.eval₂ (PkgI2.toW (Ow L v) v rfl) y = 0 := by
      apply IsFractionRing.injective v PkgI4.Qbar
      rw [map_zero]
      have e1 := Polynomial.hom_eval₂ Q (PkgI2.toW (Ow L v) v rfl) (algebraMap v PkgI4.Qbar) y
      have e2 : (algebraMap v PkgI4.Qbar).comp (PkgI2.toW (Ow L v) v rfl) =
          (algebraMap L PkgI4.Qbar).comp (algebraMap (Ow L v) L) := rfl
      rw [e1, e2, ← Polynomial.eval₂_map, hQ, Polynomial.eval₂_mul, Polynomial.eval₂_C]
      have e3 : P.eval₂ (algebraMap L PkgI4.Qbar) (algebraMap v PkgI4.Qbar y) = 0 := hPy
      rw [e3, zero_mul]
    rw [hzero, map_zero]

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ResidueAlgClosure` from `ResidueAlgClosed` and `ResidueAlgebraic` (proved):** `κ(v)` is an
algebraic closure of `κ(w)`, so `IsAlgClosure.equiv` gives `j`. -/
theorem residueAlgClosure_of (h1 : ResidueAlgClosed) (h2 : ResidueAlgebraic) :
    ResidueAlgClosure := by
  intro L _ v p _ _
  letI : Algebra (kw L v) (IsLocalRing.ResidueField v) :=
    (IsLocalRing.ResidueField.map (PkgI2.toW (Ow L v) v rfl)).toAlgebra
  haveI : IsAlgClosed (IsLocalRing.ResidueField v) := h1 v
  haveI : Algebra.IsAlgebraic (kw L v) (IsLocalRing.ResidueField v) := h2 L v
  haveI : IsAlgClosure (kw L v) (IsLocalRing.ResidueField v) := ⟨inferInstance, inferInstance⟩
  let e := IsAlgClosure.equiv (kw L v) (IsLocalRing.ResidueField v) (AlgebraicClosure (kw L v))
  refine ⟨e.toRingEquiv.toRingHom, e.bijective, fun a => ?_⟩
  have h3 : IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a) =
      algebraMap (kw L v) (IsLocalRing.ResidueField v) (IsLocalRing.residue (Ow L v) a) :=
    (IsLocalRing.ResidueField.map_residue _ a).symm
  show e (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) = _
  rw [h3, AlgEquiv.commutes]

/-! ## 7. `RedRelMul` from the adjunction `Over.map ⊣ Over.pullback` -/

section RedMul

open scoped CategoryTheory.Obj

/-- The adjunction bijection `Hom(T, g^* M) ≃ Hom(g_! T, M)` is multiplicative (as in
unram-tate's `homEquiv_mul`), here for the inverse map. -/
theorem pb_symm_mul {S S' : Scheme} (g : S' ⟶ S) (M : Over S) [MonObj M] (T : Over S')
    (u w : T ⟶ (Over.pullback g).obj M) :
    ((Over.mapPullbackAdj g).homEquiv T M).symm (u * w) =
      ((Over.mapPullbackAdj g).homEquiv T M).symm u *
        ((Over.mapPullbackAdj g).homEquiv T M).symm w := by
  obtain ⟨p, rfl⟩ := ((Over.mapPullbackAdj g).homEquiv T M).surjective u
  obtain ⟨q, rfl⟩ := ((Over.mapPullbackAdj g).homEquiv T M).surjective w
  have hm : (Over.mapPullbackAdj g).homEquiv T M (p * q) =
      (Over.mapPullbackAdj g).homEquiv T M p * (Over.mapPullbackAdj g).homEquiv T M q := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_mul, MonObj.comp_mul]
  rw [← hm, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end RedMul

/-- `pb_symm_mul` for the group law of `(Over.pullback g).mapGrp.obj G` (the one of `sf 𝒜` and of
`𝒜_L`). -/
theorem pb_symm_mul' {S S' : Scheme} (g : S' ⟶ S) (G : Grp (Over S)) (T : Over S')
    (u w : T ⟶ ((Over.pullback g).mapGrp.obj G).X) :
    ((Over.mapPullbackAdj g).homEquiv T G.X).symm (u * w) =
      ((Over.mapPullbackAdj g).homEquiv T G.X).symm u *
        ((Over.mapPullbackAdj g).homEquiv T G.X).symm w :=
  pb_symm_mul g G.X T u w

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RedRelMul` holds (proved):** the product of the lifts lifts the sum, and on both the
generic point and the special fibre the passage to `𝒜` is the adjunction bijection, which is
multiplicative (`pb_symm_mul'`); `e.inv` is a homomorphism. -/
theorem redRelMul : RedRelMul := by
  intro L _ A v 𝒜 _ e j x₁ x₂ y₁ y₂ ⟨x'₁, g₁, c₁⟩ ⟨x'₂, g₂, c₂⟩
  refine ⟨x'₁ * x'₂, ?_, ?_⟩
  · have hw : Spec.map (CommRingCat.ofHom v.subtype) ≫
        (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom =
        ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj
          (PkgI3.AbVar.ptObj (K := L) PkgI4.Qbar)).hom := by
      simp only [Over.mk_hom, Over.map_obj_hom, PkgI3.AbVar.ptObj]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl
    let ι0 : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).obj
        (PkgI3.AbVar.ptObj (K := L) PkgI4.Qbar) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) :=
      Over.homMk (Spec.map (CommRingCat.ofHom v.subtype)) hw
    let u : PtQ L A → (PkgI3.AbVar.ptObj (K := L) PkgI4.Qbar ⟶
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
          𝒜).X) := fun x => genPt v 𝒜 e x
    have hs : ∀ (x : PtQ L A)
        (x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X),
        genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left →
        ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).homEquiv
          _ 𝒜.X).symm (u x) = ι0 ≫ x' := fun x x' h => Over.OverMorphism.ext h
    have hmul : u (x₁ + x₂) = u x₁ * u x₂ := by
      show (Additive.toMul x₁ * Additive.toMul x₂) ≫ e.inv.hom.hom =
        (Additive.toMul x₁ ≫ e.inv.hom.hom) * (Additive.toMul x₂ ≫ e.inv.hom.hom)
      exact MonObj.mul_comp _ _ _
    have key : ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
        (algebraMap (Ow L v) L)))).homEquiv _ 𝒜.X).symm (u (x₁ + x₂)) = ι0 ≫ (x'₁ * x'₂) :=
      (congrArg ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
        (algebraMap (Ow L v) L)))).homEquiv _ 𝒜.X).symm hmul).trans
        ((pb_symm_mul' _ 𝒜 _ (u x₁) (u x₂)).trans
          (by rw [hs x₁ x'₁ g₁, hs x₂ x'₂ g₂, MonObj.comp_mul]))
    exact congrArg Over.Hom.left key
  · have keyc : ∀ (T' : Scheme) (u : T' ⟶ pullback 𝒜.X.hom
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))))),
        (u ≫ pullback.fst _ _) ≫ 𝒜.X.hom = (u ≫ pullback.snd _ _) ≫
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))) := fun T' u => by
      rw [Category.assoc, pullback.condition, Category.assoc]
    have h2 := (keyc _ y₁.left).trans (congrArg (· ≫ Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v)))) (Over.w y₁))
    have h1 := congrArg (· ≫ 𝒜.X.hom) c₁
    have h3 : (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue v)) ≫ x'₁.left) ≫ 𝒜.X.hom =
        (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue v))) ≫
          (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom := by
      rw [Category.assoc, Category.assoc, Category.assoc, Over.w x'₁]
    have hw' : (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue v))) ≫
          (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom =
        ((Over.map (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))))).obj
          (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v)))).hom :=
      h3.symm.trans (h1.symm.trans h2)
    let ι1 : (Over.map (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))))).obj
        (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v))) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) :=
      Over.homMk (Spec.map (CommRingCat.ofHom j) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue v))) hw'
    have hs : ∀ (y : PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v)))
        (x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X),
        y.left ≫ pullback.fst 𝒜.X.hom
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v)))) =
          Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
            x'.left →
        ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm y = ι1 ≫ x' :=
      fun y x' h => Over.OverMorphism.ext (h.trans (Category.assoc _ _ _).symm)
    have key : ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
          (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm (y₁ * y₂) =
        ι1 ≫ (x'₁ * x'₂) :=
      (pb_symm_mul' _ 𝒜 _ y₁ y₂).trans (by rw [hs y₁ x'₁ c₁, hs y₂ x'₂ c₂, MonObj.comp_mul])
    exact (congrArg Over.Hom.left key).trans (Category.assoc _ _ _)


/-! ## 8. `RedTorsionQbar` from the leaf I2-Red (transport along `L‾ ≅ ℚ̄`) -/

section RedMul2

open scoped CategoryTheory.Obj

/-- The adjunction bijection `Hom(g_! T, M) ≃ Hom(T, g^* M)` is multiplicative. -/
theorem pb_mul {S S' : Scheme} (g : S' ⟶ S) (M : Over S) [MonObj M] (T : Over S')
    (p q : (Over.map g).obj T ⟶ M) :
    (Over.mapPullbackAdj g).homEquiv T M (p * q) =
      (Over.mapPullbackAdj g).homEquiv T M p * (Over.mapPullbackAdj g).homEquiv T M q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

set_option synthInstance.maxHeartbeats 400000 in
/-- The adjunction bijection sends `1` to `1`. -/
theorem pb_one {S S' : Scheme} (g : S' ⟶ S) (M : Over S) [MonObj M] (T : Over S') :
    (Over.mapPullbackAdj g).homEquiv T M 1 = 1 := by
  rw [Adjunction.homEquiv_unit, Functor.map_one, MonObj.comp_one]

end RedMul2

/-- `pb_mul` at the group law of `(Over.pullback g).mapGrp.obj G`. -/
theorem pb_mul' {S S' : Scheme} (g : S' ⟶ S) (G : Grp (Over S)) (T : Over S')
    (p q : (Over.map g).obj T ⟶ G.X) (r u w : T ⟶ ((Over.pullback g).mapGrp.obj G).X)
    (hr : r = (Over.mapPullbackAdj g).homEquiv T G.X (p * q))
    (hu : u = (Over.mapPullbackAdj g).homEquiv T G.X p)
    (hw : w = (Over.mapPullbackAdj g).homEquiv T G.X q) : r = u * w := by
  subst hr hu hw
  exact pb_mul g G.X T p q

set_option synthInstance.maxHeartbeats 400000 in
/-- `pb_one` at the group law of `(Over.pullback g).mapGrp.obj G`. -/
theorem pb_one' {S S' : Scheme} (g : S' ⟶ S) (G : Grp (Over S)) (T : Over S')
    (r : T ⟶ ((Over.pullback g).mapGrp.obj G).X)
    (hr : r = (Over.mapPullbackAdj g).homEquiv T G.X 1) : r = 1 := by
  subst hr
  exact pb_one g G.X T

/-- **`OwDVR` (GLUE, standard: a valuation ring of a number field in which `p` is not a unit is
the localization of `𝓞_L` at a nonzero prime, a DVR; e.g. Neukirch, *Algebraic Number Theory*,
Ch. II (locator UNVERIFIED)).** Needed to apply I2-Red, whose base is a DVR. -/
def OwDVR : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (v : ValuationSubring PkgI4.Qbar) (p : ℕ), p.Prime →
    PkgI4.LiesOver v p → IsDiscreteValuationRing (Ow L v)

/-- The place `w = ψ⁻¹(v)` of `L‾` for an `L`-isomorphism `ψ : L‾ ≅ ℚ̄`. -/
abbrev wOf {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar) :
    ValuationSubring (AlgebraicClosure L) :=
  v.comap (ψ : AlgebraicClosure L →+* PkgI4.Qbar)

theorem hw_of {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) :
    (wOf ψ v).comap (algebraMap L (AlgebraicClosure L)) = Ow L v := by
  ext x
  simp [ValuationSubring.mem_comap]

/-- `ψ` restricted to `O_w ≅ O_v`. -/
def psiW {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar) :
    wOf ψ v ≃+* v where
  toFun y := ⟨ψ y, y.2⟩
  invFun z := ⟨ψ.symm z, by
    show ψ (ψ.symm z) ∈ v
    rw [AlgEquiv.apply_symm_apply]
    exact z.2⟩
  left_inv y := Subtype.ext (ψ.symm_apply_apply _)
  right_inv z := Subtype.ext (ψ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul ψ _ _)
  map_add' a b := Subtype.ext (map_add ψ _ _)

theorem psiW_toW {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (a : Ow L v) :
    psiW ψ v (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v) a) = PkgI2.toW (Ow L v) v rfl a :=
  Subtype.ext (by
    show ψ (algebraMap L (AlgebraicClosure L) (a : L)) = algebraMap L PkgI4.Qbar (a : L)
    exact ψ.commutes _)

set_option synthInstance.maxHeartbeats 400000 in
/-- `Spec(j ∘ κ(ψ)) : Spec κ(w)‾ → Spec κ(w')` over `Spec O_w`, where `w' = ψ⁻¹(v)` (an
isomorphism when `j` is bijective). -/
def iotaW {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) :
    (Over.map (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v))))).obj
        (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) (by
    simp only [Over.mk_hom, Over.map_obj_hom, PkgI2.specOver]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rw [psiW_toW ψ v a]
    exact hjc a)

set_option synthInstance.maxHeartbeats 400000 in
/-- `Θ`: I2's `κ(w')`-points of `𝒜` to `κ(w)‾`-points of the special fibre (the adjunction
bijection applied to `ι ≫ y`, written out). -/
def thetaW {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (y : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X) :
    PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v)) :=
  Over.homMk (pullback.lift (iotaW ψ v j hjc ≫ y).left
    (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v))).hom (Over.w (iotaW ψ v j hjc ≫ y)))
    (pullback.lift_snd _ _ _)

set_option synthInstance.maxHeartbeats 400000 in
theorem thetaW_left {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (y : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X) :
    (thetaW ψ v 𝒜 j hjc y).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v)))) =
      Spec.map (CommRingCat.ofHom
        (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom)) ≫ y.left :=
  pullback.lift_fst _ _ _

set_option synthInstance.maxHeartbeats 400000 in
theorem thetaW_symm {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (y : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X) :
    ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm (thetaW ψ v 𝒜 j hjc y) =
      iotaW ψ v j hjc ≫ y :=
  Over.OverMorphism.ext (thetaW_left ψ v 𝒜 j hjc y)

set_option synthInstance.maxHeartbeats 400000 in
/-- `Θ` as a monoid homomorphism. -/
def thetaHom {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) :
    (Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X) →*
      PkgI2.Pts (sf 𝒜) (AlgebraicClosure (kw L v)) where
  toFun := thetaW ψ v 𝒜 j hjc
  map_one' := by
    apply ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm.injective
    rw [thetaW_symm, MonObj.comp_one]
    have h := pb_one' (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Ow L v)))) 𝒜
      (PkgI2.specOver (kw L v) (AlgebraicClosure (kw L v))) _ rfl
    exact (((Over.mapPullbackAdj _).homEquiv _ 𝒜.X).symm_apply_eq.mpr h.symm).symm
  map_mul' y₁ y₂ := by
    apply ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm.injective
    rw [thetaW_symm, MonObj.comp_mul]
    exact ((pb_symm_mul' _ 𝒜 _ (thetaW ψ v 𝒜 j hjc y₁) (thetaW ψ v 𝒜 j hjc y₂)).trans
      (by rw [thetaW_symm, thetaW_symm])).symm

set_option synthInstance.maxHeartbeats 400000 in
theorem iotaW_isIso_left {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (hjb : Function.Bijective j) :
    IsIso (Spec.map (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) := by
  have hb : Function.Bijective (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom) :=
    hjb.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).bijective
  haveI : IsIso (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom)) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
theorem thetaW_injective {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (hjb : Function.Bijective j)
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) :
    Function.Injective (thetaW ψ v 𝒜 j hjc) := by
  intro y₁ y₂ h
  haveI := iotaW_isIso_left ψ v j hjb
  have h1 := congrArg ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm h
  rw [thetaW_symm, thetaW_symm] at h1
  have h2 := congrArg Over.Hom.left h1
  apply Over.OverMorphism.ext
  exact (cancel_epi (Spec.map (CommRingCat.ofHom
    (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom)))).mp h2

set_option synthInstance.maxHeartbeats 400000 in
theorem thetaW_surjective {L : IF} (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar)
    (v : ValuationSubring PkgI4.Qbar) (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v)) (hjb : Function.Bijective j)
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a)) :
    Function.Surjective (thetaW ψ v 𝒜 j hjc) := by
  intro yt
  haveI := iotaW_isIso_left ψ v j hjb
  let z := ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm yt
  have hz2 : z.left ≫ 𝒜.X.hom = (iotaW ψ v j hjc).left ≫ (Over.mk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v)))))).hom :=
    (Over.w z).trans (Over.w (iotaW ψ v j hjc)).symm
  have hw : (inv (Spec.map (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) ≫ z.left) ≫ 𝒜.X.hom =
      (Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v)))))).hom :=
    (Category.assoc _ _ _).trans ((congrArg (inv (Spec.map (CommRingCat.ofHom
      (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) ≫ ·) hz2).trans
      (IsIso.inv_hom_id_assoc _ _))
  refine ⟨Over.homMk _ hw, ?_⟩
  apply ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue (Ow L v))))).homEquiv _ 𝒜.X).symm.injective
  rw [thetaW_symm]
  apply Over.OverMorphism.ext
  exact IsIso.hom_inv_id_assoc (Spec.map (CommRingCat.ofHom
    (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom))) z.left

set_option synthInstance.maxHeartbeats 400000 in
/-- **I2's reduction relation gives `RedRel`** (transport along `ψ`; proved). -/
theorem redRel_of_isReductionOf {L : IF} {A : PkgI3.AbVar L}
    (ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar) (v : ValuationSubring PkgI4.Qbar)
    (𝒜 : Grp (Over (Spec (.of (Ow L v)))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj 𝒜 ≅
      ObjBridge.toGrp A)
    (j : IsLocalRing.ResidueField v →+* AlgebraicClosure (kw L v))
    (hjc : ∀ a : Ow L v, j (IsLocalRing.residue v (PkgI2.toW (Ow L v) v rfl a)) =
        algebraMap (kw L v) (AlgebraicClosure (kw L v)) (IsLocalRing.residue (Ow L v) a))
    (x : A.Pt (AlgebraicClosure L))
    (y : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue (wOf ψ v)).comp
        (PkgI2.toW (Ow L v) (wOf ψ v) (hw_of ψ v))))) ⟶ 𝒜.X)
    (h : PkgI2.IsReductionOf 𝒜 e (wOf ψ v) (hw_of ψ v) x y) :
    RedRel v 𝒜 e j (Additive.ofMul (UnramTate.trPt A ψ x)) (thetaW ψ v 𝒜 j hjc y) := by
  obtain ⟨xw, hg, hc⟩ := h
  have hov : (Spec.map (CommRingCat.ofHom (psiW ψ v : wOf ψ v →+* v)) ≫ xw.left) ≫ 𝒜.X.hom =
      (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom := by
    rw [Category.assoc, Over.w xw]
    simp only [Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact congrArg Subtype.val (psiW_toW ψ v a)
  refine ⟨Over.homMk _ hov, ?_, ?_⟩
  · have hring : Spec.map (CommRingCat.ofHom (ψ : AlgebraicClosure L →+* PkgI4.Qbar)) ≫
        Spec.map (CommRingCat.ofHom (wOf ψ v).subtype) =
        Spec.map (CommRingCat.ofHom v.subtype) ≫
          Spec.map (CommRingCat.ofHom (psiW ψ v : wOf ψ v →+* v)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl
    have h1 := congrArg (Spec.map (CommRingCat.ofHom
      (ψ : AlgebraicClosure L →+* PkgI4.Qbar)) ≫ ·) hg
    have h2 := congrArg (· ≫ xw.left) hring
    simp only [Category.assoc] at h2
    exact ((Category.assoc _ _ _).trans h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ xw.left) hring).trans (Category.assoc _ _ _)))
  · have hring : Spec.map (CommRingCat.ofHom
        (j.comp (IsLocalRing.ResidueField.mapEquiv (psiW ψ v)).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue (wOf ψ v))) =
        Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue v)) ≫
          Spec.map (CommRingCat.ofHom (psiW ψ v : wOf ψ v →+* v)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      rfl
    refine (thetaW_left ψ v 𝒜 j hjc y).trans ?_
    rw [hc]
    have h3 := congrArg (· ≫ xw.left) hring
    simp only [Category.assoc] at h3
    exact h3

/-- `t = σ⁻¹|_{O_w}` (for `σ ∈ D(v)`, `L/ℚ` Galois). -/
def tSig {L : IF} [IsGalois ℚ L] {v : ValuationSubring PkgI4.Qbar} (σ : PkgI4.GQ)
    (hσ : σ ∈ v.decompositionSubgroup ℚ) : Ow L v →+* Ow L v where
  toFun a := ⟨(σ⁻¹).restrictNormal L (a : L), by
    show algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L (a : L)) ∈ v
    rw [AlgEquiv.restrictNormal_commutes]
    exact (sigV σ⁻¹ (inv_mem hσ) ⟨_, a.2⟩).2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

/-- `t = σ⁻¹|_{O_w}` induces `Frob⁻¹` on `κ(w)` (proved from `IsArithFrob`). -/
theorem tSig_residue {L : IF} [IsGalois ℚ L] {v : ValuationSubring PkgI4.Qbar} {σ : PkgI4.GQ}
    {p : ℕ} (hσ : PkgI4.IsArithFrob σ v p) (a : Ow L v) :
    IsLocalRing.residue (Ow L v) (tSig σ hσ.1 a) ^ p = IsLocalRing.residue (Ow L v) a := by
  apply (IsLocalRing.ResidueField.map (PkgI2.toW (Ow L v) v rfl)).injective
  rw [map_pow, IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
    ← residue_sigV hσ]
  congr 1
  apply Subtype.ext
  show σ (algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L (a : L))) =
    algebraMap L PkgI4.Qbar (a : L)
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FExtendCore` (GLUE; leaf I2-NMP, `PkgI2.NeronMappingAbelianScheme` (BLR, *Néron models*,
§1.2), applied to the conjugate model).** `FExtend` with `t = σ⁻¹|_{O_w}` fixed (`tSig`): there is
a morphism of schemes `F̃ : 𝒜 → 𝒜` over `Spec(t)` fixing the unit section and extending `F`
(whenever `x'` is the lift of `x`, `Spec(σ|_{O_v}) ≫ x' ≫ F̃` is a lift of `f x`). See `FExtend`
for why it is true. -/
def FExtendCore : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ) (_ : PkgI4.LiesOver v p)
        (hσ : PkgI4.IsArithFrob σ v p)
        (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
        (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
          𝒜 ≅ ObjBridge.toGrp A)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ Ft : 𝒜.X.left ⟶ 𝒜.X.left,
          Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) ∧
          (η[𝒜.X]).left ≫ Ft = Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) ≫ (η[𝒜.X]).left ∧
          ∀ (x : PtQ L A)
            (x' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X),
            genMap v 𝒜 e x = Spec.map (CommRingCat.ofHom v.subtype) ≫ x'.left →
            ∃ x'' : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl))) ⟶ 𝒜.X,
              genMap v 𝒜 e (f x) = Spec.map (CommRingCat.ofHom v.subtype) ≫ x''.left ∧
              x''.left = Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫ x'.left ≫ Ft

/-- **`FExtend` from `FExtendCore` (proved):** `t = tSig σ`, `t(a)^p ≡ a` by `tSig_residue`. -/
theorem fExtend_of_core (h : FExtendCore) : FExtend := by
  intro L _ _ A F hF1 hF2 p hp v σ hv hσ 𝒜 _ e f hf
  obtain ⟨Ft, h1, h2, h3⟩ := h L A F hF1 hF2 p hp v σ hv hσ 𝒜 e f hf
  exact ⟨Ft, tSig σ hσ.1, h1, tSig_residue hσ, h2, h3⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FExtendGen` (GLUE; leaf I2-NMP, `PkgI2.NeronMappingAbelianScheme` (BLR, *Néron models*,
§1.2), applied to the conjugate model `𝒜^{(t)}`).** For `F`, `σ`, `f` as in `FExtend` and
`t = σ⁻¹|_{O_w}`: there is a morphism of schemes `F̃ : 𝒜 → 𝒜` over `Spec(t)` fixing the unit
section whose restriction to the generic fibre is `F` (through `e`):
`e⁻¹ ≫ pr₁ ≫ F̃ = F ≫ e⁻¹ ≫ pr₁` as maps `A → 𝒜`.

Why it is true: `f(x) ∈ A(ℚ̄)` for all `x` forces `F` to lie over `Spec(σ⁻¹|_L)`, so `F` is an
`L`-morphism `A → A^{(t)}`; I2-NMP for `𝒜` and its base change `𝒜^{(t)}` along `Spec t` extends
it; `F̃` fixes the unit section because both sides are sections of the separated `𝒜 → Spec O_w`
agreeing at the generic point (`f(0) = 0`). -/
def FExtendGen : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (F : A.X.left ⟶ A.X.left), IsFinite F → Surjective F →
    ∀ p : ℕ, p.Prime →
      ∀ (v : ValuationSubring PkgI4.Qbar) (σ : PkgI4.GQ) (_ : PkgI4.LiesOver v p)
        (hσ : PkgI4.IsArithFrob σ v p)
        (𝒜 : Grp (Over (Spec (.of (Ow L v))))) [PkgI2.IsAbelianScheme 𝒜]
        (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))).mapGrp.obj
          𝒜 ≅ ObjBridge.toGrp A)
        (f : PtQ L A →+ PtQ L A), (∀ x : PtQ L A, (Additive.toMul (f x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F) →
        ∃ Ft : 𝒜.X.left ⟶ 𝒜.X.left,
          Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) ∧
          (η[𝒜.X]).left ≫ Ft = Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) ≫ (η[𝒜.X]).left ∧
          (e.inv.hom.hom : A.X ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom
              (algebraMap (Ow L v) L)))).obj 𝒜.X).left ≫
            pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))) ≫ Ft =
          F ≫ (e.inv.hom.hom : A.X ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom
              (algebraMap (Ow L v) L)))).obj 𝒜.X).left ≫
            pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)))

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FExtendCore` from `FExtendGen` (proved):** the lift of `f x` is
`Spec(σ|_{O_v}) ≫ x' ≫ F̃`; it lies over `Spec(toW)` since `σ ∘ t = id` on `O_w`, and restricts to
`f x` by `hf`, the generic compatibility and `Spec σ ≫ Spec(O_v ⊂ ℚ̄) = Spec(O_v ⊂ ℚ̄) ≫ Spec σ_v`. -/
theorem fExtendCore_of_gen (h : FExtendGen) : FExtendCore := by
  intro L _ _ A F hF1 hF2 p hp v σ hv hσ 𝒜 _ e f hf
  obtain ⟨Ft, h1, h2, h3⟩ := h L A F hF1 hF2 p hp v σ hv hσ 𝒜 e f hf
  refine ⟨Ft, h1, h2, fun x x' hx' => ?_⟩
  have hring1 : Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫
      Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)) ≫
        Spec.map (CommRingCat.ofHom (tSig σ hσ.1)) =
      Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    show σ (algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L (a : L))) =
      algebraMap L PkgI4.Qbar (a : L)
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have hov : (Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) ≫ x'.left ≫ Ft) ≫ 𝒜.X.hom =
      (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW (Ow L v) v rfl)))).hom := by
    rw [Category.assoc, Category.assoc, h1, ← Category.assoc x'.left, Over.w x']
    exact hring1
  refine ⟨Over.homMk _ hov, ?_, rfl⟩
  have hring2 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom v.subtype) =
      Spec.map (CommRingCat.ofHom v.subtype) ≫ Spec.map (CommRingCat.ofHom (sigV σ hσ.1)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hfx := hf x
  have hx'' := (Category.assoc _ _ _).symm.trans hx'
  have hx3 := ((congrArg ((Additive.toMul x).left ≫ ·) (Category.assoc _ _ Ft).symm).trans
    (Category.assoc _ _ Ft).symm).trans ((congrArg (· ≫ Ft) hx'').trans (Category.assoc _ _ _))
  exact (Category.assoc _ _ _).trans <|
    (congrArg (· ≫ _) hfx).trans <|
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).trans <|
    (congrArg (fun m => _ ≫ (Additive.toMul x).left ≫ m) h3.symm).trans <|
    (congrArg (_ ≫ ·) hx3).trans <|
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x'.left ≫ Ft) hring2).trans
      (Category.assoc _ _ _))

/-! ## 9. `FrobMorph` from the existence of the absolute Frobenius -/

/-- **`AbsFrob` (GLUE; the absolute Frobenius of an `𝔽_p`-scheme; standard, e.g. SGA 5 XIV,
Stacks Tag 0CC6 (locators UNVERIFIED); not in Mathlib 4.35).** For a scheme `X` over a field `k`
of characteristic `p` there is an endomorphism `Fr_X` (the identity on the space, `f ↦ f^p` on
sections) lying over `Fr_{Spec k} = Spec(z ↦ z^p)`, and natural for points: for every ring `R` of
characteristic `p` and `g : Spec R → X`, `Spec(r ↦ r^p) ≫ g = g ≫ Fr_X`. -/
def AbsFrob : Prop :=
  ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (X : Over (Spec (.of k))),
    ∃ Fr : X.left ⟶ X.left,
      Fr ≫ X.hom = X.hom ≫ Spec.map (CommRingCat.ofHom (frobenius k p)) ∧
      ∀ (R : Type) [CommRing R] [CharP R p] (g : Spec (.of R) ⟶ X.left),
        Spec.map (CommRingCat.ofHom (frobenius R p)) ≫ g = g ≫ Fr

/-- A ring endomorphism inducing an inverse Frobenius on the residue field is local. -/
theorem isLocalHom_of_resPow {O : Type} [CommRing O] [IsLocalRing O] {p : ℕ} (hp : p.Prime)
    (t : O →+* O) (hres : ∀ a, IsLocalRing.residue O (t a) ^ p = IsLocalRing.residue O a) :
    IsLocalHom t := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : IsLocalRing.residue O a = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hna)
  rw [← hres a] at h1
  have h2 : IsLocalRing.residue O (t a) = 0 := pow_eq_zero_iff hp.ne_zero |>.mp h1
  exact ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h2)) ha

/-- The unit section of the special fibre, followed by the projection to `𝒜`, is the closed
point followed by the unit section of `𝒜` (proved). -/
theorem sf_eta_fst {O : Type} [CommRing O] [IsLocalRing O] (𝒜 : Grp (Over (Spec (.of O)))) :
    (η[(sf 𝒜).X]).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ (η[𝒜.X]).left := by
  let g' := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  let F := Over.pullback g'
  have hε : (Functor.LaxMonoidal.ε F).left ≫ pullback.snd (𝟙 (Spec (.of O))) g' = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε F)
  have hε2 : (Functor.LaxMonoidal.ε F).left ≫ pullback.fst (𝟙 (Spec (.of O))) g' = g' := by
    have hc : pullback.fst (𝟙 (Spec (.of O))) g' = pullback.snd (𝟙 (Spec (.of O))) g' ≫ g' := by
      rw [← pullback.condition, Category.comp_id]
    rw [hc, ← Category.assoc, hε, Category.id_comp]
  have hmap : (F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' =
      pullback.fst (𝟙 (Spec (.of O))) g' ≫ (η[𝒜.X]).left := pullback.lift_fst _ _ _
  show ((Functor.LaxMonoidal.ε F) ≫ F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' = _
  rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc, hε2]

set_option synthInstance.maxHeartbeats 400000 in
/-- **`FrobMorph` from `AbsFrob` (proved):** `β = Fr_Ā ≫ F̄`, with `F̄ = F̃ ×_{Spec t} Spec(t̄)`
(`pullback.map`) and `t̄` the map induced by `t` on `κ(O)` (`t̄ = Frob⁻¹`); `β` lies over
`Spec(Frob ∘ t̄) = id`; it fixes `0` (`sf_eta_fst`, point-naturality at the unit section); the
point formula is point-naturality at `y`. -/
theorem frobMorph_of (hA : AbsFrob) : FrobMorph := by
  intro O _ _ p hp hk 𝒜 _ Ft t hover hres hzero
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := isLocalHom_of_resPow hp t hres
  let tb := IsLocalRing.ResidueField.map t
  have htb : ∀ z, frobenius (IsLocalRing.ResidueField O) p (tb z) = z := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    exact hres a
  let g' := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  have heq2 : g' ≫ Spec.map (CommRingCat.ofHom t) = Spec.map (CommRingCat.ofHom tb) ≫ g' := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hid : Spec.map (CommRingCat.ofHom (frobenius (IsLocalRing.ResidueField O) p)) ≫
      Spec.map (CommRingCat.ofHom tb) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show (frobenius (IsLocalRing.ResidueField O) p).comp tb = RingHom.id _ from
      RingHom.ext htb, CommRingCat.ofHom_id, Spec.map_id]
  let Fb : pullback 𝒜.X.hom g' ⟶ pullback 𝒜.X.hom g' :=
    pullback.map 𝒜.X.hom g' 𝒜.X.hom g' Ft (Spec.map (CommRingCat.ofHom tb))
      (Spec.map (CommRingCat.ofHom t)) hover.symm heq2
  have hFb1 : Fb ≫ pullback.fst 𝒜.X.hom g' = pullback.fst 𝒜.X.hom g' ≫ Ft :=
    pullback.lift_fst _ _ _
  have hFb2 : Fb ≫ pullback.snd 𝒜.X.hom g' =
      pullback.snd 𝒜.X.hom g' ≫ Spec.map (CommRingCat.ofHom tb) := pullback.lift_snd _ _ _
  obtain ⟨Fr0, hFr1, hFr2⟩ := hA (IsLocalRing.ResidueField O) p
    (Over.mk (pullback.snd 𝒜.X.hom g'))
  let Fr : pullback 𝒜.X.hom g' ⟶ pullback 𝒜.X.hom g' := Fr0
  have hFr1' : Fr ≫ pullback.snd 𝒜.X.hom g' = pullback.snd 𝒜.X.hom g' ≫
      Spec.map (CommRingCat.ofHom (frobenius (IsLocalRing.ResidueField O) p)) := hFr1
  have hFr2' : ∀ (R : Type) [CommRing R] [CharP R p] (g : Spec (.of R) ⟶ pullback 𝒜.X.hom g'),
      Spec.map (CommRingCat.ofHom (frobenius R p)) ≫ g = g ≫ Fr := fun R _ _ g => hFr2 R g
  have hw : (Fr ≫ Fb) ≫ pullback.snd 𝒜.X.hom g' = pullback.snd 𝒜.X.hom g' := by
    rw [Category.assoc, hFb2, ← Category.assoc, hFr1', Category.assoc, hid, Category.comp_id]
  let e0 : Spec (.of (IsLocalRing.ResidueField O)) ⟶ pullback 𝒜.X.hom g' := (η[(sf 𝒜).X]).left
  have he0 : e0 ≫ pullback.fst 𝒜.X.hom g' = g' ≫ (η[𝒜.X]).left := sf_eta_fst 𝒜
  have he0s : e0 ≫ pullback.snd 𝒜.X.hom g' = 𝟙 _ := Over.w η[(sf 𝒜).X]
  refine ⟨Over.homMk (U := (sf 𝒜).X) (V := (sf 𝒜).X) (Fr ≫ Fb) hw, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    show e0 ≫ Fr ≫ Fb = e0
    have hn := hFr2' (IsLocalRing.ResidueField O) e0
    rw [← Category.assoc, ← hn, Category.assoc]
    have hη : e0 ≫ Fb = Spec.map (CommRingCat.ofHom tb) ≫ e0 := by
      apply pullback.hom_ext
      · rw [Category.assoc, hFb1, ← Category.assoc, he0, Category.assoc, Category.assoc, he0,
          hzero, ← Category.assoc, heq2, Category.assoc]
      · rw [Category.assoc, hFb2, ← Category.assoc, he0s, Category.id_comp, Category.assoc, he0s,
          Category.comp_id]
    rw [hη, ← Category.assoc, hid, Category.id_comp]
  · intro y φ hφ
    haveI : CharP (AlgebraicClosure (IsLocalRing.ResidueField O)) p :=
      charP_of_injective_algebraMap (algebraMap (IsLocalRing.ResidueField O) _).injective p
    have hφ' : φ = frobenius _ p := RingHom.ext hφ
    subst hφ'
    let yl : Spec (.of (AlgebraicClosure (IsLocalRing.ResidueField O))) ⟶ pullback 𝒜.X.hom g' :=
      y.left
    have hn := hFr2' (AlgebraicClosure (IsLocalRing.ResidueField O)) yl
    show (yl ≫ Fr ≫ Fb) ≫ pullback.fst 𝒜.X.hom g' = _ ≫ yl ≫ pullback.fst 𝒜.X.hom g' ≫ Ft
    rw [Category.assoc, Category.assoc, hFb1, ← Category.assoc, ← Category.assoc, ← hn,
      Category.assoc, Category.assoc]

/-- **Main result, finest form: `AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the glue `ResidueAlgClosure`, `RedRelMul`, `RedTorsionQbar`,
`FExtend`, `FrobMorph` (proved).** -/
theorem algFrobRed_of_fine (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hR : ResidueAlgClosure) (hM : RedRelMul) (h2 : RedTorsionQbar) (hE : FExtend)
    (hFr : FrobMorph) : FrobTrace.AlgFrobRed :=
  algFrobRed_of_split hG hS hR hM h2 (reductionFrobGood_of hS hE hFr)

/-- **`TateBridge35` from I3.M0 and the seven pieces (proved).** -/
theorem tateBridge35_of_fine (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hR : ResidueAlgClosure) (hM : RedRelMul)
    (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_fine hG hS hR hM h2 hE hFr)

/-- **`AlgFrobRed` with `ResidueAlgClosure` split (proved).** Leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`; glue `ResidueAlgClosed`, `ResidueAlgebraic`,
`RedRelMul`, `RedTorsionQbar`, `FExtend`, `FrobMorph`. -/
theorem algFrobRed_of_finest (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hC : ResidueAlgClosed) (hA : ResidueAlgebraic) (hM : RedRelMul) (h2 : RedTorsionQbar)
    (hE : FExtend) (hFr : FrobMorph) : FrobTrace.AlgFrobRed :=
  algFrobRed_of_fine hG hS (residueAlgClosure_of hC hA) hM h2 hE hFr

/-- **`AlgFrobRed` with `ResidueAlgClosed` discharged (proved).** Leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`; glue `ResidueAlgebraic`, `RedRelMul`,
`RedTorsionQbar`, `FExtend`, `FrobMorph`. -/
theorem algFrobRed_of_final (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hA : ResidueAlgebraic) (hM : RedRelMul) (h2 : RedTorsionQbar) (hE : FExtend)
    (hFr : FrobMorph) : FrobTrace.AlgFrobRed :=
  algFrobRed_of_finest hG hS residueAlgClosed hA hM h2 hE hFr

/-- **`TateBridge35` from I3.M0 and the seven remaining pieces (proved).** -/
theorem tateBridge35_of_final (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hA : ResidueAlgebraic) (hM : RedRelMul)
    (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_final hG hS hA hM h2 hE hFr)

/-- **Main result: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the glue `RedRelMul`, `RedTorsionQbar`, `FExtend`, `FrobMorph`
(proved).** Everything else (conjugating the place, isolating the finite set, the special fibre
as an abelian variety, the residue characteristic, the valuative criterion, `κ(v) ≅ κ(w)‾`,
`σ = Frob` on `κ(v)`, rigidity) is proved here or by Mathlib / mul-rigidity. -/
theorem algFrobRed_of_main (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hM : RedRelMul) (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_final hG hS residueAlgebraic hM h2 hE hFr

/-- **`TateBridge35` from I3.M0 and the six remaining pieces (proved).** -/
theorem tateBridge35_of_main (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hM : RedRelMul) (h2 : RedTorsionQbar) (hE : FExtend)
    (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_main hG hS hM h2 hE hFr)

/-- **Main result: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite` and
`SmoothGeomConnIntegral` and the glue `RedTorsionQbar`, `FExtend`, `FrobMorph` (proved).**
Proved here (or in Mathlib / mul-rigidity): conjugating the place, isolating the finite set, the
special fibre as an abelian variety (from `SmoothGeomConnIntegral`), the residue characteristic and
the units `ℓⁿ`, the valuative criterion (existence and uniqueness of lifts), `κ(v) ≅ κ(w)‾`
(`residueAlgClosed`, `residueAlgebraic`), the reduction map as a homomorphism (`redRelMul`),
`σ = Frob` on `κ(v)`, rigidity. -/
theorem algFrobRed_of_five (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) : FrobTrace.AlgFrobRed :=
  algFrobRed_of_main hG hS redRelMul h2 hE hFr

/-- **`TateBridge35` from I3.M0 and the five pieces (proved).** -/
theorem tateBridge35_of_five (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (h2 : RedTorsionQbar) (hE : FExtend) (hFr : FrobMorph) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_five hG hS h2 hE hFr)

/-! ### `OwDVR` (proved; adapted from neron-lg's `dvrAt_center`) -/

section DVR

open NumberField

/-- The DVR `𝓞_{L,P}` of a nonzero prime `P` of `𝓞_L`, as a valuation subring of `L` (as in
neron-lg's `dvrAt`). -/
noncomputable def dvrAt' {K : Type} [Field K] [NumberField K]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ValuationSubring K :=
  (P.valuation K).valuationSubring

instance {K : Type} [Field K] [NumberField K] (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (dvrAt' P) := by
  unfold dvrAt'; infer_instance

theorem ringOfIntegers_mem' {K : Type} [Field K] [NumberField K] (O : ValuationSubring K)
    (x : 𝓞 K) : (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral O (x : K) from x.isIntegral_coe.tower_top)
  exact hy ▸ y.2

/-- The inclusion `𝓞_K → O`. -/
def toO' {K : Type} [Field K] [NumberField K] (O : ValuationSubring K) : 𝓞 K →+* O :=
  (algebraMap (𝓞 K) K).codRestrict O.toSubring (ringOfIntegers_mem' O)

/-- `p ∈ 𝔪_{O_w}` for `v ∣ p`. -/
theorem natCast_mem_maximalIdeal {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ}
    (hp : p.Prime) (hv : PkgI4.LiesOver v p) :
    (p : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) := by
  have h1 : ((p : Ow L v) : L) ∈ (Ow L v).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    intro hin
    rw [ValuationSubring.mem_comap, map_inv₀] at hin
    have he : (algebraMap L PkgI4.Qbar ((p : Ow L v) : L)) = (p : PkgI4.Qbar) := by simp
    rw [he] at hin
    have hv' := hv
    unfold PkgI4.LiesOver at hv'
    rw [ValuationSubring.mem_nonunits_iff_or] at hv'
    rcases hv' with h0 | h0
    · exact (Nat.cast_ne_zero.mpr hp.ne_zero) h0
    · exact h0 hin
  exact (ValuationSubring.coe_mem_nonunits_iff).mp h1

/-- **`OwDVR` holds (proved):** `O_w` contains `𝓞_L`; its center `P = 𝔪_{O_w} ∩ 𝓞_L` is a nonzero
prime (it contains `p`); `𝓞_{L,P} ⊆ O_w`, and a DVR is a maximal proper valuation subring
(`ValuationSubring.eq_of_le_of_ne_top`), so `O_w = 𝓞_{L,P}`. -/
theorem owDVR : OwDVR := by
  intro L _ v p hp hv
  haveI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have hpm := natCast_mem_maximalIdeal (L := L) hp hv
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
    { asIdeal := (IsLocalRing.maximalIdeal (Ow L v)).comap (toO' (Ow L v))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro hbot
        have hmem : (p : 𝓞 L) ∈ (IsLocalRing.maximalIdeal (Ow L v)).comap (toO' (Ow L v)) := by
          rw [Ideal.mem_comap, map_natCast]; exact hpm
        rw [hbot, Ideal.mem_bot] at hmem
        exact hp.ne_zero (by exact_mod_cast hmem) }
  have hP : ∀ x : 𝓞 L, x ∈ P.asIdeal ↔ toO' (Ow L v) x ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    fun x => Iff.rfl
  have heq : dvrAt' P = Ow L v := by
    apply ValuationSubring.eq_of_le_of_ne_top
    · intro x hx
      obtain ⟨n, d, hnd⟩ :=
        IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P x hx
      have hd : IsUnit (toO' (Ow L v) d) := by
        by_contra h
        exact d.2 ((hP d).2 ((IsLocalRing.mem_maximalIdeal _).2 h))
      have hvd : (Ow L v).valuation (algebraMap (𝓞 L) L d) = 1 :=
        ((Ow L v).valuation_eq_one_iff _).1 hd
      apply (Ow L v).mem_of_valuation_le_one
      have h2 := congrArg (Ow L v).valuation hnd
      rw [map_mul, hvd, _root_.mul_one] at h2
      rw [h2]
      exact (Ow L v).valuation_le_one (toO' (Ow L v) n)
    · intro htop
      have hall : ∀ y : L, y ∈ Ow L v := by
        intro y; rw [htop]; exact ValuationSubring.mem_top y
      have hp0 : ((p : Ow L v) : L) ≠ 0 := by
        simp only [ne_eq, map_natCast]
        push_cast
        exact_mod_cast hp.ne_zero
      have hu : IsUnit (p : Ow L v) := by
        refine isUnit_iff_exists_inv.2 ⟨⟨_, hall (((p : Ow L v) : L))⁻¹⟩, Subtype.ext ?_⟩
        rw [Subring.coe_mul]
        exact mul_inv_cancel₀ hp0
      exact (IsLocalRing.mem_maximalIdeal _).1 hpm hu
  have key : ∀ O' : ValuationSubring L, dvrAt' P = O' → IsDiscreteValuationRing O' := by
    rintro O' rfl; infer_instance
  exact key _ heq

end DVR

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RedTorsionQbar` from the leaf I2-Red and `OwDVR` (proved).** Transport along an
`L`-isomorphism `ψ : L‾ ≅ ℚ̄` (`UnramTate.trPt`) and the bijective homomorphism `Θ` from I2's
`κ(w')`-points of `𝒜` to the `κ(w)‾`-points of `sf 𝒜`; I2's reductions are `RedRel`s
(`redRel_of_isReductionOf`), reductions are unique (`redRel_unique`) and additive
(`redRelMul`). -/
theorem redTorsionQbar_of (hRed : PkgI2.ReductionTorsionBijective.{0}) (hD : OwDVR) :
    RedTorsionQbar := by
  intro L _ A p hp v hv 𝒜 _ e j hjb hjc m hm hmu
  haveI := hD L v p hp hv
  haveI : Algebra.IsAlgebraic L PkgI4.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  haveI : IsAlgClosure L PkgI4.Qbar := ⟨inferInstance, inferInstance⟩
  let ψ : AlgebraicClosure L ≃ₐ[L] PkgI4.Qbar :=
    IsAlgClosure.equiv L (AlgebraicClosure L) PkgI4.Qbar
  obtain ⟨hR1, hR2⟩ := hRed L (Ow L v) (wOf ψ v) (hw_of ψ v) (ObjBridge.toGrp A) 𝒜 e m hm hmu
  let Φ := UnramTate.trPt A ψ
  let Θ := thetaHom ψ v 𝒜 j hjc
  have hΘinj := thetaW_injective ψ v 𝒜 j hjb hjc
  have hΘsurj := thetaW_surjective ψ v 𝒜 j hjb hjc
  have hT3 := redRel_of_isReductionOf (A := A) ψ v 𝒜 e j hjc
  have hun := redRel_unique v 𝒜 e j
  have hex := exists_redRel v 𝒜 e j hjc
  have hmul := redRelMul L A v 𝒜 e j
  have h01 : RedRel v 𝒜 e j 0 1 := by
    obtain ⟨z, hz⟩ := hex 0
    have h2 := hmul 0 0 z z hz hz
    rw [add_zero] at h2
    have h3 : z * z = z := hun 0 _ _ h2 hz
    have hz1 : z = 1 := mul_eq_right.mp h3
    rw [hz1] at hz
    exact hz
  have hΘ1 : ∀ y, thetaW ψ v 𝒜 j hjc y = 1 → y = 1 := fun y h =>
    hΘinj (h.trans (map_one Θ).symm)
  have htors : ∀ x : PtQ L A, m • x = 0 →
      Φ.symm (Additive.toMul x) ∈ PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure L) m := by
    intro x hx
    show (Φ.symm (Additive.toMul x)) ^ m = 1
    rw [← map_pow, ← toMul_nsmul, hx, toMul_zero, map_one]
  have hT3' : ∀ (x : PtQ L A) yw, PkgI2.IsReductionOf 𝒜 e (wOf ψ v) (hw_of ψ v)
      (Φ.symm (Additive.toMul x)) yw → RedRel v 𝒜 e j x (thetaW ψ v 𝒜 j hjc yw) := by
    intro x yw h
    have hr := hT3 _ yw h
    rw [show UnramTate.trPt A ψ (Φ.symm (Additive.toMul x)) = Additive.toMul x from
      Φ.apply_symm_apply _, ofMul_toMul] at hr
    exact hr
  constructor
  · intro x hx
    obtain ⟨yw, ⟨hyw1, hyw2⟩, -⟩ := hR1 _ (htors x hx)
    have hr := hT3' x yw hyw2
    refine ⟨Additive.ofMul (thetaW ψ v 𝒜 j hjc yw), ⟨?_, hr⟩, ?_⟩
    · rw [← ofMul_pow]
      show Additive.ofMul (Θ yw ^ m) = 0
      rw [← map_pow, hyw1, map_one]
      rfl
    · rintro y' ⟨-, hy'⟩
      exact Additive.toMul.injective (hun x _ _ hy' hr)
  · intro yt hyt
    obtain ⟨yw, hyw⟩ := hΘsurj (Additive.toMul yt)
    have hywt : yw ^ m = 1 := by
      apply hΘinj
      show Θ (yw ^ m) = Θ 1
      rw [map_pow, map_one]
      show (thetaW ψ v 𝒜 j hjc yw) ^ m = 1
      rw [hyw, ← toMul_nsmul, hyt, toMul_zero]
    obtain ⟨xw0, ⟨hxw1, hxw2⟩, -⟩ := hR2 yw hywt
    let xw : A.Pt (AlgebraicClosure L) := xw0
    have hr := hT3 xw yw hxw2
    rw [hyw] at hr
    have hx2t : m • Additive.ofMul (Φ xw) = 0 := by
      rw [← ofMul_pow, ← map_pow]
      have : xw ^ m = 1 := hxw1
      rw [this, map_one]
      rfl
    refine ⟨Additive.ofMul (Φ xw), ⟨hx2t, hr⟩, ?_⟩
    rintro x1 ⟨hx1t, hx1r⟩
    have hd : RedRel v 𝒜 e j (x1 - Additive.ofMul (Φ xw)) 1 := by
      obtain ⟨yd, hyd⟩ := hex (x1 - Additive.ofMul (Φ xw))
      have h3 := hmul _ _ yd (Additive.toMul yt) hyd hr
      rw [sub_add_cancel] at h3
      have h4 : yd * Additive.toMul yt = Additive.toMul yt := hun x1 _ _ h3 hx1r
      rw [mul_eq_right.mp h4] at hyd
      exact hyd
    have hdt : m • (x1 - Additive.ofMul (Φ xw)) = 0 := by
      rw [smul_sub, hx1t, hx2t, sub_zero]
    obtain ⟨yd', ⟨hyd'1, hyd'2⟩, -⟩ := hR1 _ (htors _ hdt)
    have hyd'eq : yd' = 1 := hΘ1 yd' (hun _ _ _ (hT3' _ yd' hyd'2) hd)
    have h1t : (1 : PkgI2.Pts (ObjBridge.toGrp A) (AlgebraicClosure L)) ∈
        PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure L) m := one_pow m
    obtain ⟨y0, ⟨hy01, hy02⟩, -⟩ := hR1 1 h1t
    have hy0eq : y0 = 1 := by
      have hr0 := hT3 1 y0 hy02
      rw [map_one, ofMul_one] at hr0
      exact hΘ1 y0 (hun 0 _ _ hr0 h01)
    have hxd1 := (hR2 1 (one_pow m)).unique ⟨htors _ hdt, hyd'eq ▸ hyd'2⟩ ⟨h1t, hy0eq ▸ hy02⟩
    have h5 : Additive.toMul (x1 - Additive.ofMul (Φ xw)) = 1 := by
      have h6 := congrArg Φ hxd1
      rw [MulEquiv.apply_symm_apply] at h6
      exact h6.trans (map_one Φ)
    exact sub_eq_zero.mp (Additive.toMul.injective (h5.trans toMul_zero.symm))

/-- **`AlgFrobRed` from the leaves `GoodRedCofinite`, `SmoothGeomConnIntegral`, I2-Red (kernel
leaf `PkgI2.ReductionTorsionBijective`) and the glue `OwDVR`, `FExtend`, `FrobMorph` (proved).** -/
theorem algFrobRed_of_I2 (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hD : OwDVR) (hE : FExtend) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_five hG hS (redTorsionQbar_of hRed hD) hE hFr

/-- **`TateBridge35` from I3.M0, I2-Red and the five other pieces (proved).** -/
theorem tateBridge35_of_I2 (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0}) (hD : OwDVR)
    (hE : FExtend) (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_I2 hG hS hRed hD hE hFr)

/-- **Main result, final form: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite`
and `SmoothGeomConnIntegral`, the kernel leaf I2-Red (`PkgI2.ReductionTorsionBijective`), and the
glue `FExtend` and `FrobMorph` (proved).** -/
theorem algFrobRed_of_leaves (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtend) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_I2 hG hS hRed owDVR hE hFr

/-- **`TateBridge35` from I3.M0, I2-Red, `GoodRedCofinite`, `SmoothGeomConnIntegral`, `FExtend`,
`FrobMorph` (proved).** -/
theorem tateBridge35_of_leaves (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtend)
    (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_leaves hG hS hRed hE hFr)

/-- **Main result, finest form: `FrobTrace.AlgFrobRed` from the leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`, the kernel leaf I2-Red, and the glue `FExtendCore`
and `FrobMorph` (proved).** -/
theorem algFrobRed_of_core (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendCore) (hFr : FrobMorph) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_leaves hG hS hRed (fExtend_of_core hE) hFr

/-- **`TateBridge35` from I3.M0, I2-Red, `GoodRedCofinite`, `SmoothGeomConnIntegral`,
`FExtendCore`, `FrobMorph` (proved).** -/
theorem tateBridge35_of_core (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hE : FExtendCore) (hFr : FrobMorph) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_core hG hS hRed hE hFr)

/-- **Main result with `FrobMorph` reduced: `FrobTrace.AlgFrobRed` from the leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`, the kernel leaf I2-Red, and the glue `FExtendCore` and
`AbsFrob` (proved).** -/
theorem algFrobRed_of_absFrob (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendCore) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_core hG hS hRed hE (frobMorph_of hA)

/-- **`TateBridge35` from I3.M0, I2-Red, `GoodRedCofinite`, `SmoothGeomConnIntegral`,
`FExtendCore`, `AbsFrob` (proved).** -/
theorem tateBridge35_of_absFrob (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hE : FExtendCore) (hA : AbsFrob) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_absFrob hG hS hRed hE hA)

/-- **Main result, finest form: `FrobTrace.AlgFrobRed` from the leaf candidates
`GoodRedCofinite`, `SmoothGeomConnIntegral`, the kernel leaf I2-Red, and the glue `FExtendGen` and
`AbsFrob` (proved).** -/
theorem algFrobRed_of_gen (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_absFrob hG hS hRed (fExtendCore_of_gen hE) hA

/-- **`TateBridge35` from I3.M0, I2-Red, `GoodRedCofinite`, `SmoothGeomConnIntegral`,
`FExtendGen`, `AbsFrob` (proved).** -/
theorem tateBridge35_of_gen (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hE : FExtendGen) (hA : AbsFrob) : G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_gen hG hS hRed hE hA)

end AlgFrobRedRed

end



/-!
# afr-absfrob: the absolute Frobenius of a scheme of characteristic `p`

Construction (not in Mathlib 4.35): for a scheme `X` with `(p : Γ(X, ⊤)) = 0`, `fr p X` is the
identity on the underlying space and `s ↦ s ^ p` on every ring of sections.
-/

noncomputable section

namespace AbsFrobDef

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

variable (p : ℕ) [hp : Fact p.Prime]

/-- `x ↦ x ^ p` as a ring endomorphism of a commutative ring in which `p = 0` (the ring may be
trivial, so no `CharP` instance is assumed). -/
def powHom (R : Type*) [CommRing R] (h : (p : R) = 0) : R →+* R where
  toFun x := x ^ p
  map_one' := one_pow _
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.out.ne_zero
  map_add' x y := by
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim _ _
    · have := (CharP.charP_iff_prime_eq_zero hp.out).2 h
      exact add_pow_char x y p

@[simp] theorem powHom_apply (R : Type*) [CommRing R] (h : (p : R) = 0) (x : R) :
    powHom p R h x = x ^ p := rfl

omit hp in
/-- `p = 0` in every ring of sections of `X` if it is `0` in the global sections. -/
theorem natCast_sections {X : Scheme.{u}} (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) :
    (p : Γ(X, U)) = 0 := by
  have := congrArg (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom hX
  rwa [map_natCast, map_zero] at this

/-- The Frobenius on the structure presheaf. -/
def frobC (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    X.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat (𝟙 (X : TopCat))).obj X.presheaf where
  app U := CommRingCat.ofHom (powHom p _ (natCast_sections p hX U.unop))
  naturality U V i := by
    ext x
    exact (map_pow (X.presheaf.map i).hom x p).symm

/-- The absolute Frobenius as a morphism of presheafed spaces. -/
def frobPSh (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    X.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := 𝟙 _
  c := frobC p X hX

/-- The stalk map of the absolute Frobenius is `a ↦ a ^ p`. -/
theorem frob_stalkMap (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (x : X)
    (a : X.presheaf.stalk x) :
    ((frobPSh p X hX).stalkMap x).hom a = a ^ p := by
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  have := PresheafedSpace.stalkMap_germ_apply (frobPSh p X hX) U x hxU s
  erw [this]
  show X.presheaf.germ U x hxU (s ^ p) = _
  rw [map_pow]

/-- **The absolute Frobenius** `Fr_X : X ⟶ X` of a scheme with `p = 0` on `X`: the identity on
the underlying space, `s ↦ s ^ p` on sections (local on stalks since `a ^ p` a unit forces `a` a
unit). -/
def fr (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) : X ⟶ X :=
  Scheme.Hom.mk
    { toHom := frobPSh p X hX
      prop := fun x => ⟨fun a ha => by
        rw [frob_stalkMap p X hX x a] at ha
        exact (isUnit_pow_iff hp.out.ne_zero).mp ha⟩ }

@[simp] theorem fr_base (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) :
    (fr p X hX).base = 𝟙 _ := rfl

theorem fr_app (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0) (U : X.Opens) :
    (fr p X hX).app U = CommRingCat.ofHom (powHom p _ (natCast_sections p hX U)) := rfl

/-- **Naturality of the absolute Frobenius:** `f ≫ Fr_X = Fr_Y ≫ f` for every morphism
`f : Y ⟶ X` of schemes on which `p = 0`. -/
theorem fr_naturality {X Y : Scheme.{u}} (f : Y ⟶ X) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) : f ≫ fr p X hX = fr p Y hY ≫ f := by
  have hb : (f ≫ fr p X hX).base = (fr p Y hY ≫ f).base := by
    rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, fr_base, fr_base, Category.comp_id,
      Category.id_comp]
  refine Scheme.Hom.ext hb fun U => ?_
  rw [show (eqToHom (congr((Opens.map $hb.symm).obj U))).op =
      𝟙 (op ((Opens.map (f ≫ fr p X hX).base).obj U)) from
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app, fr_app, fr_app]
  ext s
  exact map_pow (f.app U).hom s p

omit hp in
theorem natCast_Spec (R : CommRingCat.{u}) (h : (p : R) = 0) : (p : Γ(Spec R, ⊤)) = 0 := by
  have := congrArg (Scheme.ΓSpecIso R).inv.hom h
  rwa [map_natCast, map_zero] at this

omit hp in
theorem natCast_of_hom {R : CommRingCat.{u}} (h : (p : R) = 0) {X : Scheme.{u}}
    (f : X ⟶ Spec R) : (p : Γ(X, ⊤)) = 0 := by
  have := congrArg f.appTop.hom (natCast_Spec p R h)
  rwa [map_natCast, map_zero] at this

/-- **The absolute Frobenius of an affine scheme** is `Spec` of `r ↦ r ^ p`. -/
theorem fr_Spec (R : CommRingCat.{u}) (h : (p : R) = 0) :
    fr p (Spec R) (natCast_Spec p R h) = Spec.map (CommRingCat.ofHom (powHom p R h)) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso R).hom, Scheme.ΓSpecIso_naturality]
  ext s
  exact map_pow (Scheme.ΓSpecIso R).hom.hom s p

end AbsFrobDef

namespace AlgFrobRedRed

open CategoryTheory AlgebraicGeometry


/-- `frobenius R p` is `AbsFrobDef.powHom`. -/
theorem frobenius_eq_powHom (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    frobenius R p = AbsFrobDef.powHom p R (CharP.cast_eq_zero R p) :=
  RingHom.ext fun _ => rfl

/-- **`AbsFrob` (proved):** `Fr_X = AbsFrobDef.fr`. -/
theorem absFrob : AbsFrob := by
  intro k _ p _ _ X
  have hk : ((p : ℕ) : CommRingCat.of k) = 0 := CharP.cast_eq_zero k p
  have hX := AbsFrobDef.natCast_of_hom p hk X.hom
  refine ⟨AbsFrobDef.fr p X.left hX, ?_, fun R _ _ g => ?_⟩
  · rw [frobenius_eq_powHom, ← AbsFrobDef.fr_Spec p (.of k) hk,
      AbsFrobDef.fr_naturality p X.hom]
  · have hR : ((p : ℕ) : CommRingCat.of R) = 0 := CharP.cast_eq_zero R p
    rw [frobenius_eq_powHom, ← AbsFrobDef.fr_Spec p (.of R) hR, AbsFrobDef.fr_naturality p g]

end AlgFrobRedRed



/-! # afr-absfrob, part 2: `FExtendGen` from the Néron mapping property (leaf I2-NMP)

Appended by `build.sh` after alg-frob-red's `AlgFrobRed.lean` (verbatim copy) and the
absolute-Frobenius part. -/

noncomputable section

namespace AlgFrobRedRed

open CategoryTheory AlgebraicGeometry Limits
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

/-- **Galois rigidity of embeddings (proved).** For a normal extension `L/ℚ`, a domain `R` and two
ring maps `ψ₁, ψ₂ : L → R` which agree after some ring map `χ : R → Q` to a nontrivial ring,
`ψ₁ = ψ₂`. (`ψ₂ ℓ` is a root of the minimal polynomial of `ℓ`, which splits in `L`; so
`ψ₂ ℓ = ψ₁ r` for a conjugate `r`, and `χ ∘ ψ₁` is injective.) -/
theorem ringHom_eq_of_normal {L R Q : Type*} [Field L] [Algebra ℚ L] [Normal ℚ L]
    [CommRing R] [IsDomain R] [CommRing Q] [Nontrivial Q]
    (ψ₁ ψ₂ : L →+* R) (χ : R →+* Q) (h : χ.comp ψ₁ = χ.comp ψ₂) : ψ₁ = ψ₂ := by
  ext ℓ
  have hint : IsIntegral ℚ ℓ := Normal.isIntegral inferInstance ℓ
  have hsp := Normal.splits (inferInstance : Normal ℚ L) ℓ
  have hc : ψ₁.comp (algebraMap ℚ L) = ψ₂.comp (algebraMap ℚ L) := RingHom.ext_rat _ _
  have hne : ((minpoly ℚ ℓ).map (algebraMap ℚ L)).map ψ₁ ≠ 0 :=
    Polynomial.map_ne_zero (Polynomial.map_ne_zero (minpoly.ne_zero hint))
  have hroot : ψ₂ ℓ ∈ (((minpoly ℚ ℓ).map (algebraMap ℚ L)).map ψ₁).roots := by
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.map_map, hc,
      ← Polynomial.map_map, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
  rw [hsp.roots_map ψ₁, Multiset.mem_map] at hroot
  obtain ⟨r, -, hr⟩ := hroot
  have hrl : r = ℓ := (χ.comp ψ₁).injective (by
    show χ (ψ₁ r) = χ (ψ₁ ℓ)
    rw [hr]
    exact (RingHom.congr_fun h ℓ).symm)
  rw [← hr, hrl]

/-- **Morphisms from an integral scheme to `Spec L`, `L/ℚ` normal, agreeing at one field-valued
point, are equal (proved).** Via `Γ(X, ⊤)` (a domain) and `ringHom_eq_of_normal`. -/
theorem hom_spec_eq_of_point {L : Type} [Field L] [Algebra ℚ L] [Normal ℚ L] {X : Scheme.{0}}
    [IsIntegral X] {K : Type} [Field K] (g₁ g₂ : X ⟶ Spec (.of L)) (x : Spec (.of K) ⟶ X)
    (h : x ≫ g₁ = x ≫ g₂) : g₁ = g₂ := by
  apply ext_of_isAffine
  have h' := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h'
  have key := ringHom_eq_of_normal ((Scheme.ΓSpecIso (.of L)).inv ≫ g₁.appTop).hom
    ((Scheme.ΓSpecIso (.of L)).inv ≫ g₂.appTop).hom (x.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
    (by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
      congr 1
      simp only [Category.assoc]
      rw [reassoc_of% h'])
  rw [← cancel_epi (Scheme.ΓSpecIso (.of L)).inv]
  exact CommRingCat.hom_ext key

/-- `Spec` of an injective ring map is dominant (proved; the kernel is `0 ≤ nilradical`). -/
theorem isDominant_Spec_map_of_injective {R S : CommRingCat.{0}} (φ : R ⟶ S)
    (h : Function.Injective φ.hom) : IsDominant (Spec.map φ) := by
  refine ⟨?_⟩
  show DenseRange (PrimeSpectrum.comap φ.hom)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [h (hx.trans (map_zero _).symm)]
  exact zero_mem _

/-- Cancelling `Spec(s)` for an automorphism `s` of `ℚ̄` (proved). -/
theorem spec_aut_cancel (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {X : Scheme.{0}}
    {a b : Spec (.of (AlgebraicClosure ℚ)) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ a =
      Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ b) :
    a = b := by
  have hi : Spec.map (CommRingCat.ofHom (s.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
      Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (s.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp
          (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) = RingHom.id _ from
        RingHom.ext fun x => s.symm_apply_apply x,
      CommRingCat.ofHom_id, Spec.map_id]
  calc a = (Spec.map (CommRingCat.ofHom (s.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
        Spec.map (CommRingCat.ofHom (s : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) ≫ a := by
          rw [hi, Category.id_comp]
    _ = b := by rw [Category.assoc, h, ← Category.assoc, hi, Category.id_comp]

set_option synthInstance.maxHeartbeats 400000 in
/-- The unit section of a base change `(Over.pullback g').mapGrp.obj 𝒜`, followed by the first
projection, is `g'` followed by the unit section of `𝒜` (proved; `sf_eta_fst` for any `g'`). -/
theorem pb_eta_fst {S S' : Scheme.{0}} (g' : S' ⟶ S) (𝒜 : Grp (Over S)) :
    (η[((Over.pullback g').mapGrp.obj 𝒜).X]).left ≫ pullback.fst 𝒜.X.hom g' =
      g' ≫ (η[𝒜.X]).left := by
  let F := Over.pullback g'
  have hε : (Functor.LaxMonoidal.ε F).left ≫ pullback.snd (𝟙 S) g' = 𝟙 _ :=
    Over.w (Functor.LaxMonoidal.ε F)
  have hε2 : (Functor.LaxMonoidal.ε F).left ≫ pullback.fst (𝟙 S) g' = g' := by
    have hc : pullback.fst (𝟙 S) g' = pullback.snd (𝟙 S) g' ≫ g' := by
      rw [← pullback.condition, Category.comp_id]
    rw [hc, ← Category.assoc, hε, Category.id_comp]
  have hmap : (F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' =
      pullback.fst (𝟙 S) g' ≫ (η[𝒜.X]).left := pullback.lift_fst _ _ _
  show ((Functor.LaxMonoidal.ε F) ≫ F.map η[𝒜.X]).left ≫ pullback.fst 𝒜.X.hom g' = _
  rw [Over.comp_left, Category.assoc, hmap, ← Category.assoc, hε2]

/-- `Spec(O_w → L)`. -/
abbrev jSpec (L : IF) (v : ValuationSubring PkgI4.Qbar) :
    Spec (.of L) ⟶ Spec (.of (Ow L v)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L))

/-- `Spec(t)`, `t = σ⁻¹|_{O_w}`. -/
abbrev tSpec {L : IF} [IsGalois ℚ L] {v : ValuationSubring PkgI4.Qbar} (σ : PkgI4.GQ)
    (hσ : σ ∈ v.decompositionSubgroup ℚ) : Spec (.of (Ow L v)) ⟶ Spec (.of (Ow L v)) :=
  Spec.map (CommRingCat.ofHom (tSig σ hσ))

/-- `τ = σ⁻¹|_L`. -/
abbrev tauL (L : IF) [IsGalois ℚ L] (σ : PkgI4.GQ) : L →+* L :=
  (((σ⁻¹).restrictNormal L : L ≃ₐ[ℚ] L) : L →+* L)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **`FExtendGen` from the leaf I2-NMP (proved).**
1. `F` lies over `Spec τ`, `τ = σ⁻¹|_L`: both `F ≫ A → Spec L` and `A → Spec L → Spec L` agree at
   the `ℚ̄`-point `0` (from `f 0 = 0`), and `A` is integral (`hom_spec_eq_of_point`).
2. `ℬ = 𝒜 ×_{Spec t} Spec O_w` (the conjugate model) is an abelian scheme (base change).
3. `φ = (e ≫ F ≫ e⁻¹ ≫ pr₁, pr₂) : 𝒜_L → ℬ_L` is an `L`-morphism; I2-NMP gives `G : 𝒜 → ℬ`
   over `O_w` with `G_L = φ`; `F̃ = G ≫ pr₁` lies over `Spec t` and restricts to `F`.
4. `F̃` fixes the unit section: both sides agree on `Spec L` (because `F(0) = 0` twisted, by
   separatedness of `A` and dominance of `Spec ℚ̄ → Spec L`), hence on `Spec O_w`
   (separatedness of `𝒜`, dominance of `Spec L → Spec O_w`). -/
theorem fExtendGen_of_nmp (hN : PkgI2.NeronMappingAbelianScheme.{0}) : FExtendGen := by
  intro L _ _ A F _ _ p hp v σ hv hσ 𝒜 h𝒜 e f hf
  generalize hσ.1 = hσ1
  haveI : IsDiscreteValuationRing (Ow L v) := owDVR L v p hp hv
  haveI : IsProper 𝒜.X.hom := h𝒜.proper
  haveI : Smooth 𝒜.X.hom := h𝒜.smooth
  haveI : GeometricallyConnected 𝒜.X.hom := h𝒜.geomConnected
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  -- ring identities
  have hR1 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫ Spec.map (CommRingCat.ofHom (tauL L σ)) =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    show σ (algebraMap L PkgI4.Qbar ((σ⁻¹).restrictNormal L a)) = algebraMap L PkgI4.Qbar a
    rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  have hR2 : jSpec L v ≫ tSpec σ hσ1 = Spec.map (CommRingCat.ofHom (tauL L σ)) ≫ jSpec L v := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    rfl
  -- the zero point
  let x0 : Spec (.of Qbar) ⟶ A.X.left := (Additive.toMul (0 : PtQ L A)).left
  have hu : (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar)).left =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) :=
    (Category.comp_id _).symm.trans
      (Over.w (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar)))
  have hx0 : x0 = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫ (η[A.X]).left := by
    show (CartesianMonoidalCategory.toUnit (PkgI3.AbVar.ptObj (K := L) Qbar)).left ≫
      (η[A.X]).left = _
    rw [hu]
    rfl
  have hx0w : x0 ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) :=
    Over.w (Additive.toMul (0 : PtQ L A))
  have hηw : (η[A.X]).left ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
  have hf0 : Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
      x0 ≫ F = x0 := by
    have := hf 0
    rw [map_zero] at this
    exact this.symm
  have hpt : x0 ≫ F = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫
      Spec.map (CommRingCat.ofHom (tauL L σ)) ≫ (η[A.X]).left := by
    apply spec_aut_cancel (act σ)
    rw [hf0, reassoc_of% hR1]
    exact hx0
  -- Step 1: `F` lies over `Spec τ`
  have hFover : F ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (tauL L σ)) := by
    apply hom_spec_eq_of_point _ _ x0
    rw [reassoc_of% hpt, hηw, reassoc_of% hx0w]
    erw [Category.comp_id]
  -- `F(0) = 0`, twisted
  have hF0 : (η[A.X]).left ≫ F = Spec.map (CommRingCat.ofHom (tauL L σ)) ≫ (η[A.X]).left := by
    haveI := isDominant_Spec_map_of_injective (CommRingCat.ofHom (algebraMap L Qbar))
      (algebraMap L Qbar).injective
    refine ext_of_isDominant_of_isSeparated (X := Spec (.of L)) A.X.hom ?_
      (Spec.map (CommRingCat.ofHom (algebraMap L Qbar))) ?_
    · simp only [Category.assoc]
      rw [hFover, reassoc_of% hηw, hηw]
      erw [Category.comp_id]
    · calc _ = x0 ≫ F := by rw [hx0, Category.assoc]
        _ = _ := hpt
  -- Step 2: the conjugate model
  let ℬ := (Over.pullback (tSpec σ hσ1)).mapGrp.obj 𝒜
  haveI hℬ : PkgI2.IsAbelianScheme ℬ :=
    ⟨show IsProper (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) from inferInstance,
      show Smooth (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) from inferInstance,
      show GeometricallyConnected (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) from inferInstance⟩
  -- Step 3: the generic morphism and I2-NMP
  let E : pullback 𝒜.X.hom (jSpec L v) ⟶ A.X.left := e.hom.hom.hom.left
  let Ei : A.X.left ⟶ pullback 𝒜.X.hom (jSpec L v) := e.inv.hom.hom.left
  have hEi : Ei ≫ E = 𝟙 _ := congrArg (fun m => m.hom.hom.left) e.inv_hom_id
  have hEw : E ≫ A.X.hom = pullback.snd 𝒜.X.hom (jSpec L v) := Over.w e.hom.hom.hom
  have hEiw : Ei ≫ pullback.snd 𝒜.X.hom (jSpec L v) = A.X.hom := Over.w e.inv.hom.hom
  have c1 : (E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v)) ≫ 𝒜.X.hom =
      (pullback.snd 𝒜.X.hom (jSpec L v) ≫ jSpec L v) ≫ tSpec σ hσ1 := by
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% hEiw, reassoc_of% hFover, reassoc_of% hEw, hR2]
  let inner : pullback 𝒜.X.hom (jSpec L v) ⟶ pullback 𝒜.X.hom (tSpec σ hσ1) :=
    pullback.lift (E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v))
      (pullback.snd 𝒜.X.hom (jSpec L v) ≫ jSpec L v) c1
  let φl : pullback 𝒜.X.hom (jSpec L v) ⟶
      pullback (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) (jSpec L v) :=
    pullback.lift inner (pullback.snd 𝒜.X.hom (jSpec L v)) (pullback.lift_snd _ _ _)
  let φ : (Over.pullback (jSpec L v)).obj 𝒜.X ⟶ (Over.pullback (jSpec L v)).obj ℬ.X :=
    Over.homMk φl (pullback.lift_snd _ _ _)
  obtain ⟨G, hG⟩ := (hN L (Ow L v) 𝒜 ℬ).2 φ
  have hG' : (Over.pullback (jSpec L v)).map G = φ := hG
  let Gl : 𝒜.X.left ⟶ pullback 𝒜.X.hom (tSpec σ hσ1) := G.left
  let Ft : 𝒜.X.left ⟶ 𝒜.X.left := Gl ≫ pullback.fst 𝒜.X.hom (tSpec σ hσ1)
  have hGl : pullback.fst 𝒜.X.hom (jSpec L v) ≫ Gl =
      φl ≫ pullback.fst (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) (jSpec L v) := by
    have h1 : ((Over.pullback (jSpec L v)).map G).left ≫
        pullback.fst (pullback.snd 𝒜.X.hom (tSpec σ hσ1)) (jSpec L v) =
        pullback.fst 𝒜.X.hom (jSpec L v) ≫ G.left := pullback.lift_fst _ _ _
    have h2 : ((Over.pullback (jSpec L v)).map G).left = φl := congrArg (fun m => m.left) hG'
    rw [← h2]
    exact h1.symm
  have hfst : pullback.fst 𝒜.X.hom (jSpec L v) ≫ Ft =
      E ≫ F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) := by
    show pullback.fst 𝒜.X.hom (jSpec L v) ≫ Gl ≫ pullback.fst 𝒜.X.hom (tSpec σ hσ1) = _
    rw [← Category.assoc (pullback.fst 𝒜.X.hom (jSpec L v)), hGl, Category.assoc φl]
    simp only [φl, inner, pullback.lift_fst_assoc, pullback.lift_fst]
  have hC3 : Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) ≫ Ft =
      F ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) := by
    rw [hfst, ← Category.assoc Ei E, hEi, Category.id_comp]
  have hGw : Gl ≫ pullback.snd 𝒜.X.hom (tSpec σ hσ1) = 𝒜.X.hom := Over.w G
  have hC1 : Ft ≫ 𝒜.X.hom = 𝒜.X.hom ≫ tSpec σ hσ1 := by
    show (Gl ≫ pullback.fst 𝒜.X.hom (tSpec σ hσ1)) ≫ 𝒜.X.hom = _
    rw [Category.assoc, pullback.condition, reassoc_of% hGw]
  refine ⟨Ft, hC1, ?_, hC3⟩
  -- Step 4: the unit section
  have hηO : (η[𝒜.X]).left ≫ 𝒜.X.hom = 𝟙 _ := Over.w η[𝒜.X]
  have hηL : jSpec L v ≫ (η[𝒜.X]).left =
      (η[A.X]).left ≫ Ei ≫ pullback.fst 𝒜.X.hom (jSpec L v) := by
    rw [← pb_eta_fst (jSpec L v) 𝒜, ← Category.assoc]
    congr 1
    have h1 : η[A.X] ≫ e.inv.hom.hom = η[((Over.pullback (jSpec L v)).mapGrp.obj 𝒜).X] :=
      IsMonHom.one_hom _
    exact (congrArg (fun m => m.left) h1).symm
  haveI := isDominant_Spec_map_of_injective (CommRingCat.ofHom (algebraMap (Ow L v) L))
    (Subtype.val_injective)
  refine ext_of_isDominant_of_isSeparated (X := Spec (.of (Ow L v))) 𝒜.X.hom ?_ (jSpec L v) ?_
  · simp only [Category.assoc]
    rw [hC1, reassoc_of% hηO, hηO]
    erw [Category.comp_id]
  · rw [reassoc_of% hηL, hC3, reassoc_of% hF0, reassoc_of% hR2, hηL]

/-- **`FExtendCore` from I2-NMP (proved).** -/
theorem fExtendCore_of_nmp (hN : PkgI2.NeronMappingAbelianScheme.{0}) : FExtendCore :=
  fExtendCore_of_gen (fExtendGen_of_nmp hN)

/-- **Main result: `FrobTrace.AlgFrobRed` from the leaf candidates `GoodRedCofinite`,
`SmoothGeomConnIntegral` and the kernel leaves I2-Red, I2-NMP (proved).** alg-frob-red's two glue
Props are discharged: `AbsFrob` (`absFrob`, Mathlib only) and `FExtendGen` (`fExtendGen_of_nmp`). -/
theorem algFrobRed_of_nmp (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen hG hS hRed (fExtendGen_of_nmp hN) absFrob

/-- **`TateBridge35` from I3.M0, the two leaf candidates and I2-Red, I2-NMP (proved).** -/
theorem tateBridge35_of_nmp (hT : PkgI3.TateModuleFree) (hG : GoodRedCofinite)
    (hS : SmoothGeomConnIntegral) (hRed : PkgI2.ReductionTorsionBijective.{0})
    (hN : PkgI2.NeronMappingAbelianScheme.{0}) : G14Bridge.TateBridge35 :=
  tateBridge35_of_gen hT hG hS hRed (fExtendGen_of_nmp hN) absFrob

end AlgFrobRedRed



/-! # frob-pieces: `GoodRedCofinite` from spreading out (task frob-pieces)

Appended (by `scratch/frob-pieces/build.sh`) to a verbatim copy of
`scratch/alg-frob-red/AlgFrobRed.lean`. -/

noncomputable section

namespace FrobPiecesGood

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

set_option synthInstance.maxHeartbeats 400000 in
/-- **`AbSchemeSpreadsOut` (LEAF candidate, published: spreading out an abelian variety to an
abelian scheme).** An abelian variety `A` over a number field `L ⊆ ℚ̄` extends to an abelian
scheme (I2's `IsAbelianScheme`: a group object, proper, smooth, geometrically connected) over a
finitely generated subring `R = ℤ[s] ⊆ L`, with generic fibre isomorphic to `A` as a group object.
Source: `L = colim R` over finitely generated subrings; the scheme, group law and axioms descend to
some `R` (EGA IV₃ 8.8.2), as do properness (EGA IV₃ 8.10.5 (xii)) and smoothness (EGA IV₄ 17.7.8);
geometric connectedness of the fibres holds after shrinking `R` to a normal ring with fraction
field `L`, e.g. `𝓞_L[1/N]` (finitely generated: an integral basis and `1/N`), by Zariski's
connectedness theorem (EGA III₁ 4.3; this is `FrobPiecesNeron.ProperSmoothGenConnected`), or
over a nonempty open of `Spec R` (EGA IV₃ 9.7.7, with a generic-point argument). Locators UNVERIFIED. Same input as
neron-lg's glue N1-g1 `AbVarSpreadsOut`, plus geometric connectedness of the fibres. -/
def AbSchemeSpreadsOut : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (A : PkgI3.AbVar L),
    ∃ (s : Finset L) (𝒜 : Grp (Over (Spec (.of (Subring.closure (s : Set L)))))),
      PkgI2.IsAbelianScheme 𝒜 ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap (Subring.closure (s : Set L)) L)))).mapGrp.obj 𝒜 ≅ ObjBridge.toGrp A)

/-- A nonzero integer prime to `p` is a unit in `O_w` for `w ∣ p`. -/
theorem isUnit_intCast_of_coprime {L : IF} {v : ValuationSubring PkgI4.Qbar} {p : ℕ}
    (hp : p.Prime) (hv : PkgI4.LiesOver v p) {y : ℤ}
    (hpy : ¬ p ∣ y.natAbs) : IsUnit (y : Ow L v) := by
  by_contra hnu
  have hym : (y : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  have hpm := natCast_mem_maximalIdeal (L := L) hp hv
  have hcop : IsCoprime (p : ℤ) y := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := (Nat.Prime.coprime_iff_not_dvd hp).2 hpy
    simpa [Int.gcd] using this
  obtain ⟨u, w, huw⟩ := hcop
  have h1 : ((u * p + w * y : ℤ) : Ow L v) ∈ IsLocalRing.maximalIdeal (Ow L v) := by
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hym)
  rw [huw, Int.cast_one] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)

set_option synthInstance.maxHeartbeats 400000 in
/-- Base change of a group object along equal morphisms. -/
theorem pullbackGrp_congr {X Y : Scheme} {f f' : X ⟶ Y} (h : f = f') (𝒜 : Grp (Over Y)) :
    Nonempty ((Over.pullback f).mapGrp.obj 𝒜 ≅ (Over.pullback f').mapGrp.obj 𝒜) := by
  subst h; exact ⟨Iso.refl _⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **`GoodRedCofinite` from `AbSchemeSpreadsOut` (proved).** Let `𝒜/ℤ[s]` spread out `A`, and
`y ≠ 0` an integer with `y·a` integral for every `a ∈ s` (`exists_integral_multiples`). For a prime
`p ∤ y` and `w ∣ p`, `y` is a unit and integral elements lie in the valuation ring `O_w`, so
`ℤ[s] ⊆ O_w`; the base change of `𝒜` to `O_w` is an abelian scheme (base-change stability) whose
generic fibre is that of `𝒜` (`Over.pullbackComp`, `Functor.mapGrpNatIso`). -/
theorem goodRedCofinite_of (h : AbSchemeSpreadsOut) : GoodRedCofinite := by
  intro L _ A
  letI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  obtain ⟨s, 𝒜, h𝒜, ⟨e⟩⟩ := h L A
  obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨y.natAbs.primeFactors, fun p hp hpS v hv => ?_⟩
  have hpy : ¬ p ∣ y.natAbs := fun hd =>
    hpS (Nat.mem_primeFactors.2 ⟨hp, hd, Int.natAbs_ne_zero.2 hy0⟩)
  obtain ⟨u, hu⟩ := isUnit_intCast_of_coprime (L := L) hp hv hpy
  have hinv : (y : L)⁻¹ ∈ Ow L v := by
    have h2 : ((u⁻¹ : (Ow L v)ˣ) : Ow L v) * (y : Ow L v) = 1 := by rw [← hu]; exact u.inv_mul
    have h3 : (((u⁻¹ : (Ow L v)ˣ) : Ow L v) : L) * (y : L) = 1 := by
      have := congrArg (fun z : Ow L v => (z : L)) h2
      simpa using this
    rw [← eq_inv_of_mul_eq_one_left h3]
    exact ((u⁻¹ : (Ow L v)ˣ) : Ow L v).2
  have hmem : ∀ a ∈ s, a ∈ Ow L v := by
    intro a ha
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1
      (show IsIntegral (Ow L v) (y • a) from (hyint a ha).tower_top)
    have hyL : (y : L) ≠ 0 := by exact_mod_cast hy0
    have ha' : a = (y : L)⁻¹ * (y • a) := by
      rw [zsmul_eq_mul, ← _root_.mul_assoc, inv_mul_cancel₀ hyL, _root_.one_mul]
    rw [ha', ← hb]
    exact mul_mem hinv b.2
  have hle : Subring.closure (s : Set L) ≤ (Ow L v).toSubring :=
    Subring.closure_le.2 (fun a ha => hmem a ha)
  let φ : Subring.closure (s : Set L) →+* Ow L v := Subring.inclusion hle
  let g := Spec.map (CommRingCat.ofHom φ)
  refine ⟨(Over.pullback g).mapGrp.obj 𝒜, ?_, ?_⟩
  · have := h𝒜.proper; have := h𝒜.smooth; have := h𝒜.geomConnected
    refine ⟨?_, ?_, ?_⟩
    · show IsProper (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show Smooth (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show GeometricallyConnected (Limits.pullback.snd 𝒜.X.hom g); infer_instance
  · have hcomp : Spec.map (CommRingCat.ofHom (algebraMap (Ow L v) L)) ≫ g =
        Spec.map (CommRingCat.ofHom (algebraMap (Subring.closure (s : Set L)) L)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    refine ⟨(Functor.mapGrpCompIso.app 𝒜).symm ≪≫
      (Functor.mapGrpNatIso (Over.pullbackComp _ _).symm).app 𝒜 ≪≫ ?_⟩
    exact (pullbackGrp_congr hcomp 𝒜).some ≪≫ e

end FrobPiecesGood

end



/-! # frob-pieces: `GoodRedCofinite` from neron-lg's glue N1-g1 `AbVarSpreadsOut` and Zariski's
connectedness theorem (task frob-pieces)

`HasAbelianSchemeAway` and `AbVarSpreadsOut` below are verbatim copies (docstring and `def`) of
the declarations of the same names in `scratch/neron-lg/NeronLG.lean` (namespace
`ZInQ.NeronLG`), under the same `open`s (checked by `scratch/frob-pieces/py/verbatim_check.py`). -/

noncomputable section

namespace FrobPiecesNeron

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI3 (AbVar)
open scoped Obj

/-- `B` extends to an abelian scheme over `𝓞_L[1/f]`: a smooth proper group scheme whose generic
fibre is identified with `B` as a group scheme (over every presentation of `𝓞_L[1/f]`). -/
def HasAbelianSchemeAway (L : Type) [Field L] [NumberField L] (B : AbVar L) (f : 𝓞 L) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away f R] [Algebra R L]
    [IsScalarTower (𝓞 L) R L],
    ∃ (G : Over (Spec (CommRingCat.of R))) (_ : GrpObj G) (_ : Smooth G.hom) (_ : IsProper G.hom)
      (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X),
      letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
        Functor.grpObjObj
      IsMonHom gen.hom

/-- **Glue N1-g1 (spreading out an abelian variety).** An abelian variety `B` over a number field
`L` extends to an abelian scheme over `𝓞_L[1/f]` for some nonzero `f ∈ 𝓞_L`. Textbook (a
candidate for a textbook leaf): `L = colim 𝓞_L[1/f]`, so `B`, its group law, unit and inverse
and the group axioms (equalities of morphisms) descend to some `𝓞_L[1/f]` (EGA IV₃ 8.8.2), as do
properness (EGA IV₃ 8.10.5 (xii)) and smoothness (EGA IV₄ 17.7.8 (ii)); all locators UNVERIFIED.
Mathlib v4.35 has the descent of morphisms for affine transition maps
(`AlgebraicGeometry/.../AffineTransitionLimit.lean`, EGA IV 8.8.2) but not the descent of schemes
or of properness and smoothness. -/
def AbVarSpreadsOut : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : AbVar L), ∃ f : 𝓞 L, f ≠ 0 ∧ HasAbelianSchemeAway L B f

set_option synthInstance.maxHeartbeats 400000 in
/-- **`ProperSmoothGenConnected` (LEAF candidate, published: Zariski's connectedness theorem).**
A smooth proper scheme `X` over `R = 𝓞_L[1/f]` (any presentation) whose generic fibre is
geometrically connected is geometrically connected over `R`. Proof (STANDARD): `R ≅ 𝓞_L[1/f]`
is normal with fraction field `L` (the case `f = 0` is vacuous: no ring map from the zero ring to
`L`), and `X_L` is geometrically reduced (smooth) and geometrically connected and proper, so
`H⁰(X_L, 𝒪) = L`; `f_*𝒪_X` is a finite `R`-algebra, torsion-free since `X` is flat (smooth), so
it lies inside `H⁰(X_L, 𝒪) = L` and is integral over the normal `R`, hence
`f_*𝒪_X = 𝒪_{Spec R}`; then all fibres of the proper `f` are geometrically connected (Zariski's
connectedness theorem, EGA III₁ 4.3.1–4.3.4; locators UNVERIFIED). The fibres are nonempty since
`X → Spec R` is open (smooth), closed (proper), `X ≠ ∅` and `Spec R` is connected. Not in Mathlib
v4.35 (no Stein factorization). -/
def ProperSmoothGenConnected : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (f : 𝓞 L) (R : Type) [CommRing R] [Algebra (𝓞 L) R]
    [IsLocalization.Away f R] [Algebra R L] [IsScalarTower (𝓞 L) R L]
    (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProper X.hom →
    GeometricallyConnected
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj X).hom →
    GeometricallyConnected X.hom

/-- Geometrically integral implies geometrically connected. -/
theorem geometricallyConnected_of_geometricallyIntegral {X Y : Scheme.{0}} (g : X ⟶ Y)
    [GeometricallyIntegral g] : GeometricallyConnected g := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
  infer_instance

/-- `A` has good reduction at `O` if an abelian scheme over a ring `R` mapping to `O` (compatibly
with the maps to `K`) has generic fibre `≅ A`: base change along `Spec O → Spec R`. -/
theorem hasGoodReduction_of_base {K : Type} [Field K] (O : ValuationSubring K) {R : Type}
    [CommRing R] (ιR : R →+* K) (φ : R →+* O) (hφ : (algebraMap O K).comp φ = ιR)
    (A : Grp (Over (Spec (.of K)))) (𝒜 : Grp (Over (Spec (.of R))))
    (h𝒜 : PkgI2.IsAbelianScheme 𝒜)
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom ιR))).mapGrp.obj 𝒜 ≅ A) :
    PkgI2.HasGoodReduction A O := by
  let g := Spec.map (CommRingCat.ofHom φ)
  refine ⟨(Over.pullback g).mapGrp.obj 𝒜, ?_, ?_⟩
  · have := h𝒜.proper; have := h𝒜.smooth; have := h𝒜.geomConnected
    refine ⟨?_, ?_, ?_⟩
    · show IsProper (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show Smooth (Limits.pullback.snd 𝒜.X.hom g); infer_instance
    · show GeometricallyConnected (Limits.pullback.snd 𝒜.X.hom g); infer_instance
  · have hcomp : Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ g =
        Spec.map (CommRingCat.ofHom ιR) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hφ]
    exact ⟨(Functor.mapGrpCompIso.app 𝒜).symm ≪≫
      (Functor.mapGrpNatIso (Over.pullbackComp _ _).symm).app 𝒜 ≪≫
      (FrobPiecesGood.pullbackGrp_congr hcomp 𝒜).some ≪≫ e⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **`GoodRedCofinite` from neron-lg's N1-g1 `AbVarSpreadsOut` and `ProperSmoothGenConnected`
(proved).** Spread `A` out to `G/𝓞_L[1/f]` (presentation `Localization.Away f`); `G` is
geometrically connected by `ProperSmoothGenConnected` (its generic fibre is `≅ A`, geometrically
integral). `S` is the set of prime factors of `N = |N_{L/ℚ}(f)|`: for `p ∉ S` and `w ∣ p`, `N` is a
unit of `O_w` and `N ∈ (f)`, so `f` is a unit of `O_w`, and `𝓞_L[1/f] → L` factors through `O_w`
(`IsLocalization.Away.lift`); conclude by base change (`hasGoodReduction_of_base`). -/
theorem goodRedCofinite_of_neron (hsp : AbVarSpreadsOut) (hc : ProperSmoothGenConnected) :
    AlgFrobRedRed.GoodRedCofinite := by
  intro L _ A
  letI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  obtain ⟨f, hf0, hf⟩ := hsp L A
  have hfL : IsUnit (algebraMap (𝓞 L) L f) :=
    isUnit_iff_ne_zero.2 (by simpa using hf0)
  let R := Localization.Away f
  letI : Algebra R L := (IsLocalization.Away.lift f hfL).toAlgebra
  haveI : IsScalarTower (𝓞 L) R L := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsLocalization.Away.lift_eq f hfL x).symm)
  obtain ⟨G, hG, hGs, hGp, gen, hgen⟩ := hf R
  have hgc : GeometricallyConnected G.hom := by
    refine hc L f R G hGs hGp ?_
    have h1 : GeometricallyConnected A.X.hom := geometricallyConnected_of_geometricallyIntegral _
    have h2 : ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G).hom =
        gen.hom.left ≫ A.X.hom := (Over.w gen.hom).symm
    rw [h2]
    have hR : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0})
      gen.hom.left A.X.hom).2 h1
  let N : ℕ := Ideal.absNorm (Ideal.span {f})
  have hN0 : N ≠ 0 := by
    simp only [N, ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hf0
  refine ⟨N.primeFactors, fun p hp hpS v hv => ?_⟩
  have hpN : ¬ p ∣ (N : ℤ).natAbs := by
    rw [Int.natAbs_natCast]
    exact fun hd => hpS (Nat.mem_primeFactors.2 ⟨hp, hd, hN0⟩)
  have hNu : IsUnit ((N : ℤ) : AlgFrobRedRed.Ow L v) :=
    FrobPiecesGood.isUnit_intCast_of_coprime (L := L) hp hv hpN
  have hfu : IsUnit (AlgFrobRedRed.toO' (AlgFrobRedRed.Ow L v) f) := by
    by_contra hnu
    have hfm : AlgFrobRedRed.toO' (AlgFrobRedRed.Ow L v) f ∈
        IsLocalRing.maximalIdeal (AlgFrobRedRed.Ow L v) := (IsLocalRing.mem_maximalIdeal _).2 hnu
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {f}))
    have : ((N : ℤ) : AlgFrobRedRed.Ow L v) ∈ IsLocalRing.maximalIdeal (AlgFrobRedRed.Ow L v) := by
      have := congrArg (AlgFrobRedRed.toO' (AlgFrobRedRed.Ow L v)) hc'
      rw [map_mul, map_natCast] at this
      rw [Int.cast_natCast, ← this]
      exact Ideal.mul_mem_left _ _ hfm
    exact (IsLocalRing.mem_maximalIdeal _).1 this hNu
  let φ : R →+* AlgFrobRedRed.Ow L v := IsLocalization.Away.lift f hfu
  have hφ : (algebraMap (AlgFrobRedRed.Ow L v) L).comp φ = algebraMap R L := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, φ, IsLocalization.Away.lift_eq]
    exact (IsLocalization.Away.lift_eq f hfL x).symm
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
    Functor.grpObjObj
  exact hasGoodReduction_of_base _ (algebraMap R L) φ hφ _ (Grp.mk G) ⟨hGp, hGs, hgc⟩
    (Grp.mkIso' gen)

end FrobPiecesNeron

end



/-! # frob-pieces: `AlgFrobRed` with `SmoothGeomConnIntegral` discharged and `GoodRedCofinite`
replaced by `AbSchemeSpreadsOut` -/

noncomputable section

namespace FrobPiecesGood

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

/-- **alg-frob-red's `SmoothGeomConnIntegral`, proved** (it is definitionally the verbatim copy
`FrobPieces.SmoothGeomConnIntegral` of `ZInQKernel/Contrib/FrobPieces/SmoothGeomConnIntegral.lean`,
proved there from the vendored Tau Ceti theorem `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`). -/
theorem smoothGeomConnIntegral : AlgFrobRedRed.SmoothGeomConnIntegral :=
  FrobPieces.smoothGeomConnIntegral

/-- **`AlgFrobRed` from `AbSchemeSpreadsOut`, I2-Red, `FExtendGen`, `AbsFrob` (proved).** -/
theorem algFrobRed_of_spread (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen (goodRedCofinite_of hG) smoothGeomConnIntegral hRed hE hA

/-- **`AlgFrobRed` from `GoodRedCofinite`, I2-Red, `FExtendGen`, `AbsFrob` (proved).** -/
theorem algFrobRed_of_four (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen hG smoothGeomConnIntegral hRed hE hA

/-- **`TateBridge35` from I3.M0, `AbSchemeSpreadsOut`, I2-Red, `FExtendGen`, `AbsFrob`
(proved).** -/
theorem tateBridge35_of_spread (hT : PkgI3.TateModuleFree) (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_spread hG hRed hE hA)

/-- **`AlgFrobRed` from neron-lg's glue N1-g1 `AbVarSpreadsOut`, `ProperSmoothGenConnected`,
I2-Red, `FExtendGen`, `AbsFrob` (proved).** -/
theorem algFrobRed_of_neron (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_gen (FrobPiecesNeron.goodRedCofinite_of_neron hsp hc) smoothGeomConnIntegral hRed
    hE hA

/-- **`TateBridge35` from I3.M0, N1-g1, `ProperSmoothGenConnected`, I2-Red, `FExtendGen`,
`AbsFrob` (proved).** -/
theorem tateBridge35_of_neron (hT : PkgI3.TateModuleFree) (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_neron hsp hc hRed hE hA)

end FrobPiecesGood

end




/-! # frob-pieces: the combined form with afr-absfrob's `AbsFrob` and `FExtendGen`

Appended by `build_full.sh` after afr-absfrob's assembled `AfrAbsFrob.lean` (verbatim copy, which
begins with alg-frob-red's `AlgFrobRed.lean`) and this task's parts. -/

noncomputable section

namespace FrobPiecesGood

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

/-- **`FrobTrace.AlgFrobRed` from neron-lg's glue N1-g1 `AbVarSpreadsOut`, the leaf candidate
`ProperSmoothGenConnected` and the kernel leaves I2-Red, I2-NMP (proved).** -/
theorem algFrobRed_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_nmp (FrobPiecesNeron.goodRedCofinite_of_neron hsp hc) smoothGeomConnIntegral
    hRed hN

/-- **`FrobTrace.AlgFrobRed` from `AbSchemeSpreadsOut` and the kernel leaves I2-Red, I2-NMP
(proved).** -/
theorem algFrobRed_of_spread_nmp (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_nmp (goodRedCofinite_of hG) smoothGeomConnIntegral hRed hN

/-- **`FrobTrace.AlgFrobRed` from `GoodRedCofinite` and the kernel leaves I2-Red, I2-NMP
(proved).** -/
theorem algFrobRed_of_goodRed_nmp (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  algFrobRed_of_nmp hG smoothGeomConnIntegral hRed hN

/-- **`G14Bridge.TateBridge35` from I3.M0, N1-g1, `ProperSmoothGenConnected`, I2-Red, I2-NMP
(proved).** -/
theorem tateBridge35_of_neron_nmp (hT : PkgI3.TateModuleFree)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_neron_nmp hsp hc hRed hN)

/-- **`G14Bridge.TateBridge35` from I3.M0, `AbSchemeSpreadsOut`, I2-Red, I2-NMP (proved).** -/
theorem tateBridge35_of_spread_nmp (hT : PkgI3.TateModuleFree) (hG : AbSchemeSpreadsOut)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_spread_nmp hG hRed hN)

end FrobPiecesGood

end



/-! # linked-frob: linked-tate's glue `UnramTate.LinkedFrob`, reduced to frob-trace's `AlgFrobLink`

`UnramTate.LinkedFrob` (scratch/linked-tate/parts/97_linkeddata.lean, compiled above, unchanged) asks
g14-trace's `FrobTraceLink` for the canonical operators `tmOf … ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at
`ℓ = 5, 3`. frob-trace's `AlgFrobLink` (copied above, verbatim) gives, outside a finite set `S` of
primes, at every arithmetic Frobenius `τ` above `p ∉ S` and for every `g` (here `g = h`), one abelian
variety `Ā` over a field of characteristic `p`, `α' ∈ End(Ā)`, `N ≠ 0` and, for every `ℓ ≠ p`, a
`ℚ_ℓ`-isomorphism carrying `N·V_ℓ(m_{gτg⁻¹})` to `V_ℓ(α')`. frob-trace's `frobCompare_opV_conjE`
turns that into the kernel's `FrobCompare` for `opV(Θ ∘ m_{hτh⁻¹} ∘ Θ⁻¹)`, which is `tmOf … ℓ τ`.
The set is `S ∪ {3, 5}`, so that `ℓ ≠ p` at `ℓ = 3, 5`. -/

section LinkedFrobSec

noncomputable section

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

namespace LinkedFrobRed

/-- `tmOf … ℓ τ` is `opV(Θ ∘ m_{hτh⁻¹} ∘ Θ⁻¹)` (definitional). -/
theorem tmOf_eq {L L' : IF} (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ)
    (m : GQ → (PtQ L A →+ PtQ L A)) (ℓ : ℕ) [Fact ℓ.Prime] (τ : PkgI4.GQ) :
    tmOf hLL' A Θ h m ℓ τ =
      opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m (h * τ * h⁻¹))) :=
  rfl

/-- **`LinkedFrob` from frob-trace's `AlgFrobLink` (proved).** Only three of the descent-datum
clauses are used (`m_σ` is the Galois action on `G_L`, the coset rule, algebraicity `F_σ`). -/
theorem linkedFrob_of_algFrobLink (hF : FrobTrace.AlgFrobLink) : UnramTate.LinkedFrob := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD Θ h hΘ m a n d h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨S, hS⟩ := hF L A m h3 h4 h8
  refine ⟨S ∪ {3, 5}, fun p hp hpS v τ hv hτ => ?_⟩
  have hpS' : p ∉ S := fun h' => hpS (Finset.mem_union_left _ h')
  have hp3 : (3 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  have hp5 : (5 : ℕ) ≠ p := fun h' => hpS (Finset.mem_union_right _ (by simp [← h']))
  obtain ⟨k, _, hk, Ab, α, N', hN', hΨ⟩ := hS p hp hpS' v τ hv hτ h
  obtain ⟨Ψ3, hΨ3⟩ := hΨ 3 hp3
  obtain ⟨Ψ5, hΨ5⟩ := hΨ 5 hp5
  refine ⟨k, inferInstance, hk, Ab, α, N', hN', ?_, ?_⟩
  · rw [tmOf_eq]
    exact FrobTrace.frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 3 Ab α N' Ψ3 hΨ3
  · rw [tmOf_eq]
    exact FrobTrace.frobCompare_opV_conjE A _ Θ (m (h * τ * h⁻¹)) 5 Ab α N' Ψ5 hΨ5

/-- **`LinkedFrob` from frob-trace's `AlgFrobRed` (proved):** frob-trace's
`AlgFrobRed → AlgFrobOne → AlgFrobLink`. -/
theorem linkedFrob_of_algFrobRed (hR : FrobTrace.AlgFrobRed) : UnramTate.LinkedFrob :=
  linkedFrob_of_algFrobLink (FrobTrace.algFrobLink_of_one (FrobTrace.algFrobOne_of_red hR))

end LinkedFrobRed

end

end LinkedFrobSec

/-! # linked-frob: `LinkedFrob` from the frob chain, and `GluePieces4`

`GluePieces4` is linked-tate's `GluePieces3` (scratch/linked-tate/parts/99_bundle3.lean; all fields
copied verbatim with their docstrings) with the field `linkedFrob` replaced by frob-pieces'
`AbVarSpreadsOut` (neron-lg's N1-g1) and `ProperSmoothGenConnected`; I2-NMP and I2-Red are the
textbook leaves `t.t3`, `t.t4` of the bundle. -/

section LinkedFrobBundleSec

noncomputable section

namespace LinkedFrobRed

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate AlgFrobRedRed

/-- **`LinkedFrob` from alg-frob-red's five inputs (proved).** -/
theorem linkedFrob_of_gen (hG : GoodRedCofinite) (hS : SmoothGeomConnIntegral)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hE : FExtendGen) (hA : AbsFrob) :
    UnramTate.LinkedFrob :=
  linkedFrob_of_algFrobRed (algFrobRed_of_gen hG hS hRed hE hA)

/-- **`LinkedFrob` from `GoodRedCofinite`, I2-Red and I2-NMP (proved;** frob-pieces' and
afr-absfrob's discharge of `SmoothGeomConnIntegral`, `FExtendGen`, `AbsFrob`). -/
theorem linkedFrob_of_goodRed_nmp (hG : GoodRedCofinite)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    UnramTate.LinkedFrob :=
  linkedFrob_of_algFrobRed (FrobPiecesGood.algFrobRed_of_goodRed_nmp hG hRed hN)

/-- **`LinkedFrob` from N1-g1 `AbVarSpreadsOut`, `ProperSmoothGenConnected`, I2-Red and I2-NMP
(proved).** -/
theorem linkedFrob_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    UnramTate.LinkedFrob :=
  linkedFrob_of_algFrobRed (FrobPiecesGood.algFrobRed_of_neron_nmp hsp hc hRed hN)


end LinkedFrobRed

end

end LinkedFrobBundleSec


end  -- assemble-port: closes an unclosed `noncomputable section` of the copied files

end  -- assemble-port: closes an unclosed `noncomputable section` of the copied files


end G0A3_z93_linkedfrob

section G0A3_z93z_ltlocal
/-! ## assemble-port (stretch): lg-kerwild + lt-local, de-duplicated against this file (mk/mk_z93b.py) -/


-- BEGIN verbatim body of scratch/local-glue/LocalGlue.lean

/-! # local-data: `LocalData p r` (scratch/g15-ram) on G8's `r`

Assembled by `scratch/local-data/build.sh`. Check with
`lake env lean scratch/local-data/LocalData.lean`. The first part (through `end Reduction`) is a
verbatim copy of `scratch/g15-ram/G15Ram.lean` lines 8-1384; then verbatim definitions from
`scratch/g0-mod-galois/part_galois.lean`; then §4 (new). -/

/-!
# g15-ram: the open Prop `G15RamG` of g0-mod-newform (G15, clauses (i)-(ii))

Check with `lake env lean scratch/g15-ram/G15Ram.lean`.

* §0. Verbatim copies (from `scratch/g0-mod-newform/part_new.lean`, `NewForm.lean` lines
  1684-1690, 2037, 2448-2464) of `ModData`, `U0`, `LocalRamG`, `G15RamG`, and (from
  `scratch/g0-mod-galois/part_galois.lean` line 164) of `G0Galois.G11Out`.
* §1. The named smaller Props (glue), each with its glue step and source.
* §2. Local field: `upperBreakFix_of_hilbertSerre` (proved): Glazer's break bound
  `G_{ℚ_p}^t ⊆ G_F` for `t > 4a²` when `e(F/ℚ_p) ≤ a!`, at the level of `LadicCond`'s
  `upperAbs`, from the transport `HilbertSerreLadic` of T20 + T21 and the kernel's D1 arithmetic
  `GlueConductor.upper_break_le`.
* §3. The reduction `g15RamG_of_pieces` (proved).

Leaves and glue targets are hypotheses (`def … : Prop`); no `sorry`, no `axiom`.
-/

noncomputable section

/-! ## §0. Verbatim copies -/

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

end G0Galois

namespace G0ModNewform

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar

section LocalRamSec

open LadicCond
open PkgI4 (GQp)

end LocalRamSec

end G0ModNewform

/-! ## §1. The smaller named Props -/

namespace G15Ram

open PkgI4 (GQp GaloisRep)
open LadicCond G0ModNewform

section Local

variable (p : ℕ) [Fact p.Prime]

variable {ℓ : ℕ} [Fact ℓ.Prime]

end Local

/-! ## §2. Local field: the break bound at the level of `upperAbs` (proved) -/

section Break

variable {p : ℕ} [Fact p.Prime] {F : Fld p}

end Break

/-! ## §2b. Positive upper groups are wild (proved) -/

section Wild

variable {p : ℕ} [Fact p.Prime]

end Wild

/-! ## §2d. Wild inertia fixes tame extensions (proved) -/

section Tame

variable {p : ℕ} [Fact p.Prime]

end Tame

/-! ## §2c. `HilbertSerreLadic` from T20 + T21 (proved by t-different) and a DVR model -/

section Bridge

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {p : ℕ} [Fact p.Prime]

end Bridge

/-! ## §2e. The DVR model over `ℤ_p`: the arithmetic conjuncts are automatic -/

section BridgeZp

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {p : ℕ} [Fact p.Prime]

end BridgeZp

/-! ## §2f. The `ℤ_p`-model `𝓞_F = integralClosure ℤ_p F` (proved): `LadicDVRModelZp` -/

section DVRModelSec

open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

section Model

variable (F : Fld p)

attribute [local instance] algZpF

variable [FiniteDimensional ℚ_[p] F]

end Model

section Model2

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] algZpF

omit [FiniteDimensional ℚ_[p] F] in
variable {F}

end Model2

section Galois

attribute [local instance] algZpF FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] torsionFree_OF

end Galois

section Filtration

attribute [local instance] algZpF

variable {F : Fld p} [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

end Filtration

section Card

attribute [local instance] algZpF

variable {F : Fld p} [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

end Card

section FinalZp

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {p : ℕ} [Fact p.Prime]

end FinalZp

end DVRModelSec

/-! ## §3. The reduction (proved) -/

section Reduction

end Reduction

end G15Ram

/-! ## §3' (local-data). Verbatim copies from scratch/g0-mod-galois/part_galois.lean -/

section G0GaloisSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ### Objects -/

end G0Galois

end

end G0GaloisSec

/-! ## §4 (local-data). `LocalData p r` on G8's `r`, from G7's data

The copied `LocalData p r` (§1) is a predicate on a bare `r : GaloisRep ℓ 2`. Here:

* `largePrimeData_iff`, `localData_large_iff` (proved): for `p > D`, `LocalData p r ↔ r` is
  trivial on wild inertia. So `LocalData` fails for any `r` wildly ramified at some `p > D`
  (e.g. `ψ ⊕ 1`, `ψ` a Dirichlet character of conductor `p²`), and cannot be proved for
  arbitrary `r`: it is a claim about the `r` that G8 builds.
* **Main result** `localData_of_g7` (proved): for `r` as in G8's output (`G0Galois.G8Out`) on
  `ρ = GlueDescent.rho Tm a β`, `LocalData p r` follows, at every prime `p`, from
  `G7Clauses β ε L` (clauses of G4/G7) and `LocalGlue p Tm a β L` (the Tate-module glue
  `TorsionFieldWild` at `p ≤ D`, `TateWildTrivialL` at `p > D`, and `BetaUpper` at `p = 2`).
  `g15RamG_of_g7` composes it with g15-ram's `g15RamG_of_localData`.
* On the way (all proved): `twistShape_of_g8` (`r` is scalar where `ρ` is), `betaTame_of_odd`,
  `betaOpen_of_isLocallyConstant`, `wild_fix_root` (wild inertia fixes `μ_n`, `p² ∤ n`),
  `galChar_decomp_wild`, `betaSqWild_of_chi`, `betaCharOn_of_cocycle`, `wild_fix_small_degree`
  (wild inertia fixes every `E` with `[E:ℚ_p] < p`), `exists_finGal_ramCard_le` (Galois closure
  with `e ≤ [E:ℚ_p]!`), `exists_local_field_le` (`[L_v:ℚ_p] ≤ [L:ℚ]`).
-/

namespace G15Ram

open PkgI4 (GQp GaloisRep GQ decomp)
open LadicCond G0ModNewform

section LocalDataSec

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### The characterization at `p > D` -/

/-- At `p > D` the local data say exactly that `r` is trivial on wild inertia: `F` is tame, so
`P_p ⊆ G_F` (`wildFixTame`), and `r = β = 1` on `G_F ∩ P_p`. Conversely take `F = ℚ_p`. -/
theorem largePrimeData_iff (r : GaloisRep ℓ 2) :
    LargePrimeData p r ↔ ∀ σ ∈ wildSet, r.restrictLocal p σ = 1 := by
  constructor
  · rintro ⟨F, β, hF, hpe, hsh, htm⟩ σ hσ
    have hfix : σ ∈ fixSet F := wildFixTame F hF hpe hσ
    have h1 := hsh σ ⟨hfix, hσ⟩
    rw [htm σ ⟨hfix, hσ⟩, Matrix.scalar_apply, Matrix.diagonal_one] at h1
    exact Units.ext h1
  · intro h
    have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
    have hcard : ramCard (⊥ : Fld p) 0 = 1 := by
      have h1 := one_le_ramCard hF 0
      have h2 : ramCard (⊥ : Fld p) 0 ≤ 1 := by
        unfold ramCard
        have hfin := (finite_restr hF (ramSet (⊥ : Fld p) 0)).to_subtype
        refine Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => ?_⟩
        apply Subtype.ext
        obtain ⟨σ, -, hσ⟩ := a.2
        obtain ⟨τ, -, hτ⟩ := b.2
        rw [← hσ, ← hτ]
        funext x
        obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
        simp only [restr, ← hq, AlgEquiv.commutes]
      omega
    refine ⟨⊥, fun _ => 1, hF, ?_, ?_, fun _ _ => rfl⟩
    · rw [hcard]; exact (Fact.out : p.Prime).not_dvd_one
    · intro σ hσ
      rw [h σ hσ.2, Matrix.scalar_apply, Matrix.diagonal_one]
      rfl

/-- **`LocalData` at `p > D`, characterized (proved).** -/
theorem localData_large_iff (r : GaloisRep ℓ 2) (hp : (ZInQ.heightD : ℝ) < p) :
    LocalData p r ↔ ∀ σ ∈ wildSet, r.restrictLocal p σ = 1 := by
  rw [← largePrimeData_iff]
  constructor
  · exact fun h => h.2 hp
  · exact fun h => ⟨fun hle => absurd hp (not_lt.mpr hle), fun _ => h⟩

/-! ### From `ρ` to `r` (linear algebra) -/

/-- If `e` intertwines `ρ` with `m ⊕ m` and `ρ(g)` is the scalar `c`, then `m(g)` is the scalar
`c`. -/
theorem mat_eq_scalar_of_intertwines {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {f : G → Module.End (PadicAlgCl ℓ) V} {m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)}
    {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines f m e) {g : G} {c : PadicAlgCl ℓ} (hg : f g = c • 1) :
    m g = Matrix.scalar (Fin 2) c := by
  have hv : ∀ x : Fin 2 → PadicAlgCl ℓ, (m g).mulVec x = c • x := by
    intro x
    have := h g (e.symm (x, x))
    rw [hg, LinearMap.smul_apply, Module.End.one_apply, map_smul,
      LinearEquiv.apply_symm_apply] at this
    exact (congrArg Prod.fst this).symm
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hv x, Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

/-! ### The smaller Props on G7's data at `p` -/

/-- **Glue on G4/G7 + R6 + D2 (N5 L719-727, L819-823; at `p > D` G3 + Néron–Ogg–Shafarevich,
N5 L848-851).** On `G_F ∩ P_p` (pushed to `G_ℚ` by `decomp`) the twisted Tate action
`a_σ μ_σ ∘ σ` (`a σ • Tm σ`) is the identity. Glazer: for `σ ∈ G_L` (`F ⊇ L_v`) the descent
datum has `a_σ μ_σ = 1`, so `a_σ Tm σ` is the Tate action of `A/L`; `A` is semistable over
`F ⊇ L_v(A[3])` (`A[5]` if `p = 3`) by Raynaud's criterion (R6, `PkgI2.RaynaudCriterion`), and
then wild inertia acts trivially on `V_ℓ` (D2, `PkgI2.D2_fixed_of_raynaud`); at `p > D`, `A` has
good reduction (G3) and inertia acts trivially (`PkgI2.inertiaTrivial_of_goodReduction`).
Only claimed for `p ≠ ℓ` (D2 and Néron–Ogg–Shafarevich are about `V_ℓ`, `ℓ ≠ p`; at `p = ℓ` it is
false in general); `g15RamG_of_g8` uses it only at `p ≠ ℓ`. -/
def TateWildTrivial {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, a (decomp p σ) • Tm (decomp p σ) = 1

/-- **Glue on G7's `β` (D3 + T16; N5 L823-844).** `β` is trivial on `G_{ℚ_p}^t ∩ G_F` for
`t > U`. At odd `p` it follows from `BetaTame` (`betaUpper_of_betaTame`); at `p = 2` from local
reciprocity with the upper numbering theorem (T16, `PkgI6.LocalReciprocityUpper`) and
`(U_F^{e+1})⁴ = U_F^{3e+1}` (D3, `GlueConductor.fourth_pow_mem`) applied to the character
`β|_{G_F}`, `ψ ≥ id`, and `max(4D², 3e) ≤ U₀` (`GlueConductor.max_le_U0`). -/
def BetaUpper (β : GQ → PadicAlgCl ℓ) (F : Fld p) (U : ℝ) : Prop :=
  ∀ t : ℝ, U < t → ∀ σ ∈ upperAbs p t ∩ fixSet F, β (decomp p σ) = 1

/-- **Glue on G7's `β` at odd `p` (N5 L835-838, L848-851).** `β` is trivial on `G_F ∩ P_p`.
Proved for odd `p` from `BetaCharOn`, `BetaSqWild`, `BetaOpen` (`betaTame_of_odd`). -/
def BetaTame (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β (decomp p σ) = 1

/-- **Glue on G7 (`∂β = ε` with `ε` inflated from `Gal(L/ℚ)` and normalized; N5 L664-700).**
On `G_F` (`F ⊇ L_v`, so `decomp(G_F) ⊆ G_L`) the cochain `β` is a character. -/
def BetaCharOn (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, β (decomp p (σ * τ)) = β (decomp p σ) * β (decomp p τ)

/-- **Glue on G7 (`β² = χ`, `χ` a Dirichlet character of level `N = ∏ lev q`, `lev p = p` for
odd `p`, so `χ` is tame at odd `p`; N5 L677-683; g0-mod-field `G7Data`).** `β² = 1` on
`G_F ∩ P_p`. -/
def BetaSqWild (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β (decomp p σ) ^ 2 = 1

/-- **Glue (local constancy of `β`, g0-mod-field `G7Data`: `IsLocallyConstant β`, and the
continuity of `decomp`).** `β ∘ decomp` is trivial on `G_{F'}` for some finite Galois `F'`. -/
def BetaOpen (β : GQ → PadicAlgCl ℓ) : Prop :=
  ∃ F' : Fld p, IsFinGal F' ∧ ∀ σ ∈ fixSet F', β (decomp p σ) = 1

/-! ### The reduction -/

/-- **`TwistShape` from G8's output (proved).** With `ρ = β⁻¹ a Tm` and `a Tm = 1` on
`G_F ∩ P_p`, `ρ = β⁻¹` there, and `r` is the same scalar (`e` intertwines `ρ` with `r ⊕ r`). -/
theorem twistShape_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r) {F : Fld p}
    (hT : TateWildTrivial Tm a F) :
    TwistShape p r F (fun σ => (β (decomp p σ))⁻¹) := by
  obtain ⟨-, e, he, -⟩ := hG8
  intro σ hσ
  have hρ : GlueDescent.rho Tm a β (decomp p σ) = (β (decomp p σ))⁻¹ • 1 := by
    unfold GlueDescent.rho
    rw [mul_smul, hT σ hσ]
  exact mat_eq_scalar_of_intertwines he hρ

theorem twistUpper_of_betaUpper {β : GQ → PadicAlgCl ℓ} {F : Fld p} {U : ℝ}
    (h : BetaUpper β F U) : TwistUpper p F (fun σ => (β (decomp p σ))⁻¹) U := by
  intro t ht σ hσ
  simp only [h t ht σ hσ, inv_one]

theorem twistTame_of_betaTame {β : GQ → PadicAlgCl ℓ} {F : Fld p}
    (h : BetaTame β F) : TwistTame p F (fun σ => (β (decomp p σ))⁻¹) := by
  intro σ hσ
  simp only [h σ hσ, inv_one]

/-- **`BetaUpper` from `BetaTame` (proved):** `G_{ℚ_p}^t ⊆ P_p` for `t > 0` (`upperWild`). -/
theorem betaUpper_of_betaTame {β : GQ → PadicAlgCl ℓ} {F : Fld p} {U : ℝ} (hU : 0 ≤ U)
    (h : BetaTame β F) : BetaUpper β F U := by
  intro t ht σ hσ
  exact h σ ⟨hσ.2, upperWild t (lt_of_le_of_lt hU ht) hσ.1⟩

/-- **Corrected form of `LocalData p r`: the local data of G7 at `p` (GLUE on G4/G7 + R6 + D2 +
D3 + T16; N5 L813-851).** A Prop on G7's data `(Tm, a, β)` instead of on the bare `r`: at
`p ≤ D` a finite Galois `F ⊆ ℚ̄_p` with `e(F/ℚ_p) ≤ (DG₀)!` (Glazer: the Galois closure of
`L_v(A[3])`, `A[5]` if `p = 3`, of degree `≤ (DG₀)!`) on which `TateWildTrivial` and
`BetaUpper` (bound `U₀`) hold; at `p > D` a tame finite Galois `F` (the Galois closure of `L_v`,
`[L_v:ℚ_p] ≤ D < p`) with `TateWildTrivial` and `BetaTame`. -/
def G7LocalData {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ F : Fld p, IsFinGal F ∧
      ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
      TateWildTrivial Tm a F ∧ BetaUpper β F U0) ∧
    ((ZInQ.heightD : ℝ) < p → ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
      TateWildTrivial Tm a F ∧ BetaTame β F)

/-- **`LocalData p r` for G8's `r` (proved).** For `r` as in G8's output on
`ρ = GlueDescent.rho Tm a β`, `G7LocalData p Tm a β` gives `LocalData p r`, with the local
twist `σ ↦ β(σ)⁻¹`. -/
theorem localData_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (h : G7LocalData (p := p) Tm a β) : LocalData p r := by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨F, hF, he, hT, hB⟩ := h.1 hp
    exact ⟨F, _, hF, he, twistShape_of_g8 hG8 hT, twistUpper_of_betaUpper hB⟩
  · obtain ⟨F, hF, he, hT, hB⟩ := h.2 hp
    exact ⟨F, _, hF, he, twistShape_of_g8 hG8 hT, twistTame_of_betaTame hB⟩

/-- **`G15RamG D u` from G8's outputs for `D.r5`, `D.r3` and G7's local data (proved).**
Composes `localData_of_g8` with g15-ram's `g15RamG_of_localData`. The G7/G8 data for `r₅` and
`r₃` may live on different models (`K₅`, `A₅`) and (`K₃`, `A₃`). -/
theorem g15RamG_of_g8 {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : ModData L A) (u : ℚ)
    {K₅ : Type} [Field K₅] [NumberField K₅] {A₅ : PkgI3.AbVar K₅}
    {Tm₅ : GQ → Module.End (PadicAlgCl 5) (G0Galois.Vb A₅ 5)} {a₅ β₅ : GQ → PadicAlgCl 5}
    (hG8₅ : G0Galois.G8Out A₅ 5 (GlueDescent.rho Tm₅ a₅ β₅) D.r5)
    {K₃ : Type} [Field K₃] [NumberField K₃] {A₃ : PkgI3.AbVar K₃}
    {Tm₃ : GQ → Module.End (PadicAlgCl 3) (G0Galois.Vb A₃ 3)} {a₃ β₃ : GQ → PadicAlgCl 3}
    (hG8₃ : G0Galois.G8Out A₃ 3 (GlueDescent.rho Tm₃ a₃ β₃) D.r3)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G7LocalData p ⟨hp⟩ 5 _ _ _ _ Tm₅ a₅ β₅)
    (h3 : G7LocalData (p := 5) Tm₃ a₃ β₃)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_localData D u (fun p hp hp5 => @localData_of_g8 p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ hG8₅
    (h5 p hp hp5)) (localData_of_g8 hG8₃ h3) h11₅ h11₃

/-! ### `BetaTame` at odd `p` (proved) -/

/-- A wild `σ` has `σ^{p^a}` fixing a given finite Galois `F'` for some `a`: the restriction
`s ∈ Gal(F'/ℚ_p)` has order `p^a m` with `p ∤ m`, and the wild `σ^{p^a}` has restriction of
order `m` prime to `p`, so it fixes `F'` (`fix_of_wild_pow`). -/
theorem exists_pow_fix_of_wild {σ : GQp p} (hσ : σ ∈ wildSet) {F' : Fld p} (hF' : IsFinGal F') :
    ∃ a : ℕ, σ ^ (p ^ a) ∈ fixSet F' := by
  haveI : FiniteDimensional ℚ_[p] F' := hF'.1
  haveI : Normal ℚ_[p] F' := hF'.2.to_normal
  set s := AlgEquiv.restrictNormalHom F' σ with hs
  have hm0 : 0 < orderOf s := orderOf_pos s
  obtain ⟨a, m, hpm, hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' p
    (Fact.out : p.Prime).ne_one
  refine ⟨a, ?_⟩
  have hm0' : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hdec; omega
  intro x hx
  have hsm : AlgEquiv.restrictNormalHom F' ((σ ^ (p ^ a)) ^ m) = 1 := by
    rw [map_pow, map_pow, ← hs, ← pow_mul, ← hdec, pow_orderOf_eq_one]
  have hfix : ((σ ^ (p ^ a)) ^ m) x = x :=
    (AlgEquiv.restrictNormal_eq_one_iff F' _).mp hsm x hx
  exact fix_of_wild_pow (wildSet_pow hσ _) hm0' hpm hfix

theorem fixSet_pow {F : Fld p} {σ : GQp p} (hσ : σ ∈ fixSet F) (k : ℕ) : σ ^ k ∈ fixSet F := by
  induction k with
  | zero => intro x _; rfl
  | succ k ih =>
    intro x hx
    rw [pow_succ, AlgEquiv.mul_apply, hσ x hx, ih x hx]

/-- **`BetaTame` at odd `p` (proved).** If `β` is a character on `G_F`, `β² = 1` on
`G_F ∩ P_p`, and `β ∘ decomp` dies on an open `G_{F'}`, then `β = 1` on `G_F ∩ P_p` for odd `p`:
`β(σ)^{p^a} = β(σ^{p^a}) = 1` with `σ^{p^a} ∈ G_{F'}`, and `β(σ)² = 1`, `gcd(p^a, 2) = 1`. -/
theorem betaTame_of_odd (hp2 : p ≠ 2) {β : GQ → PadicAlgCl ℓ} {F : Fld p}
    (hmul : BetaCharOn β F) (hsq : BetaSqWild β F) (hopen : BetaOpen (p := p) β) :
    BetaTame β F := by
  obtain ⟨F', hF', h1⟩ := hopen
  intro σ hσ
  obtain ⟨a, ha⟩ := exists_pow_fix_of_wild hσ.2 hF'
  have hpow : ∀ k : ℕ, β (decomp p (σ ^ (k + 1))) = β (decomp p σ) ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ σ (k + 1), hmul _ (fixSet_pow hσ.1 _) _ hσ.1, ih, ← pow_succ]
  have hpa : β (decomp p σ) ^ (p ^ a) = 1 := by
    have hpos : 0 < p ^ a := pow_pos (Fact.out : p.Prime).pos a
    obtain ⟨k, hk⟩ : ∃ k, p ^ a = k + 1 := ⟨p ^ a - 1, by omega⟩
    rw [hk, ← hpow k, ← hk]
    exact h1 _ ha
  have hcop : Nat.Coprime (p ^ a) 2 := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp2
  have := pow_gcd_eq_one.mpr ⟨hpa, hsq σ hσ⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this

/-- `β(1) = 1` for a nonzero `β` that is a character on `G_F`. -/
theorem beta_one_of_charOn {β : GQ → PadicAlgCl ℓ} {F : Fld p} (hm : BetaCharOn β F)
    (h0 : β 1 ≠ 0) : β 1 = 1 := by
  have h := hm 1 (fun _ _ => rfl) 1 (fun _ _ => rfl)
  rw [mul_one, map_one] at h
  have h' : β 1 * β 1 = β 1 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ h0 h'

/-- **`BetaOpen` from local constancy (proved).** If `β : G_ℚ → ℚ̄_ℓ` is locally constant
(g0-mod-field's `G7Data` has `IsLocallyConstant β` for the `ℂ^×`-valued `β`; any transport of
the values preserves it) and `β(1) = 1`, then `β ∘ decomp` is trivial on `G_{F'}` for a finite
Galois `F'`: `decomp` is continuous (Mathlib's `Field.absoluteGaloisGroup.map`), the fibre over
`1` is an open neighbourhood of `1`, so it contains the fixer of a finite `E`
(`krullTopology_mem_nhds_one_iff`), and of its normal closure `F'`. -/
theorem betaOpen_of_isLocallyConstant {β : GQ → PadicAlgCl ℓ} (hβ : IsLocallyConstant β)
    (h1 : β 1 = 1) : BetaOpen (p := p) β := by
  set S : Set (GQp p) := {σ | β (decomp p σ) = 1} with hSdef
  have hcont : Continuous (decomp p) :=
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous
  have hS : S ∈ nhds (1 : GQp p) := by
    have hopen : IsOpen S := (hβ.comp_continuous hcont).isOpen_fiber 1
    refine hopen.mem_nhds ?_
    show β (decomp p 1) = 1
    rw [map_one, h1]
  obtain ⟨E, hEfin, hE⟩ := (krullTopology_mem_nhds_one_iff ℚ_[p] (Kbar p) S).mp hS
  set F' := IntermediateField.normalClosure ℚ_[p] E (Kbar p) with hF'
  haveI : FiniteDimensional ℚ_[p] F' := normalClosure.is_finiteDimensional ℚ_[p] E (Kbar p)
  haveI : Normal ℚ_[p] F' := normalClosure.normal ℚ_[p] E (Kbar p)
  refine ⟨F', ⟨inferInstance, IsGalois.mk⟩, fun σ hσ => ?_⟩
  have hσE : σ ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hσ x (E.le_normalClosure hx)
  exact hE hσE

/-- **Corrected form at odd `p` (GLUE).** `G7LocalData` with the `β`-side replaced by
`BetaCharOn` and `BetaSqWild` on the same `F` (local constancy and `β(1) ≠ 0` are separate
hypotheses of `g7LocalData_of_odd`). -/
def G7LocalDataOdd {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ F : Fld p, IsFinGal F ∧
      ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
      TateWildTrivial Tm a F ∧ BetaCharOn β F ∧ BetaSqWild β F) ∧
    ((ZInQ.heightD : ℝ) < p → ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
      TateWildTrivial Tm a F ∧ BetaCharOn β F ∧ BetaSqWild β F)

/-- **`G7LocalData` at odd `p` (proved)** from `G7LocalDataOdd`, local constancy of `β` and
`β(1) ≠ 0` (`G0Galois.G7Out` has `∀ g, β g ≠ 0`). -/
theorem g7LocalData_of_odd (hp2 : p ≠ 2) {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a β : GQ → PadicAlgCl ℓ}
    (hβ : IsLocallyConstant β) (h0 : β 1 ≠ 0) (h : G7LocalDataOdd (p := p) Tm a β) :
    G7LocalData (p := p) Tm a β := by
  have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨F, hF, he, hT, hm, hs⟩ := h.1 hp
    have hopen := betaOpen_of_isLocallyConstant (p := p) hβ (beta_one_of_charOn hm h0)
    exact ⟨F, hF, he, hT, betaUpper_of_betaTame hU0 (betaTame_of_odd hp2 hm hs hopen)⟩
  · obtain ⟨F, hF, he, hT, hm, hs⟩ := h.2 hp
    have hopen := betaOpen_of_isLocallyConstant (p := p) hβ (beta_one_of_charOn hm h0)
    exact ⟨F, hF, he, hT, betaTame_of_odd hp2 hm hs hopen⟩

/-! ### `BetaSqWild` at odd `p` from `β² = χ` (proved)

Wild inertia fixes every root of unity of order `n` with `p² ∤ n` (`wild_fix_root`, norms only);
so the cyclotomic character mod `N`, and every Dirichlet character mod `N`, is trivial on
`decomp(P_p)` when `p² ∤ N` (`galChar_decomp_wild`); and `p² ∤ chiLevel T₋` for odd `p`
(`not_sq_dvd_chiLevel`). -/

theorem norm_eq_one_of_pow_eq_one {η : Kbar p} {n : ℕ} (hn : 0 < n) (h : η ^ n = 1) :
    ‖η‖ = 1 := by
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp this

theorem norm_sum_range_le_one {f : ℕ → Kbar p} (m : ℕ) (hf : ∀ k < m, ‖f k‖ ≤ 1) :
    ‖∑ k ∈ Finset.range m, f k‖ ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (max_le (ih fun k hk => hf k (by omega)) (hf m (by omega)))

theorem norm_pow_sub_one_le {η : Kbar p} (h1 : ‖η‖ = 1) (i : ℕ) : ‖η ^ i - 1‖ ≤ ‖η - 1‖ := by
  have he : η ^ i - 1 = (∑ k ∈ Finset.range i, η ^ k) * (η - 1) := (geom_sum_mul η i).symm
  rw [he, norm_mul]
  have hs : ‖∑ k ∈ Finset.range i, η ^ k‖ ≤ 1 :=
    norm_sum_range_le_one i fun k _ => by rw [norm_pow, h1, one_pow]
  calc ‖∑ k ∈ Finset.range i, η ^ k‖ * ‖η - 1‖ ≤ 1 * ‖η - 1‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ = ‖η - 1‖ := one_mul _

/-- A root of unity of order prime to `p` congruent to `1` is `1`. -/
theorem eq_one_of_pow_eq_one_of_norm_lt {η : Kbar p} {m : ℕ} (hm0 : 0 < m) (hpm : ¬ p ∣ m)
    (hη : η ^ m = 1) (hlt : ‖η - 1‖ < 1) : η = 1 := by
  by_contra hne
  have h1 : ‖η‖ = 1 := norm_eq_one_of_pow_eq_one hm0 hη
  have hsub : η - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hgeom : ∑ k ∈ Finset.range m, η ^ k = 0 := by
    have := geom_sum_mul η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right hsub
  have hm : (m : Kbar p) = ∑ k ∈ Finset.range m, (1 - η ^ k) := by
    rw [Finset.sum_sub_distrib, hgeom, sub_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have hlt' : ‖∑ k ∈ Finset.range m, (1 - η ^ k)‖ < 1 :=
    norm_sum_range_lt one_pos m fun k _ => by
      rw [norm_sub_rev]; exact lt_of_le_of_lt (norm_pow_sub_one_le h1 k) hlt
  rw [← hm, norm_natCast_kbar hpm] at hlt'
  exact lt_irrefl _ hlt'

/-- Wild inertia fixes roots of unity of order prime to `p`. -/
theorem wild_fix_prime_to_p {σ : GQp p} (hσ : σ ∈ wildSet) {ζ : Kbar p} {m : ℕ} (hm0 : 0 < m)
    (hpm : ¬ p ∣ m) (hζ : ζ ^ m = 1) : σ ζ = ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hm0.ne'] at hζ; exact zero_ne_one hζ
  set η := σ ζ * ζ⁻¹ with hη
  have hηm : η ^ m = 1 := by
    rw [hη, mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hlt : ‖η - 1‖ < 1 := by
    have he : η - 1 = (σ ζ - ζ) * ζ⁻¹ := by rw [hη, sub_mul, mul_inv_cancel₀ hζ0]
    rw [he, norm_mul, norm_inv]
    have hw := hσ ζ hζ0
    have hpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
    rw [mul_inv_lt_iff₀ hpos, one_mul]
    exact hw
  have := eq_one_of_pow_eq_one_of_norm_lt hm0 hpm hηm hlt
  rw [hη, mul_inv_eq_one₀ hζ0] at this
  exact this

/-- Wild inertia fixes the `p`-th roots of unity. -/
theorem wild_fix_p_root {σ : GQp p} (hσ : σ ∈ wildSet) {ζ : Kbar p} (hζ : ζ ^ p = 1) :
    σ ζ = ζ := by
  have hp := (Fact.out : p.Prime)
  by_contra hne
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hp.ne_zero] at hζ; exact zero_ne_one hζ
  have hζ1 : ζ ≠ 1 := by rintro rfl; exact hne (map_one σ)
  have h1ζ : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hp.pos hζ
  set η := σ ζ * ζ⁻¹ with hη
  have hηp : η ^ p = 1 := by
    rw [hη, mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hη1 : η ≠ 1 := by
    intro h; rw [hη, mul_inv_eq_one₀ hζ0] at h; exact hne h
  have h1η : ‖η‖ = 1 := norm_eq_one_of_pow_eq_one hp.pos hηp
  have hord : orderOf η = p := orderOf_eq_prime hηp hη1
  have hprim : IsPrimitiveRoot η p := by
    have := IsPrimitiveRoot.orderOf η
    rwa [hord] at this
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hζ
  have hx0 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
  have hw := hσ (ζ - 1) hx0
  have he : σ (ζ - 1) - (ζ - 1) = ζ * (η - 1) := by
    rw [map_sub, map_one, hη]; field_simp; ring
  rw [he, norm_mul, h1ζ, one_mul, ← hi] at hw
  exact lt_irrefl _ (lt_of_lt_of_le hw (norm_pow_sub_one_le h1η i))

/-- **Wild inertia fixes `μ_n` for `p² ∤ n` (proved).** -/
theorem wild_fix_root {σ : GQp p} (hσ : σ ∈ wildSet) {ζ : Kbar p} {n : ℕ} (hn0 : 0 < n)
    (hp2 : ¬ p ^ 2 ∣ n) (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  have hp := (Fact.out : p.Prime)
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hpm : ¬ p ∣ m := by
      rintro ⟨k, rfl⟩; exact hp2 ⟨k, by ring⟩
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by simp [h] at hn0
    have hζ0 : ζ ≠ 0 := by
      rintro rfl; rw [zero_pow hn0.ne'] at hζ; exact zero_ne_one hζ
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
    have hy : σ (ζ ^ p) = ζ ^ p :=
      wild_fix_prime_to_p hσ hm0 hpm (by rw [← pow_mul, hζ])
    have hz : σ (ζ ^ m) = ζ ^ m :=
      wild_fix_p_root hσ (by rw [← pow_mul, mul_comm, hζ])
    have hb : ((p.gcd m : ℕ) : ℤ) = p * p.gcdA m + m * p.gcdB m := Nat.gcd_eq_gcd_ab p m
    rw [hcop.gcd_eq_one, Nat.cast_one] at hb
    have hdec : ζ = (ζ ^ p) ^ (p.gcdA m) * (ζ ^ m) ^ (p.gcdB m) := by
      rw [← zpow_natCast, ← zpow_natCast (ζ) m, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, ← hb,
        zpow_one]
    rw [hdec, map_mul, map_zpow₀, map_zpow₀, hy, hz]
  · exact wild_fix_prime_to_p hσ hn0 hpn hζ

/-- The embedding `ℚ̄ → ℚ̄_p` that `decomp` uses. -/
def embP : PkgI4.Qbar →+* Kbar p :=
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom

/-- `embP ∘ decomp σ = σ ∘ embP` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
theorem decomp_spec (σ : GQp p) (x : PkgI4.Qbar) : embP (decomp p σ x) = σ (embP x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

theorem decomp_fix_root {σ : GQp p} (hσ : σ ∈ wildSet) {x : PkgI4.Qbar} {n : ℕ} (hn0 : 0 < n)
    (hp2 : ¬ p ^ 2 ∣ n) (hx : x ^ n = 1) : decomp p σ x = x := by
  apply (embP (p := p)).injective
  rw [decomp_spec]
  exact wild_fix_root hσ hn0 hp2 (by rw [← map_pow, hx, map_one])

/-- **The cyclotomic character mod `N` is trivial on `decomp(P_p)` when `p² ∤ N` (proved).** -/
theorem cyc_decomp_wild {N : ℕ} [NeZero N] (hp2 : ¬ p ^ 2 ∣ N) {σ : GQp p}
    (hσ : σ ∈ wildSet) : GlueDescent.B2Q.cyc N (decomp p σ) = 1 := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  by_cases hN1 : N = 1
  · subst hN1; exact Subsingleton.elim _ _
  haveI : Fact (1 < N) := ⟨by omega⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  apply Units.ext
  have hu := modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
    (GlueDescent.B2Q.toRingAut (decomp p σ)) (c := 1) (fun t ht => by
      rw [ZMod.val_one, pow_one]
      have htN : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ N = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N t).mp ht, Units.val_one]
      exact decomp_fix_root hσ hN0 hp2 htN)
  have hc : GlueDescent.B2Q.cyc N (decomp p σ) = modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
      (GlueDescent.B2Q.toRingAut (decomp p σ)) := rfl
  rw [hc, Units.val_one]
  exact hu.symm

/-- **Every Dirichlet character mod `N`, as a Galois character, is trivial on `decomp(P_p)`
when `p² ∤ N` (proved).** -/
theorem galChar_decomp_wild {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hp2 : ¬ p ^ 2 ∣ N) {σ : GQp p} (hσ : σ ∈ wildSet) :
    GlueDescent.B2Q.galChar χ (decomp p σ) = 1 := by
  change χ.toUnitHom (GlueDescent.B2Q.cyc N (decomp p σ)) = 1
  rw [cyc_decomp_wild hp2 hσ, map_one]

/-- **`p² ∤ chiLevel T₋` for odd `p` (proved)**, `T₋` a finite set of primes (`lev q = q` for odd
`q`, `lev 2 = 4`). -/
theorem not_sq_dvd_chiLevel (hp2 : p ≠ 2) {Tm : Finset ℕ} (hTm : ∀ q ∈ Tm, q.Prime) :
    ¬ p ^ 2 ∣ GlueDescent.chiLevel Tm := by
  have hp := (Fact.out : p.Prime)
  intro h
  have hpp : p ∣ GlueDescent.chiLevel Tm := (dvd_pow_self p two_ne_zero).trans h
  have hmem : p ∈ Tm := by
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpp
    have hqp := hTm q hq
    unfold GlueDescent.lev at hpq
    split_ifs at hpq with h2
    · subst h2
      have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hpq)
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this) hp2
    · rwa [(Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq]
  unfold GlueDescent.chiLevel at h
  rw [← Finset.mul_prod_erase Tm _ hmem] at h
  have hlev : GlueDescent.lev p = p := by unfold GlueDescent.lev; rw [if_neg hp2]
  rw [hlev, pow_two] at h
  have hdvd := Nat.dvd_of_mul_dvd_mul_left hp.pos h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  have hqp := hTm q (Finset.mem_of_mem_erase hq)
  have hqne := Finset.ne_of_mem_erase hq
  unfold GlueDescent.lev at hpq
  split_ifs at hpq with h2
  · subst h2
    have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hpq)
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this) hp2
  · exact hqne ((Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq).symm

/-- **`BetaSqWild` at odd `p` (proved)** from `β² = ι ∘ χ` on `G_F` (`χ` a Dirichlet character
mod `N = chiLevel T₋` for a set `T₋` of primes, as in g0-mod-field's `G7Data`; `ι` the transport
of values `ℂ^× → ℚ̄_ℓ^×`). -/
theorem betaSqWild_of_chi (hp2 : p ≠ 2) {β : GQ → PadicAlgCl ℓ} {F : Fld p} {Tm : Finset ℕ}
    (hTm : ∀ q ∈ Tm, q.Prime) [NeZero (GlueDescent.chiLevel Tm)]
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tm)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ)
    (hsq : ∀ σ ∈ fixSet F, β (decomp p σ) ^ 2 = (ι (GlueDescent.B2Q.galChar χ (decomp p σ)) :
      PadicAlgCl ℓ)) :
    BetaSqWild β F := by
  intro σ hσ
  rw [hsq σ hσ.1, galChar_decomp_wild χ (not_sq_dvd_chiLevel hp2 hTm) hσ.2, map_one,
    Units.val_one]

/-! ### `BetaCharOn` from `∂β = ε` (proved) -/

/-- `decomp(G_F) ⊆ G_L` when `F ⊇ embP(L)` (`L ⊆ ℚ̄`; `F ⊇ L_v` for the place `v` of `embP`). -/
theorem decomp_fix_of_le {L : IntermediateField ℚ PkgI4.Qbar} {F : Fld p}
    (hLF : ∀ x ∈ L, embP x ∈ F) {σ : GQp p} (hσ : σ ∈ fixSet F) :
    ∀ x ∈ L, decomp p σ x = x := by
  intro x hx
  apply (embP (p := p)).injective
  rw [decomp_spec]
  exact hσ _ (hLF x hx)

/-- **`BetaCharOn` from G7's `∂β = ε` (proved).** If `β g β h = ε(g,h) β(gh)` (a clause of
`G0Galois.G7Out`), `ε = 1` on `G_L × G_L` (`ε` is inflated from `Gal(L/ℚ)` and normalized,
g0-mod-field `DescentDatum`), and `F ⊇ embP(L)`, then `β` is a character on `G_F`. -/
theorem betaCharOn_of_cocycle {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) {L : IntermediateField ℚ PkgI4.Qbar}
    (hε : ∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)
    {F : Fld p} (hLF : ∀ x ∈ L, embP x ∈ F) : BetaCharOn β F := by
  intro σ hσ τ hτ
  rw [hβ, hε _ _ (decomp_fix_of_le hLF hσ) (decomp_fix_of_le hLF hτ), one_mul, map_mul]

/-! ### Wild inertia fixes fields of degree `< p` (proved) -/

/-- **Wild inertia fixes every finite `E ⊆ ℚ̄_p` with `[E:ℚ_p] < p` (proved).** For `x ∈ E`
and wild `σ`, `σ^{p^a}` fixes the Galois closure of `ℚ_p(x)` (`exists_pow_fix_of_wild`), so the
`σ`-orbit of `x` has `p`-power size; its elements are distinct roots of the minimal polynomial
of `x`, of degree `≤ [E:ℚ_p] < p`; so the orbit is `{x}`. (This replaces "the Galois closure of
`L_v` is tame" at `p > D`.) -/
theorem wild_fix_small_degree {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E < p) : wildSet ⊆ fixSet E := by
  classical
  intro σ hσ x hx
  let F := FiniteGaloisIntermediateField.adjoin ℚ_[p] ({x} : Set (Kbar p))
  have hF : IsFinGal F.toIntermediateField := ⟨inferInstance, inferInstance⟩
  have hxF : x ∈ F.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin ℚ_[p] {x} rfl
  obtain ⟨a, ha⟩ := exists_pow_fix_of_wild hσ hF
  have hper : Function.IsPeriodicPt σ (p ^ a) x := by
    unfold Function.IsPeriodicPt Function.IsFixedPt
    rw [← AlgEquiv.coe_pow]
    exact ha x hxF
  set k := Function.minimalPeriod σ x with hk
  have hkdvd : k ∣ p ^ a := hper.minimalPeriod_dvd
  have hkpos : 0 < k := hper.minimalPeriod_pos (pow_pos (Fact.out : p.Prime).pos a)
  -- the orbit lies in the roots of the minimal polynomial
  have hint : IsIntegral ℚ_[p] x := IsIntegral.of_finite ℚ_[p] (⟨x, hx⟩ : E) |>.map E.val
  set P := minpoly ℚ_[p] x with hP
  have hroot : ∀ i : ℕ, (σ^[i] x) ∈ P.aroots (Kbar p) := by
    intro i
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [← AlgEquiv.coe_pow, Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval,
      map_zero]
  have hcard : k ≤ P.natDegree := by
    have hinj : Set.InjOn (fun i => σ^[i] x) (Finset.range k : Set ℕ) := by
      intro i hi j hj hij
      have := Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := x)
      exact this (by simpa using hi) (by simpa using hj) hij
    have hsub : (Finset.range k).image (fun i => σ^[i] x) ⊆ (P.aroots (Kbar p)).toFinset := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact Multiset.mem_toFinset.mpr (hroot i)
    calc k = ((Finset.range k).image (fun i => σ^[i] x)).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ (P.aroots (Kbar p)).toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (P.aroots (Kbar p)) := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := by
          rw [Polynomial.aroots_def]
          exact (Polynomial.card_roots' _).trans Polynomial.natDegree_map_le
  have hdeg : P.natDegree ≤ Module.finrank ℚ_[p] E := by
    have h1 : (minpoly ℚ_[p] (⟨x, hx⟩ : E)).natDegree ≤ Module.finrank ℚ_[p] E :=
      minpoly.natDegree_le _
    rwa [IntermediateField.minpoly_eq] at h1
  have hkp : k < p := lt_of_le_of_lt (hcard.trans hdeg) hE
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hkdvd
  have hb0 : b = 0 := by
    by_contra hb0
    have : p ≤ p ^ b := Nat.le_self_pow hb0 p
    omega
  rw [hb0, pow_zero] at hb
  have h1 : Function.IsPeriodicPt σ 1 x := by
    rw [← hb]; exact Function.isPeriodicPt_minimalPeriod σ x
  exact h1

/-- **`LocalData` at `p > D` from a field of degree `< p` (proved).** If `E ⊆ ℚ̄_p` has
`[E:ℚ_p] < p` (Glazer: `E = L_v`, `[L_v:ℚ_p] ≤ D < p`) and `a·Tm` and `β` are trivial on
`G_E ∩ P_p`, then `LocalData p r` holds at `p > D` for G8's `r`. -/
theorem localData_large_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (hp : (ZInQ.heightD : ℝ) < p) {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E < p) (hT : TateWildTrivial Tm a E) (hB : BetaTame β E) :
    LocalData p r := by
  rw [localData_large_iff r hp]
  intro σ hσ
  have hfix := wild_fix_small_degree hE hσ
  have h1 : ((r.restrictLocal p σ : GL (Fin 2) (PadicAlgCl ℓ)) :
      Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = Matrix.scalar (Fin 2) ((β (decomp p σ))⁻¹) :=
    twistShape_of_g8 hG8 hT σ ⟨hfix, hσ⟩
  rw [hB σ ⟨hfix, hσ⟩, inv_one, Matrix.scalar_apply, Matrix.diagonal_one] at h1
  exact Units.ext h1

/-! ### The Galois closure and `e ≤ [E:ℚ_p]!` (proved) -/

/-- `e(F/ℚ_p) ≤ [F:ℚ_p]` for finite Galois `F`. -/
theorem ramCard_zero_le_finrank {F : Fld p} (hF : IsFinGal F) :
    ramCard F 0 ≤ Module.finrank ℚ_[p] F := by
  haveI : FiniteDimensional ℚ_[p] F := hF.1
  haveI : IsGalois ℚ_[p] F := hF.2
  haveI : Normal ℚ_[p] F := hF.2.to_normal
  rw [ramCard_zero_eq F hF, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_le_card_group _

/-- **A finite `E ⊆ ℚ̄_p` lies in a finite Galois `F` with `e(F/ℚ_p) ≤ n!` when
`[E:ℚ_p] ≤ n` (proved).** `F` = the splitting field in `ℚ̄_p` of the minimal polynomial `f` of a
primitive element of `E`; `Gal(F/ℚ_p)` acts faithfully on the `≤ deg f ≤ n` roots
(as in `GlueRepo.Numerics.splitting_degree_le`). -/
theorem exists_finGal_ramCard_le {E : Fld p} [FiniteDimensional ℚ_[p] E] {n : ℕ}
    (hE : Module.finrank ℚ_[p] E ≤ n) :
    ∃ F : Fld p, IsFinGal F ∧ E ≤ F ∧ ramCard F 0 ≤ n.factorial := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[p] E
  set a : Kbar p := (α : Kbar p) with ha
  have hint : IsIntegral ℚ_[p] a := (IsIntegral.of_finite ℚ_[p] α).map E.val
  set f := minpoly ℚ_[p] a with hf
  have hf0 : f ≠ 0 := minpoly.ne_zero hint
  have hsplit : (f.map (algebraMap ℚ_[p] (Kbar p))).Splits := IsAlgClosed.splits _
  set F : Fld p := IntermediateField.adjoin ℚ_[p] (f.rootSet (Kbar p)) with hFdef
  haveI : Polynomial.IsSplittingField ℚ_[p] F f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  haveI : FiniteDimensional ℚ_[p] F := Polynomial.IsSplittingField.finiteDimensional F f
  have hsep : f.Separable := minpoly.irreducible hint |>.separable
  haveI : IsGalois ℚ_[p] F := IsGalois.of_separable_splitting_field hsep
  have hdeg : f.natDegree ≤ n := by
    have h1 : (minpoly ℚ_[p] α).natDegree ≤ Module.finrank ℚ_[p] E := minpoly.natDegree_le _
    rw [IntermediateField.minpoly_eq] at h1
    exact h1.trans hE
  have hfin : Module.finrank ℚ_[p] F ≤ n.factorial := by
    rw [(Polynomial.IsSplittingField.algEquiv F f).toLinearEquiv.finrank_eq,
      ← Polynomial.Gal.card_of_separable hsep]
    have : Fact ((f.map (algebraMap ℚ_[p] f.SplittingField)).Splits) :=
      ⟨Polynomial.SplittingField.splits f⟩
    calc Nat.card f.Gal ≤ Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) :=
          Nat.card_le_card_of_injective _ (Polynomial.Gal.galActionHom_injective f _)
      _ = (Nat.card (f.rootSet f.SplittingField)).factorial := Nat.card_perm
      _ ≤ n.factorial := by
          apply Nat.factorial_le
          rw [Nat.card_coe_set_eq]
          exact (Polynomial.ncard_rootSet_le f _).trans hdeg
  have hEF : E ≤ F := by
    intro y hy
    have h1 : (⟨y, hy⟩ : E) ∈ IntermediateField.adjoin ℚ_[p] {α} := by rw [hα]; trivial
    have h2 : y ∈ (IntermediateField.adjoin ℚ_[p] {α}).map E.val :=
      ⟨⟨y, hy⟩, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    have hroot : a ∈ f.rootSet (Kbar p) := by
      rw [Polynomial.mem_rootSet]
      exact ⟨hf0, minpoly.aeval ℚ_[p] a⟩
    have hle : IntermediateField.adjoin ℚ_[p] {E.val α} ≤ F :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.subset_adjoin _ _ hroot)
    exact hle h2
  have hFG : IsFinGal F := ⟨inferInstance, inferInstance⟩
  exact ⟨F, hFG, hEF, (ramCard_zero_le_finrank hFG).trans hfin⟩

theorem tateWildTrivial_mono {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a : GQ → PadicAlgCl ℓ} {E F : Fld p} (hEF : E ≤ F)
    (h : TateWildTrivial Tm a E) : TateWildTrivial Tm a F :=
  fun σ hσ => h σ ⟨fun x hx => hσ.1 x (hEF hx), hσ.2⟩

theorem betaUpper_mono {β : GQ → PadicAlgCl ℓ} {E F : Fld p} {U : ℝ} (hEF : E ≤ F)
    (h : BetaUpper β E U) : BetaUpper β F U :=
  fun t ht σ hσ => h t ht σ ⟨hσ.1, fun x hx => hσ.2 x (hEF hx)⟩

/-- **`LocalData` at `p ≤ D` from a field of degree `≤ DG₀` (proved).** If `E ⊆ ℚ̄_p` has
`[E:ℚ_p] ≤ DG₀` (Glazer: `E = L_v(A[3])`, `A[5]` if `p = 3`) and `TateWildTrivial`, `BetaUpper`
hold on `E`, then `LocalData p r` holds at `p ≤ D` for G8's `r` (`F` = the Galois closure,
`exists_finGal_ramCard_le`). -/
theorem localData_small_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0)
    (hT : TateWildTrivial Tm a E) (hB : BetaUpper β E U0) : SmallPrimeData p r := by
  obtain ⟨F, hF, hEF, he⟩ := exists_finGal_ramCard_le hE
  exact ⟨F, _, hF, he, twistShape_of_g8 hG8 (tateWildTrivial_mono hEF hT),
    twistUpper_of_betaUpper (betaUpper_mono hEF hB)⟩

/-! ### Assembly at odd `p` (proved) -/

/-- **`LocalData p r` at odd `p` for G8's `r`, from G7's clauses and one named glue Prop
(proved).** Hypotheses:
* G8's output for `ρ = GlueDescent.rho Tm a β` (`G0Galois.G8Out`, proved by g0-mod-galois `g8`);
* clauses of G7 (`G0Galois.G7Out`: `∂β = ε`, `β ≠ 0`; g0-mod-field `G7Data`/`DescentDatum`,
  with the values moved to `ℚ̄_ℓ` by `ι`: `β` locally constant, `β² = ι ∘ χ` for a Dirichlet
  character `χ` mod `chiLevel T₋`, `T₋` a set of primes, and `ε = 1` on `G_L × G_L`, as `ε` is
  inflated from `Gal(L/ℚ)` with `ε(1,1) = 1`);
* at `p ≤ D`: a finite `E ⊆ ℚ̄_p` containing `embP(L)` with `[E:ℚ_p] ≤ DG₀` (Glazer:
  `E = L_v(A[3])`, `A[5]` if `p = 3`) and `TateWildTrivial` on `E`;
* at `p > D`: a finite `E ⊇ embP(L)` with `[E:ℚ_p] < p` (Glazer: `E = L_v`, degree `≤ D`) and
  `TateWildTrivial` on `E`.
The `β`-side (`BetaUpper`, `BetaTame`) is fully proved from these clauses. -/
theorem localData_of_g7_odd (hp2 : p ≠ 2) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (hβε : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (hβlc : IsLocallyConstant β)
    {Tmin : Finset ℕ} (hTm : ∀ q ∈ Tmin, q.Prime) [NeZero (GlueDescent.chiLevel Tmin)]
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tmin)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ)
    (hsq : ∀ g, β g ^ 2 = (ι (GlueDescent.B2Q.galChar χ g) : PadicAlgCl ℓ))
    {L : IntermediateField ℚ PkgI4.Qbar}
    (hε : ∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)
    (hsmall : (p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧
      (∀ x ∈ L, embP x ∈ E) ∧ Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0 ∧
      TateWildTrivial Tm a E)
    (hlarge : (ZInQ.heightD : ℝ) < p → ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧
      (∀ x ∈ L, embP x ∈ E) ∧ Module.finrank ℚ_[p] E < p ∧ TateWildTrivial Tm a E) :
    LocalData p r := by
  have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
  have htame : ∀ E : Fld p, (∀ x ∈ L, embP x ∈ E) → BetaTame β E := by
    intro E hLE
    have hm := betaCharOn_of_cocycle (p := p) hβε hε hLE
    have hs := betaSqWild_of_chi hp2 (F := E) hTm χ ι (fun σ _ => hsq _)
    have ho := betaOpen_of_isLocallyConstant (p := p) hβlc (beta_one_of_charOn hm (hβ0 1))
    exact betaTame_of_odd hp2 hm hs ho
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨E, hEfd, hLE, hdeg, hT⟩ := hsmall hp
    exact localData_small_of_g8 hG8 hdeg hT (betaUpper_of_betaTame hU0 (htame E hLE))
  · obtain ⟨E, hEfd, hLE, hdeg, hT⟩ := hlarge hp
    exact (localData_large_of_g8 hG8 hp hdeg hT (htame E hLE)).2 hp

/-! ### `p > D` from `[L:ℚ] ≤ D` (proved) -/

/-- **`[ℚ_p · embP(L) : ℚ_p] ≤ [L:ℚ]` (proved).** For a number field `L ⊆ ℚ̄`, the field
`E = ℚ_p(embP α)` (`α` a primitive element of `L`) contains `embP(L)` and has degree
`≤ deg minpoly_ℚ α = [L:ℚ]` (the minimal polynomial over `ℚ_p` divides the image of the one
over `ℚ`). This is `[L_v:ℚ_p] ≤ [L:ℚ]`. -/
theorem exists_local_field_le (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] :
    ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ (∀ x ∈ L, embP x ∈ E) ∧
      Module.finrank ℚ_[p] E ≤ Module.finrank ℚ L := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  set αQ : PkgI4.Qbar := (α : PkgI4.Qbar) with hαQ
  have hintQ : IsIntegral ℚ αQ := (IsIntegral.of_finite ℚ α).map L.val
  set g := minpoly ℚ αQ with hg
  set a : Kbar p := embP αQ with ha
  have hroot : Polynomial.aeval a (g.map (algebraMap ℚ ℚ_[p])) = 0 := by
    rw [Polynomial.aeval_map_algebraMap, ha]
    have : Polynomial.aeval (embP (p := p) αQ) g = embP (Polynomial.aeval αQ g) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
      congr 1
      exact RingHom.ext_rat _ _
    rw [this, minpoly.aeval, map_zero]
  have hg0 : g.map (algebraMap ℚ ℚ_[p]) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℚ_[p]).injective).mpr (minpoly.ne_zero hintQ)
  have hint : IsIntegral ℚ_[p] a :=
    ⟨_, (minpoly.monic hintQ).map _, by
      rw [← Polynomial.aeval_def]; exact hroot⟩
  set E : Fld p := IntermediateField.adjoin ℚ_[p] {a} with hE
  haveI : FiniteDimensional ℚ_[p] E := IntermediateField.adjoin.finiteDimensional hint
  refine ⟨E, inferInstance, ?_, ?_⟩
  · intro x hx
    have h1 : (⟨x, hx⟩ : L) ∈ IntermediateField.adjoin ℚ {α} := by rw [hα]; trivial
    have h2 : x ∈ (IntermediateField.adjoin ℚ {α}).map L.val := ⟨⟨x, hx⟩, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    have h3 : embP (p := p) x ∈
        (IntermediateField.adjoin ℚ {L.val α}).map (embP (p := p)).toRatAlgHom :=
      ⟨x, h2, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h3
    have hle : IntermediateField.adjoin ℚ {(embP (p := p)).toRatAlgHom (L.val α)} ≤
        E.restrictScalars ℚ := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.mem_adjoin_simple_self ℚ_[p] a
    exact hle h3
  · rw [IntermediateField.adjoin.finrank hint]
    have hdvd : minpoly ℚ_[p] a ∣ g.map (algebraMap ℚ ℚ_[p]) := minpoly.dvd ℚ_[p] a hroot
    have h1 := Polynomial.natDegree_le_of_dvd hdvd hg0
    rw [Polynomial.natDegree_map] at h1
    have h2 : g.natDegree = Module.finrank ℚ L := by
      have h3 : (minpoly ℚ α).natDegree ≤ Module.finrank ℚ L := minpoly.natDegree_le _
      have h4 : Module.finrank ℚ L ≤ (minpoly ℚ α).natDegree := by
        have := IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ α)
        rw [hα, IntermediateField.finrank_top'] at this
        omega
      rw [hg, ← IntermediateField.minpoly_eq]
      omega
    omega

/-- **Glue on G3 + Néron–Ogg–Shafarevich + the descent datum on `G_L` (N5 L848-851).** At
`p > D`: on wild inertia elements whose image in `G_ℚ` lies in `G_L`, `a_σ μ_σ ∘ σ` is the
identity (it is the Tate action of `A/L`, which has good reduction at `v ∤ 3`, so inertia acts
trivially, `PkgI2.inertiaTrivial_of_goodReduction`). Only claimed for `p ≠ ℓ`. -/
def TateWildTrivialL {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∀ σ ∈ wildSet, (∀ x ∈ L, decomp p σ x = x) → a (decomp p σ) • Tm (decomp p σ) = 1

theorem tateWildTrivial_of_L {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a : GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (h : TateWildTrivialL (p := p) Tm a L) {E : Fld p}
    (hLE : ∀ x ∈ L, embP x ∈ E) : TateWildTrivial Tm a E :=
  fun σ hσ => h σ hσ.2 (decomp_fix_of_le hLE hσ.1)

/-- **`LocalData p r` at `p > D` for G8's `r` (proved)** from G7's clauses (as in
`localData_of_g7_odd`), `[L:ℚ] ≤ D` (G4's output `G4Out`), and `TateWildTrivialL`. -/
theorem localData_of_g7_large {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (hβε : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (hβlc : IsLocallyConstant β)
    {Tmin : Finset ℕ} (hTm : ∀ q ∈ Tmin, q.Prime) [NeZero (GlueDescent.chiLevel Tmin)]
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tmin)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ)
    (hsq : ∀ g, β g ^ 2 = (ι (GlueDescent.B2Q.galChar χ g) : PadicAlgCl ℓ))
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L]
    (hε : ∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (hp : (ZInQ.heightD : ℝ) < p)
    (hT : TateWildTrivialL (p := p) Tm a L) :
    LocalData p r := by
  have hpD : ZInQ.heightD < p := by exact_mod_cast hp
  have hp2 : p ≠ 2 := by
    have := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
    omega
  obtain ⟨E, hEfd, hLE, hdeg⟩ := exists_local_field_le (p := p) L
  refine localData_of_g7_odd hp2 hG8 hβε hβ0 hβlc hTm χ ι hsq hε
    (fun hle => absurd hp (not_lt.mpr hle)) (fun _ => ⟨E, hEfd, hLE, ?_, ?_⟩)
  · omega
  · exact tateWildTrivial_of_L hT hLE

/-! ### Final form: the glue on `L_v = ℚ_p · embP(L)` and the assembly for every `p` -/

/-- `L_v = ℚ_p · embP(L) ⊆ ℚ̄_p`, the completion of `L ⊆ ℚ̄` at the place of `embP`. -/
def Lv (L : IntermediateField ℚ PkgI4.Qbar) : Fld p :=
  IntermediateField.adjoin ℚ_[p] (embP '' (L : Set PkgI4.Qbar))

theorem embP_mem_Lv {L : IntermediateField ℚ PkgI4.Qbar} {x : PkgI4.Qbar} (hx : x ∈ L) :
    embP x ∈ Lv (p := p) L :=
  IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩

theorem Lv_le {L : IntermediateField ℚ PkgI4.Qbar} {E : Fld p} (h : ∀ x ∈ L, embP x ∈ E) :
    Lv (p := p) L ≤ E :=
  IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

/-- `[L_v:ℚ_p] ≤ [L:ℚ]` (proved, from `exists_local_field_le`). -/
theorem Lv_fin (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] :
    FiniteDimensional ℚ_[p] (Lv (p := p) L) ∧
      Module.finrank ℚ_[p] (Lv (p := p) L) ≤ Module.finrank ℚ L := by
  obtain ⟨E, hEfd, hLE, hdeg⟩ := exists_local_field_le (p := p) L
  have hle := Lv_le (p := p) hLE
  have hfd : FiniteDimensional ℚ_[p] (Lv (p := p) L) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  exact ⟨hfd, (IntermediateField.finrank_le_of_le_right hle).trans hdeg⟩

/-- **The clauses of G4/G7 used here (GLUE: transport between g0-mod-field's `ℂ^×`-valued data
and g0-mod-galois's `ℚ̄_ℓ`-valued `G7Out`).** `L ⊆ ℚ̄` (G4's Hom field) is finite with
`[L:ℚ] ≤ D` (`G4Out`); `∂β = ε` and `β ≠ 0` (`G0Galois.G7Out`); `β` locally constant and
`β² = ι ∘ χ` for a Dirichlet character `χ` mod `chiLevel T₋`, `T₋` a set of primes (`G7Data`, with
`ι : ℂ^× → ℚ̄_ℓ^×` the transport of values); `ε = 1` on `G_L × G_L` (`DescentDatum`: `ε` inflated
from `Gal(L/ℚ)` with `ε(1,1) = 1`). Note: g0-mod-field's interface `G7Data` (and so `AfterG7`)
does not carry `[L:ℚ] ≤ D`; `G4Out` does. -/
def G7Clauses (β : GQ → PadicAlgCl ℓ) (ε : GQ → GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  FiniteDimensional ℚ L ∧ Module.finrank ℚ L ≤ ZInQ.heightD ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧ IsLocallyConstant β ∧
  (∃ (Tmin : Finset ℕ) (_ : ∀ q ∈ Tmin, q.Prime) (_ : NeZero (GlueDescent.chiLevel Tmin))
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tmin)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ),
    ∀ g, β g ^ 2 = (ι (GlueDescent.B2Q.galChar χ g) : PadicAlgCl ℓ)) ∧
  (∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)

/-- **Glue on G4/G7 + R6 + D2 + the torsion field (N5 L813-818).** There is a finite
`E ⊇ L_v` with `[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` on which `a·Tm` is trivial on wild inertia. Glazer:
`E = L_v(A[3])` (`A[5]` if `p = 3`), `[E:L_v] ≤ |GL₄(𝔽₅)| = G₀ = 116064000000`
(`A[m] ≅ (ℤ/m)⁴`, `PkgI2.TorsionStructure`); `A` is semistable over `E` (R6,
`PkgI2.RaynaudCriterion`), so wild inertia acts trivially on `V_ℓ(A)` (D2,
`PkgI2.D2_fixed_of_raynaud`), and `a_σ μ_σ = 1` on `G_L` (`DescentDatum`). Only for `p ≠ ℓ`. -/
def TorsionFieldWild {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    TateWildTrivial Tm a E

/-- **The local glue at `p`.** `TorsionFieldWild` at `p ≤ D`, `TateWildTrivialL` at `p > D`, and
at `p = 2` the bound for `β` on `L_v` (`BetaUpper`, glue on T16 + D3 + Herbrand's `ψ ≥ id`,
N5 L826-844; `β|_{G_{L_v}}` is a character with `β⁴ = 1` on units since the 2-part of `χ` has
conductor `4`). -/
def LocalGlue {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → TorsionFieldWild (p := p) Tm a L) ∧
  ((ZInQ.heightD : ℝ) < p → TateWildTrivialL (p := p) Tm a L) ∧
  (p = 2 → BetaUpper β (Lv (p := p) L) U0)

/-- **`LocalData p r` for G8's `r`, every prime `p` (proved)** from G8's output, the G4/G7
clauses (`G7Clauses`) and the local glue (`LocalGlue`). -/
theorem localData_of_g7 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2} {L : IntermediateField ℚ PkgI4.Qbar}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r) (hC : G7Clauses β ε L)
    (hG : LocalGlue (p := p) Tm a β L) : LocalData p r := by
  obtain ⟨hLfd, hLD, hβε, hβ0, hβlc, ⟨Tmin, hTm, hNZ, χ, ι, hsq⟩, hε⟩ := hC
  obtain ⟨hLvfd, hLvdeg⟩ := Lv_fin (p := p) L
  have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  -- the field of `TorsionFieldWild` has degree `≤ D G₀`
  have hsmall : (p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧
      (∀ x ∈ L, embP x ∈ E) ∧ Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0 ∧
      TateWildTrivial Tm a E := by
    intro hp
    obtain ⟨E, hEfd, hLvE, hdeg, hT⟩ := hG.1 hp
    refine ⟨E, hEfd, fun x hx => hLvE (embP_mem_Lv hx), ?_, hT⟩
    calc Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) := hdeg
      _ ≤ ZInQ.heightG0 * ZInQ.heightD := Nat.mul_le_mul_left _ (hLvdeg.trans hLD)
      _ = ZInQ.heightD * ZInQ.heightG0 := Nat.mul_comm _ _
  by_cases hp2 : p = 2
  · subst hp2
    have hle : ((2 : ℕ) : ℝ) ≤ (ZInQ.heightD : ℝ) := by exact_mod_cast (by omega : 2 ≤ ZInQ.heightD)
    refine ⟨fun hp => ?_, fun hp => absurd hp (not_lt.mpr hle)⟩
    obtain ⟨E, hEfd, hLvE, hdeg, hT⟩ := hG.1 hp
    obtain ⟨E', hE'fd, hLE', hdeg', hT'⟩ := hsmall hp
    exact localData_small_of_g8 hG8 hdeg' hT' (betaUpper_mono (Lv_le hLE') (hG.2.2 rfl))
  · refine localData_of_g7_odd hp2 hG8 hβε hβ0 hβlc hTm χ ι hsq hε hsmall (fun hp => ?_)
    have hpD : ZInQ.heightD < p := by exact_mod_cast hp
    exact ⟨Lv (p := p) L, hLvfd, fun x hx => embP_mem_Lv hx, by omega,
      tateWildTrivial_of_L (hG.2.1 hp) (fun x hx => embP_mem_Lv hx)⟩

/-- **`G15RamG D u` from G8's outputs, the G4/G7 clauses and the local glue (proved).**
The G7/G8 data for `r₅` and `r₃` (models `A₅/K₅`, `A₃/K₃`, Hom fields `L₅`, `L₃`). -/
theorem g15RamG_of_g7 {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : ModData L A) (u : ℚ)
    {K₅ : Type} [Field K₅] [NumberField K₅] {A₅ : PkgI3.AbVar K₅}
    {Tm₅ : GQ → Module.End (PadicAlgCl 5) (G0Galois.Vb A₅ 5)} {a₅ β₅ : GQ → PadicAlgCl 5}
    {ε₅ : GQ → GQ → PadicAlgCl 5} {L₅ : IntermediateField ℚ PkgI4.Qbar}
    (hG8₅ : G0Galois.G8Out A₅ 5 (GlueDescent.rho Tm₅ a₅ β₅) D.r5) (hC₅ : G7Clauses β₅ ε₅ L₅)
    (hG₅ : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalGlue p ⟨hp⟩ 5 _ _ _ _ Tm₅ a₅ β₅ L₅)
    {K₃ : Type} [Field K₃] [NumberField K₃] {A₃ : PkgI3.AbVar K₃}
    {Tm₃ : GQ → Module.End (PadicAlgCl 3) (G0Galois.Vb A₃ 3)} {a₃ β₃ : GQ → PadicAlgCl 3}
    {ε₃ : GQ → GQ → PadicAlgCl 3} {L₃ : IntermediateField ℚ PkgI4.Qbar}
    (hG8₃ : G0Galois.G8Out A₃ 3 (GlueDescent.rho Tm₃ a₃ β₃) D.r3) (hC₃ : G7Clauses β₃ ε₃ L₃)
    (hG₃ : LocalGlue (p := 5) Tm₃ a₃ β₃ L₃)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_localData D u
    (fun p hp hp5 => @localData_of_g7 p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ _ _ hG8₅ hC₅ (hG₅ p hp hp5))
    (localData_of_g7 hG8₃ hC₃ hG₃) h11₅ h11₃

/-! ### Non-vacuity (proved) -/

/-- **`G7LocalData` is satisfiable (proved):** it holds for trivial data (`Tm = 1`, `a = 1`,
`β = 1`, `F = ℚ_p`), so it is not contradictory. -/
theorem g7LocalData_triv {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V] :
    G7LocalData (p := p) (fun _ => (1 : Module.End (PadicAlgCl ℓ) V)) (fun _ => 1)
      (fun _ => 1) := by
  have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
  have he : ramCard (⊥ : Fld p) 0 = 1 := by
    have h1 := one_le_ramCard hF 0
    have h2 := ramCard_zero_le_finrank hF
    rw [IntermediateField.finrank_bot] at h2
    omega
  have hT : TateWildTrivial (p := p) (fun _ => (1 : Module.End (PadicAlgCl ℓ) V))
      (fun _ => (1 : PadicAlgCl ℓ)) ⊥ := fun _ _ => one_smul _ _
  refine ⟨fun _ => ⟨⊥, hF, ?_, hT, fun _ _ _ _ => rfl⟩,
    fun _ => ⟨⊥, hF, ?_, hT, fun _ _ => rfl⟩⟩
  · rw [he]; exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  · rw [he]; exact (Nat.Prime.one_lt Fact.out).ne' ∘ Nat.dvd_one.mp

/-- **`G7Clauses` and `LocalGlue` are satisfiable (proved):** both hold for trivial data
(`β = 1`, `ε = 1`, `L = ℚ`, `Tm = 1`, `a = 1`, `χ = 1`, `ι = 1`). -/
theorem g7Clauses_triv : G7Clauses (ℓ := ℓ) (fun _ => 1) (fun _ _ => 1) ⊥ := by
  have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  refine ⟨inferInstance, ?_, fun _ _ => by simp, fun _ => one_ne_zero,
    IsLocallyConstant.const _, ⟨∅, fun q hq => absurd hq (Finset.notMem_empty q),
      ⟨by simp [GlueDescent.chiLevel]⟩, 1, 1, fun _ => by simp⟩, fun _ _ _ _ => rfl⟩
  rw [IntermediateField.finrank_bot]
  omega

theorem localGlue_triv {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] :
    LocalGlue (p := p) (fun _ => (1 : Module.End (PadicAlgCl ℓ) V)) (fun _ => 1) (fun _ => 1) L := by
  obtain ⟨hfd, -⟩ := Lv_fin (p := p) L
  have hG0 : 1 ≤ ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num
  refine ⟨fun _ => ⟨Lv (p := p) L, hfd, le_rfl, ?_, fun _ _ => one_smul _ _⟩,
    fun _ _ _ _ => one_smul _ _, fun _ _ _ _ _ => rfl⟩
  exact Nat.le_mul_of_pos_left _ hG0

end LocalDataSec

end G15Ram



/-! ## §5' (local-glue). Verbatim copy from scratch/g0-mod-galois/part_galois.lean lines 40-58 -/

noncomputable section

namespace G0Galois


end G0Galois

end

/-! ## §6 (local-glue). `LocalGlue p Tm a β L` on G7's data

`LocalGlue p Tm a β L` (§4 above, copied verbatim from scratch/local-data) is a predicate on
arbitrary operators `Tm`, scalars `a`, `β` and a field `L`. Here:

* `not_localGlue_zero` (proved): it fails for `Tm = 0` at every `p > D`, so it is not a closed
  theorem; it is a claim about the data that G7 builds.
* **Main result** `localGlue_of_g7` (proved): for G7's data (`G0Galois.G7Out`, with the clauses
  `G7Clauses`), `LocalGlue p Tm a β L` follows from three named Props about the abelian surface
  `A/K` and the kernel field, with no `Tm` or `a` left:
  - `KerWild K β L`: wild inertia elements of `G_L` killed by `β` lie in `G_K` (G7Data's kernel
    field clause `G_{L'} = G_L ∩ ker β`, transported);
  - `TateWildK p A ℓ` (`p ≥ 7`): wild inertia at `p` in `G_K` acts trivially on `V_ℓ(A)`;
  - `TateWildKE p A ℓ β L` (`p ≤ 5`): the same on `G_E` for a field `E ⊇ L_v` of degree
    `≤ G₀[L_v:ℚ_p]`, on which also `β` kills wild inertia;
  and `BetaUpper` at `p = 2` (unchanged).
* `tate_eq_one_of_torsFix` (proved): `σ` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` if it fixes every
  `ℓⁿ`-torsion point; so `TateWildK`, `TateWildKE` reduce to statements on torsion points
  (`TorsFixWild`, `TorsFixWildE`), the form in which Raynaud's criterion (R6) and D2 are stated.
-/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GaloisRep GQ decomp)
open LadicCond G0ModNewform
open CategoryTheory MonObj

section LocalGlueSec

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### `LocalGlue` is not a closed statement -/

/-- **`LocalGlue` fails for `Tm = 0` at every `p > D` (proved).** `σ = 1` is wild and fixes
`L`, and `1 • 0 ≠ 1` on the nonzero space `ℚ̄_ℓ`. -/
theorem not_localGlue_zero (hp : (ZInQ.heightD : ℝ) < p) (L : IntermediateField ℚ PkgI4.Qbar) :
    ¬ LocalGlue (p := p) (fun _ => (0 : Module.End (PadicAlgCl ℓ) (PadicAlgCl ℓ))) (fun _ => 1)
      (fun _ => 1) L := by
  intro h
  have h1 := h.2.1 hp 1 one_mem_wildSet (fun x _ => by rw [map_one]; rfl)
  have h2 := LinearMap.congr_fun h1 1
  simp at h2

/-! ### Fixing `L` and fixing `L_v` -/

/-- If `decomp σ` fixes `L`, then `σ` fixes `L_v = ℚ_p · embP(L)` (proved). -/
theorem fixSet_Lv_of_fix {L : IntermediateField ℚ PkgI4.Qbar} {σ : GQp p}
    (h : ∀ x ∈ L, decomp p σ x = x) : σ ∈ fixSet (Lv (p := p) L) := by
  have hle : Lv (p := p) L ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    apply Lv_le
    intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have hσ : σ ∈ MulAction.stabilizer (GQp p) (embP (p := p) x) := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, ← decomp_spec, h x hx]
    have := (Subgroup.zpowers_le.mpr hσ) hf
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
  intro y hy
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hy) σ (Subgroup.mem_zpowers σ)

/-- `σ` fixes `L_v` iff `decomp σ` fixes `L` (proved). -/
theorem fixSet_Lv_iff {L : IntermediateField ℚ PkgI4.Qbar} {σ : GQp p} :
    σ ∈ fixSet (Lv (p := p) L) ↔ ∀ x ∈ L, decomp p σ x = x :=
  ⟨fun h => decomp_fix_of_le (fun _ hx => embP_mem_Lv hx) h, fixSet_Lv_of_fix⟩

/-! ### `β` on wild inertia of `G_L` at odd `p` -/

/-- **`β` kills wild inertia of `G_L` at odd `p` (proved)** from G7's clauses: on `G_{L_v}`,
`β` is a character (`∂β = ε`, `ε = 1` on `G_L²`) with `β² = χ` tame (`χ` mod `chiLevel T₋`) and
open kernel (local constancy), so `betaTame_of_odd` applies with `F = L_v`. -/
theorem beta_wild_of_clauses (hp2 : p ≠ 2) {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L) {σ : GQp p} (hσ : σ ∈ wildSet)
    (hfix : ∀ x ∈ L, decomp p σ x = x) : β (decomp p σ) = 1 := by
  obtain ⟨-, -, hβε, hβ0, hβlc, ⟨Tmin, hTm, hNZ, χ, ιc, hsq⟩, hε⟩ := hC
  have hm : BetaCharOn β (Lv (p := p) L) :=
    betaCharOn_of_cocycle hβε hε (fun _ hx => embP_mem_Lv hx)
  have hs : BetaSqWild β (Lv (p := p) L) :=
    betaSqWild_of_chi hp2 hTm χ ιc (fun _ _ => hsq _)
  have hopen := betaOpen_of_isLocallyConstant (p := p) hβlc (beta_one_of_charOn hm (hβ0 1))
  exact betaTame_of_odd hp2 hm hs hopen σ ⟨fixSet_Lv_of_fix hfix, hσ⟩

/-! ### The smaller named Props -/

/-- **Glue: G7Data's kernel field clause, transported (N5 L702-716; g0-mod-field `G7Data`,
clause `σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`).** Every `g ∈ G_L` with `β(g) = 1` lies in `G_K`
(the image of `resQ K`), for the model field `K = L'` of `G0Galois.G7Out`. Notes: (i) `resQ K`
is taken along the embedding `K ↪ ℚ̄` that Mathlib's `Field.absoluteGaloisGroup.map` chooses;
`L'` is Galois over `ℚ`, so `G_{L'}` is normal and does not depend on that embedding; (ii) the
`ℚ̄_ℓ`-valued `β` here is `ι ∘ β_ℂ` (F5 of local-data), so `β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1` needs `ι`
injective on the roots of unity, which a transport `ℂ^× → ℚ̄_ℓ^×` can be chosen to be. -/
def KerWild (K : Type) [Field K] [NumberField K] (β : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∀ g : GQ, (∀ x ∈ L, g x = x) → β g = 1 → g ∈ (G0Galois.resQ K).range

/-- **Glue on R6 (`PkgI2.RaynaudCriterion`), D2 (`PkgI2.D2_fixed_of_raynaud`) and I2-Tors
(`PkgI2.TorsionStructure`) at `p ≥ 7`, `p ≠ ℓ` (N5 L813-818).** Wild inertia at `p` (at the place
of `embP`) inside `G_K` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)`. Proof plan: `m = 3` (`m = 4` if
`p = 13`); `|GL₄(ℤ/m)|` is prime to `p`, so a wild `σ' ∈ G_K` (whose action on the finite group
`A[m] ≅ (ℤ/m)⁴` has `p`-power order) fixes `A[m]`; over `K(A[m])` Raynaud gives `(σ'-1)² = 0` on
`A[ℓⁿ]`, and D2 gives `σ'` fixes `A[ℓⁿ]`; `tate_eq_one_of_torsFix`. Only true for `p ≠ ℓ`.
(Equivalently: for `p > 2g + 1` inertia acts tamely on `V_ℓ`, Grothendieck, SGA 7 I, Exp. IX;
locator UNVERIFIED.) -/
def TateWildK {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K,
    G0Galois.resQ K σ' = decomp p σ → G0Galois.tate A ℓ σ' = 1

/-- **Glue at `p ∈ {2, 3, 5}`, `p ≠ ℓ` (N5 L813-818, L826-833), on R6, D2, I2-Tors and the
descent of `A` to `L`.** There is a finite `E ⊇ L_v` with `[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` such that
every wild `σ` fixing `E` has `β(σ) = 1` and acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` through `G_K`.
Glazer: `A = (A_L)_{L'}` with `A_L` over `L`; `E = L_v'(A_L[3])` (`A_L[5]` if `p = 3`), where at
`p = 2` `L_v'/L_v` (degree `≤ 4`) kills `β` on wild inertia (`β|G_{L_v}` has order `≤ 4` on
inertia since the `2`-part of `χ` has conductor `4`; an unramified twist removes the rest; at odd
`p`, `L_v' = L_v` by `beta_wild_of_clauses`); `[E:L_v] ≤ 4·|GL₄(𝔽₃)| ≤ G₀`, resp.
`|GL₄(𝔽₅)| = G₀`. Raynaud and D2 on `A_L/E`. Not provable from `A/K` alone at these primes:
`|GL₄(ℤ/m)|` is divisible by `2`, `3` and `5` for every `m ≥ 3`. -/
def TateWildKE {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet E ∩ wildSet, β (decomp p σ) = 1 ∧
      ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
        G0Galois.tate A ℓ σ' = 1

/-! ### The reduction -/

/-- On a wild `σ` with `decomp σ ∈ G_L`, `β(decomp σ) = 1`, `a·Tm` is the Tate action through
`G_K` (proved, from `G7Out` and `KerWild`). -/
theorem aTm_eq_one_of_kerWild {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hK : KerWild K β L) {g : GQ} (hfix : ∀ x ∈ L, g x = x) (hβ : β g = 1)
    (htate : ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = g →
      G0Galois.tate A ℓ σ' = 1) :
    a g • Tm g = 1 := by
  obtain ⟨σ', rfl⟩ := hK g hfix hβ
  obtain ⟨hT, ha, -⟩ := h7.2.2.2.2.2.2.1 σ'
  rw [hT, ha, one_smul, htate σ' rfl]

/-- **`LocalGlue` on G7's data (proved).** For `Tm, a, β` as in `G0Galois.G7Out` with the
clauses `G7Clauses`, `LocalGlue p Tm a β L` follows from `KerWild` (all `p`), `TateWildK` at
`p ≥ 7`, `TateWildKE` at `p ≤ 5`, and `BetaUpper` at `p = 2`. At `p ≥ 7`, `p ≤ D`, the field of
`TorsionFieldWild` is `L_v` itself. -/
theorem localGlue_of_g7 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hW : 7 ≤ p → TateWildK (p := p) A ℓ) (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L)
    (hB : p = 2 → BetaUpper β (Lv (p := p) L) U0) :
    LocalGlue (p := p) Tm a β L := by
  have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  have hpp : p.Prime := Fact.out
  have h7le : ¬ p ≤ 5 → 7 ≤ p := by
    intro h
    by_contra h'
    have : p = 6 := by omega
    exact absurd (this ▸ hpp) (by norm_num)
  -- at `p ≥ 7`: wild `σ` with `decomp σ ∈ G_L` has `a·Tm = 1`
  have hbig : 7 ≤ p → ∀ σ ∈ wildSet (p := p), (∀ x ∈ L, decomp p σ x = x) →
      a (decomp p σ) • Tm (decomp p σ) = 1 := by
    intro h7p σ hσ hfix
    have hp2 : p ≠ 2 := by omega
    exact aTm_eq_one_of_kerWild h7 hK hfix (beta_wild_of_clauses hp2 hC hσ hfix)
      (hW h7p σ hσ)
  refine ⟨fun hpD => ?_, fun hpD => ?_, hB⟩
  · by_cases h5 : p ≤ 5
    · obtain ⟨E, hEfd, hLvE, hdeg, hEw⟩ := hE h5
      refine ⟨E, hEfd, hLvE, hdeg, fun σ hσ => ?_⟩
      have hfix := decomp_fix_of_le (fun _ hx => hLvE (embP_mem_Lv hx)) hσ.1
      exact aTm_eq_one_of_kerWild h7 hK hfix (hEw σ hσ).1 (hEw σ hσ).2
    · have : FiniteDimensional ℚ L := hC.1
      obtain ⟨hfd, -⟩ := Lv_fin (p := p) L
      have hG0 : 1 ≤ ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num
      refine ⟨Lv (p := p) L, hfd, le_rfl, Nat.le_mul_of_pos_left _ hG0, fun σ hσ => ?_⟩
      exact hbig (h7le h5) σ hσ.2 (fixSet_Lv_iff.mp hσ.1)
  · have hpD' : ZInQ.heightD < p := by exact_mod_cast hpD
    exact fun σ hσ hfix => hbig (by omega) σ hσ hfix

/-! ### From torsion points to `V_ℓ` -/

/-- **`σ` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` if it fixes every `ℓⁿ`-torsion point (proved).**
`T_ℓ(A)` is the group of compatible sequences `(xₙ)` with `xₙ ∈ A(K̄)[ℓⁿ]`
(`PkgI3.Tate.pow_smul_eq_zero`), and `σ` acts termwise. -/
theorem tate_eq_one_of_torsFix {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Field.absoluteGaloisGroup K)
    (h : ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ P = P) :
    G0Galois.tate A ℓ σ = 1 := by
  have hT : A.galT (ℓ := ℓ) σ = LinearMap.id := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    have hx : (ℓ ^ n) • x.1 n = 0 := PkgI3.Tate.pow_smul_eq_zero x.2 n
    have hP : (Additive.toMul (x.1 n)) ^ (ℓ ^ n) = 1 := by
      rw [← toMul_nsmul, hx]; rfl
    change Additive.ofMul (A.galAct σ (Additive.toMul (x.1 n))) = x.1 n
    rw [h n _ hP]; rfl
  have hR : A.galRep ℓ σ = LinearMap.id := by
    change (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ] = LinearMap.id
    rw [hT, LinearMap.baseChange_id]
  change (A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) = LinearMap.id
  rw [hR, LinearMap.baseChange_id]

/-- **Glue on R6 + D2 + I2-Tors, on torsion points (`p ≥ 7`, `p ≠ ℓ`; N5 L813-818).** Wild
inertia at `p` inside `G_K` fixes every `ℓⁿ`-torsion point of `A(K̄)`. This is the form of
`PkgI2.D2_fixed_of_raynaud`; what remains is the bridge from the number field `K` with the place
of `embP` (`resQ`, `decomp`, `wildSet`) to the valuation-ring setting of PkgI2 (a DVR `O ⊆ K(A[m])`
and a valuation ring `w` of `K̄` over it), the base change of `A` to `K(A[m])`, and the
`p`-power order of a wild `σ'` on the finite set `A[m]` (see `TateWildK`). -/
def TorsFixWild {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K,
    G0Galois.resQ K σ' = decomp p σ →
      ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P

theorem tateWildK_of_torsFixWild {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    (h : TorsFixWild (p := p) A ℓ) : TateWildK (p := p) A ℓ :=
  fun σ hσ σ' hσ' => tate_eq_one_of_torsFix A ℓ σ' (h σ hσ σ' hσ')

/-- **Glue at `p ∈ {2, 3, 5}` on torsion points** (as `TateWildKE`, with "acts trivially on
`V_ℓ`" replaced by "fixes every `ℓⁿ`-torsion point"). -/
def TorsFixWildE {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet E ∩ wildSet, β (decomp p σ) = 1 ∧
      ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
        ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P

theorem tateWildKE_of_torsFixWildE {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {β : GQ → PadicAlgCl ℓ} {L : IntermediateField ℚ PkgI4.Qbar}
    (h : TorsFixWildE (p := p) A ℓ β L) : TateWildKE (p := p) A ℓ β L := by
  obtain ⟨E, hEfd, hLvE, hdeg, hw⟩ := h
  exact ⟨E, hEfd, hLvE, hdeg, fun σ hσ =>
    ⟨(hw σ hσ).1, fun σ' hσ' => tate_eq_one_of_torsFix A ℓ σ' ((hw σ hσ).2 σ' hσ')⟩⟩

/-- **Glue at `p ∈ {3, 5}`, `p ≠ ℓ` (as `TorsFixWildE` without the `β` clause, which is
automatic at odd `p`: `torsFixWildE_of_odd`).** Some finite `E ⊇ L_v` with
`[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` has every wild `σ ∈ G_E` fixing `A(K̄)[ℓⁿ]` through `G_K`. Glazer:
`E = L_v(A_L[5])` (`p = 3`), `L_v(A_L[3])` (`p = 5`), for the model `A_L` over `L`; R6 and D2. -/
def TorsFixWildOdd {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet E ∩ wildSet, ∀ σ' : Field.absoluteGaloisGroup K,
      G0Galois.resQ K σ' = decomp p σ →
        ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P

/-- At odd `p`, `TorsFixWildOdd` and G7's clauses give `TorsFixWildE` (proved). -/
theorem torsFixWildE_of_odd (hp2 : p ≠ 2) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L)
    (h : TorsFixWildOdd (p := p) A ℓ L) : TorsFixWildE (p := p) A ℓ β L := by
  obtain ⟨E, hEfd, hLvE, hdeg, hw⟩ := h
  exact ⟨E, hEfd, hLvE, hdeg, fun σ hσ => ⟨beta_wild_of_clauses hp2 hC hσ.2
    (decomp_fix_of_le (fun _ hx => hLvE (embP_mem_Lv hx)) hσ.1), hw σ hσ⟩⟩

/-! ### `BetaUpper` at `p = 2` without T16 (proved from a degree-`4` twist field) -/

/-- **Glue at `p = 2` (N5 L826-844; replaces T16 + D3 + Herbrand).** Some finite `M ⊇ L_v` with
`[M:L_v] ≤ 4` has `β = 1` on wild inertia of `G_M`. Proof plan: on `G_{L_v}`, `β` is a character
(`betaCharOn_of_cocycle`) and `β⁴ = χ²` is unramified at `2` (the `2`-part of `χ` is the
character mod `4`, of order `2`; the odd parts are unramified at `2`); an unramified `η` with
`η⁴ = β⁴` exists (`G_{L_v}/I` is procyclic and `β⁴` has finite order), and `M` is the kernel
field of `β η⁻¹`, of order dividing `4`. On wild inertia `η = 1`. -/
def BetaTwist2 (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ M : Fld p, FiniteDimensional ℚ_[p] M ∧ Lv (p := p) L ≤ M ∧
    Module.finrank ℚ_[p] M ≤ 4 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet M ∩ wildSet, β (decomp p σ) = 1

/-- **`BetaUpper` from `BetaTwist2` and G7's clauses (proved), with no class field theory.**
`[M:ℚ_p] ≤ 4D ≤ DG₀`; its Galois closure `F` has `e(F) ≤ (DG₀)!` (`exists_finGal_ramCard_le`), so
`G_{ℚ_p}^t ⊆ G_F ⊆ G_M` for `t > U₀ = 4(DG₀)²` (`UpperBreakFix`, proved from T20 + T21 and
`ladicDVRModelZp`), and `G_{ℚ_p}^t` is wild (`upperWild`). -/
theorem betaUpper_of_twist {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L)
    (h : BetaTwist2 (p := p) β L) : BetaUpper β (Lv (p := p) L) U0 := by
  haveI : FiniteDimensional ℚ L := hC.1
  obtain ⟨M, hMfd, hLvM, hdeg, hM⟩ := h
  obtain ⟨-, hLv⟩ := Lv_fin (p := p) L
  have hG0 : 4 ≤ ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num
  have hMn : Module.finrank ℚ_[p] M ≤ ZInQ.heightD * ZInQ.heightG0 := by
    calc Module.finrank ℚ_[p] M ≤ 4 * Module.finrank ℚ_[p] (Lv (p := p) L) := hdeg
      _ ≤ ZInQ.heightG0 * ZInQ.heightD := Nat.mul_le_mul hG0 (hLv.trans hC.2.1)
      _ = ZInQ.heightD * ZInQ.heightG0 := Nat.mul_comm _ _
  obtain ⟨F, hF, hMF, he⟩ := exists_finGal_ramCard_le hMn
  have ha : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
    Nat.mul_pos GlueDescent.heightD_pos (by unfold ZInQ.heightG0; norm_num)
  have hUB : UpperBreakFix p :=
    upperBreakFix_of_hilbertSerre (hilbertSerre_of_model (ladicDVRModel_of_Zp ladicDVRModelZp))
  have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
  intro t ht σ hσ
  have hfix : σ ∈ fixSet F := hUB F hF _ ha he t (by unfold U0 at ht; exact ht) hσ.1
  have hwild : σ ∈ wildSet := upperWild (p := p) t (by linarith) hσ.1
  exact hM σ ⟨fun x hx => hfix x (hMF hx), hwild⟩

/-- **`LocalGlue` on G7's data with `BetaTwist2` at `p = 2` (proved)**: as `localGlue_of_g7`,
with `BetaUpper` replaced by the smaller `BetaTwist2` (`betaUpper_of_twist`). -/
theorem localGlue_of_g7_twist {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hW : 7 ≤ p → TateWildK (p := p) A ℓ) (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L)
    (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_g7 h7 hC hK hW hE (fun h => betaUpper_of_twist hC (hB h))

end LocalGlueSec

end G15Ram


/-! ## §7 (local-glue). `TorsFixWild` at `p ≥ 7` from Raynaud's criterion and I2-Tors

`torsFixWild_of_raynaud` (proved): `TorsFixWild` at `p ≥ 7`, `p ≠ ℓ`, follows from
* `WildIter`: a wild `σ'` has `p`-power period on each point of `A(K̄)` (proved in §7b, `wildIter`);
* `TorsGL A m` for `m = 3, 7`: `A(K̄)[m] ≅ (ℤ/m)⁴` as groups (the instance of the leaf I2-Tors,
  `torsGL_of_leaf`);
* `RaynaudPlace A m` for `m = 3` (`p ≠ 13`), `m = 7` (`p = 13`): a wild `σ'` fixing `A(K̄)[m]`
  satisfies `(σ' - 1)² = 0` on
  `A(K̄)[ℓⁿ]` (the instance of the leaf R6 at the place of `embP`; bridge glue).
The algebra in between is proved: `|GL₄(𝔽₃)| = 2⁹·3⁶·5·13` and `13 ∤ |GL₄(𝔽₇)|`, so the action of
a wild `σ'` on `A[m]` has order prime to `p` and `p`-power, hence is trivial
(`iterate_card_GL_fix`); then `(σ'-1)² = 0` and a `p`-power period force `σ' = 1` on
`A[ℓⁿ]` (`fixed_of_unipSq_of_iterate'`, the core of D2). -/

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj

section TorsSec

/-- **An additive structure of `S ≅ (ℤ/q)ⁿ` bounds the period (proved).** If `φ : G →* G` is
injective, maps the multiplicatively closed `S` into itself, and `S ≅ (ℤ/q)ⁿ` as groups, then
`φ^[N] = id` on `S`, `N = |GLₙ(𝔽_q)|`. -/
theorem iterate_card_GL_fix {G : Type*} [Group G] (φ : G →* G) (hinj : Function.Injective φ)
    (S : Set G) (hS : ∀ x ∈ S, φ x ∈ S) (hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (q : ℕ) [Fact q.Prime] (n : ℕ) (e : S ≃ (Fin n → ZMod q))
    (he : ∀ (x y : S) (h : x.1 * y.1 ∈ S), e ⟨x.1 * y.1, h⟩ = e x + e y) :
    ∀ x ∈ S, φ^[Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod q))] x = x := by
  set φS : S → S := fun x => ⟨φ x, hS x x.2⟩ with hφS
  set f : (Fin n → ZMod q) → (Fin n → ZMod q) := fun v => e (φS (e.symm v)) with hf
  have hadd : ∀ a b, f (a + b) = f a + f b := by
    intro a b
    set x := e.symm a
    set y := e.symm b
    have hxy : e.symm (a + b) = ⟨x.1 * y.1, hSmul _ x.2 _ y.2⟩ := by
      apply e.injective
      rw [Equiv.apply_symm_apply, he x y, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hφxy : φS ⟨x.1 * y.1, hSmul _ x.2 _ y.2⟩ =
        ⟨(φS x).1 * (φS y).1, hSmul _ (φS x).2 _ (φS y).2⟩ := by
      apply Subtype.ext
      simp [hφS, map_mul]
    simp only [hf]
    rw [hxy, hφxy, he]
  have hfinj : Function.Injective f := by
    intro a b h
    have h1 := e.injective h
    have h2 : φ (e.symm a).1 = φ (e.symm b).1 := congrArg Subtype.val h1
    exact e.symm.injective (Subtype.ext (hinj h2))
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  let fA : (Fin n → ZMod q) →+ (Fin n → ZMod q) := AddMonoidHom.mk' f hadd
  let fL := fA.toZModLinearMap q
  let fLE := LinearEquiv.ofBijective fL hfbij
  let u : LinearMap.GeneralLinearGroup (ZMod q) (Fin n → ZMod q) :=
    ⟨fLE.toLinearMap, fLE.symm.toLinearMap, by ext v; simp, by ext v; simp⟩
  set N := Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod q)) with hN
  have hcard : Nat.card (LinearMap.GeneralLinearGroup (ZMod q) (Fin n → ZMod q)) = N :=
    (Nat.card_congr (Matrix.GeneralLinearGroup.toLin).toEquiv).symm
  have huN : u ^ N = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have hfN : ∀ v, f^[N] v = v := by
    intro v
    have h1 : ((u ^ N : LinearMap.GeneralLinearGroup (ZMod q) (Fin n → ZMod q)) :
        Module.End (ZMod q) (Fin n → ZMod q)) v = v := by rw [huN]; rfl
    rw [Units.val_pow_eq_pow_val, Module.End.pow_apply] at h1
    exact h1
  have hsemi : Function.Semiconj e φS f := by
    intro x
    simp [hf]
  have hval : Function.Semiconj (Subtype.val : S → G) φS φ := fun x => rfl
  intro x hx
  have h1 : e (φS^[N] ⟨x, hx⟩) = e ⟨x, hx⟩ := by
    rw [(hsemi.iterate_right N) ⟨x, hx⟩]
    exact hfN _
  have h2 := congrArg Subtype.val (e.injective h1)
  rw [(hval.iterate_right N) ⟨x, hx⟩] at h2
  exact h2

/-- `|GL₄(𝔽₃)| = 80·78·72·54 = 24261120 = 2⁹·3⁶·5·13` (proved). -/
theorem card_GL4_three : Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 3)) = 24261120 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

/-- `|GL₄(𝔽₇)| = 2400·2394·2352·2058` (proved). -/
theorem card_GL4_seven :
    Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 7)) = 2400 * 2394 * 2352 * 2058 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

theorem coprime_card_GL4_three {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (h13 : p ≠ 13) :
    Nat.Coprime p 24261120 := by
  rw [hp.coprime_iff_not_dvd]
  intro h
  have hfac : (24261120 : ℕ) = 2 ^ 9 * 3 ^ 6 * 5 * 13 := by norm_num
  rw [hfac] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h; omega

theorem coprime_card_GL4_seven : Nat.Coprime 13 (2400 * 2394 * 2352 * 2058) := by norm_num

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]

/-- **D2's algebraic core on PkgI3 points (proved; as `PkgI2.fixed_of_unipSq_of_iterate`).** If
`(σ - 1)² x = 0`, `x ∈ A(K̄)[ℓⁿ]`, and `σ^{qᵃ} x = x` with `qᵃ` prime to `ℓⁿ`, then `σ x = x`. -/
theorem fixed_of_unipSq_of_iterate' (A : PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (x : A.Pt (AlgebraicClosure K)) (ℓ n q a : ℕ) (hcop : Nat.Coprime (q ^ a) (ℓ ^ n))
    (hx : x ^ (ℓ ^ n) = 1)
    (hu : A.galAct σ (A.galAct σ x) * (A.galAct σ x)⁻¹ * (A.galAct σ x)⁻¹ * x = 1)
    (hit : (A.galAct σ)^[q ^ a] x = x) : A.galAct σ x = x := by
  set N := A.galAct σ x * x⁻¹ with hN
  have hσN : A.galAct σ N = N := by
    rw [hN, map_mul, map_inv]
    have h2 : A.galAct σ (A.galAct σ x) * (A.galAct σ x)⁻¹ =
        ((A.galAct σ x)⁻¹ * x)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hu]; group
    rw [h2, mul_inv_rev, inv_inv, mul_comm]
  have hiter : ∀ k : ℕ, (A.galAct σ)^[k] x = N ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hσN, pow_succ, hN]
      group
  have h1 : N ^ (q ^ a) = 1 := by
    have := hiter (q ^ a)
    rw [hit] at this
    exact (mul_eq_right.mp this.symm)
  have h2 : N ^ (ℓ ^ n) = 1 := by
    rw [hN, mul_pow, ← map_pow, hx, map_one, inv_pow, hx]; simp
  have hN1 : N = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [hN] at hN1
  exact mul_inv_eq_one.mp hN1

/-- **Glue (bridge): wild elements have `p`-power period on points.** For wild `σ` and
`σ' ∈ G_K` over `decomp σ`, every `P ∈ A(K̄)` has `σ'^{pᵃ} P = P` for some `a`. Proof plan: `P` is
defined over a finite `F ⊆ K̄` (a `K̄`-point of a scheme of finite type over `K`); `qEmb K` is an
isomorphism `ℚ̄ ≅ K̄` (both are algebraic closures of `ℚ`), and `embP` sends `qEmb⁻¹(F)` into a
finite extension of `ℚ_p`, whose Galois closure is fixed by some `σ^{pᵃ}`
(`exists_pow_fix_of_wild`, local-data). -/
def WildIter (A : PkgI3.AbVar K) : Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
    ∀ P : A.Pt (AlgebraicClosure K), ∃ a : ℕ, (A.galAct σ')^[p ^ a] P = P

/-- **The instance of the leaf I2-Tors on `A` (`A(K̄)[m] ≅ (ℤ/m)⁴` as groups).** Proved from
`ObjBridge.TorsionStructure` for `dim A = 2` in `torsGL_of_leaf`. -/
def TorsGL (A : PkgI3.AbVar K) (m : ℕ) : Prop :=
  ∃ e : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} ≃ (Fin 4 → ZMod m),
    ∀ (x y : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1})
      (h : x.1 * y.1 ∈ {P : A.Pt (AlgebraicClosure K) | P ^ m = 1}),
      e ⟨x.1 * y.1, h⟩ = e x + e y

/-- **Glue on the leaf R6 (`PkgI2.RaynaudCriterion`) at the place of `embP` (N5 L813-818).**
A wild `σ' ∈ G_K` (over `decomp σ`, `σ ∈ wildSet`) that fixes `A(K̄)[m]` satisfies
`(σ' - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ ≠ p`. Proof plan: R6 on `K' = K(A[m])`
(over which `A[m]` is rational, `m ≥ 3` prime to `p`) with the valuation ring of `K'` at the
place of `embP` (a DVR) and a valuation ring `w` of `K̄` over it; `σ'` fixes `K'`, and a wild
element is in the inertia group of `w`. What is missing is that bridge (PkgI2's setting is a
field with a DVR and `AlgebraicClosure`; here `G_K`, `resQ`, `decomp`) and the base change of
`A` to `K'`. Claimed only for `m ≥ 3` prime to `p` (used with `m = 3` for `p ≠ 13` and `m = 7`
for `p = 13`; for `m = p` Raynaud's criterion does not apply and the statement can fail). -/
def RaynaudPlace (A : PkgI3.AbVar K) (m : ℕ) : Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
    (∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P) →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ (n : ℕ) (x : A.Pt (AlgebraicClosure K)), x ^ (ℓ ^ n) = 1 →
      A.galAct σ' (A.galAct σ' x) * (A.galAct σ' x)⁻¹ * (A.galAct σ' x)⁻¹ * x = 1

/-- **`TorsGL` from the leaf I2-Tors (proved)**, for `dim A = 2` (a clause of `G7Out`). -/
theorem torsGL_of_leaf (hT : ObjBridge.TorsionStructure) (A : PkgI3.AbVar K) (hdim : A.dim = 2)
    (m : ℕ) (hm : 0 < m) : TorsGL A m := by
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  obtain ⟨e, he⟩ := hT K (ObjBridge.toGrp A) 2 m (by exact_mod_cast hdim) hm hmK
  exact ⟨e, he⟩

/-- `σ⁻¹ (σ P) = P` on points (proved). -/
theorem galAct_inv_galAct (A : PkgI3.AbVar K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (P : A.Pt (AlgebraicClosure K)) :
    A.galAct σ⁻¹ (A.galAct σ P) = P := by
  change PkgI3.AbVar.galHom σ⁻¹ ≫ PkgI3.AbVar.galHom σ ≫ P = P
  rw [← Category.assoc, ← PkgI3.AbVar.galHom_mul, inv_mul_cancel, PkgI3.AbVar.galHom_one,
    Category.id_comp]

theorem galAct_injective (A : PkgI3.AbVar K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    Function.Injective (A.galAct (L := AlgebraicClosure K) σ) := by
  intro x y h
  have h1 := congrArg (A.galAct σ⁻¹) h
  rwa [galAct_inv_galAct, galAct_inv_galAct] at h1

/-- A wild `σ'` fixes `A(K̄)[m]` when `p ∤ |GL₄(ℤ/m)|` (proved from `WildIter` and `TorsGL`). -/
theorem fix_torsion_of_coprime {A : PkgI3.AbVar K} (hI : WildIter (p := p) A) (m : ℕ)
    [Fact m.Prime] (hT : TorsGL A m)
    (hcop : Nat.Coprime p (Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod m))))
    {σ : GQp p} (hσ : σ ∈ wildSet) {σ' : Field.absoluteGaloisGroup K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) :
    ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P := by
  obtain ⟨e, he⟩ := hT
  intro P hP
  have hfix := iterate_card_GL_fix (A.galAct σ') (galAct_injective A σ')
    {P : A.Pt (AlgebraicClosure K) | P ^ m = 1}
    (fun x hx => by
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [← map_pow, hx, map_one])
    (fun x hx y hy => by
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      rw [mul_pow, hx, hy, _root_.one_mul]) m 4 e he P hP
  obtain ⟨a, ha⟩ := hI σ hσ σ' hσ' P
  have h1 : Function.IsPeriodicPt (A.galAct σ') (p ^ a) P := ha
  have h2 : Function.IsPeriodicPt (A.galAct σ')
      (Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod m))) P := hfix
  have h3 := h1.gcd h2
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left a hcop)] at h3
  exact h3

/-! ### `WildIter` from `PtFinite` (proved) -/

/-- `σ (τ P) = (στ) P` on points (proved). -/
theorem galAct_galAct (A : PkgI3.AbVar K) (σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (P : A.Pt (AlgebraicClosure K)) : A.galAct σ (A.galAct τ P) = A.galAct (σ * τ) P := by
  change PkgI3.AbVar.galHom σ ≫ PkgI3.AbVar.galHom τ ≫ P = PkgI3.AbVar.galHom (σ * τ) ≫ P
  rw [PkgI3.AbVar.galHom_mul, Category.assoc]

theorem galAct_iterate (A : PkgI3.AbVar K) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (P : A.Pt (AlgebraicClosure K)) (k : ℕ) : (A.galAct σ)^[k] P = A.galAct (σ ^ k) P := by
  induction k with
  | zero =>
    change P = PkgI3.AbVar.galHom 1 ≫ P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  | succ k ih => rw [Function.iterate_succ_apply', ih, galAct_galAct, ← pow_succ']

/-- `qEmb K : ℚ̄ → K̄` is onto (proved): `K̄` is integral over `ℚ` (`K` is a number field), hence
over the algebraically closed `ℚ̄`. -/
theorem qEmbRing_surjective (K : Type) [Field K] [NumberField K] :
    Function.Surjective (G0Galois.qEmbRing K) := by
  have hint : Algebra.IsIntegral ℚ (AlgebraicClosure K) := Algebra.IsIntegral.trans K
  have h : ((G0Galois.qEmbRing K).comp (algebraMap ℚ (AlgebraicClosure ℚ))).IsIntegral := by
    rw [Subsingleton.elim ((G0Galois.qEmbRing K).comp (algebraMap ℚ (AlgebraicClosure ℚ)))
      (algebraMap ℚ (AlgebraicClosure K))]
    exact hint.isIntegral
  exact (IsAlgClosed.ringHom_bijective_of_isIntegral _ (RingHom.IsIntegral.tower_top _ _ h)).2

theorem pow_fix_mono {G X : Type*} [Group G] [MulAction G X] {g : G} {x : X} {q b a : ℕ}
    (h : g ^ (q ^ b) • x = x) (hba : b ≤ a) : g ^ (q ^ a) • x = x := by
  have hmem : g ^ (q ^ b) ∈ MulAction.stabilizer G x := h
  have : g ^ (q ^ a) = (g ^ (q ^ b)) ^ (q ^ (a - b)) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hba]
  rw [this]
  exact (MulAction.stabilizer G x).pow_mem hmem _

/-- **A wild `σ'` has `p`-power period on each element of `K̄` (proved).** `x = qEmb y`;
`σ^{pᵃ}` fixes the normal closure of `ℚ_p(embP y)` (`exists_pow_fix_of_wild`), so
`decomp(σ^{pᵃ})` fixes `y` (`decomp_spec`), and `σ'^{pᵃ} x = qEmb(decomp(σ^{pᵃ}) y) = x`
(`resQ_spec`). -/
theorem wild_pow_fix_elem {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (x : AlgebraicClosure K) :
    ∃ a : ℕ, (σ' ^ (p ^ a)) x = x := by
  obtain ⟨y, rfl⟩ := qEmbRing_surjective K x
  set E : Fld p := IntermediateField.adjoin ℚ_[p] {embP (p := p) y}
  haveI : FiniteDimensional ℚ_[p] E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  set F' := IntermediateField.normalClosure ℚ_[p] E (Kbar p)
  haveI : FiniteDimensional ℚ_[p] F' := normalClosure.is_finiteDimensional ℚ_[p] E (Kbar p)
  haveI : Normal ℚ_[p] F' := normalClosure.normal ℚ_[p] E (Kbar p)
  obtain ⟨a, ha⟩ := exists_pow_fix_of_wild hσ (F' := F') ⟨inferInstance, IsGalois.mk⟩
  refine ⟨a, ?_⟩
  have hyE : embP (p := p) y ∈ F' :=
    E.le_normalClosure (IntermediateField.mem_adjoin_simple_self ℚ_[p] _)
  have hdec : decomp p (σ ^ (p ^ a)) y = y := by
    apply (embP (p := p)).injective
    rw [decomp_spec]
    exact ha _ hyE
  have h1 : G0Galois.qEmbRing K (G0Galois.resQ K (σ' ^ (p ^ a)) y) =
      (σ' ^ (p ^ a)) (G0Galois.qEmbRing K y) := G0Galois.resQ_spec K _ y
  have hpow : G0Galois.resQ K (σ' ^ (p ^ a)) = (G0Galois.resQ K σ') ^ (p ^ a) := map_pow _ _ _
  rw [hpow, hσ', ← map_pow, hdec] at h1
  exact h1.symm

/-- **A wild `σ'` has `p`-power period on each finite `F ⊆ K̄` over `K` (proved)**, from
`wild_pow_fix_elem` on a basis. -/
theorem wild_pow_fix_field {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (F : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K F] : ∃ a : ℕ, ∀ x ∈ F, (σ' ^ (p ^ a)) x = x := by
  set b := Module.finBasis K F
  choose c hc using fun i => wild_pow_fix_elem hσ hσ' ((b i : F) : AlgebraicClosure K)
  refine ⟨∑ i, c i, fun x hx => ?_⟩
  have hb : ∀ i, (σ' ^ (p ^ (∑ i, c i))) ((b i : F) : AlgebraicClosure K) = b i := fun i =>
    pow_fix_mono (G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hc i)
      (Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) (Finset.mem_univ i))
  have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • ((b i : F) : AlgebraicClosure K) := by
    have h := congrArg (fun z : F => (z : AlgebraicClosure K)) (b.sum_repr ⟨x, hx⟩).symm
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    exact h
  rw [hx', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, hb i, ← Algebra.smul_def]

/-- **Glue (Mathlib-level): `K̄`-points are defined over finite extensions.** Every
`P ∈ A(K̄)` is fixed by `G_F` for a finite `F ⊆ K̄` over `K` (a `K̄`-point of a scheme of finite
type over `K` factors through `Spec F`, `F` generated by the images of finitely many coordinates;
standard, e.g. EGA I/IV, locator UNVERIFIED). -/
def PtFinite (A : PkgI3.AbVar K) : Prop :=
  ∀ P : A.Pt (AlgebraicClosure K), ∃ F : IntermediateField K (AlgebraicClosure K),
    FiniteDimensional K F ∧ ∀ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (∀ x ∈ F, τ x = x) → A.galAct τ P = P

/-- **`WildIter` from `PtFinite` (proved).** -/
theorem wildIter_of_ptFinite {A : PkgI3.AbVar K} (h : PtFinite A) : WildIter (p := p) A := by
  intro σ hσ σ' hσ' P
  obtain ⟨F, hF, hP⟩ := h P
  obtain ⟨a, ha⟩ := wild_pow_fix_field (σ' := σ') hσ hσ' F
  have hit := galAct_iterate A σ' P (p ^ a)
  exact ⟨a, hit.trans (hP _ ha)⟩

/-- **`TorsFixWild` at `p ≥ 7`, `p ≠ ℓ`, from `WildIter`, I2-Tors and Raynaud at the place
(proved).** `m = 3` (`m = 7` if `p = 13`): the wild `σ'` fixes `A[m]`
(`fix_torsion_of_coprime`), so `(σ'-1)² = 0` on `A[ℓⁿ]` (`RaynaudPlace`), and with a `p`-power
period it fixes `A[ℓⁿ]` (`fixed_of_unipSq_of_iterate'`). -/
theorem torsFixWild_of_raynaud {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hI : WildIter (p := p) A) (hT3 : TorsGL A 3) (hT7 : TorsGL A 7)
    (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3) (hR7 : p = 13 → RaynaudPlace (p := p) A 7) :
    TorsFixWild (p := p) A ℓ := by
  intro σ hσ σ' hσ' n x hx
  have hpp : p.Prime := Fact.out
  have hfixm : ∃ m, (∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P) ∧
      RaynaudPlace (p := p) A m := by
    by_cases h13 : p = 13
    · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      refine ⟨7, fix_torsion_of_coprime hI 7 hT7 ?_ hσ hσ', hR7 h13⟩
      rw [card_GL4_seven, h13]; exact coprime_card_GL4_seven
    · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      refine ⟨3, fix_torsion_of_coprime hI 3 hT3 ?_ hσ hσ', hR3 h13⟩
      rw [card_GL4_three]; exact coprime_card_GL4_three hpp h7 h13
  obtain ⟨m, hm, hR⟩ := hfixm
  obtain ⟨a, ha⟩ := hI σ hσ σ' hσ' x
  have hcop : Nat.Coprime (p ^ a) (ℓ ^ n) :=
    Nat.Coprime.pow a n ((Nat.coprime_primes hpp Fact.out).mpr (Ne.symm hℓp))
  exact fixed_of_unipSq_of_iterate' A σ' x ℓ n p a hcop hx
    (hR σ hσ σ' hσ' hm ℓ Fact.out hℓp n x hx) ha

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaves I2-Tors and (through `RaynaudPlace`) R6,
and the bridge `WildIter` (proved).** `dim A = 2` is a clause of `G7Out`. -/
theorem tateWildK_of_leaves {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2)
    (hI : WildIter (p := p) A) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_torsFixWild (torsFixWild_of_raynaud hℓp h7 hI (torsGL_of_leaf hTors A hdim 3
    (by norm_num)) (torsGL_of_leaf hTors A hdim 7 (by norm_num)) hR3 hR7)

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaf I2-Tors, `PtFinite` and `RaynaudPlace`
(proved).** -/
theorem tateWildK_of_leaves' {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2)
    (hPt : PtFinite A) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_leaves hℓp h7 hTors hdim (wildIter_of_ptFinite hPt) hR3 hR7

end TorsSec

end G15Ram

end


/-! ## §7b (local-glue). `PtFinite` proved: `K̄`-points come from finite extensions

`K̄ = colim F` over the finite subextensions `F` of `K̄/K` (as in scratch/morph-descend's
`ringCoconeIsColimit`, there for `ℚ̄`), so `Spec K̄ = lim Spec F`; since `A → Spec K` is smooth,
hence locally of finite presentation, Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
(Stacks 01ZC) factors every `K`-morphism `Spec K̄ → A` through some `Spec F`. -/

noncomputable section

namespace G15Ram

open CategoryTheory Limits AlgebraicGeometry

section PtFiniteSec

variable {K : Type} [Field K]

/-- The finite subextensions of `K̄/K`, ordered by inclusion. -/
abbrev FIdx (K : Type) [Field K] : Type :=
  {F : IntermediateField K (AlgebraicClosure K) // FiniteDimensional K F}

instance : IsDirectedOrder (FIdx K) where
  directed F₁ F₂ := by
    obtain ⟨F₁, h₁⟩ := F₁
    obtain ⟨F₂, h₂⟩ := F₂
    exact ⟨⟨F₁ ⊔ F₂, IntermediateField.finiteDimensional_sup F₁ F₂⟩,
      show F₁ ≤ F₁ ⊔ F₂ from le_sup_left, show F₂ ≤ F₁ ⊔ F₂ from le_sup_right⟩

instance : Nonempty (FIdx K) := ⟨⟨⊥, inferInstance⟩⟩

/-- The diagram `F ↦ F` of rings. -/
def fRingDiag (K : Type) [Field K] : FIdx K ⥤ CommRingCat where
  obj F := CommRingCat.of F.1
  map f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `K̄` as a cocone. -/
def fRingCocone (K : Type) [Field K] : Cocone (fRingDiag K) where
  pt := CommRingCat.of (AlgebraicClosure K)
  ι := { app F := CommRingCat.ofHom (algebraMap F.1 (AlgebraicClosure K))
         naturality _ _ _ := rfl }

/-- `K̄ = colim F` over the finite subextensions (as morph-descend's `ringCoconeIsColimit`). -/
def fRingCoconeIsColimit (K : Type) [Field K] : IsColimit (fRingCocone K) := by
  haveI : ReflectsColimit (fRingDiag K) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : AlgebraicClosure K)
    have hx : _root_.IsIntegral K x := Algebra.IsIntegral.isIntegral _
    have : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
      IntermediateField.adjoin.finiteDimensional hx
    exact ⟨⟨IntermediateField.adjoin K {x}, this⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩
  · intro i x y h
    exact ⟨i, 𝟙 i, by rw [Subtype.ext h]⟩

/-- The diagram `F ↦ Spec F` of schemes. -/
def fSpecDiag (K : Type) [Field K] : (FIdx K)ᵒᵖ ⥤ Scheme where
  obj F := Spec (CommRingCat.of F.unop.1)
  map f := Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom)
  map_id F := by
    rw [show CommRingCat.ofHom (IntermediateField.inclusion (leOfHom (𝟙 F).unop)).toRingHom =
      𝟙 _ from rfl, Spec.map_id]
  map_comp f g := by
    rw [← Spec.map_comp]
    rfl

/-- `Spec K̄` as a cone over `fSpecDiag`. -/
def fSpecCone (K : Type) [Field K] : Cone (fSpecDiag K) where
  pt := Spec (CommRingCat.of (AlgebraicClosure K))
  π := { app F := Spec.map (CommRingCat.ofHom (algebraMap F.unop.1 (AlgebraicClosure K)))
         naturality F F' f := by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
          change _ = _ ≫ Spec.map _
          rw [← Spec.map_comp]
          rfl }

/-- `Spec K̄ = lim Spec F` (proved; `Spec` turns the colimit `fRingCoconeIsColimit` into a limit). -/
def fSpecConeIsLimit (K : Type) [Field K] : IsLimit (fSpecCone K) := by
  have h := isLimitOfPreserves Scheme.Spec (fRingCoconeIsColimit K).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro F F' f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro F
    simp only [Iso.refl_hom, Category.id_comp]

/-- **`PtFinite` holds for every abelian variety (proved).** -/
theorem ptFinite (A : PkgI3.AbVar K) : PtFinite A := by
  intro P
  have h3 : ∀ {i j : (FIdx K)ᵒᵖ} (f : i ⟶ j), IsAffineHom ((fSpecDiag K).map f) := fun f => by
    change IsAffineHom (Spec.map _); infer_instance
  have h1 : ∀ i, CompactSpace ((fSpecDiag K).obj i) := fun i => by
    change CompactSpace (Spec _); infer_instance
  have h2 : ∀ i, QuasiSeparatedSpace ((fSpecDiag K).obj i) := fun i => by
    change QuasiSeparatedSpace (Spec _); infer_instance
  let t : fSpecDiag K ⟶ (Functor.const _).obj (Spec (CommRingCat.of K)) :=
    { app F := Spec.map (CommRingCat.ofHom (algebraMap K F.unop.1))
      naturality F F' f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map]
        change Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp]
        rfl }
  have ha : (fSpecCone K).π ≫ t = (Functor.const _).map (P.left ≫ A.X.hom) := by
    ext F
    simp only [NatTrans.comp_app, Functor.const_map_app]
    change Spec.map _ ≫ Spec.map _ = P.left ≫ A.X.hom
    rw [← Spec.map_comp, Over.w P]
    rfl
  obtain ⟨F, g, hg, -⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (fSpecDiag K) t A.X.hom
      (fSpecCone K) (fSpecConeIsLimit K) P.left ha
  refine ⟨F.unop.1, F.unop.2, fun τ hτ => ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (τ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ P.left =
    P.left
  rw [← hg]
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) ?_)
  refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
  ext x
  exact hτ x.1 x.2

/-- **`WildIter` holds for every abelian variety (proved)**: `wildIter_of_ptFinite` and
`ptFinite`. -/
theorem wildIter {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) : WildIter (p := p) A :=
  wildIter_of_ptFinite (ptFinite A)

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaf I2-Tors and the instances `RaynaudPlace`
of the leaf R6 alone (proved).** -/
theorem tateWildK_of_raynaud {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h7 : 7 ≤ p)
    (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_leaves hℓp h7 hTors hdim (wildIter A) hR3 hR7

end PtFiniteSec

end G15Ram

end


/-! ## §7c' (local-glue). Verbatim slices of scratch/neron-lg/NeronLG.lean (origin/wip/neron-lg)
l.207-215, l.225-236, l.1406-1472 -/

noncomputable section

namespace ZInQ.NeronLG

open NumberField
open CategoryTheory MonObj

/-- The discrete valuation ring `𝓞_{L,v}` of a nonzero prime `v` of `𝓞_L`, as a valuation subring
of `L` (the ring of the `v`-adic valuation). -/
noncomputable def dvrAt {L : Type} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : ValuationSubring L :=
  (v.valuation L).valuationSubring

instance {L : Type} [Field L] [NumberField L] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    IsDiscreteValuationRing (dvrAt v) := by
  unfold dvrAt; infer_instance

section Classify

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K]

/-- Every valuation subring of a number field contains `𝓞_K` (it is integrally closed). -/
theorem ringOfIntegers_mem (O : ValuationSubring K) (x : 𝓞 K) : (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral O (x : K) from x.isIntegral_coe.tower_top)
  exact hy ▸ y.2

/-- The inclusion `𝓞_K → O`. -/
def toO (O : ValuationSubring K) : 𝓞 K →+* O :=
  (algebraMap (𝓞 K) K).codRestrict O.toSubring (ringOfIntegers_mem O)

theorem toO_coe (O : ValuationSubring K) (x : 𝓞 K) : ((toO O x : O) : K) = algebraMap (𝓞 K) K x :=
  rfl

end Classify

section Restrict

variable {K : Type} [Field K] [NumberField K]

/-- The center of a valuation subring `O ≠ ⊤` of a number field on `𝓞_K`: a nonzero prime. -/
def center' (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := (IsLocalRing.maximalIdeal O).comap (toO O)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy⟩ : ∃ y : K, y ∉ O := by
      by_contra h
      push_neg at h
      exact hO (eq_top_iff.2 fun y _ => h y)
    have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
    have hyi : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hy
    let x : O := ⟨y⁻¹, hyi⟩
    have hx : x ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu'⟩ := hu
      apply hy
      have : ((u⁻¹ : Oˣ) : O) * x = 1 := by rw [← hu']; exact u.inv_mul
      have h2 : ((((u⁻¹ : Oˣ) : O) : K)) * y⁻¹ = 1 := congrArg Subtype.val this
      have h3 : y = (((u⁻¹ : Oˣ) : O) : K) := by
        field_simp at h2
        exact h2.symm
      rw [h3]; exact (((u⁻¹ : Oˣ) : O)).2
    have hx0 : x ≠ 0 := fun h => inv_ne_zero hy0 (congrArg Subtype.val h)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (x : K)
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero hb
    have ha : toO O a = x * toO O b := by
      apply Subtype.ext
      rw [toO_coe, Subring.coe_mul, toO_coe, ← hab, div_mul_cancel₀ _ hb0]
    intro hbot
    have hmem : a ∈ (IsLocalRing.maximalIdeal O).comap (toO O) := by
      rw [Ideal.mem_comap, ha]; exact Ideal.mul_mem_right _ _ hx
    rw [hbot, Ideal.mem_bot] at hmem
    apply hx0
    apply Subtype.ext
    rw [← hab, hmem, map_zero, zero_div]; rfl

/-- **Every valuation subring `O ≠ ⊤` of a number field is `𝓞_{K,v}` (proved).** -/
theorem dvrAt_center' (O : ValuationSubring K) (hO : O ≠ ⊤) : dvrAt (center' O hO) = O := by
  apply ValuationSubring.eq_of_le_of_ne_top _ _ hO
  intro x hx
  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (center' O hO) x hx
  have hd : IsUnit (toO O d) := by
    by_contra h
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hvd : O.valuation (algebraMap (𝓞 K) K d) = 1 := (O.valuation_eq_one_iff _).1 hd
  apply O.mem_of_valuation_le_one
  have h2 := congrArg O.valuation hnd
  rw [map_mul, hvd, _root_.mul_one] at h2
  rw [h2]
  exact O.valuation_le_one (toO O n)

/-- Every valuation subring `O ≠ ⊤` of a number field is a DVR. -/
theorem isDiscreteValuationRing_of_ne_top (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by
  rw [← dvrAt_center' O hO]
  infer_instance

end Restrict

end ZInQ.NeronLG

end


/-! ## §7c'' (local-glue). Verbatim copy of scratch/unram-tate/BCPoints.lean
(origin/wip/unram-tate) l.14-142 -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace UnramTate

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

end BC

section Tr

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

end Tr

end UnramTate

end


/-! ## §7c (local-glue). Raynaud's criterion (R6) at the place of `embP`: the rational case

`raynaudPlace_rational` (proved): if `A[m]` is `K`-rational (`m ≥ 3`, `p ∤ m`), the leaf R6
(`ObjBridge.RaynaudCriterion`) gives `RaynaudPlace A m`. The valuation-theoretic bridge is proved:
* `wK`, `OK`: the valuation subrings of `K̄` and `K` at the place of `embP` (norm `≤ 1` after
  `K̄ ≅ ℚ̄ → ℚ̄_p`); `OK` is a DVR (`OK_ne_top` and neron-lg's `isDiscreteValuationRing_of_ne_top`);
* `m`, `ℓ` prime to `p` are units of `OK`;
* a wild `σ'` (over `decomp σ`) lies in the inertia group of `wK` (`isInertia_of_wild`).
The general case of `RaynaudPlace` needs R6 over `K(A[m])` and the base change of `A`. -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj
open scoped Pointwise

section RaynaudSec

/-- The valuation subring `{x : ‖f x‖ ≤ 1}` for a ring map `f` to an ultrametric normed field. -/
def normVS {F E : Type*} [Field F] [NormedField E] [IsUltrametricDist E] (f : F →+* E) :
    ValuationSubring F where
  carrier := {x | ‖f x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha
  mem_or_inv_mem' x := by
    by_cases h : ‖f x‖ ≤ 1
    · exact Or.inl h
    · right
      show ‖f x⁻¹‖ ≤ 1
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h))

theorem mem_normVS {F E : Type*} [Field F] [NormedField E] [IsUltrametricDist E] (f : F →+* E)
    (x : F) : x ∈ normVS f ↔ ‖f x‖ ≤ 1 := Iff.rfl

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]

/-- `ℚ̄ ≅ K̄` (`qEmbRing` is bijective). -/
def eK (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
  RingEquiv.ofBijective (G0Galois.qEmbRing K)
    ⟨(G0Galois.qEmbRing K).injective, qEmbRing_surjective K⟩

/-- `K̄ ≅ ℚ̄ → ℚ̄_p`, the place of `embP` on `K̄`. -/
def ιbar (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] :
    AlgebraicClosure K →+* Kbar p :=
  (embP (p := p)).comp (eK K).symm.toRingHom

/-- The valuation ring of `K̄` at the place of `embP`. -/
def wK (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] :
    ValuationSubring (AlgebraicClosure K) :=
  normVS (ιbar p K)

/-- The valuation ring of `K` at the place of `embP`. -/
def OK (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] : ValuationSubring K :=
  normVS ((ιbar p K).comp (algebraMap K (AlgebraicClosure K)))

theorem wK_comap : (wK p K).comap (algebraMap K (AlgebraicClosure K)) = OK p K := by
  ext x; exact Iff.rfl

theorem OK_ne_top : OK p K ≠ ⊤ := by
  intro h
  have hmem : ((p : K))⁻¹ ∈ OK p K := by rw [h]; exact ValuationSubring.mem_top _
  rw [OK, mem_normVS] at hmem
  simp only [map_inv₀, map_natCast, norm_inv] at hmem
  rw [norm_p_kbar, inv_inv] at hmem
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

instance OK_dvr : IsDiscreteValuationRing (OK p K) :=
  ZInQ.NeronLG.isDiscreteValuationRing_of_ne_top _ OK_ne_top

/-- A natural number prime to `p` is a unit of `OK`. -/
theorem isUnit_natCast_OK {n : ℕ} (hn : ¬ p ∣ n) : IsUnit ((n : OK p K)) := by
  have hnorm : ‖(n : Kbar p)‖ = 1 := norm_natCast_kbar hn
  have hn0 : (n : K) ≠ 0 := by
    intro h0
    have : (n : Kbar p) = 0 := by
      have := congrArg ((ιbar p K).comp (algebraMap K (AlgebraicClosure K))) h0
      simpa using this
    rw [this, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hinv : ((n : K))⁻¹ ∈ OK p K := by
    rw [OK, mem_normVS]
    simp only [map_inv₀, map_natCast, norm_inv, hnorm, inv_one, le_refl]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change ((n : OK p K) : K) * ((n : K))⁻¹ = 1
  rw [show ((n : OK p K) : K) = (n : K) from by simp]
  exact mul_inv_cancel₀ hn0

/-- `ιbar ∘ σ' = σ ∘ ιbar` for `σ'` over `decomp σ` (proved, from `resQ_spec`, `decomp_spec`). -/
theorem ιbar_apply {σ : GQp p} {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (y : AlgebraicClosure K) :
    ιbar p K (σ' y) = σ (ιbar p K y) := by
  obtain ⟨z, rfl⟩ := (eK K).surjective y
  have h1 : σ' (eK K z) = eK K (decomp p σ z) := by
    have := G0Galois.resQ_spec K σ' z
    rw [hσ'] at this
    exact this.symm
  simp only [ιbar, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [h1, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, decomp_spec]

theorem norm_wild_eq {σ : GQp p} (hσ : σ ∈ wildSet) (u : Kbar p) : ‖σ u‖ = ‖u‖ := by
  by_cases hu : u = 0
  · rw [hu, map_zero]
  have h := hσ u hu
  have : σ u = u + (σ u - u) := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h),
    max_eq_left (le_of_lt h)]

/-- **A wild `σ'` lies in the inertia group of `wK` (proved).** -/
theorem isInertia_of_wild {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) : PkgI2.IsInertia (wK p K) σ' := by
  have hnorm : ∀ y, ‖ιbar p K (σ' y)‖ = ‖ιbar p K y‖ := fun y => by
    rw [ιbar_apply hσ', norm_wild_eq hσ]
  have hnorm' : ∀ y, ‖ιbar p K (σ'⁻¹ y)‖ = ‖ιbar p K y‖ := fun y => by
    have := hnorm (σ'⁻¹ y)
    rw [show σ' (σ'⁻¹ y) = y from by
      change (σ' * σ'⁻¹) y = y; rw [mul_inv_cancel]; rfl] at this
    exact this.symm
  have hdec : σ' ∈ (wK p K).decompositionSubgroup K := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change ‖ιbar p K (σ'⁻¹ x)‖ ≤ 1 ↔ ‖ιbar p K x‖ ≤ 1
    rw [hnorm']
  refine ⟨hdec, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨σ', hdec⟩ : (wK p K).decompositionSubgroup K) • IsLocalRing.residue (wK p K) a =
    IsLocalRing.residue (wK p K) a
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  set b : wK p K := (⟨σ', hdec⟩ : (wK p K).decompositionSubgroup K) • a - a with hb
  have hbval : (b : AlgebraicClosure K) = σ' a - a := rfl
  have hlt : ‖ιbar p K (b : AlgebraicClosure K)‖ < 1 := by
    rw [hbval, map_sub, ιbar_apply hσ']
    by_cases ha0 : ιbar p K (a : AlgebraicClosure K) = 0
    · rw [ha0, map_zero, sub_zero, norm_zero]; exact zero_lt_one
    · exact lt_of_lt_of_le (hσ _ ha0) a.2
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.1 hu
  have hc' : ιbar p K (b : AlgebraicClosure K) * ιbar p K (c : AlgebraicClosure K) = 1 := by
    rw [← map_mul]
    have := congrArg Subtype.val hc
    simp only [Subring.coe_mul, OneMemClass.coe_one] at this
    rw [show ((b * c : wK p K) : AlgebraicClosure K) = (b : AlgebraicClosure K) * c from rfl] at this
    rw [this, map_one]
  have hcn : ‖ιbar p K (c : AlgebraicClosure K)‖ ≤ 1 := c.2
  have := congrArg norm hc'
  rw [norm_mul, norm_one] at this
  have h0 : 0 ≤ ‖ιbar p K (b : AlgebraicClosure K)‖ := norm_nonneg _
  nlinarith

/-- **`RaynaudPlace` when `A[m]` is `K`-rational, from the leaf R6 (proved).** -/
theorem raynaudPlace_rational (hR6 : ObjBridge.RaynaudCriterion) (A : PkgI3.AbVar K) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m)
    (hrat : ∀ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct τ P = P) :
    RaynaudPlace (p := p) A m := by
  intro σ hσ σ' hσ' _ ℓ hℓ hℓp n x hx
  have hℓp' : ¬ p ∣ ℓ := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  exact hR6 K (OK p K) (wK p K) wK_comap (ObjBridge.toGrp A) m hm3 (isUnit_natCast_OK hpm)
    hrat σ' (isInertia_of_wild hσ hσ') ℓ hℓ (isUnit_natCast_OK hℓp') n x hx

end RaynaudSec


/-! ### The general case: R6 over the field of `A[m]`, via the base change of `A` -/

section RaynaudGen

variable {p : ℕ} [Fact p.Prime]

/-- `normVS f ≠ ⊤` for a map of a field to `ℚ̄_p` (`1/p ∉`). -/
theorem normVS_ne_top {F : Type} [Field F] [CharZero F] (f : F →+* Kbar p) : normVS f ≠ ⊤ := by
  intro h
  have hmem : ((p : F))⁻¹ ∈ normVS f := by rw [h]; exact ValuationSubring.mem_top _
  rw [mem_normVS] at hmem
  simp only [map_inv₀, map_natCast, norm_inv] at hmem
  rw [norm_p_kbar, inv_inv] at hmem
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

/-- A natural number prime to `p` is a unit of `normVS f`. -/
theorem isUnit_natCast_normVS {F : Type} [Field F] (f : F →+* Kbar p) {n : ℕ} (hn : ¬ p ∣ n) :
    IsUnit ((n : normVS f)) := by
  have hnorm : ‖(n : Kbar p)‖ = 1 := norm_natCast_kbar hn
  have hn0 : (n : F) ≠ 0 := by
    intro h0
    have : (n : Kbar p) = 0 := by simpa using congrArg f h0
    rw [this, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hinv : ((n : F))⁻¹ ∈ normVS f := by
    rw [mem_normVS]
    simp only [map_inv₀, map_natCast, norm_inv, hnorm, inv_one, le_refl]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change ((n : normVS f) : F) * ((n : F))⁻¹ = 1
  rw [show ((n : normVS f) : F) = (n : F) from by simp]
  exact mul_inv_cancel₀ hn0

/-- **Wild elements are inertial (general form, proved).** If `f ∘ τ = σ ∘ f` with `σ` wild, then
`τ` lies in the inertia group of `normVS f`. -/
theorem isInertia_of_wild_gen {K₀ Ω : Type} [Field K₀] [Field Ω] [Algebra K₀ Ω]
    (f : Ω →+* Kbar p) {σ : GQp p} (hσ : σ ∈ wildSet) (τ : Ω ≃ₐ[K₀] Ω)
    (hf : ∀ y, f (τ y) = σ (f y)) : PkgI2.IsInertia (normVS f) τ := by
  have hnorm : ∀ y, ‖f (τ y)‖ = ‖f y‖ := fun y => by rw [hf, norm_wild_eq hσ]
  have hnorm' : ∀ y, ‖f (τ⁻¹ y)‖ = ‖f y‖ := fun y => by
    have := hnorm (τ⁻¹ y)
    rw [show τ (τ⁻¹ y) = y from by
      change (τ * τ⁻¹) y = y; rw [mul_inv_cancel]; rfl] at this
    exact this.symm
  have hdec : τ ∈ (normVS f).decompositionSubgroup K₀ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change ‖f (τ⁻¹ x)‖ ≤ 1 ↔ ‖f x‖ ≤ 1
    rw [hnorm']
  refine ⟨hdec, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨τ, hdec⟩ : (normVS f).decompositionSubgroup K₀) • IsLocalRing.residue (normVS f) a =
    IsLocalRing.residue (normVS f) a
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  set b : normVS f := (⟨τ, hdec⟩ : (normVS f).decompositionSubgroup K₀) • a - a with hb
  have hbval : (b : Ω) = τ a - a := rfl
  have hlt : ‖f (b : Ω)‖ < 1 := by
    rw [hbval, map_sub, hf]
    by_cases ha0 : f (a : Ω) = 0
    · rw [ha0, map_zero, sub_zero, norm_zero]; exact zero_lt_one
    · exact lt_of_lt_of_le (hσ _ ha0) a.2
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.1 hu
  have hc' : f (b : Ω) * f (c : Ω) = 1 := by
    rw [← map_mul]
    have := congrArg Subtype.val hc
    simp only [Subring.coe_mul, OneMemClass.coe_one] at this
    rw [show ((b * c : normVS f) : Ω) = (b : Ω) * c from rfl] at this
    rw [this, map_one]
  have hcn : ‖f (c : Ω)‖ ≤ 1 := c.2
  have := congrArg norm hc'
  rw [norm_mul, norm_one] at this
  have h0 : 0 ≤ ‖f (b : Ω)‖ := norm_nonneg _
  nlinarith

variable {K : Type} [Field K] [NumberField K]

/-- The stabilizer of `A(K̄)[m]` in `G_K`. -/
def torsStab (A : PkgI3.AbVar K) (m : ℕ) :
    Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) where
  carrier := {τ | ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct τ P = P}
  mul_mem' {a b} ha hb P hP := by
    rw [← galAct_galAct, hb P hP, ha P hP]
  one_mem' P _ := by
    change PkgI3.AbVar.galHom 1 ≫ P = P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  inv_mem' {a} ha P hP := by
    calc A.galAct a⁻¹ P = A.galAct a⁻¹ (A.galAct a P) := by rw [ha P hP]
      _ = P := galAct_inv_galAct A a P

/-- The stabilizer of `A[m]` contains `G_{F'}` for a finite `F'/K` (from `ptFinite`, `A[m]`
finite by I2-Tors). -/
theorem exists_fin_le_torsStab (A : PkgI3.AbVar K) (m : ℕ) [NeZero m] (hT : TorsGL A m) :
    ∃ F' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K F' ∧
      F'.fixingSubgroup ≤ torsStab A m := by
  obtain ⟨e, -⟩ := hT
  haveI : Finite {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} := Finite.of_equiv _ e.symm
  choose F hF hP using fun P : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} => ptFinite A P.1
  haveI : ∀ i, FiniteDimensional K (F i) := hF
  refine ⟨⨆ i, F i, inferInstance, fun τ hτ P hPm => ?_⟩
  refine hP ⟨P, hPm⟩ τ (fun x hx => ?_)
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
  exact hτ x ((le_iSup F ⟨P, hPm⟩) hx)

/-- **`RaynaudPlace` from the leaves R6 and I2-Tors (proved), for `dim A = 2`, `3 ≤ m`,
`p ∤ m`.** R6 is applied over `F = K(A[m])` (the fixed field of the stabilizer of `A[m]`, finite
by `ptFinite`) to the base change `A_F`, with the valuation rings at the place of `embP`
transported along `K̄ ≅ F̄`; points of `A_F` are those of `A` (`bcPt`, `trPt`, copied from
scratch/unram-tate). -/
theorem raynaudPlace_of_R6 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (A : PkgI3.AbVar K) (hdim : A.dim = 2) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m) : RaynaudPlace (p := p) A m := by
  intro σ hσ σ' hσ' hfix ℓ hℓ hℓp n x hx
  set σg : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ' with hσg
  haveI : NeZero m := ⟨by omega⟩
  set H := torsStab A m with hHdef
  obtain ⟨F', hF'fd, hF'H⟩ := exists_fin_le_torsStab A m (torsGL_of_leaf hTors A hdim m (by omega))
  have hHopen : IsOpen (H : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isOpen_mono hF'H (IntermediateField.fixingSubgroup_isOpen F')
  have hHclosed : IsClosed (H : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isClosed_of_isOpen H hHopen
  set F : IntermediateField K (AlgebraicClosure K) := IntermediateField.fixedField H with hFdef
  have hFH : F.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  have hFF' : F ≤ F' := by
    intro y hy
    rw [← InfiniteGalois.fixedField_fixingSubgroup F']
    rw [IntermediateField.mem_fixedField_iff] at hy ⊢
    exact fun τ hτ => hy τ (hF'H hτ)
  haveI : FiniteDimensional K F :=
    Module.Finite.of_injective (IntermediateField.inclusion hFF').toLinearMap
      (IntermediateField.inclusion hFF').injective
  haveI : FiniteDimensional ℚ F := Module.Finite.trans K F
  haveI : NumberField F := ⟨⟩
  -- `σ'` fixes `F`
  have hσ'F : ∀ y ∈ F, σg y = y := fun y hy =>
    ((IntermediateField.mem_fixedField_iff _ _).mp hy) σg hfix
  have hℓp' : ¬ p ∣ ℓ := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  -- `K̄` is an algebraic closure of `F`
  haveI : IsAlgClosure F (AlgebraicClosure K) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) (L := F) (A := AlgebraicClosure K)⟩
  let Ω := AlgebraicClosure F
  let ψ : Ω ≃ₐ[F] AlgebraicClosure K := IsAlgClosure.equiv F Ω (AlgebraicClosure K)
  let σF : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K :=
    { σg.toRingEquiv with commutes' := fun c => hσ'F c c.2 }
  let σ₁ : Ω ≃ₐ[F] Ω := (ψ.trans σF).trans ψ.symm
  have hσ₁ : ∀ y, ψ (σ₁ y) = σg (ψ y) := fun y => by
    simp only [σ₁, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
    rfl
  let f₁ : Ω →+* Kbar p := (ιbar p K).comp (ψ : Ω →+* AlgebraicClosure K)
  have hf₁ : ∀ y, f₁ (σ₁ y) = σ (f₁ y) := fun y => by
    change ιbar p K (ψ (σ₁ y)) = σ (ιbar p K (ψ y))
    rw [hσ₁ y]
    exact ιbar_apply (σ' := σg) hσ' (ψ y)
  let w₁ : ValuationSubring Ω := normVS f₁
  let O₁ : ValuationSubring F := normVS (f₁.comp (algebraMap F Ω))
  have hw₁ : w₁.comap (algebraMap F Ω) = O₁ := by ext; exact Iff.rfl
  haveI : IsDiscreteValuationRing O₁ :=
    ZInQ.NeronLG.isDiscreteValuationRing_of_ne_top _ (normVS_ne_top _)
  -- points of `A_F` over `Ω` are points of `A` over `K̄`
  let A₁ : PkgI3.AbVar F := A.baseChange F
  let ψK : Ω ≃ₐ[K] AlgebraicClosure K := ψ.restrictScalars K
  let Φ : A₁.Pt Ω ≃* A.Pt (AlgebraicClosure K) :=
    (UnramTate.bcPt A Ω).trans (UnramTate.trPt A ψK)
  have hΦ : ∀ (τ₁ : Ω ≃ₐ[F] Ω) (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
      (∀ y, τ (ψ y) = ψ (τ₁ y)) → ∀ z, Φ (A₁.galAct τ₁ z) = A.galAct τ (Φ z) := by
    intro τ₁ τ h z
    change UnramTate.trPt A ψK (UnramTate.bcPt A Ω (A₁.galAct τ₁ z)) =
      A.galAct τ (UnramTate.trPt A ψK (UnramTate.bcPt A Ω z))
    rw [UnramTate.bcPt_galAct, UnramTate.trPt_galAct A ψK (τ₁.restrictScalars K) τ h]
  have hrat : ∀ τ₁ : Ω ≃ₐ[F] Ω, ∀ z ∈ PkgI2.torsion (ObjBridge.toGrp A₁) Ω m,
      PkgI2.galAct (ObjBridge.toGrp A₁) τ₁ z = z := by
    intro τ₁ z₀ hz
    let z : A₁.Pt Ω := z₀
    change A₁.galAct τ₁ z = z
    let τF : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K := (ψ.symm.trans τ₁).trans ψ
    let τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τF.restrictScalars K
    have hτ : ∀ y, τ (ψ y) = ψ (τ₁ y) := fun y => by
      change ψ (τ₁ (ψ.symm (ψ y))) = ψ (τ₁ y)
      rw [AlgEquiv.symm_apply_apply]
    have hτH : τ ∈ H := by
      rw [← hFH, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      exact τF.commutes ⟨y, hy⟩
    have hz' : z ^ m = 1 := hz
    have hzm : (Φ z) ^ m = 1 := by rw [← map_pow, hz', map_one]
    have h1 := hΦ τ₁ τ hτ z
    rw [hτH (Φ z) hzm] at h1
    exact Φ.injective h1
  have hxm : (Φ.symm x) ^ (ℓ ^ n) = 1 := by rw [← map_pow, hx, map_one]
  have hU := hR6 F O₁ w₁ hw₁ (ObjBridge.toGrp A₁) m hm3 (isUnit_natCast_normVS _ hpm) hrat σ₁
    (isInertia_of_wild_gen f₁ hσ σ₁ hf₁) ℓ hℓ (isUnit_natCast_normVS _ hℓp') n (Φ.symm x) hxm
  have hU' : A₁.galAct σ₁ (A₁.galAct σ₁ (Φ.symm x)) * (A₁.galAct σ₁ (Φ.symm x))⁻¹ *
      (A₁.galAct σ₁ (Φ.symm x))⁻¹ * Φ.symm x = 1 := hU
  have hcomm : ∀ z, Φ (A₁.galAct σ₁ z) = A.galAct σg (Φ z) :=
    hΦ σ₁ σg (fun y => (hσ₁ y).symm)
  have h2 := congrArg Φ hU'
  simp only [map_one, map_mul, map_inv, hcomm, MulEquiv.apply_symm_apply] at h2
  exact h2

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaves R6 and I2-Tors alone (proved).**
`m = 3` for `p ≠ 13`, `m = 7` for `p = 13` (`raynaudPlace_of_R6`, `tateWildK_of_raynaud`). -/
theorem tateWildK_of_R6 (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    {A : PkgI3.AbVar K} (hdim : A.dim = 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h7 : 7 ≤ p) :
    TateWildK (p := p) A ℓ := by
  have hp : p.Prime := Fact.out
  refine tateWildK_of_raynaud hℓp h7 hTors hdim (fun _ => raynaudPlace_of_R6 hR6 hTors A hdim
    (by norm_num) ?_) (fun h13 => raynaudPlace_of_R6 hR6 hTors A hdim (by norm_num) ?_)
  · intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  · intro h
    rw [h13] at h
    norm_num at h

/-- **`LocalGlue` on G7's data from the leaves R6 and I2-Tors (proved), with the remaining glue
`KerWild`, `TateWildKE` (`p ≤ 5`) and `BetaTwist2` (`p = 2`).** At `p ≥ 7`, `p ≠ ℓ`, no glue is
left. -/
theorem localGlue_of_leaves (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_g7_twist h7 hC hK (fun h => tateWildK_of_R6 hR6 hTors h7.1 (Ne.symm hpℓ) h) hE hB

end RaynaudGen

end G15Ram

end

namespace RQ

theorem numberField_of_fd (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] : NumberField L := ⟨⟩

/-- An element of `G_ℚ` as an automorphism of `ℚ̄`. -/
def actQ (τ : Field.absoluteGaloisGroup ℚ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := τ
/-- An element of `G_K` as an automorphism of `\bar K`. -/
def actK {K : Type} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- `resQ K σ` is `σ` transported along the embedding `g : ℚ̄ → \bar K` that
`Field.absoluteGaloisGroup.map` chooses. -/
theorem resQ_comm' (K : Type) [Field K] [NumberField K] :
    ∃ g : AlgebraicClosure ℚ →+* AlgebraicClosure K, ∀ σ x,
      g (actQ (G0Galois.resQ K σ) x) = actK σ (g x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  let g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := g.toAlgebra
  haveI : IsScalarTower ℚ (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) σ) (AlgebraicClosure ℚ) x

/-- **`ResQRange` proved**: for finite Galois `L ⊆ ℚ̄`, the image of `resQ L` is `Fix(L)`
(normality of `L` gives `g(L) = L` inside `\bar L`; `g` is bijective because `\bar L/ℚ` is
algebraic). -/
theorem resQ_range (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] [IsGalois ℚ L] :
    (@G0Galois.resQ L _ (numberField_of_fd L)).range = L.fixingSubgroup := by
  haveI := numberField_of_fd L
  obtain ⟨g0, hcomm⟩ := resQ_comm' L
  let g : PkgI4.Qbar →ₐ[ℚ] AlgebraicClosure L := g0.toRatAlgHom
  have hg : ∀ x, g x = g0 x := fun _ => rfl
  -- `g` is bijective (`AlgebraicClosure L` is algebraic over `ℚ`)
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L) := by
    haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
    haveI : Algebra.IsAlgebraic L (AlgebraicClosure L) := AlgebraicClosure.isAlgebraic L
    exact Algebra.IsAlgebraic.trans ℚ L (AlgebraicClosure L)
  have hgbij : Function.Bijective g := by
    letI : Algebra PkgI4.Qbar (AlgebraicClosure L) := g.toAlgebra
    haveI : IsScalarTower ℚ PkgI4.Qbar (AlgebraicClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L) := inferInstance
    haveI : Algebra.IsIntegral PkgI4.Qbar (AlgebraicClosure L) := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : L →ₐ[ℚ] AlgebraicClosure L := IsScalarTower.toAlgHom ℚ L (AlgebraicClosure L)
  let e : L ≃ₐ[ℚ] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal ℚ ψ.fieldRange := Normal.of_algEquiv e
  let f : ψ.fieldRange →ₐ[ℚ] AlgebraicClosure L := (g.comp L.val).comp e.symm.toAlgHom
  have hf := AlgHom.fieldRange_of_normal f
  have hgL : ∀ x : L, ∃ y : L, g x = ψ y := by
    intro x
    have hx : g x ∈ f.fieldRange := ⟨e x, by simp [f]⟩
    rw [hf] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy.symm⟩
  have hLg : ∀ y : L, ∃ x : L, g x = ψ y := by
    intro y
    have hy : ψ y ∈ f.fieldRange := by rw [hf]; exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hy
    exact ⟨e.symm z, by simpa [f] using hz⟩
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    refine (IntermediateField.mem_fixingSubgroup_iff L (actQ (G0Galois.resQ L σ))).mpr ?_
    intro x hx
    apply g.toRingHom.injective
    show g (actQ (G0Galois.resQ L σ) x) = g x
    rw [hg, hcomm σ x, ← hg]
    obtain ⟨y, hy⟩ := hgL ⟨x, hx⟩
    have hy' : g x = ψ y := hy
    rw [hy']
    exact (actK σ).commutes y
  · intro hτ'
    have hτ := (IntermediateField.mem_fixingSubgroup_iff L (actQ τ)).mp hτ'
    let eg : PkgI4.Qbar ≃+* AlgebraicClosure L := RingEquiv.ofBijective g.toRingHom hgbij
    let τ' : PkgI4.Qbar ≃ₐ[ℚ] PkgI4.Qbar := τ
    let σ₀ : AlgebraicClosure L ≃+* AlgebraicClosure L := (eg.symm.trans τ'.toRingEquiv).trans eg
    have hσ₀ : ∀ x, σ₀ (g x) = g (τ' x) := by
      intro x
      show eg (τ' (eg.symm (eg x))) = g (τ' x)
      rw [RingEquiv.symm_apply_apply]; rfl
    have hfix : ∀ y : L, σ₀ (algebraMap L (AlgebraicClosure L) y) =
        algebraMap L (AlgebraicClosure L) y := by
      intro y
      obtain ⟨x, hx⟩ := hLg y
      have hx' : g x = algebraMap L (AlgebraicClosure L) y := hx
      rw [← hx', hσ₀, show τ' (x : PkgI4.Qbar) = x from hτ x x.2]
    let σ : Field.absoluteGaloisGroup L := AlgEquiv.ofRingEquiv (f := σ₀) hfix
    refine ⟨σ, ?_⟩
    apply AlgEquiv.ext
    intro x
    apply g.toRingHom.injective
    show g (actQ (G0Galois.resQ L σ) x) = g (τ' x)
    rw [hg, hcomm σ x, ← hg]
    exact hσ₀ x

end RQ

/-! ## §7d (local-glue). `p ≤ 5`: the torsion field of a model over `L` (proved from a descent Prop)

At `p ∈ {2, 3, 5}` the trick of §7 (`p ∤ |GL₄(𝔽_m)|`) is not available (finding G3), and Glazer
uses the model `A_L` over the Hom field `L` (N5 L813-818): `E = L_v(A_L[m])`, of degree
`≤ |GL₄(𝔽_m)|` over `L_v`. Here:
* `DescentPts A L` (GLUE, new): `L/ℚ` is Galois and `A` has a model `A₀` over `L` with
  `dim A₀ = 2` and a group isomorphism `A₀(L̄) ≅ A(K̄)` intertwining `σ₀ ∈ G_L` with `σ' ∈ G_K`
  whenever both restrict to the same element of `G_ℚ`;
* `index_torsStab_le` (proved): `[G_L : Stab(A₀[q])] ≤ |GL₄(𝔽_q)|` (I2-Tors);
* `torsFix_of_descent` (proved): from R6, I2-Tors and `DescentPts`, for `q ≠ p` prime, `q ≥ 3`, and
  any finite `M ⊇ L_v`, there is `E ⊇ M` with `[E:ℚ_p] ≤ |GL₄(𝔽_q)|·[M:ℚ_p]` on whose wild inertia
  every `ℓⁿ`-torsion point of `A(K̄)` is fixed (`ℓ ≠ p`). `E` is the fixed field of the open
  subgroup `decomp⁻¹(resQ_L(Stab)) ∩ G_M`; its degree is the index (Mathlib's
  `finrank_eq_fixingSubgroup_index`);
* `torsFixWildOdd_of_descent`, `torsFixWildE_two_of_descent`, `tateWildKE_of_descent`,
  `localGlue_of_descent` (proved). -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj

section DescentSec

variable {p : ℕ} [Fact p.Prime]

attribute [local instance] RQ.numberField_of_fd

/-- **Glue (the descent of `A` to the Hom field `L`; N5 L813-818; g0-mod-field: `G7Data` carries
`A : AbVar L` and `TateBridge` takes `A_{L'}` to be its base change to `L'`).** `L/ℚ` is Galois, and
`A/K` has a model `A₀/L` (`dim A₀ = 2`) with a group isomorphism `φ : A₀(L̄) ≅ A(K̄)` such that
`φ ∘ σ₀ = σ' ∘ φ` whenever `σ₀ ∈ G_L` and `σ' ∈ G_K` have the same image in `G_ℚ` (`resQ`). For
`K = L'` and `A = (A₀)_{L'}` this is the base change of points (`bcPt`) along an identification
`L̄ ≅ L̄'` compatible with `qEmb L` and `qEmb L'`; if Mathlib's choices of the embeddings
`L ↪ ℚ̄` (inside `resQ L`, `resQ L'`) differ on `L` by `γ ∈ Gal(L/ℚ)`, the model is the conjugate
`A₀ ×_{L,γ} L`, so the existential is still met. -/
def DescentPts {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] : Prop :=
  IsGalois ℚ L ∧
  ∃ (A₀ : PkgI3.AbVar L) (φ : A₀.Pt (AlgebraicClosure L) ≃* A.Pt (AlgebraicClosure K)),
    A₀.dim = 2 ∧ ∀ (σ₀ : Field.absoluteGaloisGroup L) (σ' : Field.absoluteGaloisGroup K),
      G0Galois.resQ L σ₀ = G0Galois.resQ K σ' →
        ∀ P : A₀.Pt (AlgebraicClosure L), φ (A₀.galAct σ₀ P) = A.galAct σ' (φ P)

variable {K : Type} [Field K] [NumberField K]

/-- **`[G_K : Stab(A[q])] ≤ |GL₄(𝔽_q)|` (proved)** from `A(K̄)[q] ≅ (ℤ/q)⁴` (`TorsGL`): the
action on `A[q]` is a homomorphism `G_K → GL(𝔽_q⁴)` whose kernel is the stabilizer. -/
theorem index_torsStab_le (A : PkgI3.AbVar K) (q : ℕ) [Fact q.Prime] (hT : TorsGL A q) :
    (torsStab A q).index ≠ 0 ∧
      (torsStab A q).index ≤ Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) := by
  set S := {P : A.Pt (AlgebraicClosure K) | P ^ q = 1} with hSdef
  obtain ⟨e, he⟩ := hT
  have hS : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : S), A.galAct σ x.1 ∈ S :=
    fun σ x => by
      have hx : x.1 ^ q = 1 := x.2
      show (A.galAct σ x.1) ^ q = 1
      rw [← map_pow, hx, map_one]
  have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := fun x hx y hy => by
    simp only [hSdef, Set.mem_setOf_eq] at hx hy ⊢
    rw [mul_pow, hx, hy, _root_.one_mul]
  let f : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) → (Fin 4 → ZMod q) → (Fin 4 → ZMod q) :=
    fun σ v => e ⟨A.galAct σ (e.symm v).1, hS σ _⟩
  have hadd : ∀ σ a b, f σ (a + b) = f σ a + f σ b := by
    intro σ a b
    set x := e.symm a
    set y := e.symm b
    have hxy : e.symm (a + b) = ⟨x.1 * y.1, hSmul _ x.2 _ y.2⟩ := by
      apply e.injective
      rw [Equiv.apply_symm_apply, he x y, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have h1 : (⟨A.galAct σ (e.symm (a + b)).1, hS σ _⟩ : S) =
        ⟨(A.galAct σ x.1) * (A.galAct σ y.1), hSmul _ (hS σ x) _ (hS σ y)⟩ := by
      apply Subtype.ext
      simp only [hxy, map_mul]
    show e ⟨A.galAct σ (e.symm (a + b)).1, hS σ _⟩ = e ⟨A.galAct σ x.1, hS σ x⟩ +
      e ⟨A.galAct σ y.1, hS σ y⟩
    rw [h1, he ⟨A.galAct σ x.1, hS σ x⟩ ⟨A.galAct σ y.1, hS σ y⟩]
  have hmul : ∀ σ τ v, f (σ * τ) v = f σ (f τ v) := by
    intro σ τ v
    show e ⟨A.galAct (σ * τ) (e.symm v).1, _⟩ =
      e ⟨A.galAct σ (e.symm (e ⟨A.galAct τ (e.symm v).1, _⟩)).1, _⟩
    congr 1
    apply Subtype.ext
    simp only [Equiv.symm_apply_apply]
    rw [galAct_galAct]
  have hone : ∀ v, f 1 v = v := by
    intro v
    show e ⟨A.galAct 1 (e.symm v).1, _⟩ = v
    have h1 : (⟨A.galAct 1 (e.symm v).1, hS 1 _⟩ : S) = e.symm v := by
      apply Subtype.ext
      change PkgI3.AbVar.galHom 1 ≫ (e.symm v).1 = (e.symm v).1
      rw [PkgI3.AbVar.galHom_one, Category.id_comp]
    rw [h1, Equiv.apply_symm_apply]
  let fL : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →
      ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) := fun σ =>
    { ((AddMonoidHom.mk' (f σ) (hadd σ)).toZModLinearMap q) with
      invFun := f σ⁻¹
      left_inv := fun v => by
        change f σ⁻¹ (f σ v) = v
        rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun v => by
        change f σ (f σ⁻¹ v) = v
        rw [← hmul, mul_inv_cancel, hone] }
  let ρ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
      ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) :=
    { toFun := fL
      map_one' := LinearEquiv.ext hone
      map_mul' := fun σ τ => LinearEquiv.ext (hmul σ τ) }
  have hker : ρ.ker ≤ torsStab A q := by
    intro σ hσ P hP
    have h1 : f σ (e ⟨P, hP⟩) = e ⟨P, hP⟩ := by
      have := congrArg (fun g : (Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q) => g (e ⟨P, hP⟩))
        (MonoidHom.mem_ker.mp hσ)
      exact this
    have h2 := e.injective h1
    simp only [Equiv.symm_apply_apply] at h2
    exact congrArg Subtype.val h2
  set N := Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) with hN
  have hcard : Nat.card ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) = N :=
    (Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod q)
      (Fin 4 → ZMod q)).toEquiv).symm.trans
      (Nat.card_congr (Matrix.GeneralLinearGroup.toLin).toEquiv).symm
  haveI : Finite ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) :=
    Finite.of_equiv _ ((Matrix.GeneralLinearGroup.toLin).toEquiv.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod q) (Fin 4 → ZMod q)).toEquiv)
  have hkerI : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
  have hr1 : 0 < Nat.card ρ.range := Nat.card_pos
  have hrN : Nat.card ρ.range ≤ N := hcard ▸ Subgroup.card_le_card_group _
  have hdvd : (torsStab A q).index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hker
  have hpos : 0 < (torsStab A q).index := Nat.pos_of_dvd_of_pos hdvd (hkerI ▸ hr1)
  exact ⟨hpos.ne', (Nat.le_of_dvd (hkerI ▸ hr1) hdvd).trans (hkerI ▸ hrN)⟩

/-- `resQ K` is injective (proved): `qEmb K ∘ resQ K τ = τ ∘ qEmb K` and `qEmb K` is onto. -/
theorem resQ_injective' : Function.Injective (G0Galois.resQ K) := by
  intro τ₁ τ₂ h
  let τ₁' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τ₁
  let τ₂' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τ₂
  show τ₁' = τ₂'
  apply AlgEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := qEmbRing_surjective K y
  have h1 := G0Galois.resQ_spec K τ₁' x
  have h2 := G0Galois.resQ_spec K τ₂' x
  change τ₁' (G0Galois.qEmbRing K x) = τ₂' (G0Galois.qEmbRing K x)
  rw [← h1, ← h2]
  exact congrArg (fun g => G0Galois.qEmbRing K (g x)) h

/-- **The torsion field of the model over `L` (proved)** from the leaves R6 (`raynaudPlace_of_R6`)
and I2-Tors and the glue `DescentPts`. For a prime `q ≥ 3`, `q ≠ p`, and a finite `M ⊇ L_v`,
there is a finite `E ⊇ M` with `[E:ℚ_p] ≤ |GL₄(𝔽_q)|·[M:ℚ_p]` such that every wild `σ ∈ G_E` fixes
every `ℓⁿ`-torsion point of `A(K̄)` through `G_K` (`ℓ ≠ p`). `E` is the fixed field of
`H = decomp⁻¹(resQ_L(Stab(A₀[q]))) ∩ G_M`, which is open (it contains `G_{E₀}`, `E₀` generated over
`M` by a basis of `L(A₀[q])`, finite by `ptFinite`), and `[E:ℚ_p] = [G_{ℚ_p} : H]`. For wild
`σ ∈ G_E`, `decomp σ = resQ_L σ₀` with `σ₀` fixing `A₀[q]`; Raynaud (`RaynaudPlace A₀ q`) and the
`p`-power period (`wildIter`) give that `σ₀` fixes `A₀[ℓⁿ]` (D2), and `φ` carries this to `A`. -/
theorem torsFix_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (q : ℕ) [Fact q.Prime] (hq3 : 3 ≤ q) (hpq : q ≠ p)
    (M : Fld p) [FiniteDimensional ℚ_[p] M] (hLvM : Lv (p := p) L ≤ M) :
    ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ M ≤ E ∧
      Module.finrank ℚ_[p] E ≤
        Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) * Module.finrank ℚ_[p] M ∧
      ∀ σ ∈ fixSet E ∩ wildSet, ∀ σ' : Field.absoluteGaloisGroup K,
        G0Galois.resQ K σ' = decomp p σ →
          ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P := by
  obtain ⟨hGal, A₀, φ, hdim₀, hφ⟩ := hD
  have hp : p.Prime := Fact.out
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp Fact.out).mp h).symm
  have hT₀ : TorsGL A₀ q := torsGL_of_leaf hTors A₀ hdim₀ q (by omega)
  obtain ⟨hidx0, hidx⟩ := index_torsStab_le A₀ q hT₀
  obtain ⟨F', hF'fd, hF'⟩ := exists_fin_le_torsStab A₀ q hT₀
  let Stab : Subgroup (Field.absoluteGaloisGroup L) := torsStab A₀ q
  let ρL : Field.absoluteGaloisGroup L →* GQ := G0Galois.resQ L
  have hρinj : Function.Injective ρL := resQ_injective'
  have hrange : ρL.range = L.fixingSubgroup := RQ.resQ_range L
  let Hq : Subgroup GQ := Stab.map ρL
  let GM : Subgroup (GQp p) := M.fixingSubgroup
  let H : Subgroup (GQp p) := Hq.comap (decomp p) ⊓ GM
  -- `decomp` of `G_M` fixes `L`
  have hdecL : ∀ σ : GQp p, σ ∈ fixSet M → decomp p σ ∈ L.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
      (decomp_fix_of_le (fun x hx => hLvM (embP_mem_Lv hx)) hσ)
  -- the open subgroup `G_{E₀}` inside `H`
  haveI : FiniteDimensional L F' := hF'fd
  haveI : Module.Free L F' := Module.Free.of_divisionRing L F'
  let b := Module.finBasis L F'
  let eL : AlgebraicClosure ℚ ≃+* AlgebraicClosure L :=
    RingEquiv.ofBijective (G0Galois.qEmbRing L)
      ⟨(G0Galois.qEmbRing L).injective, qEmbRing_surjective L⟩
  let S₀ : Set (Kbar p) := Set.range fun i => embP (eL.symm (b i : AlgebraicClosure L))
  haveI : Finite S₀ := Set.finite_range _ |>.to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] S₀) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E₀ : Fld p := M ⊔ IntermediateField.adjoin ℚ_[p] S₀
  have hE₀H : E₀.fixingSubgroup ≤ H := by
    intro σ hσ
    have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ
    have hσM : σ ∈ fixSet M := fun x hx => hσ' x (le_sup_left (a := M) hx)
    have hσS : ∀ i, decomp p σ (eL.symm (b i : AlgebraicClosure L)) =
        eL.symm (b i : AlgebraicClosure L) := by
      intro i
      apply (embP (p := p)).injective
      rw [decomp_spec]
      exact hσ' _ (le_sup_right (a := M)
        (IntermediateField.subset_adjoin ℚ_[p] S₀ ⟨i, rfl⟩))
    obtain ⟨σ₀, hσ₀⟩ : decomp p σ ∈ ρL.range := hrange ▸ hdecL σ hσM
    let σ₀' : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L := σ₀
    have hσ₀b : ∀ i, σ₀' (b i : AlgebraicClosure L) = b i := by
      intro i
      have h1 := G0Galois.resQ_spec L σ₀' (eL.symm (b i : AlgebraicClosure L))
      have h2 : G0Galois.qEmbRing L (eL.symm (b i : AlgebraicClosure L)) = b i :=
        eL.apply_symm_apply _
      change G0Galois.qEmbRing L (ρL σ₀ _) = _ at h1
      rw [hσ₀, hσS i, h2] at h1
      exact h1.symm
    have hσ₀F : σ₀' ∈ F'.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      have hsum := b.sum_repr ⟨z, hz⟩
      set c := b.repr ⟨z, hz⟩ with hc
      have hz' : z = ∑ i, c i • (b i : AlgebraicClosure L) := by
        have := congrArg (fun w : F' => (w : AlgebraicClosure L)) hsum
        simp only at this
        rw [← this, IntermediateField.coe_sum]
        rfl
      rw [hz', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, hσ₀b i]
    refine ⟨?_, (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσM⟩
    show decomp p σ ∈ Hq
    exact ⟨σ₀', hF' hσ₀F, hσ₀⟩
  have hHopen : IsOpen (H : Set (GQp p)) :=
    Subgroup.isOpen_mono hE₀H (IntermediateField.fixingSubgroup_isOpen E₀)
  have hHclosed : IsClosed (H : Set (GQp p)) := Subgroup.isClosed_of_isOpen H hHopen
  let E : Fld p := IntermediateField.fixedField H
  have hEH : E.fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  -- the index
  have hmapLe : GM.map (decomp p) ≤ ρL.range := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [hrange]
    exact hdecL σ ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ)
  have hrel1 : Hq.relIndex ρL.range = Stab.index := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hρinj,
      Subgroup.relIndex_top_right]
  have hrel2 : Hq.relIndex (GM.map (decomp p)) ≤ Stab.index := by
    rw [← hrel1]
    exact Subgroup.relIndex_le_of_le_right hmapLe (by rw [hrel1]; exact hidx0)
  have hrel3 : Hq.relIndex (GM.map (decomp p)) ≠ 0 := fun h0 =>
    hidx0 (hrel1 ▸ Subgroup.relIndex_eq_zero_of_le_right hmapLe h0)
  have hHidx : H.index = (Hq.comap (decomp p)).relIndex GM * GM.index := Subgroup.index_inf
  rw [Subgroup.relIndex_comap] at hHidx
  have hMfr : Module.finrank ℚ_[p] M = GM.index :=
    IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) M
  have hEfr : Module.finrank ℚ_[p] E = H.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) E, hEH]
  have hMpos : 0 < Module.finrank ℚ_[p] M := Module.finrank_pos
  have hEpos : 0 < Module.finrank ℚ_[p] E := by
    rw [hEfr, hHidx]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hrel3) (hMfr ▸ hMpos)
  refine ⟨E, Module.finite_of_finrank_pos hEpos, ?_, ?_, ?_⟩
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp (Subgroup.mem_inf.mp hτ).2 x hx
  · rw [hEfr, hHidx, hMfr]
    exact Nat.mul_le_mul_right _ (hrel2.trans hidx)
  · intro σ hσ σ' hσ' n P hP
    have hσE : σ ∈ E.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσ.1
    rw [hEH] at hσE
    obtain ⟨σ₀, hσ₀S, hσ₀⟩ := (Subgroup.mem_inf.mp hσE).1
    have hσ₀' : G0Galois.resQ L σ₀ = decomp p σ := hσ₀
    have hR := raynaudPlace_of_R6 (p := p) hR6 hTors A₀ hdim₀ hq3 hpq'
    set Q := φ.symm P with hQdef
    have hQ : Q ^ (ℓ ^ n) = 1 := by rw [hQdef, ← map_pow, hP, map_one]
    have hu := hR σ hσ.2 σ₀ hσ₀' (fun R hR' => hσ₀S R hR') ℓ Fact.out hℓp n Q hQ
    obtain ⟨a, ha⟩ := wildIter (p := p) A₀ σ hσ.2 σ₀ hσ₀' Q
    have hcop : Nat.Coprime (p ^ a) (ℓ ^ n) :=
      Nat.Coprime.pow a n ((Nat.coprime_primes hp Fact.out).mpr (Ne.symm hℓp))
    have hfix := fixed_of_unipSq_of_iterate' A₀ σ₀ Q ℓ n p a hcop hQ hu ha
    have h1 := hφ σ₀ σ' (hσ₀'.trans hσ'.symm) Q
    rw [hfix, hQdef, MulEquiv.apply_symm_apply] at h1
    exact h1.symm

/-- `|GL₄(𝔽₅)| = G₀ = 116064000000` (proved). -/
theorem card_GL4_five :
    Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 5)) = ZInQ.heightG0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  unfold ZInQ.heightG0
  norm_num

/-- **`TorsFixWildOdd` at every `p ≠ ℓ` (proved)** from the leaves R6, I2-Tors and the glue
`DescentPts`: `torsFix_of_descent` with `M = L_v` and `q = 3` (`q = 5` if `p = 3`);
`|GL₄(𝔽₃)| = 24261120 ≤ G₀` and `|GL₄(𝔽₅)| = G₀` (Glazer's `E = L_v(A_L[3])`, resp. `A_L[5]`). -/
theorem torsFixWildOdd_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : TorsFixWildOdd (p := p) A ℓ L := by
  obtain ⟨hLvfd, -⟩ := Lv_fin (p := p) L
  haveI := hLvfd
  have key : ∃ q : ℕ, ∃ _ : Fact q.Prime, 3 ≤ q ∧ q ≠ p ∧
      Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) ≤ ZInQ.heightG0 := by
    by_cases h3 : p = 3
    · exact ⟨5, ⟨by norm_num⟩, by norm_num, by omega, card_GL4_five.le⟩
    · refine ⟨3, ⟨by norm_num⟩, le_refl _, Ne.symm h3, ?_⟩
      rw [card_GL4_three]
      unfold ZInQ.heightG0
      norm_num
  obtain ⟨q, hq, hq3, hqp, hqN⟩ := key
  obtain ⟨E, hEfd, hLvE, hdeg, hfix⟩ :=
    torsFix_of_descent hR6 hTors hD hℓp q hq3 hqp (Lv (p := p) L) le_rfl
  exact ⟨E, hEfd, hLvE, hdeg.trans (Nat.mul_le_mul_right _ hqN), hfix⟩

/-- **`TorsFixWildE` from `BetaTwist2` (proved; used at `p = 2`, valid for `p ≠ 3`)**:
`torsFix_of_descent` with `q = 3` over `BetaTwist2`'s `M`; `4·|GL₄(𝔽₃)| ≤ G₀`. -/
theorem torsFixWildE_of_twist (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hp3 : p ≠ 3) {β : GQ → PadicAlgCl ℓ}
    (hB : BetaTwist2 (p := p) β L) : TorsFixWildE (p := p) A ℓ β L := by
  obtain ⟨M, hMfd, hLvM, hMdeg, hMβ⟩ := hB
  haveI := hMfd
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨E, hEfd, hME, hdeg, hfix⟩ :=
    torsFix_of_descent hR6 hTors hD hℓp 3 le_rfl (Ne.symm hp3) M hLvM
  refine ⟨E, hEfd, hLvM.trans hME, ?_, fun σ hσ =>
    ⟨hMβ σ ⟨fun x hx => hσ.1 x (hME hx), hσ.2⟩, hfix σ hσ⟩⟩
  rw [card_GL4_three] at hdeg
  calc Module.finrank ℚ_[p] E ≤ 24261120 * Module.finrank ℚ_[p] M := hdeg
    _ ≤ 24261120 * (4 * Module.finrank ℚ_[p] (Lv (p := p) L)) := Nat.mul_le_mul_left _ hMdeg
    _ = 97044480 * Module.finrank ℚ_[p] (Lv (p := p) L) := by ring
    _ ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) :=
        Nat.mul_le_mul_right _ (by unfold ZInQ.heightG0; norm_num)

/-- **`TateWildKE` at every `p ≠ ℓ` (proved)** from R6, I2-Tors, `DescentPts`, G7's clauses and,
at `p = 2`, `BetaTwist2`. -/
theorem tateWildKE_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime]
    {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hC : G7Clauses β ε L)
    (hD : DescentPts A L) (hℓp : ℓ ≠ p) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    TateWildKE (p := p) A ℓ β L := by
  by_cases h2 : p = 2
  · exact tateWildKE_of_torsFixWildE
      (torsFixWildE_of_twist hR6 hTors hD hℓp (by omega) (hB h2))
  · exact tateWildKE_of_torsFixWildE
      (torsFixWildE_of_odd h2 hC (torsFixWildOdd_of_descent hR6 hTors hD hℓp))

/-- **`LocalGlue p Tm a β L` on G7's data (proved)** from the leaves R6 and I2-Tors and the glue
`KerWild` (all `p`), `DescentPts` (`p ≤ 5`) and `BetaTwist2` (`p = 2`). -/
theorem localGlue_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    [FiniteDimensional ℚ L] (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hD : p ≤ 5 → DescentPts A L) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_leaves hR6 hTors hpℓ h7 hC hK
    (fun h5 => tateWildKE_of_descent hR6 hTors hC (hD h5) (Ne.symm hpℓ) hB) hB

/-- **`KerWild` from G7Data's kernel-field clause (proved).** If `L'` is finite Galois,
`G_{L'} = G_L ∩ ker β_ℂ` (g0-mod-field `G7Data`/`G7Out`: `σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`, with
`GQL L = L.fixingSubgroup`), and the `ℚ̄_ℓ`-valued `β` is `ι ∘ β_ℂ` for an injective
`ι : ℂ^× →* ℚ̄_ℓ^×`, then `KerWild L' β L` for G7Out's model field `K = L'`. This is the clause that
g0-assemble's `TateBridge` must add to its output (finding G8). -/
theorem kerWild_of_g7Data {ℓ : ℕ} [Fact ℓ.Prime] {L L' : IntermediateField ℚ PkgI4.Qbar}
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (βC : GQ → ℂˣ)
    (hker : ∀ σ : GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (ιC : ℂˣ →* (PadicAlgCl ℓ)ˣ) (hι : Function.Injective ιC) {β : GQ → PadicAlgCl ℓ}
    (hβ : ∀ g, β g = (ιC (βC g) : PadicAlgCl ℓ)) : KerWild L' β L := by
  intro g hgL hg1
  have h1 : ιC (βC g) = ιC 1 := by
    rw [map_one]
    exact Units.ext (by rw [Units.val_one, ← hβ g, hg1])
  have h2 : βC g = 1 := hι h1
  have h3 : g ∈ L'.fixingSubgroup :=
    (hker g).mpr ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).mpr hgL, h2⟩
  rw [RQ.resQ_range L']
  exact h3

end DescentSec

end G15Ram

end


/-! ## §7e (local-glue). `BetaTwist2` from an unramified fourth root (proved)

`BetaTwist2 β L` (§7, `p = 2`) is reduced to two smaller Props:
* `Beta4Inertia β L` (GLUE on G7's `β² = ι ∘ χ`): `β⁴ = 1` on the inertia subgroup of `G_{L_v}`;
* `UnramRoots p ℓ` (GLUE, textbook: `G_F/I_F ≅ Ẑ` is topologically generated by a Frobenius and
  `F` has an unramified extension of every degree; Serre, *Local Fields*, Ch. III §5 and IV §2,
  locators UNVERIFIED): a continuous character of `G_F` trivial on inertia has an unramified
  continuous fourth root.
`betaTwist2_of_roots` (proved): `M` is the fixed field of `{σ ∈ G_{L_v} : β(σ) = η(σ)}`, the kernel
of the character `β/η` with values in `μ₄(ℚ̄_ℓ)`, so `[M:L_v] ≤ 4`, and `β = η = 1` on wild inertia
of `G_M`. -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond

section TwistSec

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Glue on G7's clauses at `p = 2` (N5 L826-833).** `β⁴ = 1` on the inertia subgroup of
`G_{L_v}` (`inertiaSet` is the inertia subgroup of `G_{ℚ_p}`). Proof plan: on `G_{L_v}`,
`β⁴ = ι ∘ χ²` (G7: `β² = ι ∘ galChar χ`), with `χ` mod `N = chiLevel T₋`, `N = 4^a N'`, `N'` odd
squarefree, `a ≤ 1`; inertia at `2` fixes the roots of unity of odd order (they are unramified:
distinct `N'`-th roots of unity are at distance `1`), so `cyc_N(σ) ∈ (ℤ/4)^× × {1}`, of exponent
`2`, and `χ² (cyc_N σ) = 1`. -/
def Beta4Inertia (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∀ σ ∈ fixSet (Lv (p := p) L) ∩ inertiaSet, β (decomp p σ) ^ 4 = 1

variable (p ℓ) in
/-- **Glue (textbook; Serre, *Local Fields*, Ch. III §5 and Ch. IV §2, locators UNVERIFIED): an
unramified fourth root.** For a finite `F/ℚ_p` and a character `ψ` of `G_F` with values in
`ℚ̄_ℓ^×` that is trivial on some open `G_{F''}` and on the inertia subgroup `G_F ∩ I`, there is a
character `η` of `G_F`, trivial on some open `G_{F₁}` and on `G_F ∩ I`, with `η⁴ = ψ` on `G_F`.
(`ψ` factors through `Gal(F_m/F) ≅ ℤ/m`, `F_m` unramified of degree `m`, generated by Frobenius;
take `ξ` with `ξ⁴ = ψ(Frob)`, of order `d ∣ 4m`, and `η(σ) = ξ^k` for `σ|_{F_d} = Frob^k`.) -/
def UnramRoots : Prop :=
  ∀ (F : Fld p), FiniteDimensional ℚ_[p] F → ∀ ψ : GQp p → PadicAlgCl ℓ,
    (∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, ψ (σ * τ) = ψ σ * ψ τ) →
    (∃ F'' : Fld p, FiniteDimensional ℚ_[p] F'' ∧ ∀ σ ∈ fixSet F'', ψ σ = 1) →
    (∀ σ ∈ fixSet F ∩ inertiaSet, ψ σ = 1) →
    ∃ η : GQp p → PadicAlgCl ℓ,
      (∃ F₁ : Fld p, FiniteDimensional ℚ_[p] F₁ ∧ ∀ σ ∈ fixSet F₁, η σ = 1) ∧
      (∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, η (σ * τ) = η σ * η τ) ∧
      (∀ σ ∈ fixSet F, η σ ^ 4 = ψ σ) ∧
      (∀ σ ∈ fixSet F ∩ inertiaSet, η σ = 1)

/-- **`BetaTwist2` from G7's clauses, `Beta4Inertia` and `UnramRoots` (proved).** -/
theorem betaTwist2_of_roots {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L) (hU : UnramRoots p ℓ)
    (h4 : Beta4Inertia (p := p) β L) : BetaTwist2 (p := p) β L := by
  haveI : FiniteDimensional ℚ L := hC.1
  obtain ⟨hFfd, -⟩ := Lv_fin (p := p) L
  set F : Fld p := Lv (p := p) L with hFdef
  haveI := hFfd
  have hLF : ∀ x ∈ L, embP x ∈ F := fun x hx => embP_mem_Lv hx
  have hmul : BetaCharOn (p := p) β F := betaCharOn_of_cocycle hC.2.2.1 hC.2.2.2.2.2.2 hLF
  have hβ0 : ∀ g, β g ≠ 0 := hC.2.2.2.1
  have hβ1 : β 1 = 1 := by
    have h := hC.2.2.1 1 1
    rw [hC.2.2.2.2.2.2 1 1 (fun _ _ => rfl) (fun _ _ => rfl), one_mul, mul_one] at h
    exact (mul_right_eq_self₀.mp h).resolve_right (hβ0 1)
  obtain ⟨F', hF'gal, hF'⟩ := betaOpen_of_isLocallyConstant (p := p) hC.2.2.2.2.1 hβ1
  haveI : FiniteDimensional ℚ_[p] F' := hF'gal.1
  -- the fourth root
  obtain ⟨η, ⟨F₁, hF₁fd, hF₁⟩, hηmul, hη4, hηI⟩ := hU F hFfd (fun σ => β (decomp p σ) ^ 4)
    (fun σ hσ τ hτ => by beta_reduce; rw [hmul σ hσ τ hτ, mul_pow])
    ⟨F', hF'gal.1, fun σ hσ => by beta_reduce; rw [hF' σ hσ, one_pow]⟩ h4
  haveI := hF₁fd
  have hη0 : ∀ σ ∈ fixSet F, η σ ≠ 0 := fun σ hσ h0 => by
    have := hη4 σ hσ
    rw [h0, zero_pow (by norm_num)] at this
    exact pow_ne_zero 4 (hβ0 _) this.symm
  have h1F : (1 : GQp p) ∈ fixSet F := fun _ _ => rfl
  have hη1 : η 1 = 1 := by
    have h := hηmul 1 h1F 1 h1F
    rw [mul_one] at h
    exact ((mul_right_eq_self₀.mp h.symm).resolve_right (hη0 1 h1F))
  have hβd1 : β (decomp p 1) = 1 := by rw [map_one]; exact hβ1
  have hinvF : ∀ σ ∈ fixSet F, σ⁻¹ ∈ fixSet F := fun σ hσ x hx => by
    conv_lhs => rw [← hσ x hx]
    exact σ.symm_apply_apply x
  have hmulF : ∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, σ * τ ∈ fixSet F := fun σ hσ τ hτ x hx => by
    show σ (τ x) = x
    rw [hτ x hx, hσ x hx]
  -- the subgroup `U = {σ ∈ G_F : β σ = η σ}`
  let U : Subgroup (GQp p) :=
    { carrier := {σ | σ ∈ fixSet F ∧ β (decomp p σ) = η σ}
      mul_mem' := fun {σ τ} hσ hτ => ⟨hmulF σ hσ.1 τ hτ.1, by
        rw [hmul σ hσ.1 τ hτ.1, hηmul σ hσ.1 τ hτ.1, hσ.2, hτ.2]⟩
      one_mem' := ⟨h1F, by rw [hβd1, hη1]⟩
      inv_mem' := fun {σ} hσ => ⟨hinvF σ hσ.1, by
        have hb := hmul σ⁻¹ (hinvF σ hσ.1) σ hσ.1
        have he := hηmul σ⁻¹ (hinvF σ hσ.1) σ hσ.1
        rw [inv_mul_cancel, hβd1] at hb
        rw [inv_mul_cancel, hη1] at he
        rw [hσ.2] at hb
        have hne := hη0 σ hσ.1
        calc β (decomp p σ⁻¹) = β (decomp p σ⁻¹) * η σ * (η σ)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
          _ = η σ⁻¹ * η σ * (η σ)⁻¹ := by rw [← hb, he]
          _ = η σ⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]⟩ }
  let GF : Subgroup (GQp p) := F.fixingSubgroup
  have hmemGF : ∀ σ : GQp p, σ ∈ GF ↔ σ ∈ fixSet F := fun σ =>
    IntermediateField.mem_fixingSubgroup_iff _ _
  have hUGF : U ≤ GF := fun σ hσ => (hmemGF σ).mpr hσ.1
  -- the character `β/η : G_F → μ₄`
  let f : GF →* (PadicAlgCl ℓ)ˣ :=
    { toFun := fun σ => Units.mk0 (β (decomp p σ.1) * (η σ.1)⁻¹)
        (mul_ne_zero (hβ0 _) (inv_ne_zero (hη0 _ ((hmemGF _).mp σ.2))))
      map_one' := by
        ext
        show β (decomp p 1) * (η 1)⁻¹ = 1
        rw [hβd1, hη1, inv_one, mul_one]
      map_mul' := fun σ τ => by
        ext
        simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul]
        rw [hmul σ.1 ((hmemGF _).mp σ.2) τ.1 ((hmemGF _).mp τ.2),
          hηmul σ.1 ((hmemGF _).mp σ.2) τ.1 ((hmemGF _).mp τ.2), mul_inv]
        ring }
  have hker : U.subgroupOf GF = f.ker := by
    ext σ
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    have hσF := (hmemGF _).mp σ.2
    constructor
    · intro h
      ext
      simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, Units.val_one]
      rw [h.2, mul_inv_cancel₀ (hη0 _ hσF)]
    · intro h
      refine ⟨hσF, ?_⟩
      have h' := congrArg Units.val h
      simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, Units.val_one] at h'
      have hne := hη0 _ hσF
      calc β (decomp p σ.1) = β (decomp p σ.1) * (η σ.1)⁻¹ * η σ.1 := by
            rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
        _ = η σ.1 := by rw [h', one_mul]
  have hrange : f.range ≤ rootsOfUnity 4 (PadicAlgCl ℓ) := by
    rintro _ ⟨σ, rfl⟩
    rw [mem_rootsOfUnity]
    ext
    have hσF := (hmemGF _).mp σ.2
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_pow_eq_pow_val, Units.val_mk0,
      Units.val_one]
    rw [mul_pow, inv_pow, ← hη4 _ hσF, mul_inv_cancel₀ (pow_ne_zero 4 (hη0 _ hσF))]
  have hrel : U.relIndex GF ≤ 4 := by
    rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    exact (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity _ _)
  have hrel0 : U.relIndex GF ≠ 0 := by
    rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    haveI : Finite f.range :=
      Finite.of_injective (Subgroup.inclusion hrange) (Subgroup.inclusion_injective hrange)
    exact Nat.card_pos.ne'
  -- `U` is open: it contains `G_{F ⊔ F' ⊔ F₁}`
  let E₀ : Fld p := F ⊔ F' ⊔ F₁
  have hE₀U : E₀.fixingSubgroup ≤ U := by
    intro σ hσ
    have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ
    have hσF : σ ∈ fixSet F := fun x hx => hσ' x ((show F ≤ E₀ from le_sup_left.trans le_sup_left) hx)
    have hσF' : σ ∈ fixSet F' := fun x hx => hσ' x ((show F' ≤ E₀ from le_sup_right.trans le_sup_left) hx)
    have hσF₁ : σ ∈ fixSet F₁ := fun x hx => hσ' x ((show F₁ ≤ E₀ from le_sup_right) hx)
    exact ⟨hσF, by rw [hF' σ hσF', hF₁ σ hσF₁]⟩
  have hUopen : IsOpen (U : Set (GQp p)) :=
    Subgroup.isOpen_mono hE₀U (IntermediateField.fixingSubgroup_isOpen E₀)
  have hUclosed : IsClosed (U : Set (GQp p)) := Subgroup.isClosed_of_isOpen U hUopen
  let M : Fld p := IntermediateField.fixedField U
  have hMU : M.fixingSubgroup = U := InfiniteGalois.fixingSubgroup_fixedField ⟨U, hUclosed⟩
  have hMfr : Module.finrank ℚ_[p] M = U.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) M, hMU]
  have hFfr : Module.finrank ℚ_[p] F = GF.index :=
    IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) F
  have hUidx : U.index = U.relIndex GF * GF.index := (Subgroup.relIndex_mul_index hUGF).symm
  have hFpos : 0 < Module.finrank ℚ_[p] F := Module.finrank_pos
  have hMpos : 0 < Module.finrank ℚ_[p] M := by
    rw [hMfr, hUidx]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hrel0) (hFfr ▸ hFpos)
  refine ⟨M, Module.finite_of_finrank_pos hMpos, ?_, ?_, ?_⟩
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    exact hτ.1 x hx
  · rw [hMfr, hUidx, ← hFfr]
    exact Nat.mul_le_mul_right _ hrel
  · intro σ hσ
    have hσM : σ ∈ M.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσ.1
    rw [hMU] at hσM
    rw [hσM.2]
    exact hηI σ ⟨hσM.1, wildSet_subset_inertiaSet hσ.2⟩

/-! ### `Beta4Inertia` at `p = 2` from G7's clauses (proved) -/

/-- Inertia fixes the roots of unity of order prime to `p` (proved; as `wild_fix_prime_to_p`). -/
theorem inertia_fix_prime_to_p {σ : GQp p} (hσ : σ ∈ inertiaSet) {ζ : Kbar p} {m : ℕ}
    (hm0 : 0 < m) (hpm : ¬ p ∣ m) (hζ : ζ ^ m = 1) : σ ζ = ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hm0.ne'] at hζ; exact zero_ne_one hζ
  have h1 : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hm0 hζ
  set η := σ ζ * ζ⁻¹ with hη
  have hηm : η ^ m = 1 := by
    rw [hη, mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hlt : ‖η - 1‖ < 1 := by
    have he : η - 1 = (σ ζ - ζ) * ζ⁻¹ := by rw [hη, sub_mul, mul_inv_cancel₀ hζ0]
    rw [he, norm_mul, norm_inv, h1, inv_one, mul_one]
    exact hσ ζ h1.le
  have := eq_one_of_pow_eq_one_of_norm_lt hm0 hpm hηm hlt
  rw [hη, mul_inv_eq_one₀ hζ0] at this
  exact this

/-- `σ²` fixes the fourth roots of unity (proved): `σ(i) = ±i`. -/
theorem sq_fix_four (σ : GQp p) {ζ : Kbar p} (hζ : ζ ^ 4 = 1) : σ (σ ζ) = ζ := by
  have h2 : (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = 0 := by linear_combination hζ
  rcases mul_eq_zero.mp h2 with h | h
  · have h' : (ζ - 1) * (ζ + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · rw [sub_eq_zero.mp h1, map_one, map_one]
    · rw [eq_neg_of_add_eq_zero_left h1]
      simp
  · have hτ : (σ ζ - ζ) * (σ ζ + ζ) = 0 := by
      have e2 : σ ζ ^ 2 = ζ ^ 2 := by
        have e1 : ζ ^ 2 = -1 := by linear_combination h
        rw [← map_pow, e1, map_neg, map_one]
      linear_combination e2
    rcases mul_eq_zero.mp hτ with h1 | h1
    · rw [sub_eq_zero.mp h1, sub_eq_zero.mp h1]
    · have e : σ ζ = -ζ := eq_neg_of_add_eq_zero_left h1
      rw [e, map_neg, e, neg_neg]

/-- `chiLevel T₋ ∣ 4M` with `M` odd (proved; `lev 2 = 4`, `lev q = q` for odd `q`). -/
theorem chiLevel_dvd_four_mul_odd {Tm : Finset ℕ} (hTm : ∀ q ∈ Tm, q.Prime) :
    ∃ M : ℕ, ¬ 2 ∣ M ∧ GlueDescent.chiLevel Tm ∣ 4 * M := by
  refine ⟨∏ q ∈ Tm.erase 2, GlueDescent.lev q, ?_, ?_⟩
  · refine Finset.prod_induction _ (fun n => ¬ 2 ∣ n) (fun a b ha hb h => ?_) (by norm_num)
      (fun q hq => ?_)
    · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
      · exact ha h
      · exact hb h
    · have hq2 : q ≠ 2 := Finset.ne_of_mem_erase hq
      have hqp := hTm q (Finset.mem_of_mem_erase hq)
      unfold GlueDescent.lev
      rw [if_neg hq2]
      intro h
      rcases (Nat.Prime.eq_one_or_self_of_dvd hqp 2 h) with h' | h'
      · omega
      · exact hq2 h'.symm
  · by_cases h2 : 2 ∈ Tm
    · unfold GlueDescent.chiLevel
      rw [← Finset.mul_prod_erase Tm GlueDescent.lev h2]
      unfold GlueDescent.lev
      rw [if_pos rfl]
    · unfold GlueDescent.chiLevel
      rw [Finset.erase_eq_self.mpr h2]
      exact dvd_mul_left _ _

/-- At `p = 2`, `decomp(σ²)` fixes the `4M`-th roots of unity for inertia `σ`, `M` odd (proved). -/
theorem decomp_sq_fix_root (hp2 : p = 2) {σ : GQp p} (hσ : σ ∈ inertiaSet) {M : ℕ}
    (hM : ¬ 2 ∣ M) {x : PkgI4.Qbar} (hx : x ^ (4 * M) = 1) : decomp p (σ * σ) x = x := by
  apply (embP (p := p)).injective
  rw [decomp_spec]
  set ζ := embP (p := p) x
  have hζ : ζ ^ (4 * M) = 1 := by rw [← map_pow, hx, map_one]
  have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact hM (dvd_zero 2))
  have hζ0 : ζ ≠ 0 := by
    rintro h0; rw [h0, zero_pow (by omega)] at hζ; exact zero_ne_one hζ
  have hpM : ¬ p ∣ M := hp2 ▸ hM
  have hy : σ (ζ ^ 4) = ζ ^ 4 := inertia_fix_prime_to_p hσ hM0 hpM (by rw [← pow_mul, hζ])
  have hz : σ (σ (ζ ^ M)) = ζ ^ M := sq_fix_four σ (by rw [← pow_mul, mul_comm, hζ])
  have hcop : Nat.Coprime 4 M := by
    have := Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hM)
    norm_num at this
    exact this
  have hb : ((Nat.gcd 4 M : ℕ) : ℤ) = 4 * Nat.gcdA 4 M + M * Nat.gcdB 4 M := Nat.gcd_eq_gcd_ab 4 M
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have hdec : ζ = (ζ ^ 4) ^ (Nat.gcdA 4 M) * (ζ ^ M) ^ (Nat.gcdB 4 M) := by
    have hb' : ((4 : ℕ) : ℤ) * Nat.gcdA 4 M + (M : ℤ) * Nat.gcdB 4 M = 1 := by
      exact_mod_cast hb.symm
    rw [← zpow_natCast ζ 4, ← zpow_natCast ζ M, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, hb',
      zpow_one]
  show σ (σ ζ) = ζ
  rw [hdec, map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀, map_zpow₀, hz, hy, hy]

/-- At `p = 2`, the cyclotomic character mod `N ∣ 4M` (`M` odd) kills `decomp(σ²)` for inertia
`σ` (proved; as `cyc_decomp_wild`). -/
theorem cyc_decomp_sq_inertia (hp2 : p = 2) {σ : GQp p} (hσ : σ ∈ inertiaSet) {N M : ℕ}
    [NeZero N] (hM : ¬ 2 ∣ M) (hNM : N ∣ 4 * M) :
    GlueDescent.B2Q.cyc N (decomp p (σ * σ)) = 1 := by
  by_cases hN1 : N = 1
  · subst hN1; exact Subsingleton.elim _ _
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  haveI : Fact (1 < N) := ⟨by omega⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  apply Units.ext
  obtain ⟨k, hk⟩ := hNM
  have hu := modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
    (GlueDescent.B2Q.toRingAut (decomp p (σ * σ))) (c := 1) (fun t ht => by
      rw [ZMod.val_one, pow_one]
      have htN : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ N = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N t).mp ht, Units.val_one]
      exact decomp_sq_fix_root hp2 hσ hM (by rw [hk, pow_mul, htN, one_pow]))
  have hc : GlueDescent.B2Q.cyc N (decomp p (σ * σ)) = modularCyclotomicCharacter
      (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
      (GlueDescent.B2Q.toRingAut (decomp p (σ * σ))) := rfl
  rw [hc, Units.val_one]
  exact hu.symm

/-- **`Beta4Inertia` at `p = 2` from G7's clauses (proved).** `β⁴ = ι(χ(cyc_N σ))² =
ι(χ(cyc_N σ²))`, and `cyc_N(σ²) = 1` (`cyc_decomp_sq_inertia`, `chiLevel_dvd_four_mul_odd`). -/
theorem beta4Inertia_of_clauses (hp2 : p = 2) {β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) : Beta4Inertia (p := p) β L := by
  intro σ hσ
  obtain ⟨Tmin, hTmin, hNZ, χ, ι, hβχ⟩ := hC.2.2.2.2.2.1
  obtain ⟨M, hM, hNM⟩ := chiLevel_dvd_four_mul_odd hTmin
  have hc := cyc_decomp_sq_inertia hp2 hσ.2 hM hNM
  have h2 : (GlueDescent.B2Q.galChar χ (decomp p σ)) ^ 2 = 1 := by
    have hd : (GlueDescent.B2Q.galChar χ) (decomp p (σ * σ)) = 1 := by
      change χ.toUnitHom (GlueDescent.B2Q.cyc _ (decomp p (σ * σ))) = 1
      rw [hc, map_one]
    have hm := map_mul (GlueDescent.B2Q.galChar χ) (decomp p σ) (decomp p σ)
    rw [sq]
    refine hm.symm.trans ?_
    refine Eq.trans ?_ hd
    exact congrArg (⇑(GlueDescent.B2Q.galChar χ)) (map_mul (decomp p) σ σ).symm
  calc β (decomp p σ) ^ 4 = (β (decomp p σ) ^ 2) ^ 2 := by ring
    _ = ((ι (GlueDescent.B2Q.galChar χ (decomp p σ)) : PadicAlgCl ℓ)) ^ 2 := by rw [hβχ]
    _ = ((ι (GlueDescent.B2Q.galChar χ (decomp p σ) ^ 2) : PadicAlgCl ℓ)) := by
        rw [map_pow, Units.val_pow_eq_pow_val]
    _ = 1 := by rw [h2, map_one, Units.val_one]

/-- **`BetaTwist2` at `p = 2` from G7's clauses and the textbook Prop `UnramRoots` (proved).** -/
theorem betaTwist2_of_unramRoots (hp2 : p = 2) {β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hU : UnramRoots p ℓ) : BetaTwist2 (p := p) β L :=
  betaTwist2_of_roots hC hU (beta4Inertia_of_clauses hp2 hC)

variable {K : Type} [Field K] [NumberField K]

/-- **`LocalGlue p Tm a β L` on G7's data (proved)** from the leaves R6 and I2-Tors, the textbook
Prop `UnramRoots` (used at `p = 2`), and the glue `KerWild` (all `p`) and `DescentPts` (`p ≤ 5`). -/
theorem localGlue_of_unramRoots (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU : UnramRoots p ℓ) (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    [FiniteDimensional ℚ L] (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hD : p ≤ 5 → DescentPts A L) : LocalGlue (p := p) Tm a β L :=
  localGlue_of_descent hR6 hTors hpℓ h7 hC hK hD (fun h2 => betaTwist2_of_unramRoots h2 hC hU)

end TwistSec

end G15Ram

end


/-! ## §7f (local-glue). `DescentPts` for a base change (proved)

For `L ≤ L'` finite inside `ℚ̄`, `L/ℚ` Galois, and `A₀ : AbVar L` of dimension `2`,
`DescentPts (A₀)_{L'} L` holds (`descentPts_baseChange`), with `(A₀)_{L'}` the base change along
g0-mod-field's `incAlg` (as in g0-assemble's `TateBridge`). The model is the conjugate
`A₁ = A₀ ×_{L,γ} L`, where `γ ∈ Aut(L)` corrects the difference between the embeddings `L ↪ ℚ̄`
that Mathlib chooses inside `resQ L` and inside `resQ L'` (`jL L`, `jL' hLL'`; both have image
`L` since `L/ℚ` is normal). Points: `A₁(L̄) ≅ A₀(L̄_tw) ≅ A₀(L̄') ≅ (A₀)_{L'}(L̄')` by `bcPt`,
`trPt` along `θ = qEmb_{L'} ∘ qEmb_L⁻¹` (`L`-linear for the twisted structure `tw`), and `bcPt`. -/

noncomputable section

namespace G15Ram

open PkgI4 (GQ)
open CategoryTheory AlgebraicGeometry Limits MonObj

section BCDescentSec

attribute [local instance] RQ.numberField_of_fd

/-- `qEmb K` as a ring isomorphism `ℚ̄ ≃ K̄`. -/
def qEquiv (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
  RingEquiv.ofBijective (G0Galois.qEmbRing K)
    ⟨(G0Galois.qEmbRing K).injective, qEmbRing_surjective K⟩

theorem qEquiv_apply (K : Type) [Field K] [NumberField K] (x : AlgebraicClosure ℚ) :
    qEquiv K x = G0Galois.qEmbRing K x := rfl

/-- The embedding `K ↪ ℚ̄` inside `resQ K`. -/
def jK (K : Type) [Field K] [NumberField K] : K →ₐ[ℚ] AlgebraicClosure ℚ :=
  ((qEquiv K).symm.toRingHom.comp (algebraMap K (AlgebraicClosure K))).toRatAlgHom

theorem qEquiv_jK (K : Type) [Field K] [NumberField K] (x : K) :
    qEquiv K (jK K x) = algebraMap K (AlgebraicClosure K) x := by
  show qEquiv K ((qEquiv K).symm _) = _
  exact (qEquiv K).apply_symm_apply _

variable {L L' : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L]
  [FiniteDimensional ℚ L'] (hLL' : L ≤ L')

/-- The embedding `L ↪ L' ↪ ℚ̄` inside `resQ L'`. -/
def jL' : L →ₐ[ℚ] AlgebraicClosure ℚ := (jK L').comp (IntermediateField.inclusion hLL')

variable [IsGalois ℚ L]

theorem mem_range_jK (x : L) : jL' hLL' x ∈ (jK L).fieldRange := by
  have h1 := AlgHom.fieldRange_of_normal (jK L)
  have h2 := AlgHom.fieldRange_of_normal (jL' hLL')
  have hx : jL' hLL' x ∈ (jL' hLL').fieldRange := ⟨x, rfl⟩
  rw [h2] at hx
  rw [h1]
  exact hx

/-- `γ = jK_L⁻¹ ∘ jL'`, a ring endomorphism of `L`. -/
def γL : L →+* L :=
  (AlgEquiv.ofInjectiveField (jK L)).symm.toRingEquiv.toRingHom.comp
    ((jL' hLL').toRingHom.codRestrict (jK L).fieldRange (mem_range_jK hLL'))

theorem jK_γL (x : L) : jK L (γL hLL' x) = jL' hLL' x := by
  have h := congrArg Subtype.val
    ((AlgEquiv.ofInjectiveField (jK L)).apply_symm_apply ⟨jL' hLL' x, mem_range_jK hLL' x⟩)
  exact h

theorem γL_bijective : Function.Bijective (γL hLL') := by
  have hinj : Function.Injective (γL hLL') := (γL hLL').injective
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective
    (f := (γL hLL').toRatAlgHom.toLinearMap)).mp hinj

/-- g0-mod-field's `incAlg` (`L → L'`). -/
@[instance_reducible] def incAlgL : Algebra L L' := (IntermediateField.inclusion hLL').toRingHom.toAlgebra

/-- The `L`-algebra structure on `L` through `γ`. -/
@[instance_reducible] def γAlg : Algebra L L := (γL hLL').toAlgebra

/-- The twisted `L`-algebra structure on `L̄`: `x ↦ qEmb_L (jL' x)`. -/
@[instance_reducible] def twAlg : Algebra L (AlgebraicClosure L) :=
  ((qEquiv L).toRingHom.comp (jL' hLL').toRingHom).toAlgebra

/-- The `L`-algebra structure on `L̄'` through `L ⊆ L'`. -/
@[instance_reducible] def compAlg : Algebra L (AlgebraicClosure L') :=
  ((algebraMap L' (AlgebraicClosure L')).comp (IntermediateField.inclusion hLL').toRingHom).toAlgebra

theorem tower_tw : @IsScalarTower L L (AlgebraicClosure L) (γAlg hLL').toSMul
    Algebra.toSMul (twAlg hLL').toSMul :=
  @IsScalarTower.of_algebraMap_eq L L (AlgebraicClosure L) _ _ _ (γAlg hLL') _ (twAlg hLL')
    (fun x => by
      show qEquiv L (jL' hLL' x) = algebraMap L (AlgebraicClosure L) (γL hLL' x)
      rw [← qEquiv_jK, jK_γL])

theorem tower_comp : @IsScalarTower L L' (AlgebraicClosure L') (incAlgL hLL').toSMul
    Algebra.toSMul (compAlg hLL').toSMul :=
  @IsScalarTower.of_algebraMap_eq L L' (AlgebraicClosure L') _ _ _ (incAlgL hLL') _ (compAlg hLL')
    (fun x => rfl)

/-- `θ = qEmb_{L'} ∘ qEmb_L⁻¹ : L̄_tw ≃ L̄'`, `L`-linear. -/
def θL : @AlgEquiv L (AlgebraicClosure L) (AlgebraicClosure L') _ _ _ (twAlg hLL')
    (compAlg hLL') :=
  @AlgEquiv.ofRingEquiv L (AlgebraicClosure L) (AlgebraicClosure L') _ _ _ (twAlg hLL')
    (compAlg hLL') ((qEquiv L).symm.trans (qEquiv L')) (fun x => by
      show qEquiv L' ((qEquiv L).symm (qEquiv L (jL' hLL' x))) =
        algebraMap L' (AlgebraicClosure L') (IntermediateField.inclusion hLL' x)
      rw [RingEquiv.symm_apply_apply]
      exact qEquiv_jK L' _)

theorem θL_apply (x : AlgebraicClosure L) : θL hLL' x = qEquiv L' ((qEquiv L).symm x) := rfl

/-- `θ σ₀ = σ' θ` when `resQ_L σ₀ = resQ_{L'} σ'`. -/
theorem θL_galois (σ₀ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L')
    (h : G0Galois.resQ L σ₀ = G0Galois.resQ L' σ') (x : AlgebraicClosure L) :
    σ' (θL hLL' x) = θL hLL' (σ₀ x) := by
  obtain ⟨y, rfl⟩ := (qEquiv L).surjective x
  have hθ : ∀ z, θL hLL' (qEquiv L z) = qEquiv L' z := fun z => by
    rw [θL_apply, RingEquiv.symm_apply_apply]
  have h1 := G0Galois.resQ_spec L σ₀ y
  have h2 := G0Galois.resQ_spec L' σ' y
  calc σ' (θL hLL' (qEquiv L y)) = σ' (qEquiv L' y) := by rw [hθ]
    _ = qEquiv L' (G0Galois.resQ L' σ' y) := h2.symm
    _ = qEquiv L' (G0Galois.resQ L σ₀ y) :=
        congrArg (fun g : GQ => qEquiv L' (g y)) h.symm
    _ = θL hLL' (qEquiv L (G0Galois.resQ L σ₀ y)) := (hθ _).symm
    _ = θL hLL' (σ₀ (qEquiv L y)) := congrArg (θL hLL') h1

/-- The conjugate model `A₁ = A₀ ×_{L,γ} L`. -/
abbrev conjModel (A₀ : PkgI3.AbVar L) : PkgI3.AbVar L :=
  @PkgI3.AbVar.baseChange L _ A₀ L _ (γAlg hLL')

/-- The base change `(A₀)_{L'}` along `incAlg` (as in `TateBridge`). -/
abbrev bcL' (A₀ : PkgI3.AbVar L) : PkgI3.AbVar L' :=
  @PkgI3.AbVar.baseChange L _ A₀ L' _ (incAlgL hLL')

/-- `φ : A₁(L̄) ≅ A₀(L̄_tw) ≅ A₀(L̄') ≅ (A₀)_{L'}(L̄')`. -/
def φL (A₀ : PkgI3.AbVar L) :
    (conjModel hLL' A₀).Pt (AlgebraicClosure L) ≃* (bcL' hLL' A₀).Pt (AlgebraicClosure L') :=
  ((@UnramTate.bcPt L L _ _ (γAlg hLL') A₀ (AlgebraicClosure L) _ _ (twAlg hLL')
      (tower_tw hLL')).trans
    (@UnramTate.trPt L _ A₀ (AlgebraicClosure L) (AlgebraicClosure L') _ (twAlg hLL') _
      (compAlg hLL') (θL hLL'))).trans
    (@UnramTate.bcPt L L' _ _ (incAlgL hLL') A₀ (AlgebraicClosure L') _ _ (compAlg hLL')
      (tower_comp hLL')).symm

/-- `φ` intertwines `σ₀ ∈ G_L` and `σ' ∈ G_{L'}` with the same image in `G_ℚ` (proved). -/
theorem φL_galAct (A₀ : PkgI3.AbVar L) (σ₀ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L')
    (h : G0Galois.resQ L σ₀ = G0Galois.resQ L' σ')
    (P : (conjModel hLL' A₀).Pt (AlgebraicClosure L)) :
    φL hLL' A₀ ((conjModel hLL' A₀).galAct σ₀ P) =
      (bcL' hLL' A₀).galAct σ' (φL hLL' A₀ P) := by
  set b₁ := @UnramTate.bcPt L L _ _ (γAlg hLL') A₀ (AlgebraicClosure L) _ _ (twAlg hLL')
      (tower_tw hLL') with hb₁
  set t := @UnramTate.trPt L _ A₀ (AlgebraicClosure L) (AlgebraicClosure L') _ (twAlg hLL') _
      (compAlg hLL') (θL hLL') with ht
  set b₂ := @UnramTate.bcPt L L' _ _ (incAlgL hLL') A₀ (AlgebraicClosure L') _ _ (compAlg hLL')
      (tower_comp hLL') with hb₂
  have e1 := @UnramTate.bcPt_galAct L L _ _ (γAlg hLL') A₀ (AlgebraicClosure L) _ _
    (twAlg hLL') (tower_tw hLL') σ₀ P
  have e3 := @UnramTate.bcPt_galAct L L' _ _ (incAlgL hLL') A₀ (AlgebraicClosure L') _ _
    (compAlg hLL') (tower_comp hLL') σ' (b₂.symm (t (b₁ P)))
  show b₂.symm (t (b₁ ((conjModel hLL' A₀).galAct σ₀ P))) =
    (bcL' hLL' A₀).galAct σ' (b₂.symm (t (b₁ P)))
  apply b₂.injective
  rw [MulEquiv.apply_symm_apply, e3, MulEquiv.apply_symm_apply]
  erw [e1]
  exact @UnramTate.trPt_galAct L _ A₀ (AlgebraicClosure L) (AlgebraicClosure L') _ (twAlg hLL') _
    (compAlg hLL') (θL hLL') _ _ (fun x => θL_galois hLL' σ₀ σ' h x) (b₁ P)

/-- The conjugate model has the dimension of `A₀` (proved): base change along the isomorphism
`Spec γ` is homeomorphic to `A₀`. -/
theorem dim_conjModel (A₀ : PkgI3.AbVar L) : (conjModel hLL' A₀).dim = A₀.dim := by
  let e : L ≃+* L := RingEquiv.ofBijective (γL hLL') (γL_bijective hLL')
  have hiso : IsIso (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL'))) :=
    e.toCommRingCatIso.isIso_hom
  have hiso2 : IsIso (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL')))) :=
    inferInstance
  have hiso3 : IsIso (pullback.fst (C := Scheme) A₀.X.hom
      (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL'))))) := inferInstance
  show topologicalKrullDim (pullback (C := Scheme) A₀.X.hom
      (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL'))))) =
    topologicalKrullDim A₀.X.left
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.Hom.homeomorph (pullback.fst (C := Scheme) A₀.X.hom
      (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL')))))).isHomeomorph

/-- **`DescentPts` for a base change (proved).** For `L ≤ L'` finite in `ℚ̄`, `L/ℚ` Galois, and
`A₀ : AbVar L` with `dim A₀ = 2`, `DescentPts ((A₀)_{L'}) L` holds for G7Out's model field
`K = L'`, with the conjugate model `A₀ ×_{L,γ} L`. -/
theorem descentPts_baseChange (A₀ : PkgI3.AbVar L) (hdim : A₀.dim = 2) :
    DescentPts (K := L') (bcL' hLL' A₀) L :=
  ⟨inferInstance, conjModel hLL' A₀, φL hLL' A₀, (dim_conjModel hLL' A₀).trans hdim,
    fun σ₀ σ' h P => φL_galAct hLL' A₀ σ₀ σ' h P⟩

/-- **`LocalGlue` on G7's construction (proved).** For g0-mod-field's data: `L ≤ L'` finite
Galois in `ℚ̄`, `A₀ : AbVar L` with `dim A₀ = 2`, G7Out for `(A₀)_{L'}` over `K = L'`, G7's clauses,
the kernel-field clause `G_{L'} = G_L ∩ ker β_ℂ`, and the transport `β = ι ∘ β_ℂ` with `ι`
injective, `LocalGlue p Tm a β L` holds at every `p ≠ ℓ`, from the leaves R6 and I2-Tors and the
textbook Prop `UnramRoots` (used at `p = 2`). -/
theorem localGlue_of_baseChange {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : UnramRoots p ℓ) (hpℓ : p ≠ ℓ) [IsGalois ℚ L'] (A₀ : PkgI3.AbVar L)
    (hdim₀ : A₀.dim = 2)
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb (bcL' hLL' A₀) ℓ)}
    {c ε : GQ → GQ → PadicAlgCl ℓ} {a β : GQ → PadicAlgCl ℓ}
    {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb (bcL' hLL' A₀) ℓ)}
    (h7 : G0Galois.G7Out (bcL' hLL' A₀) ℓ Tm c ε a β u) (hC : G7Clauses β ε L)
    (βC : GQ → ℂˣ) (hker : ∀ σ : GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (ιC : ℂˣ →* (PadicAlgCl ℓ)ˣ) (hι : Function.Injective ιC)
    (hβ : ∀ g, β g = (ιC (βC g) : PadicAlgCl ℓ)) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_unramRoots hR6 hTors hU hpℓ h7 hC (kerWild_of_g7Data βC hker ιC hι hβ)
    (fun _ => descentPts_baseChange hLL' A₀ hdim₀)

end BCDescentSec


end G15Ram

end


noncomputable section

/-! ## §8 (local-glue). The packs: G8's data with the local glue replaced by Props on `A/K`

`G8LocalPack` is copied verbatim from scratch/local-data/tail_part.lean (the hypothesis of
local-data's tail `modularConstituent_tail_L`). `G7LocalPackK` asks instead for G7's data
(`G7Out`), G8's output, the clauses, `KerWild`, and the torsion-point Props `TorsFixWild`
(`p ≥ 7`), `TorsFixWildE` (`p ≤ 5`) and `BetaUpper` (`p = 2`) at the primes in `P`. -/

namespace G0ModNewform

open PkgI4 (Qbar GQ GaloisRep)
open PkgI3

attribute [local instance] RQ.numberField_of_fd

-- BEGIN verbatim copy (scratch/local-data/tail_part.lean)
/-- **G8's data for a representation `r` at coefficient prime `ℓ`, with the G4/G7 clauses and
the local glue at the primes `p ∈ P`** (`G15Ram.G7Clauses`, `G15Ram.LocalGlue`). -/
def G8LocalPack (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (a β : GQ → PadicAlgCl ℓ)
    (ε : GQ → GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ Qbar),
    G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧ G15Ram.G7Clauses β ε L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p → @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a β L

-- END verbatim copy

/-- **G7's data for `r` at coefficient prime `ℓ`, with the local glue at `p ∈ P` as Props on the
abelian surface `A/K` (GLUE).** -/
def G7LocalPackK (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (7 ≤ p → @G15Ram.TorsFixWild p ⟨hp⟩ K _ _ A ℓ _) ∧
      (p ≤ 5 → @G15Ram.TorsFixWildE p ⟨hp⟩ K _ _ A ℓ _ β L) ∧
      (p = 2 → @G15Ram.BetaUpper p ⟨hp⟩ ℓ _ β (@G15Ram.Lv p ⟨hp⟩ L) U0)

/-- **`G8LocalPack` from `G7LocalPackK` (proved)**, by `G15Ram.localGlue_of_g7`. -/
theorem g8LocalPack_of_K {ℓ : ℕ} [Fact ℓ.Prime] {r : GaloisRep ℓ 2} {P : ℕ → Prop}
    (h : G7LocalPackK ℓ r P) : G8LocalPack ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, a, β, ε, L, h8, hC, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hW, hE, hB⟩ := hloc p hp hP
  exact G15Ram.localGlue_of_g7 h7 hC hK (fun h => G15Ram.tateWildK_of_torsFixWild (hW h))
    (fun h => G15Ram.tateWildKE_of_torsFixWildE (hE h)) hB

/-- **G15's open Prop `G15RamG` from the packs (proved)**: g15-ram's `G15RamG D u` follows from
G7's data for `D.r5` (local glue at `p ≠ 5`) and for `D.r3` (at `p = 5`), and G11's outputs. -/
theorem g15RamG_of_packK {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A)
    (u : ℚ) (h5 : G7LocalPackK 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackK 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ := g8LocalPack_of_K h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ := g8LocalPack_of_K h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

/-- **G7's data for `r` with the local glue at `p ∈ P` in leaf form (GLUE).**
At `p ≥ 7` nothing: the local glue there follows from the leaves R6 and I2-Tors
(`G15Ram.raynaudPlace_of_R6`, `G15Ram.ptFinite`); at
`p ∈ {3, 5}`: `TorsFixWildOdd`; at `p = 2`: `TorsFixWildE` and `BetaTwist2` (which replaces
`BetaUpper`, `G15Ram.betaUpper_of_twist`). With the leaves R6 and
I2-Tors and `p ≠ ℓ` on `P`, it gives `G7LocalPackK` (`g7LocalPackK_of_R`). -/
def G7LocalPackR (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (3 ≤ p → p ≤ 5 → @G15Ram.TorsFixWildOdd p ⟨hp⟩ K _ _ A ℓ _ L) ∧
      (p = 2 → @G15Ram.TorsFixWildE p ⟨hp⟩ K _ _ A ℓ _ β L ∧ @G15Ram.BetaTwist2 p ⟨hp⟩ ℓ _ β L)

/-- **`G7LocalPackK` from `G7LocalPackR`, the leaf I2-Tors and `p ≠ ℓ` on `P` (proved).** -/
theorem g7LocalPackK_of_R (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackR ℓ r P) :
    G7LocalPackK ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hO, h2⟩ := hloc p hp hP
  refine ⟨fun h7p => ?_, fun h5 => ?_, fun h2' => G15Ram.betaUpper_of_twist hC (h2 h2').2⟩
  · exact G15Ram.torsFixWild_of_raynaud (Ne.symm (hPℓ p hP)) h7p
      (G15Ram.wildIter A) (G15Ram.torsGL_of_leaf hTors A h7.1 3 (by norm_num))
      (G15Ram.torsGL_of_leaf hTors A h7.1 7 (by norm_num))
      (fun _ => G15Ram.raynaudPlace_of_R6 hR6 hTors A h7.1 (by norm_num)
        (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
      (fun h13 => G15Ram.raynaudPlace_of_R6 hR6 hTors A h7.1 (by norm_num)
        (by rw [h13]; norm_num))
  · by_cases hp2 : p = 2
    · exact (h2 hp2).1
    · have h3 : 3 ≤ p := by have := hp.two_le; omega
      exact G15Ram.torsFixWildE_of_odd hp2 hC (hO h3 h5)

/-- **`G15RamG` from the leaf-and-bridge packs and I2-Tors (proved).** -/
theorem g15RamG_of_packR (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {L : Type} [Field L]
    [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackR 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackR 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u :=
  g15RamG_of_packK D u (g7LocalPackK_of_R hR6 hTors (fun _ h => h) h5)
    (g7LocalPackK_of_R hR6 hTors (fun p h => by rw [h]; norm_num) h3) h11₅ h11₃

/-- **G7's data for `r` with the local glue at `p ∈ P` as the glue Props of §7d (GLUE).**
`KerWild` (G7Data's kernel-field clause), and at the primes `p ∈ P`: `DescentPts A L` (the model
of `A` over `L`) when `p ≤ 5`, `BetaTwist2` when `p = 2`. Nothing at `p ≥ 7`. With the leaves R6,
I2-Tors and `p ≠ ℓ` on `P` it gives `G8LocalPack` (`g8LocalPack_of_D`). -/
def G7LocalPackD (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (p ≤ 5 → G15Ram.DescentPts A L) ∧ (p = 2 → @G15Ram.BetaTwist2 p ⟨hp⟩ ℓ _ β L)

/-- **`G8LocalPack` from `G7LocalPackD`, the leaves R6 and I2-Tors, and `p ≠ ℓ` on `P` (proved)**,
by `G15Ram.localGlue_of_descent`. -/
theorem g8LocalPack_of_D (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackD ℓ r P) :
    G8LocalPack ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, _, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, a, β, ε, L, h8, hC, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hD, hB⟩ := hloc p hp hP
  exact G15Ram.localGlue_of_descent hR6 hTors (hPℓ p hP) h7 hC hK hD hB

/-- **`G15RamG` from the descent packs and the leaves R6, I2-Tors (proved).** -/
theorem g15RamG_of_packD (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {L : Type} [Field L]
    [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackD 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackD 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ :=
    g8LocalPack_of_D hR6 hTors (fun _ h => h) h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ :=
    g8LocalPack_of_D hR6 hTors (fun p h => by rw [h]; norm_num) h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

/-- **G7's data for `r` with the local glue at `p ∈ P` reduced to two glue Props (GLUE).**
`KerWild` (G7Data's kernel-field clause) and, when some `p ∈ P` has `p ≤ 5`, `DescentPts A L`
(the model of `A` over `L`). At `p = 2` the twist is supplied by the textbook Prop
`G15Ram.UnramRoots` (`g8LocalPack_of_U`). -/
def G7LocalPackU (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ((∃ p, P p ∧ p.Prime ∧ p ≤ 5) → G15Ram.DescentPts A L)

/-- **`G8LocalPack` from `G7LocalPackU`, the leaves R6, I2-Tors, the textbook Prop `UnramRoots`
at `p = 2`, and `p ≠ ℓ` on `P` (proved)**, by `G15Ram.localGlue_of_unramRoots`. -/
theorem g8LocalPack_of_U (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : ∀ (hp : Nat.Prime 2), @G15Ram.UnramRoots 2 ⟨hp⟩ ℓ _)
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackU ℓ r P) :
    G8LocalPack ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, _, h7, h8, hC, hK, hD⟩ := h
  refine ⟨K, _, _, A, Tm, a, β, ε, L, h8, hC, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  refine G15Ram.localGlue_of_descent hR6 hTors (hPℓ p hP) h7 hC hK
    (fun h5 => hD ⟨p, hP, hp, h5⟩) (fun h2 => ?_)
  subst h2
  exact G15Ram.betaTwist2_of_unramRoots rfl hC (hU hp)

/-- **`G15RamG` from the packs `G7LocalPackU` (proved).** -/
theorem g15RamG_of_packU (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU2 : ∀ (hp : Nat.Prime 2) (ℓ : ℕ) [Fact ℓ.Prime],
      @G15Ram.UnramRoots 2 ⟨hp⟩ ℓ _) {L : Type} [Field L]
    [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackU 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackU 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ :=
    g8LocalPack_of_U hR6 hTors (fun hp => hU2 hp 5) (fun _ h => h) h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ :=
    g8LocalPack_of_U hR6 hTors (fun hp => hU2 hp 3) (fun p h => by rw [h]; norm_num) h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

/-- **G7's data for `r` in the form of g0-mod-field's construction (GLUE: the output of an
augmented `TateBridge`).** `L ≤ L'` finite Galois in `ℚ̄`, `A₀ : AbVar L` with `dim A₀ = 2`,
G7Out and G8Out for `(A₀)_{L'}` (base change along `incAlg`), G7's clauses, the kernel-field
clause `G_{L'} = G_L ∩ ker β_ℂ` of `G7Data`, and the transport `β = ι ∘ β_ℂ` with `ι` injective.
No local Prop is asked at any prime (`g8LocalPack_of_BC`). -/
def G7LocalPackBC (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) : Prop :=
  ∃ (L L' : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L) (_ : FiniteDimensional ℚ L')
    (_ : IsGalois ℚ L) (_ : IsGalois ℚ L') (hLL' : L ≤ L') (A₀ : AbVar L)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb (G15Ram.bcL' hLL' A₀) ℓ))
    (c ε : GQ → GQ → PadicAlgCl ℓ) (a β : GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb (G15Ram.bcL' hLL' A₀) ℓ))
    (βC : GQ → ℂˣ) (ιC : ℂˣ →* (PadicAlgCl ℓ)ˣ),
    A₀.dim = 2 ∧ G0Galois.G7Out (G15Ram.bcL' hLL' A₀) ℓ Tm c ε a β u ∧
    G0Galois.G8Out (G15Ram.bcL' hLL' A₀) ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧
    (∀ σ : GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1) ∧
    Function.Injective ιC ∧ (∀ g, β g = (ιC (βC g) : PadicAlgCl ℓ))

/-- **`G8LocalPack` from `G7LocalPackBC`, the leaves R6, I2-Tors and the textbook Prop
`UnramRoots` (at `p = 2`), for `p ≠ ℓ` on `P` (proved)**, by `G15Ram.localGlue_of_baseChange`. -/
theorem g8LocalPack_of_BC (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : ∀ (p : ℕ) [Fact p.Prime], G15Ram.UnramRoots p ℓ)
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackBC ℓ r) :
    G8LocalPack ℓ r P := by
  obtain ⟨L, L', _, _, _, _, hLL', A₀, Tm, c, ε, a, β, u, βC, ιC, hdim, h7, h8, hC, hker, hι,
    hβ⟩ := h
  refine ⟨L', _, RQ.numberField_of_fd L', G15Ram.bcL' hLL' A₀, Tm, a, β, ε, L, h8, hC,
    fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  exact G15Ram.localGlue_of_baseChange hLL' hR6 hTors (hU p) (hPℓ p hP) A₀ hdim h7 hC βC hker ιC
    hι hβ

/-- **`G15RamG` from the packs `G7LocalPackBC` (proved).** -/
theorem g15RamG_of_packBC (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ) {L : Type}
    [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackBC 5 D.r5) (h3 : G7LocalPackBC 3 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ :=
    g8LocalPack_of_BC (P := fun p => p ≠ 5) hR6 hTors (fun p _ => hU p 5) (fun _ h => h) h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ :=
    g8LocalPack_of_BC (P := fun p => p = 5) hR6 hTors (fun p _ => hU p 3)
      (fun p h => by rw [h]; norm_num) h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

end G0ModNewform

end

-- END verbatim body of scratch/local-glue/LocalGlue.lean
end

section FrobTraceSec
-- BEGIN verbatim body of scratch/frob-trace/FrobTrace.lean (minus l.1632-1754, see build.sh)

/-!
# g0-mod-field: glue steps G2, G4, G7 of the H decomposition (first range of `ModularConstituent`)

Task g0-mod-field (2026-11-13). `ModularConstituent` (scratch/g0-split/Split.lean, piece 10)
covers G2, G4, G7-G16 of docs/research/h-decomposition.md §3. This file takes the range
G2 (fibre field `K`), G4 (Hom field `L`, `[L:ℚ] ≤ D`), G7 (scalar descent to `L'`,
`[L':ℚ] ≤ Q·M`), for `S = S_mul`, `R = D` (the instance `SixContactMin`).

Outputs (`def … : Prop`): `G2Out Y Φ u P` (with `RationalFibre`), `G4Out u P`, `G7Out u P`, and the clause list `G7Data`
with `G7OutUnr u P` (G7 with the twist: `L'` unramified outside `T`), for a `ℚ̄`-object `P` of
`Y₃` over `J(u)` (`FibreCtx`). The descent datum of B1 on the actual `A` is `DescentDatum`
(maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)`, `a_σ`, sign cocycle `ε`).

Proved (no `sorry`, standard axioms):
* `g2Out_of_cover`: G2's bookkeeping (a splitting field of a separable polynomial of degree
  `≤ 324` is Galois of degree `≤ 324!`).
* `descentDatum_of_conjugacy`: B1's normalization (N5 L645-663): conjugacy isogenies with
  rational discrepancy `c` give `a_σ = |ker m_σ|^{-1/4}` and the sign cocycle `ε = sgn c`.
* `g4Out_of_kernelField`: G4's bookkeeping (Hom field `L = E ⊔ K` Galois,
  `[L:ℚ] ≤ F₀·3^{r²} ≤ D` by Minkowski's bound, model by base change, B1).
* `g7Out_of_g4Out`, `g7OutUnr_of_g4Out`: G7 = B2-B3 on the actual descent datum
  (`b2_of_leaves`, `GlueB3Unram.unramified_outside_noLeaf`, `b3_of_cochain`, `degree_le_QM`) and the
  model over `L'` (`isModelOver_baseChange`, transitivity of base change).
* `fieldDescent`, `fieldDescentUnr`: the composite G2 → G4 → G7.
* `modularConstituent_of_ranges`: `ModularConstituentG` (part_split's `ModularConstituent` over
  `PkgI3.AbVar`) from this range and the next ranges bundled as `AfterG7`.

Remaining (named Props): `FibreCoverExists` (G2: Prop. TS + Lemma NV), `KernelFieldExists` (G4:
Weil restriction, Galois image in `GL_r(ℤ)`, inertia on the Tate module, the conjugacy isogenies
`ConjugacyData`), `UnramifiedSup` (compositum of unramified fields; STANDARD), the four B2 leaves
of glue-descent (`LeafHasse`, `LeafLocalTwo`, `LeafSqrtCrit`, `LeafUnramified`), and `AfterG7`
(G8-G16, the other two tasks).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField

/-! ## The outputs of G2, G4, G7 -/

/-! ## B1's normalization (proved): from conjugacy isogenies to the sign cocycle -/

/-! ## Sanity check: `DescentDatum` is satisfiable (an abelian variety over `ℚ`, `ε = 1`) -/

/-! ## Transitivity of base change -/

/-! ## G7 from G4 (proved) -/

/-! ## G7 with the twist: `L'` unramified outside `T` (proved) -/

/-! ## G2's bookkeeping (proved) -/

/-! ## G4's bookkeeping (proved) -/

/-! ## The remaining glue as Props, and the composite -/

/-! ## How G7's output feeds `ModularConstituent` -/

/-! ## Feeding g0-mod-galois' inputs (G8-G12): their `G2Out`, `G7Out` -/

namespace GaloisCopy
/-! Copied from scratch/g0-mod-galois/part_galois.lean (branch wip/g0-mod-galois at 20fa1287),
definitions `resQ`, `Vb`, `tate`, `G2Out`, `G7Out`, verbatim (namespace renamed). -/

end GaloisCopy

end G0ModField

/-!
# unram-tate: `TateBridge` reduced to named glue pieces

Everything above `end G0ModField` is `scratch/g0-mod-field/ModField.lean` verbatim (lines 1-1036),
so `G0ModField.TateBridge` is the statement as written there. Below: the operators
`ℚ̄_ℓ ⊗ ℚ_ℓ ⊗ T_ℓ(φ)` (`opV`, a ring homomorphism, proved), the quaternion matrix units
(`matrixUnits_of_quat`, copied from scratch/unram-tate/QuatUnits.lean), five named glue Props, and
the assembly `tateBridge_of_pieces` (proved).
-/

namespace UnramTate

open G0ModField

/-! ## The Tate functor on additive maps of points -/

section Ops

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]

end Ops

/-! ## Matrix units (copied from scratch/unram-tate/QuatUnits.lean, proved there) -/

section Quat

open GlueDescent

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

end Quat

/-! ## The order elements `i`, `j` of `𝒪` -/

/-! ## The named glue pieces -/

/-! ## The assembly -/

/-! ## Proofs of two pieces -/

/-! ## `EndBaseChange` (proof copied from scratch/bp-qmmoduli/QMAbVar.lean L533-557, `endBC`) -/

section BaseChangeEnd

variable {K : Type} [Field K]

end BaseChangeEnd

/-! ## `TatePoints` (generic parts copied from scratch/unram-tate/BCPoints.lean) -/

section BCPoints

open scoped CategoryTheory.Obj


end BCPoints

/-! ## `UnramifiedSup` in this context (proof copied from scratch/unram-tate/UnramSup.lean) -/

section Sup

open NumberField

end Sup

end UnramTate


/-!
# g14-trace, second file: the linked Tate bridge at `ℓ = 3, 5`

Appended to a verbatim copy of `scratch/g0-mod-field/ModField.lean` (g0-mod-field's `G7Data`,
`TateBridge`, `GaloisCopy.G7Out`). `TateBridge` gives the `ℓ`-adic data at each `ℓ` separately
(`∀ ℓ, ∃ Tm c ε' a β' uu, G7Out …`), which does not determine the traces of `r₃` against `r₅`
(g14-trace §1, `g7Out_twist`). `TateBridge35` is the linked form at `ℓ = 3, 5` that
`G14Trace.g12Spec_g14_of_galois` consumes: one pair `a, β : G_ℚ → ℚ̄` mapped to `ℚ̄₅`, `ℚ̄₃` by
embeddings `j₅`, `j₃` (TateBridge's own docstring: "mapped into `ℚ̄_ℓ` by one embedding of the
number field they generate"), and the operators `Tm_ℓ` (from one points-level `m_σ`) in the
Frobenius link at Frobenius elements. No `sorry`, no `axiom`.
-/

noncomputable section

namespace G14Bridge

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField
open GlueC10Link (FrobCompare)

end G14Bridge

end


/-!
# frob-trace: `TateBridge35` and `FrobTraceLink` (g14-trace)

Appended (by `build.sh`) to verbatim copies of `scratch/unram-tate/TateBridge.lean` (which is
`scratch/g0-mod-field/ModField.lean` L1-1036 plus unram-tate's section `UnramTate`) and of
`scratch/g14-trace/part_bridge.lean` (`G14Bridge.FrobTraceLink`, `G14Bridge.TateBridge35`).

Main result: `FrobTrace.tateBridge35_of_algFrobRed (hT : PkgI3.TateModuleFree)
(hR : AlgFrobRed) : G14Bridge.TateBridge35`, through the chain of proved implications
`AlgFrobRed → AlgFrobOne → AlgFrobLink` and `tateBridge35_of_algFrobLink`. The operators are
unram-tate's `Tm_ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` at `ℓ = 5, 3` (one points-level `m`, one `Θ`,
one `h`), the scalars are `aQ g = βQ g / γQ(hgh⁻¹)` and `βQ` with `ιC ∘ βQ = β` in `ℚ̄` (proved,
`scalarsQbar`), and the conjunct `FrobTraceLink` for these operators is derived from the glue
Prop `AlgFrobRed` (one reduction homomorphism `A(ℚ̄) → Ā(k̄)` intertwining `f = F ∘ - ∘ Spec(σ)`
with an endomorphism of the reduction, bijective on prime-to-`p` torsion).
No `sorry`, no `axiom`.
-/

noncomputable section

namespace FrobTrace

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent G0ModField UnramTate

/-! ## The Tate functor on an additive equivalence -/

/-! ## The glue Prop: reduction of the algebraic maps `m_σ` modulo `p` -/

/-! ## `AlgFrobOne` from a reduction homomorphism on points -/

/-! ## From the points-level comparison to `FrobCompare` for `opV(Θ ∘ f ∘ Θ⁻¹)` -/

/-! ## Rescaling the scalars of `G7Out` -/

/-! ## The scalars in `ℚ̄` -/

/-! ## The assembly -/

end FrobTrace

end

-- END verbatim body of scratch/frob-trace/FrobTrace.lean
end FrobTraceSec

section G0DimSec
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
open Order TensorProduct
-- BEGIN verbatim scratch/g0-dim/Dim.lean l.107-305, l.339-344
namespace G0Dim

/-! ## §1. Commutative algebra -/


/-! ## §2. Topology and schemes -/

open TopologicalSpace Topology


open AlgebraicGeometry CategoryTheory Limits

end G0Dim

end G0DimSec

/-! ## lg-kerwild: `KerWild` from G7Data through the Tate bridge, `DescentPts` on G7Data's model

Task lg-kerwild (2026-11-13). local-glue (`G15Ram.localGlue_of_unramRoots`) left two glue Props:
`G15Ram.KerWild K β L` (G7Data's kernel-field clause, dropped by `G7Out` and by g0-mod-field's
`TateBridge`, local-glue finding G8) and `G15Ram.DescentPts A L` (used at `p ≤ 5`).

This part:
* `kerWild_of_ker`: `KerWild L' β L` from G7Data's clause `G_{L'} = G_L ∩ ker β_ℂ` and any
  transport with `β(g) = 1 → β_ℂ(g) = 1`; `kerWild_of_alg` for the transport of g14-trace's
  `TateBridge35` (`β = j ∘ β_ℚ̄`, `β_ℂ = ι_ℂ ∘ β_ℚ̄`, `j`, `ι_ℂ` field embeddings, so injective);
  `kerWild_of_g7Data_alg` reads the clause off `G7Data`.
* `TateBridgeK`: g0-mod-field's `TateBridge` with `KerWild` added to its output (the correction of
  finding G8); `TateBridgeT`: `TateBridge` with the scalar transport added to its output (as
  `TateBridge35` has it); `tateBridgeK_of_T`, `tateBridge_of_K` (proved).
* `TateBridge35K`: g14-trace's `TateBridge35` with `KerWild` at `ℓ = 5, 3` added;
  `tateBridge35K_of_35 : TateBridge35 → TateBridge35K` (proved: the clause is transported from
  `G7Data`, nothing new is assumed); `tateBridgeK_five_three_of_35` (the `ℓ = 5, 3` conclusions
  of `TateBridgeK` from `TateBridge35`).
* `dim_model_of_bc`: `dim A = 2` from `dim A_{L'} = 2` (g0-dim's `pkgI3_dim_baseChange`);
  `descentPts_of_g7` : `DescentPts (A_{L'}) L` for G7Data's model `A/L`.
* `localGlue_of_tateBridge35`: local-glue's `LocalGlue` on `TateBridge35`'s data at `ℓ = 5, 3`
  from R6, I2-Tors, `UnramRoots` and `G7Clauses`, with no `KerWild` or `DescentPts` hypothesis.
-/

section LGKerWildSec

noncomputable section

namespace LGKerWild

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q G0ModField

/-! ### §1. `KerWild` from the kernel-field clause -/

/-- **`KerWild` from G7Data's kernel-field clause and a transport that detects `β = 1`
(proved).** `G_{L'} = G_L ∩ ker β_ℂ` (G7Data, `GQL L = L.fixingSubgroup`), `L'` finite Galois, and
`β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1` give `KerWild L' β_ℓ L` for `G7Out`'s model field `K = L'`. -/
theorem kerWild_of_ker {ℓ : ℕ} [Fact ℓ.Prime] {L L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] (βC : PkgI4.GQ → ℂˣ)
    (hker : ∀ σ : PkgI4.GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    {β : PkgI4.GQ → PadicAlgCl ℓ} (hβ : ∀ g, β g = 1 → βC g = 1) :
    @G15Ram.KerWild ℓ _ L' _ (RQ.numberField_of_fd L') β L := by
  intro g hgL hg1
  have h3 : g ∈ L'.fixingSubgroup :=
    (hker g).mpr ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).mpr hgL, hβ g hg1⟩
  rw [RQ.resQ_range L']
  exact h3

/-- **The algebraic transport detects `β = 1` (proved).** If `β_ℓ = j ∘ β_ℚ̄` and
`β_ℂ = ι_ℂ ∘ β_ℚ̄` for `ℚ`-algebra maps `j : ℚ̄ → ℚ̄_ℓ`, `ι_ℂ : ℚ̄ → ℂ` (injective, `ℚ̄` a field),
then `β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1`. -/
theorem transport_one {ℓ : ℕ} [Fact ℓ.Prime] (βQ : PkgI4.GQ → PkgI4.Qbar)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (βC : PkgI4.GQ → ℂˣ)
    (hC : ∀ g, ιC (βQ g) = (βC g : ℂ)) (g : PkgI4.GQ) (h1 : j (βQ g) = 1) : βC g = 1 := by
  have hQ : βQ g = 1 := j.toRingHom.injective (show j (βQ g) = j 1 by rw [h1, map_one])
  apply Units.ext
  rw [← hC g, hQ, map_one, Units.val_one]

/-- **`KerWild` for the algebraic transport (proved).** -/
theorem kerWild_of_alg {ℓ : ℕ} [Fact ℓ.Prime] {L L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] (βC : PkgI4.GQ → ℂˣ)
    (hker : ∀ σ : PkgI4.GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (βC g : ℂ)) :
    @G15Ram.KerWild ℓ _ L' _ (RQ.numberField_of_fd L') (fun g => j (βQ g)) L :=
  kerWild_of_ker βC hker (fun g h1 => transport_one βQ j ιC βC hC g h1)

/-- G7Data's kernel-field clause (clause 9), as an equality of fixing subgroups. -/
theorem g7Data_ker {u : ℚ} {P : QML3 Qbar} {L : IF} {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ}
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} {hLL' : L ≤ L'}
    (h : G7Data u P L A ε N χ β L' hLL') :
    ∀ σ : PkgI4.GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ β σ = 1 :=
  h.2.2.2.2.2.2.2.2.1

/-- **`KerWild` transported from `G7Data` (proved).** For G7's data and an algebraic form `β_ℚ̄`
of its `β` (`ι_ℂ ∘ β_ℚ̄ = β`), every `j : ℚ̄ → ℚ̄_ℓ` gives `KerWild L' (j ∘ β_ℚ̄) L`. -/
theorem kerWild_of_g7Data_alg {ℓ : ℕ} [Fact ℓ.Prime] {u : ℚ} {P : QML3 Qbar} {L : IF}
    {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L'] [IsGalois ℚ L'] {hLL' : L ≤ L'}
    (h : G7Data u P L A ε N χ β L' hLL') (βQ : PkgI4.GQ → PkgI4.Qbar)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (hC : ∀ g, ιC (βQ g) = (β g : ℂ)) :
    @G15Ram.KerWild ℓ _ L' _ (RQ.numberField_of_fd L') (fun g => j (βQ g)) L :=
  kerWild_of_alg β (g7Data_ker h) βQ j ιC hC

/-! ### §2. The corrected bridges -/

/-- **Bridge 2 with the kernel-field clause (GLUE; correction of g0-mod-field's `TateBridge`,
local-glue finding G8).** `TateBridge`'s statement, with `KerWild L' β' L` (G7Data's clause
`G_{L'} = G_L ∩ ker β`, for the `ℚ̄_ℓ`-valued `β'`: `g ∈ G_L`, `β'(g) = 1` ⟹ `g ∈ G_{L'}`) added
to its output. Source: N5 L702-716 (`L'` is the kernel field of `β|G_L`). -/
def TateBridgeK : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') β' L

/-- **Bridge 2 with the scalar transport (GLUE; the form in which `TateBridge35` states it).**
`TateBridge`'s statement with, in its output, an algebraic form `β_ℚ̄ : G_ℚ → ℚ̄` of G7Data's
`β` (`ι_ℂ ∘ β_ℚ̄ = β`) and an embedding `j : ℚ̄ → ℚ̄_ℓ` with `β' = j ∘ β_ℚ̄` (N5 L719-722: the
values of `β` are algebraic and are mapped into `ℚ̄_ℓ` by one embedding). -/
def TateBridgeT : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∃ (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
        (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ), (∀ g, β' g = j (βQ g)) ∧ ∀ g, ιC (βQ g) = (β g : ℂ)

/-- **`TateBridgeK` contains `TateBridge` (proved).** -/
theorem tateBridge_of_K (h : TateBridgeK) : TateBridge := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk ℓ _
  obtain ⟨Tm, c, ε', a, β', uu, h7, -⟩ := h u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  exact ⟨Tm, c, ε', a, β', uu, h7⟩

/-- **The transport form gives the kernel-field form (proved)**: `KerWild` is transported from
`G7Data` (`kerWild_of_g7Data_alg`). -/
theorem tateBridgeK_of_T (h : TateBridgeT) : TateBridgeK := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk ℓ _
  obtain ⟨Tm, c, ε', a, β', uu, h7, βQ, j, ιC, hj, hC⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  refine ⟨Tm, c, ε', a, β', uu, h7, ?_⟩
  have hβ' : β' = fun g => j (βQ g) := funext hj
  subst hβ'
  exact kerWild_of_g7Data_alg hD βQ j ιC hC

/-- **g14-trace's `TateBridge35` with the kernel-field clause at `ℓ = 5, 3` (GLUE).**
`TateBridge35`'s statement with `KerWild L' (j_ℓ ∘ β_ℚ̄) L` for `ℓ = 5, 3` added to the output.
It follows from `TateBridge35` (`tateBridge35K_of_35`). -/
def TateBridge35K : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5 ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3 ∧
      @G14Bridge.FrobTraceLink L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3 ∧
      (∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      @G15Ram.KerWild 5 _ L' _ (numberField_of_fd L') (fun g => j5 (βQ g)) L ∧
      @G15Ram.KerWild 3 _ L' _ (numberField_of_fd L') (fun g => j3 (βQ g)) L

/-- **`TateBridge35` gives `TateBridge35K` (proved)**: the kernel-field clause at `ℓ = 5, 3` is
transported from `G7Data` through `TateBridge35`'s own clause `ι_ℂ ∘ β_ℚ̄ = β`. -/
theorem tateBridge35K_of_35 (h : G14Bridge.TateBridge35) : TateBridge35K := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ιC, hC⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  exact ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ⟨ιC, hC⟩,
    kerWild_of_g7Data_alg hD βQ j5 ιC hC, kerWild_of_g7Data_alg hD βQ j3 ιC hC⟩

/-- **`TateBridge35` gives the `ℓ = 5` and `ℓ = 3` conclusions of `TateBridgeT` (proved).** -/
theorem tateBridgeT_at_of_35 (h : G14Bridge.TateBridge35) (u : ℚ) (P : QML3 Qbar)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
    ∀ ℓ, (ℓ = 5 ∨ ℓ = 3) → ∀ [Fact ℓ.Prime],
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∃ (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
        (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ), (∀ g, β' g = j (βQ g)) ∧ ∀ g, ιC (βQ g) = (β g : ℂ) := by
  intro ℓ hℓ _
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, -, ιC, hC⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  rcases hℓ with rfl | rfl
  · exact ⟨Tm5, c5, ε5, _, _, u5, h5, βQ, j5, ιC, fun _ => rfl, hC⟩
  · exact ⟨Tm3, c3, ε3, _, _, u3, h3, βQ, j3, ιC, fun _ => rfl, hC⟩

/-- **`TateBridge35` gives the `ℓ = 5` and `ℓ = 3` conclusions of `TateBridgeK` (proved).** -/
theorem tateBridgeK_at_of_35 (h : G14Bridge.TateBridge35) (u : ℚ) (P : QML3 Qbar)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
    ∀ ℓ, (ℓ = 5 ∨ ℓ = 3) → ∀ [Fact ℓ.Prime],
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') β' L := by
  intro ℓ hℓ _
  obtain ⟨Tm, c, ε', a, β', uu, h7, βQ, j, ιC, hj, hC⟩ :=
    tateBridgeT_at_of_35 h u P L A ε N χ β L' hLL' hD hdim hrk ℓ hℓ
  refine ⟨Tm, c, ε', a, β', uu, h7, ?_⟩
  have hβ' : β' = fun g => j (βQ g) := funext hj
  subst hβ'
  exact kerWild_of_g7Data_alg hD βQ j ιC hC

/-! ### §3. `DescentPts` on G7Data's model -/

/-- **`dim A = 2` for the model `A/L` from `dim A_{L'} = 2` (proved)**, by g0-dim's
`pkgI3_dim_baseChange` (dimension is invariant under field base change, Stacks 00P4). -/
theorem dim_model_of_bc {L L' : IF} (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2) : A.dim = 2 :=
  (@G0Dim.pkgI3_dim_baseChange L _ L' _ (incAlg hLL') A).symm.trans hdim

/-- **`DescentPts` for `A_{L'}` and G7's model field `L` (proved)**: `TateBridge`'s abelian
variety is the base change `A_{L'}` of the model `A/L` (`G7Data`), so local-glue's
`descentPts_baseChange` (with the conjugate model when Mathlib's embeddings differ, finding G9)
applies; `dim A = 2` comes from `dim A_{L'} = 2` (`dim_model_of_bc`). -/
theorem descentPts_of_g7 {L L' : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [FiniteDimensional ℚ L'] (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2) :
    @G15Ram.DescentPts L' _ (numberField_of_fd L')
      (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) L _ :=
  G15Ram.descentPts_baseChange hLL' A (dim_model_of_bc hLL' A hdim)

/-! ### §4. `LocalGlue` on the Tate bridge's data, with no local glue Prop -/

/-- **`LocalGlue` on the data of the transport form of the Tate bridge (proved).** For G7's
data, `dim A_{L'} = 2`, `G7Out` at `ℓ` for `A_{L'}` with `β' = j ∘ β_ℚ̄` where `ι_ℂ ∘ β_ℚ̄ = β`
(the output of `TateBridgeT`, or of `TateBridge35` at `ℓ = 5, 3`), and G7's clauses
(`G7Clauses`): `LocalGlue p Tm a β' L` at every `p ≠ ℓ`, from the leaves R6 and I2-Tors and the
textbook Prop `UnramRoots` (used at `p = 2`). -/
theorem localGlue_of_transport (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {u : ℚ} {P : QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    {c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (β g : ℂ))
    (h7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a
        (fun g => j (βQ g)) uu)
    (hCl : G15Ram.G7Clauses (fun g => j (βQ g)) ε' L) :
    @G15Ram.LocalGlue p _ ℓ _ _ _ _ Tm a (fun g => j (βQ g)) L := by
  haveI : NumberField L' := numberField_of_fd L'
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := h7.1
  exact G15Ram.localGlue_of_unramRoots hR6 hTors hU hpℓ h7 hCl
    (kerWild_of_g7Data_alg hD βQ j ιC hC) (fun _ => descentPts_of_g7 hLL' A hdim)

/-- **`LocalGlue` on `TateBridge35`'s data at `ℓ = 5` and `ℓ = 3` (proved).** For G7's data and the
output of g14-trace's `TateBridge35`, with G7's clauses for `j_ℓ ∘ β_ℚ̄`: `LocalGlue` at every
`p ≠ 5` for `Tm₅` and at every `p ≠ 3` for `Tm₃`, from R6, I2-Tors and `UnramRoots`. -/
theorem localGlue_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    {u : ℚ} {P : QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
    (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
    (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
    (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
    (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
    (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
    (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
    (h5 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5)
    (h3 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (β g : ℂ))
    (hCl5 : G15Ram.G7Clauses (fun g => j5 (βQ g)) ε5 L)
    (hCl3 : G15Ram.G7Clauses (fun g => j3 (βQ g)) ε3 L) :
    (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 →
      @G15Ram.LocalGlue p ⟨hp⟩ 5 _ _ _ _ Tm5 (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) L) ∧
    (∀ (p : ℕ) (hp : p.Prime), p ≠ 3 →
      @G15Ram.LocalGlue p ⟨hp⟩ 3 _ _ _ _ Tm3 (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) L) := by
  refine ⟨fun p hp hp5 => ?_, fun p hp hp3 => ?_⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    exact localGlue_of_transport hR6 hTors (hU p 5) hp5 hD βQ j5 ιC hC h5 hCl5
  · haveI : Fact p.Prime := ⟨hp⟩
    exact localGlue_of_transport hR6 hTors (hU p 3) hp3 hD βQ j3 ιC hC h3 hCl3

end LGKerWild

end

end LGKerWildSec


/-! ## lg-kerwild §5: `TateBridgeK` proved from the leaf I3.M0 (unram-tate's proof with the
kernel-field clause)

unram-tate proved g0-mod-field's `TateBridge` from I3.M0 (`tateBridge_of_tateModuleFree`) with
`β' g = γ(h g h⁻¹)`, `γ = ψ ∘ (β/a)`, `ψ` a field embedding. Below: `ScalarTransferK` adds to
unram-tate's `ScalarTransfer` the clause `γ(σ) = 1 → β(σ) = a(σ)` (the same proof gives it, `ψ`
being injective), and `tateBridgeK_of_piecesK` is unram-tate's `tateBridge_of_pieces` (proof copied)
with the extra conclusion `KerWild L' β' L`: for `g ∈ G_L` with `β'(g) = 1`, `hgh⁻¹ ∈ G_L`
(normal), `a = 1` on `G_L` (DescentDatum), so `β(hgh⁻¹) = 1`, so `hgh⁻¹ ∈ G_{L'}` (G7Data's
clause), so `g ∈ G_{L'}` (normal) `= resQ_{L'}(G_{L'})`. -/

section LGTateBridgeKSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace UnramTate

open G0ModField

/-- **Glue piece TB-iii with the kernel clause (GLUE, proved below: `scalarTransferK`).**
unram-tate's `ScalarTransfer` (statement copied) with the extra output `γ(σ) = 1 ⟹ β(σ) = a(σ)`:
the transfer of the scalars into `ℚ̄_ℓ` is injective on the values of `β/a`. -/
def ScalarTransferK : Prop :=
  ∀ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (ℓ : ℕ) [Fact ℓ.Prime] (a : GQ → ℝ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ) (n d : GQ → GQ → ℤ),
    (∀ σ τ, d σ τ ≠ 0) →
    (∀ σ τ, (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) =
      (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
    (∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ)) →
    (∀ σ, 0 < a σ) →
    (∀ σ, ∀ k ∈ GQL L', a (σ * k) = a σ ∧ β (σ * k) = β σ) →
    (∀ k ∈ GQL L', a k = 1 ∧ β k = 1) →
    ∃ gam : GQ → PadicAlgCl ℓ, (∀ σ, gam σ ≠ 0) ∧
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PadicAlgCl ℓ) / (d σ τ : PadicAlgCl ℓ)) * gam (σ * τ)) ∧
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) ∧ (∀ k ∈ GQL L', gam k = 1) ∧
      (∀ σ, gam σ = 1 → (β σ : ℂ) = ((a σ : ℝ) : ℂ))

/-- **`ScalarTransferK`, proved** (unram-tate's `scalarTransfer`, proof copied, plus the kernel
clause from the injectivity of `ψ`). -/
theorem scalarTransferK : ScalarTransferK := by
  intro L' _ _ ℓ _ a β ε n d hd hna hβe ha0 hcos hone
  let gC : GQ → ℂ := fun σ => (β σ : ℂ) / ((a σ : ℝ) : ℂ)
  let q : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have ha0' : ∀ σ, ((a σ : ℝ) : ℂ) ≠ 0 := fun σ => Complex.ofReal_ne_zero.mpr (ha0 σ).ne'
  have hq : ∀ σ τ, gC σ * gC τ = (q σ τ : ℂ) * gC (σ * τ) := by
    intro σ τ
    have h1 := hna σ τ
    have h2 : (β σ : ℂ) * β τ = ε σ τ * β (σ * τ) := by
      rw [← Units.val_mul, hβe σ τ, Units.val_mul]
    have hdC : (d σ τ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hd σ τ)
    have hε : (ε σ τ : ℂ) = (((a σ * a τ * ((n σ τ : ℝ) / d σ τ)) : ℝ) : ℂ) / ((a (σ * τ) : ℝ) : ℂ) := by
      rw [h1, mul_div_cancel_right₀ _ (ha0' _)]
    have hA := ha0' σ
    have hB := ha0' τ
    have hAB := ha0' (σ * τ)
    simp only [gC, q]
    rw [div_mul_div_comm, h2, hε]
    push_cast
    field_simp
  have hgcos : ∀ σ, ∀ k ∈ GQL L', gC (σ * k) = gC σ := by
    intro σ k hk; simp only [gC]; rw [(hcos σ k hk).1, (hcos σ k hk).2]
  have hg1 : ∀ k ∈ GQL L', gC k = 1 := by
    intro k hk; simp only [gC]; rw [(hone k hk).1, (hone k hk).2]; simp
  have hg0 : ∀ σ, gC σ ≠ 0 := fun σ => div_ne_zero (Units.ne_zero _) (ha0' σ)
  have hpow : ∀ (σ : GQ) (k : ℕ), ∃ r : ℚ, gC σ ^ k = (r : ℂ) * gC (σ ^ k) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by rw [pow_zero, pow_zero, hg1 1 (one_mem _)]; simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * q (σ ^ k) σ, ?_⟩
      rw [pow_succ, hr, _root_.mul_assoc, hq, pow_succ]
      push_cast; ring
  have hfin : ∀ σ : GQ, ∃ r : ℕ, 0 < r ∧ σ ^ r ∈ GQL L' := by
    intro σ
    let σ' : Qbar ≃ₐ[ℚ] Qbar := σ
    let s := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' σ'
    have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
    refine ⟨orderOf s, hs.orderOf_pos, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' (σ' ^ orderOf s) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L' _).mp h1 x hx
  have halg : ∀ σ, IsIntegral ℚ (gC σ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨t, ht⟩ := hpow σ r
    rw [hg1 _ hr, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ r - Polynomial.C t, Polynomial.monic_X_pow_sub_C t hr0.ne', ?_⟩
    simp [Polynomial.eval₂_sub, ht]
  let F : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range gC)
  haveI : Algebra.IsAlgebraic ℚ F := IntermediateField.isAlgebraic_adjoin (by
    rintro x ⟨σ, rfl⟩; exact halg σ)
  let ψ : F →ₐ[ℚ] PadicAlgCl ℓ := IsAlgClosed.lift
  have hmem : ∀ σ, gC σ ∈ F := fun σ => IntermediateField.subset_adjoin ℚ _ ⟨σ, rfl⟩
  let gam : GQ → PadicAlgCl ℓ := fun σ => ψ ⟨gC σ, hmem σ⟩
  refine ⟨gam, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ h0
    apply hg0 σ
    have : (⟨gC σ, hmem σ⟩ : F) = 0 := ψ.toRingHom.injective (h0.trans (map_zero ψ).symm)
    exact congrArg Subtype.val this
  · intro σ τ
    have hF : (⟨gC σ, hmem σ⟩ : F) * ⟨gC τ, hmem τ⟩ =
        algebraMap ℚ F (q σ τ) * ⟨gC (σ * τ), hmem (σ * τ)⟩ := Subtype.ext (hq σ τ)
    show ψ _ * ψ _ = _ * ψ _
    rw [← map_mul, hF, map_mul, AlgHom.commutes]
    congr 1
    simp only [q, map_div₀, map_intCast]
  · intro σ k hk
    exact congrArg ψ (Subtype.ext (hgcos σ k hk))
  · intro k hk
    show ψ _ = 1
    rw [← map_one ψ]
    exact congrArg ψ (Subtype.ext (hg1 k hk))
  · intro σ h1
    have hF : (⟨gC σ, hmem σ⟩ : F) = 1 := ψ.toRingHom.injective (h1.trans (map_one ψ).symm)
    have hg : gC σ = 1 := congrArg Subtype.val hF
    have h2 := (div_eq_one_iff_eq (ha0' σ)).mp hg
    exact h2

set_option maxHeartbeats 1000000 in
/-- **`TateBridgeK` from the five glue pieces, with `ScalarTransferK` (proved)**: unram-tate's
`tateBridge_of_pieces` (proof copied verbatim up to the final `refine`), plus the kernel-field
clause. -/
theorem tateBridgeK_of_piecesK (hP : TatePoints) (hE : EndBaseChange) (hS : ScalarTransferK)
    (hC : TateCont) (hR : ResQEmbedding) : LGKerWild.TateBridgeK := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD _hdim _hrank ℓ _
  haveI hNF : NumberField L' := numberField_of_fd L'
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, -, hmc, -⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(hE K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := hP L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gam, hgam0, hgamc, hgamcos, hgam1, hgamK⟩ := hS L' ℓ a β ε n d hd hna hβe ha0
    (fun σ k hk => ⟨(haL σ k (hLL'G k hk)).2.1, by
      have := hβe σ k
      rw [hβL' k hk, _root_.mul_one, eps_right_one L ε hεc hinf h11 σ k (hLL'G k hk),
        _root_.one_mul] at this
      exact this.symm⟩)
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  -- notation
  let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
    (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
  let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
  have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
    show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
    group
  let m' : GQ → AddMonoid.End (PtQ L A) := m
  let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
  let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
    ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
  let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => 1
  let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => gam (cj g)
  -- matrix units
  let QM : LeafQM.O →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
    R.comp ((LeafQM.AV.endPt A Qbar).comp iot)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : PadicAlgCl ℓ) (by norm_num : 0 < 2)
  have hI : QM iO * QM iO = (2 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
    rw [← map_mul, iO_sq, map_add, map_one, two_smul]
  have hJ : QM jO * QM jO = (-3 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
    rw [← map_mul, jO_sq, map_neg, map_add, map_add, map_one]
    module
  have hIJ : QM iO * QM jO = -(QM jO * QM iO) := by
    rw [← map_mul, iO_jO, map_neg, map_mul]
  obtain ⟨uu, huu⟩ := matrixUnits_of_quat s hs two_ne_zero three_ne_zero _ _ hI hJ hIJ
  have hcomm : ∀ (g : PkgI4.GQ) (o : LeafQM.O), Commute (Tm g) (QM o) := by
    intro g o
    apply Commute.map _ R
    exact hmEnd (cj g) (iot o)
  -- the relations
  have hT : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
    intro g g₂
    have h0 : d (cj g) (cj g₂) • (m' (cj g) * m' (cj g₂)) = n (cj g) (cj g₂) • m' (cj g * cj g₂) :=
      hnd (cj g) (cj g₂)
    have h1 := congrArg R h0
    rw [map_zsmul, map_zsmul, ← hcj] at h1
    have h1' : d (cj g) (cj g₂) • (Tm g * Tm g₂) = n (cj g) (cj g₂) • Tm (g * g₂) := by
      show d (cj g) (cj g₂) • (R (m' (cj g)) * R (m' (cj g₂))) = _
      rw [← map_mul]; exact h1
    have h2 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) • (Tm g * Tm g₂) =
        (n (cj g) (cj g₂) : PadicAlgCl ℓ) • Tm (g * g₂) :=
      (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
        (h1'.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
    have hd0 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
    show _ = ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) • _
    rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = c' g g₂ * a' (g * g₂) := by
    intro g g₂; simp only [a', _root_.one_mul, _root_.mul_one]
  have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
    intro g g₂; simp only [β', c']; rw [hcj]; exact hgamc _ _
  have hβ0 : ∀ g, β' g ≠ 0 := fun g => hgam0 _
  -- `G_{L'}` is normal
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  have hres : ∀ σ : Field.absoluteGaloisGroup L',
      cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
    intro σ
    have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
      rw [← resQRange L']; exact ⟨σ, rfl⟩
    exact hnorm.conj_mem _ this h
  have hTres : ∀ σ : Field.absoluteGaloisGroup L',
      Tm (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
    intro σ
    have hτ := hres σ
    let σ' : Qbar ≃ₐ[L] Qbar :=
      AlgEquiv.ofRingEquiv (f := (act (cj (@GaloisCopy.resQ L' _ hNF σ))).toRingEquiv)
        (fun x => (mem_GQL.mp (hLL'G _ hτ)) x x.2)
    have hm := hmL (cj (@GaloisCopy.resQ L' _ hNF σ)) σ' (fun x => rfl)
    rw [tate_eq_opV]
    show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m' (cj _))) = _
    congr 1
    refine DFunLike.ext _ _ fun x => ?_
    show Θ (m (cj (@GaloisCopy.resQ L' _ hNF σ)) (Θ.symm x)) = _
    rw [hm]
    show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
    rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]
  have hrho1 : ∀ σ : Field.absoluteGaloisGroup L',
      GlueDescent.rho Tm a' β' (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
    intro σ
    unfold GlueDescent.rho
    rw [hTres σ]
    simp only [β', a', hgam1 _ (hres σ), inv_one, _root_.mul_one, one_smul]
  refine ⟨Tm, c', c', a', β', uu, ⟨_hdim, _hrank, hT, ha, hβ, hβ0,
    fun σ => ⟨hTres σ, rfl, hgam1 _ (hres σ)⟩,
    fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩, ?_⟩
  -- continuity
  intro f v
  rw [continuous_iff_continuousAt]
  intro g₀
  let e₀ : Field.absoluteGaloisGroup L' → PkgI4.GQ := fun σ => g₀ * @GaloisCopy.resQ L' _ hNF σ
  have he₀ : Topology.IsOpenEmbedding e₀ :=
    (Homeomorph.mulLeft g₀).isOpenEmbedding.comp (hR L')
  have he₀1 : e₀ 1 = g₀ := by simp only [e₀, map_one, _root_.mul_one]
  have hcomp : (fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀ =
      fun σ => (f ∘ₗ GlueDescent.rho Tm a' β' g₀) (GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ v) := by
    funext σ
    simp only [Function.comp_apply, e₀, LinearMap.comp_apply]
    rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hT ha hβ hβ0, hrho1, Module.End.mul_apply]
  have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
    rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
  rw [he₀.continuousAt_iff, he₀1] at hc
  exact hc
  -- the kernel-field clause (lg-kerwild)
  intro g hgL hg1
  have hgL' : g ∈ GQL L := mem_GQL.mpr (fun x hx => hgL x hx)
  have hnormL : (L.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hcjL : cj g ∈ GQL L := hnormL.conj_mem _ hgL' h
  have haone : a (cj g) = 1 := (haL 1 (cj g) hcjL).1
  have hβC : (β (cj g) : ℂ) = 1 := by
    rw [hgamK (cj g) hg1, haone, Complex.ofReal_one]
  have hβ1 : β (cj g) = 1 := Units.ext (by rw [hβC, Units.val_one])
  have hcjL' : cj g ∈ GQL L' := (hL' (cj g)).mpr ⟨hcjL, hβ1⟩
  have hgL'' : g ∈ L'.fixingSubgroup := by
    have h4 : h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ ∈ L'.fixingSubgroup := hnorm.conj_mem _ hcjL' h⁻¹
    have e : h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g := by group
    rwa [e] at h4
  rw [RQ.resQ_range L']
  exact hgL''

/-- **`TateBridgeK` from the leaf I3.M0 alone (proved)**: g0-mod-field's `TateBridge` with the
kernel-field clause `KerWild L' β' L` in its output (lg-kerwild's correction of local-glue finding
G8), by unram-tate's construction (`tatePoints`, `endBaseChange`, `tateCont_of_tateModuleFree`,
`resQEmbedding`) and `scalarTransferK`. -/
theorem tateBridgeK_of_tateModuleFree (hT : PkgI3.TateModuleFree) : LGKerWild.TateBridgeK :=
  tateBridgeK_of_piecesK tatePoints endBaseChange scalarTransferK
    (tateCont_of_tateModuleFree hT) resQEmbedding

end UnramTate

/-- **`TateBridge35K` from I3.M0 and frob-trace's `AlgFrobRed` (proved)**: frob-trace's
`tateBridge35_of_algFrobRed` composed with `tateBridge35K_of_35`. -/
theorem LGKerWild.tateBridge35K_of_algFrobRed (hT : PkgI3.TateModuleFree)
    (hR : FrobTrace.AlgFrobRed) : LGKerWild.TateBridge35K :=
  LGKerWild.tateBridge35K_of_35 (FrobTrace.tateBridge35_of_algFrobRed hT hR)

end LGTateBridgeKSec


/-! ## lg-kerwild §6: `LocalGlue` on the data of `TateBridgeK`, every coefficient prime `ℓ` -/

section LGFinalSec

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q G0ModField

namespace LGKerWild

/-- **`LocalGlue` from `G7Out` on `A_{L'}`, `KerWild` and `G7Clauses` (proved).** For a model
`A/L` with `L ≤ L'` finite Galois, `G7Out` at `ℓ` for `A_{L'}` (base change along `incAlg`, as in
`TateBridge`), the kernel-field clause and G7's clauses: `LocalGlue` at every `p ≠ ℓ`, from R6,
I2-Tors and `UnramRoots`. `DescentPts` is discharged by `descentPts_of_g7`. -/
theorem localGlue_of_kerWild (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {L L' : IF} [FiniteDimensional ℚ L]
    [IsGalois ℚ L] [FiniteDimensional ℚ L'] (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    {c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a β' : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    (h7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu)
    (hK : @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') β' L)
    (hCl : G15Ram.G7Clauses β' ε' L) :
    @G15Ram.LocalGlue p _ ℓ _ _ _ _ Tm a β' L := by
  haveI : NumberField L' := numberField_of_fd L'
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := h7.1
  exact G15Ram.localGlue_of_unramRoots hR6 hTors hU hpℓ h7 hCl hK
    (fun _ => descentPts_of_g7 hLL' A hdim)

/-- **`TateBridgeK`'s data satisfy `LocalGlue` given G7's clauses (proved).** For G7's data,
`dim A_{L'} = 2`, `rank End(A_{L'}) = 4` and every coefficient prime `ℓ`, there are operator data
with `G7Out` at `ℓ` such that `G7Clauses β' ε' L` gives `LocalGlue p Tm a β' L` at every `p ≠ ℓ`,
from R6, I2-Tors and `UnramRoots`. No `KerWild` or `DescentPts` hypothesis. -/
theorem exists_localGlue_of_tateBridgeK (hB : TateBridgeK) (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∀ (p : ℕ) (hp : p.Prime), p ≠ ℓ → G15Ram.G7Clauses β' ε' L →
        @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a β' L := by
  obtain ⟨Tm, c, ε', a, β', uu, h7, hK⟩ := hB u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  refine ⟨Tm, c, ε', a, β', uu, h7, fun p hp hpℓ hCl => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact localGlue_of_kerWild hR6 hTors (hU p ℓ) hpℓ hLL' A h7 hK hCl

/-- **The same from the leaf I3.M0 (proved)**: `TateBridgeK` is `tateBridgeK_of_tateModuleFree`. -/
theorem exists_localGlue_of_tateModuleFree (hT : PkgI3.TateModuleFree)
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∀ (p : ℕ) (hp : p.Prime), p ≠ ℓ → G15Ram.G7Clauses β' ε' L →
        @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a β' L :=
  exists_localGlue_of_tateBridgeK (UnramTate.tateBridgeK_of_tateModuleFree hT) hR6 hTors hU
    u P L A ε N χ β L' hLL' hD hdim hrk ℓ

end LGKerWild

end LGFinalSec



/-! # lt-local, part 1: a field isomorphism `ℂ ≃ ℚ̄_ℓ` extending two given embeddings of `ℚ̄`

`exists_equiv_extending ιC j`: for embeddings `ιC : ℚ̄ → ℂ` and `j : ℚ̄ → ℚ̄_ℓ` there is a ring
isomorphism `Φ : ℂ ≃+* ℚ̄_ℓ` with `Φ ∘ ιC = j` (both fields are algebraically closed over `ℚ̄`
with transcendence bases of cardinality `𝔠`; Mathlib's `IsAlgClosure.equivOfEquiv` applied to the
`ℚ̄`-algebra isomorphism of the two polynomial rings on the bases). It transports `G7Data`'s
`ℂ^×`-valued cochain `β = ιC ∘ β_ℚ̄` to `j ∘ β_ℚ̄`, as `G7Clauses` asks.

`padic_card_le` and `padicAlgCl_card` are copied verbatim from g8-tate's `part_tools.lean`
(namespace `G8Tate`, renamed here to `LTLocal` to avoid a clash at integration). -/

noncomputable section

namespace LTLocal

open Cardinal LadicCond

/-- (copied from g8-tate) `#ℚ_p ≤ 𝔠`. -/
theorem padic_card_le (p : ℕ) [Fact p.Prime] : #ℚ_[p] ≤ 𝔠 := by
  have hex : ∀ x : ℚ_[p], ∀ n : ℕ, ∃ r : ℚ, ‖x - r‖ < 1 / ((n : ℝ) + 1) :=
    fun x n => Padic.rat_dense p x (by positivity)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hpos)
    have h1 := hf x n
    have h2 := hf y n
    rw [hxy] at h1
    have h3 : ‖x - y‖ ≤ ‖x - (f y n : ℚ_[p])‖ + ‖y - (f y n : ℚ_[p])‖ := by
      calc ‖x - y‖ = ‖(x - (f y n : ℚ_[p])) - (y - (f y n : ℚ_[p]))‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith
  calc #ℚ_[p] ≤ #(ℕ → ℚ) := mk_le_of_injective hinj
    _ = 𝔠 := by
      rw [← power_def, Cardinal.mkRat, mk_nat, aleph0_power_aleph0]

/-- (copied from g8-tate) `#ℚ̄_ℓ = 𝔠`. -/
theorem padicAlgCl_card (ℓ : ℕ) [Fact ℓ.Prime] : #(PadicAlgCl ℓ) = 𝔠 := by
  apply le_antisymm
  · calc #(PadicAlgCl ℓ) ≤ max #ℚ_[ℓ] ℵ₀ :=
          Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[ℓ] (PadicAlgCl ℓ)
      _ ≤ 𝔠 := max_le (padic_card_le ℓ) aleph0_le_continuum
  · calc 𝔠 ≤ #ℚ_[ℓ] := continuum_le_cardinal_of_nontriviallyNormedField _
      _ ≤ #(PadicAlgCl ℓ) := mk_le_of_injective (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).injective

/-- `ℚ̄` is countable. -/
theorem qbar_card_le : #PkgI4.Qbar ≤ ℵ₀ := by
  calc #PkgI4.Qbar ≤ max #ℚ ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max ℚ PkgI4.Qbar
    _ = ℵ₀ := by rw [Cardinal.mkRat, max_self]

/-- **Two algebraically closed fields of cardinality `𝔠` containing `ℚ̄` are isomorphic over
`ℚ̄` (proved).** Stated for the `ℚ̄`-algebra structures given by `ιq` and `j`. -/
theorem exists_equiv_extending_aux {K M : Type} [Field K] [Field M] [IsAlgClosed K]
    [IsAlgClosed M] (ιq : PkgI4.Qbar →+* K) (j : PkgI4.Qbar →+* M) (hK : #K = 𝔠) (hM : #M = 𝔠) :
    ∃ Φ : K ≃+* M, ∀ x, Φ (ιq x) = j x := by
  letI : Algebra PkgI4.Qbar K := ιq.toAlgebra
  letI : Algebra PkgI4.Qbar M := j.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis PkgI4.Qbar K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis PkgI4.Qbar M
  have hc : ℵ₀ < 𝔠 := aleph0_lt_continuum
  have hs' : #K = #s :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs qbar_card_le
      (hK ▸ hc)
  have ht' : #M = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht qbar_card_le
      (hM ▸ hc)
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.mp (by rw [← hs', ← ht', hK, hM])
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e' : Algebra.adjoin PkgI4.Qbar (Set.range ((↑) : s → K)) ≃ₐ[PkgI4.Qbar]
      Algebra.adjoin PkgI4.Qbar (Set.range ((↑) : t → M)) :=
    (hs.1.aevalEquiv.symm.trans (MvPolynomial.renameEquiv PkgI4.Qbar e)).trans ht.1.aevalEquiv
  refine ⟨IsAlgClosure.equivOfEquiv K M e'.toRingEquiv, fun x => ?_⟩
  have h1 : ιq x = algebraMap (Algebra.adjoin PkgI4.Qbar (Set.range ((↑) : s → K))) K
      (algebraMap PkgI4.Qbar _ x) := rfl
  rw [h1, IsAlgClosure.equivOfEquiv_algebraMap]
  show algebraMap _ M (e' (algebraMap PkgI4.Qbar _ x)) = j x
  rw [AlgEquiv.commutes]
  rfl

/-- **`ℂ ≃+* ℚ̄_ℓ` extending given embeddings of `ℚ̄` (proved).** -/
theorem exists_equiv_extending {ℓ : ℕ} [Fact ℓ.Prime] (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) :
    ∃ Φ : ℂ ≃+* PadicAlgCl ℓ, ∀ x, Φ (ιC x) = j x :=
  exists_equiv_extending_aux ιC.toRingHom j.toRingHom mk_complex (padicAlgCl_card ℓ)

end LTLocal

end


/-! # lt-local, part 2: `G7Clauses` and `dim A_{L'} = 2` for `TateBridge35`'s transported data

* `g7Clauses_of_transport`: local-data's `G7Clauses (j ∘ β_ℚ̄) ε' L` from `G7Data`, the bound
  `[L:ℚ] ≤ D` (local-data's finding F3: `G7Data` does not carry it), `ιC ∘ β_ℚ̄ = β` and
  `∂(j ∘ β_ℚ̄) = ε'` (both in `TateBridge35`'s output). The `ℂ^×`-valued clauses are carried to
  `ℚ̄_ℓ` by a field isomorphism `Φ : ℂ ≃ ℚ̄_ℓ` with `Φ ∘ ιC = j` (part 1), so that
  `j ∘ β_ℚ̄ = Φ ∘ β`; `ε' = 1` on `G_L × G_L` because `ε = 1` there (`DescentDatum`) and
  `j ∘ β_ℚ̄` has no zero. The proof of the clauses for `Φ ∘ β` follows g8-tate's
  `g7Clauses_of_g7Data` (copied, with `ε'` in place of `Φ ∘ ε`).
* `dim_bc_of_g7Data`: `dim A_{L'} = 2` from `G7Data`'s last clause `IsModelOver L' A_{L'} P`,
  `P.surface` and g0-dim's `pkgI3_dim_baseChange` (the proof of g0-split's `model_dim`). -/

noncomputable section

namespace LTLocal

open PkgI4 (GQ GQp decomp)
open LadicCond G0ModField
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent.B2
open CategoryTheory AlgebraicGeometry

/-- (copied from g8-tate) `T u` consists of primes. -/
theorem T_prime (u : ℚ) : ∀ q ∈ T u, q.Prime := by
  obtain ⟨hS, -, -⟩ := admissible_S_mul
  intro q hq
  rcases Finset.mem_union.mp hq with h | h
  · exact hS q h
  · exact Nat.prime_of_mem_primeFactors h

/-- **`G7Clauses` for the transported cochain `j ∘ β_ℚ̄` (proved).** -/
theorem g7Clauses_of_transport {ℓ : ℕ} [Fact ℓ.Prime] {u : ℚ}
    {P : QML3 Qbar} {L : IF} [FiniteDimensional ℚ L] {A : PkgI3.AbVar L}
    {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF}
    {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL')
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (βQ : PkgI4.GQ → PkgI4.Qbar)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (hC : ∀ g, ιC (βQ g) = (β g : ℂ)) {ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ}
    (hε' : ∀ g h, j (βQ g) * j (βQ h) = ε' g h * j (βQ (g * h))) :
    G15Ram.G7Clauses (fun g => j (βQ g)) ε' L := by
  obtain ⟨Φ, hΦ⟩ := exists_equiv_extending ιC j
  have hjβ : ∀ g, j (βQ g) = Φ (β g : ℂ) := fun g => by rw [← hC, hΦ]
  have hne : ∀ g, Φ (β g : ℂ) ≠ 0 := fun g => (map_ne_zero Φ).mpr (Units.ne_zero _)
  obtain ⟨-, hDD, -, -, ⟨Tm, hTmT, hN⟩, hβlc, hβsq, hβε, -⟩ := h
  have hfun : (fun g => j (βQ g)) = fun g => Φ (β g : ℂ) := funext hjβ
  refine ⟨inferInstance, hLD, hε', fun g => by simp only [hjβ]; exact hne g, ?_, ?_, ?_⟩
  · rw [hfun]
    exact hβlc.comp (fun z : ℂˣ => Φ (z : ℂ))
  · have hT : ∀ q ∈ Tm, q.Prime := fun q hq => T_prime u q (hTmT hq)
    subst hN
    refine ⟨Tm, hT, inferInstance, χ, Units.map Φ.toRingHom.toMonoidHom, fun g => ?_⟩
    show j (βQ g) ^ 2 = Φ ((GlueDescent.B2Q.galChar χ g : ℂˣ) : ℂ)
    rw [hjβ, ← map_pow, ← Units.val_pow_eq_pow_val, hβsq g]
  · intro g h hg _
    obtain ⟨hε, hinf, h11, -⟩ := hDD
    have h1 := GlueDescent.B3Q.inflatedNormalized_of L ε hε hinf h11 g h
      (Or.inl (GlueDescent.B3Q.mem_GQL.mpr hg))
    have h2 := hβε g h
    rw [h1, one_mul] at h2
    have h3 := hε' g h
    rw [hjβ, hjβ, hjβ, ← map_mul, ← Units.val_mul, h2] at h3
    exact mul_right_cancel₀ (hne (g * h)) (h3.symm.trans (one_mul _).symm)

/-- **`dim A_{L'} = 2` on G7's data (proved)**: G7Data's clause `IsModelOver L' A_{L'} P`,
`P.surface` and g0-dim's `pkgI3_dim_baseChange` (as g0-split's `model_dim`). -/
theorem dim_bc_of_g7Data {u : ℚ} {P : QML3 Qbar} {L : IF} {A : PkgI3.AbVar L}
    {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF}
    {hLL' : L ≤ L'} (h : G7Data u P L A ε N χ β L' hLL') :
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := by
  -- `first`: G7Data's model clause is its last (g0-assemble2) or second-to-last (g0-assemble3)
  have hm : IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P := by
    first
    | exact h.2.2.2.2.2.2.2.2.2.2.2
    | exact h.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨e⟩ := hm
  rw [← G0Dim.pkgI3_dim_baseChange Qbar (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')),
    ← P.surface]
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso ((Over.forget _).mapIso e)).isHomeomorph

end LTLocal

end


/-! # lt-local, part 4: `LinkedTateLocal` on `TateBridge35`'s data

* `LinkedTateLocalD` (the corrected statement): g0-assemble2's `LinkedTateLocal` with the premise
  `[L:ℚ] ≤ D` added (as g8-object's `LinkedTateDataD` adds it to `LinkedTateData`).
* `ModelEndRank4` (GLUE, named here): `rank_ℤ End(A_{L'}) = 4` on G7's model. It is
  `TateBridge35`'s second hypothesis, and a consequence of `LinkedTateLocal` itself (its `G7Out`
  contains it), so it costs no truth.
* `localGlue_at`: lg-kerwild's `localGlue_of_transport`, with `UnramRoots p ℓ` needed only at
  `p = 2` (its proof, through local-glue's `localGlue_of_descent`).
* **`linkedTateLocalD_of_tateBridge35`**: R6 + I2-Tors + `UnramRoots 2 5` + `UnramRoots 2 3` +
  `TateBridge35` + `ModelEndRank4` ⟹ `LinkedTateLocalD`.
* `linkedTateLocal_of_D`: `LinkedTateLocalD` + `G7DegreeBound` ⟹ `LinkedTateLocal` (trivial;
  shows what the unrestricted statement would need). -/

noncomputable section

-- the section-level opens of G0Assemble2.lean's `section G0A2_a85_linked`, as for the copy
open CategoryTheory.MonObj
open GlueDescent GlueC10 PkgI3
open scoped TensorProduct

namespace LTLocal

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **Glue (G5-G6 on G7's model, N5 L528-563): the endomorphism ring of `A_{L'}` has rank 4.**
For every fibre context and G7 data, `rank_ℤ End(A_{L'}) = 4`. Proof plan (not formalized):
`≥ 4` from the QM structure `ιq : 𝒪 → End(PK.A)` of `IsQMModel`, base-changed to `L'` (unram-tate's
`endBaseChange`; `𝒪` has rank 4 and `ιq` is injective because `[n] ≠ 0`, cf. g0-assemble2's
`modelNoncomm_of_mulIsogeny`); `≤ 4` from `End(A_{L'})` a division-ring order (g0-split's
`FibreSimple`, already in `GluePieces3` through FS5) and Albert's bound `[End⁰(A):ℚ] ≤ 2g` for a
simple abelian variety in characteristic `0` (Mumford, *Abelian Varieties*, §21; locator
UNVERIFIED). This is `TateBridge35`'s (and g0-mod-field's `TateBridge`'s) second hypothesis. -/
def ModelEndRank4 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4

/-- **G4's degree bound on G7's data (GLUE, N5 L532-563).** `[L:ℚ] ≤ D` for every G7 datum in a
fibre context. g0-mod-field's `G4Out` carries this bound but its `G7Data` does not (local-data's
finding F3); `G7Data` admits fields `L` larger than G4's Hom field, so this Prop is not expected to
hold as stated (SPECULATIVE). It is named only to record what the unrestricted
`LinkedTateLocal` would need on this route; the fix is to add the bound to `G7Data`
(`LinkedTateLocalD`). -/
def G7DegreeBound : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' → Module.finrank ℚ L ≤ ZInQ.heightD

/-- **Glue (corrected `LinkedTateLocal`, for `GluePieces4`):** the text of g0-assemble2's
`HSyn.G0AssembleMod.LinkedTateLocal` (GLUE field 39 of `GluePieces3`) with the premise
`Module.finrank ℚ L ≤ ZInQ.heightD` added after `G7Data`. The local data at `p > D` (tame
closure of `L_v`) and the `G7Clauses` used at every `p` need this bound (N5 L848-851:
`[L_v:ℚ_p] ≤ D < p`). Proved from `TateBridge35`, `ModelEndRank4` and leaves
(`linkedTateLocalD_of_tateBridge35`). -/
def LinkedTateLocalD : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    Module.finrank ℚ L ≤ ZInQ.heightD →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      ∀ (r₅ : PkgI4.GaloisRep 5 2) (r₃ : PkgI4.GaloisRep 3 2),
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5
          (GlueDescent.rho Tm₅ (fun g => j5 (aQ g)) (fun g => j5 (βQ g))) r₅ →
        G0Galois.G8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3
          (GlueDescent.rho Tm₃ (fun g => j3 (aQ g)) (fun g => j3 (βQ g))) r₃ →
        (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G15Ram.LocalData p ⟨hp⟩ 5 _ r₅) ∧
          G15Ram.LocalData 5 r₃

/-- **lg-kerwild's `localGlue_of_transport` with `UnramRoots` only at `p = 2` (proved; its proof,
through local-glue's `localGlue_of_descent`).** -/
theorem localGlue_at (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : p = 2 → G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {u : ℚ} {P : LeafQM.AV.QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    {c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (β g : ℂ))
    (h7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a
        (fun g => j (βQ g)) uu)
    (hCl : G15Ram.G7Clauses (fun g => j (βQ g)) ε' L) :
    @G15Ram.LocalGlue p _ ℓ _ _ _ _ Tm a (fun g => j (βQ g)) L := by
  haveI : NumberField L' := numberField_of_fd L'
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := h7.1
  exact G15Ram.localGlue_of_descent hR6 hTors hpℓ h7 hCl
    (LGKerWild.kerWild_of_g7Data_alg hD βQ j ιC hC)
    (fun _ => LGKerWild.descentPts_of_g7 hLL' A hdim)
    (fun h2 => G15Ram.betaTwist2_of_unramRoots h2 hCl (hU h2))

/-- **`LinkedTateLocalD` from `TateBridge35` (proved).** Inputs: the leaves R6
(`ObjBridge.RaynaudCriterion`) and I2-Tors (`ObjBridge.TorsionStructure`); local-glue's textbook
Prop `UnramRoots` at `p = 2` for `ℓ = 5, 3`; g14-trace's glue `TateBridge35`; the glue
`ModelEndRank4`. Steps: `dim A_{L'} = 2` (`dim_bc_of_g7Data`) and `ModelEndRank4` feed
`TateBridge35`; its output gives `G7Out` at 5 and 3, `FrobTraceLink` and `ιC ∘ βQ = β`;
`G7Clauses` for `j_ℓ ∘ βQ` (`g7Clauses_of_transport`, with `[L:ℚ] ≤ D`); `LocalGlue` at `p ≠ ℓ`
(`localGlue_at`: lg-kerwild's `KerWild` and `DescentPts` discharges); `LocalData` for every `r_ℓ`
with G8's output (local-data's `localData_of_g7`). -/
theorem linkedTateLocalD_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35) (hRk : ModelEndRank4) :
    LinkedTateLocalD := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD hLD
  letI : NumberField L' := numberField_of_fd L'
  have hdim := dim_bc_of_g7Data hD
  have hrk := hRk Y Φ π u P hctx L A ε N χ β L' hLL' hD
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ιC, hC⟩ :=
    hB u P L A ε N χ β L' hLL' hD hdim hrk
  have hCl5 := g7Clauses_of_transport hD hLD βQ j5 ιC hC h5.2.2.2.2.1
  have hCl3 := g7Clauses_of_transport hD hLD βQ j3 ιC hC h3.2.2.2.2.1
  refine ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF,
    fun r5 r3 h85 h83 => ⟨fun p hp hp5 => ?_, ?_⟩⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    exact G15Ram.localData_of_g7 h85 hCl5
      (localGlue_at hR6 hTors (fun h2 => by subst h2; exact hU5) hp5 hD βQ j5 ιC hC h5 hCl5)
  · exact G15Ram.localData_of_g7 h83 hCl3
      (localGlue_at hR6 hTors (fun h2 => absurd h2 (by norm_num)) (by norm_num) hD βQ j3 ιC hC
        h3 hCl3)

/-- `LinkedTateLocalD` and `G7DegreeBound` give g0-assemble2's `LinkedTateLocal` (proved,
trivially). -/
theorem linkedTateLocal_of_D (h : LinkedTateLocalD) (hB : G7DegreeBound) :
    HSyn.G0AssembleMod.LinkedTateLocal :=
  fun Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD =>
    h Y Φ π u P hctx L A ε N χ β L' hLL' hD (hB Y Φ π u P hctx L A ε N χ β L' hLL' hD)

/-- The unrestricted Prop gives the restricted one (proved, trivially). -/
theorem linkedTateLocalD_of_local (h : HSyn.G0AssembleMod.LinkedTateLocal) : LinkedTateLocalD :=
  fun Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD _ =>
    h Y Φ π u P hctx L A ε N χ β L' hLL' hD

/-- `ModelEndRank4` follows from `LinkedTateLocal` (its `G7Out` at `5` contains the rank), so
naming it costs no truth (proved). -/
theorem modelEndRank4_of_localD (h : LinkedTateLocalD) (hB : G7DegreeBound) :
    ModelEndRank4 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, -⟩ :=
    h Y Φ π u P hctx L A ε N χ β L' hLL' hD (hB Y Φ π u P hctx L A ε N χ β L' hLL' hD)
  exact h5.2.1

end LTLocal

end


/-! # lt-local, part 5: `ModelEndRank4` from `FibreSimple` and linked-tate's `QMEndRank`

Verbatim copies from `scratch/linked-tate/LinkedTate.lean` (with their namespace headers and opens):
* def-faltings' `ZInQ.DefFaltings.AbVar`, `AbVar.baseChange` (l.17119, l.18210-18236);
* leaf-adopt's `LeafAdopt.abVarEquiv` (l.19042-19045, l.19196-19201);
* g0-split's `HSyn.G0Split.FibreOver` and `FibreSimple` (l.33338-33340, l.33577-33590,
  l.33712-33722; `FibreSimple` is the existing `GluePieces` piece, supplied in `GluePieces3`
  through FS5);
* linked-tate's `HSyn.LinkedTate.QMEndRank` (l.42841-42844, l.43121-43135; GLUE, literature-backed:
  Mumford §19 Thm 3 and Albert's classification, §21, numbering UNVERIFIED).
New: `endDivision_of_fibreSimple` (linked-tate's proof, copied) and `modelEndRank4_of_qmEndRank`
(the argument of linked-tate's `linkedTateCore_of`). -/

noncomputable section

namespace ZInQ.DefFaltings

section ModelsSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ExteriorAlgebra

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

end ModelsSec

end ZInQ.DefFaltings

namespace LeafAdopt

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

end LeafAdopt

namespace HSyn

open scoped MatrixGroups ModularForm

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

end G0Split

end HSyn

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

end HSyn.LinkedTate

namespace LTLocal

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- (copied from linked-tate; `Qbar` written `PkgI4.Qbar`) **`EndDivision` for every number-field model of the fibre, from the
glue piece `FibreSimple`** (proved). -/
theorem endDivision_of_fibreSimple (hFS : HSyn.G0Split.FibreSimple)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : LeafQM.AV.PtEquiv Y} {π : LeafQM.AV.ToP1 Y.left} {u : ℚ}
    {P : LeafQM.AV.QML3 PkgI4.Qbar} (hctx : FibreCtx Y Φ π u P) (L' : IF)
    [FiniteDimensional ℚ L'] (A' : PkgI3.AbVar L') (hA' : IsModelOver L' A' P) :
    PkgI3.EndDivision A' := by
  obtain ⟨h1, h2, hu, y, hy, hπ⟩ := hctx
  haveI : NumberField L' := numberField_of_fd L'
  exact hFS Y Φ π h1 h2 u hu ⟨L'⟩ ((LeafAdopt.abVarEquiv L').symm A')
    ⟨algebraMap L' PkgI4.Qbar, y, P, hy, hπ, hA'⟩

/-- **`ModelEndRank4` from `FibreSimple` and `QMEndRank` (proved;** the argument of linked-tate's
`linkedTateCore_of`): G7Data's `IsQMModel` writes `A = (PK.A)_L`, its last clause gives
`EndDivision A_{L'}` through `FibreSimple`, and `QMEndRank` gives the rank. -/
theorem modelEndRank4_of_qmEndRank (hFS : HSyn.G0Split.FibreSimple)
    (hR : HSyn.LinkedTate.QMEndRank) : ModelEndRank4 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  have hmod : IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P := by
    first
    | exact hdata.2.2.2.2.2.2.2.2.2.2.2
    | exact hdata.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨K, hKL, PK, -, rfl⟩ := hdata.1
  exact hR K L L' hKL hLL' PK (endDivision_of_fibreSimple hFS hctx L' _ hmod)

/-- **`LinkedTateLocalD` from `TateBridge35`, `FibreSimple` and `QMEndRank` (proved).** -/
theorem linkedTateLocalD_of_tateBridge35' (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35)
    (hFS : HSyn.G0Split.FibreSimple) (hR : HSyn.LinkedTate.QMEndRank) : LinkedTateLocalD :=
  linkedTateLocalD_of_tateBridge35 hR6 hTors hU5 hU3 hB (modelEndRank4_of_qmEndRank hFS hR)

end LTLocal

end


/-! # lt-local, part 6 (GluePieces4 variant): `LinkedTateLocal` itself, over g0-assemble3's `G7Data`

Compiled only in the variant `LtLocal4.lean` (`build4.sh`), whose base `Base4.lean` is
`Base.lean` with g0-assemble3's fix of `G0ModField.G7Data` (the clause `[L:ℚ] ≤ D` appended,
`scratch/g0-assemble3/parts/75_modfield.lean`) and its three proof adjustments, ported by
`mk_base4.py`. Over that `G7Data`, `G7DegreeBound` is a projection, and g0-assemble2's
`LinkedTateLocal` (GLUE field 39, statement unchanged) is proved. -/

noncomputable section

namespace LTLocal

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **`G7DegreeBound` over g0-assemble3's `G7Data` (proved: its last clause).** -/
theorem g7DegreeBound_gp4 : G7DegreeBound := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  exact hD.2.2.2.2.2.2.2.2.2.2.2.2

/-- **g0-assemble2's `LinkedTateLocal` (GLUE field 39), over g0-assemble3's `G7Data` (proved)**
from the leaves R6 and I2-Tors, local-glue's textbook Prop `UnramRoots` at `p = 2` for `ℓ = 5, 3`,
g14-trace's glue `TateBridge35`, g0-split's `FibreSimple` and linked-tate's `QMEndRank`. -/
theorem linkedTateLocal_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hB : G14Bridge.TateBridge35)
    (hFS : HSyn.G0Split.FibreSimple) (hR : HSyn.LinkedTate.QMEndRank) :
    HSyn.G0AssembleMod.LinkedTateLocal :=
  linkedTateLocal_of_D (linkedTateLocalD_of_tateBridge35' hR6 hTors hU5 hU3 hB hFS hR)
    g7DegreeBound_gp4

/-- The same with `TateBridge35` from frob-trace's reduction (`FrobTrace.tateBridge35_of_algFrobRed`:
the leaf I3.M0 `PkgI3.TateModuleFree` and the glue `FrobTrace.AlgFrobRed`). -/
theorem linkedTateLocal_of_algFrobRed (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU5 : G15Ram.UnramRoots 2 5)
    (hU3 : G15Ram.UnramRoots 2 3) (hT : PkgI3.TateModuleFree) (hA : FrobTrace.AlgFrobRed)
    (hFS : HSyn.G0Split.FibreSimple) (hR : HSyn.LinkedTate.QMEndRank) :
    HSyn.G0AssembleMod.LinkedTateLocal :=
  linkedTateLocal_of_tateBridge35 hR6 hTors hU5 hU3 (FrobTrace.tateBridge35_of_algFrobRed hT hA)
    hFS hR

end LTLocal

end




end G0A3_z93z_ltlocal

section G0A3_z94_spreadout
/-! ## assemble-port: spread-out (N1-g1 `AbVarSpreadsOut` from three EGA IV leaves)

spread-out proves, in the kernel module `ZInQKernel/Contrib/SpreadOut/NumberField.lean` (merged from origin/wip/spread-out,
imported here through imports_tailD.txt), `ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega`: the body of neron-lg's
`AbVarSpreadsOut` for the kernel's `PkgI3.AbVar` (`ZInQKernel/HDecomp/Objects.lean`), from the leaves `EGAIV_8_8_2_ii`,
`EGAIV_8_10_5_xii`, `EGAIV_17_7_8_ii` (`ZInQKernel/Contrib/SpreadOut/Spread.lean`, Mathlib-only statements). The theorem
below applies it to frob-pieces' copy `FrobPiecesNeron.AbVarSpreadsOut` (over this file's `PkgI3.AbVar`, a structure with
the same five fields): an abelian variety `B` of this file is sent to the kernel's `⟨B.X⟩`, and the conclusion, which
mentions only `B.X` and its group structure, is accepted by unfolding. -/

namespace HSyn

/-- **N1-g1 from EGA IV₃ 8.8.2 (ii), EGA IV₃ 8.10.5 (xii), EGA IV₄ 17.7.8 (ii)** (spread-out). -/
theorem abVarSpreadsOut_of_ega (h882 : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii)
    (hpr : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii)
    (hsm : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii) : FrobPiecesNeron.AbVarSpreadsOut :=
  fun L _ _ B => _root_.ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega h882 hpr hsm L ⟨B.X⟩

end HSyn

#print axioms HSyn.abVarSpreadsOut_of_ega

end G0A3_z94_spreadout

section G0A3_z94b_unramroots
/-! ## assemble-port (stretch): `UnramRoots` (frob-contrib's kernel proof) for this file's copy

frob-contrib proves local-glue's textbook Prop `G15Ram.UnramRoots p ℓ` in the kernel module
`ZInQKernel/Contrib/UnramRoots/Main.lean` (`UnramRootsTask.unramRoots`; merged from origin/wip/frob-contrib, imported through
imports_tailD.txt), over the kernel's `LadicCond` definitions. This file's `G15Ram.UnramRoots` (local-glue's text, in part
z93z) is the same statement over this file's copies of those definitions; the kernel accepts the kernel theorem for it
by unfolding. -/

namespace HSyn

/-- **`UnramRoots` holds** (frob-contrib, via the kernel's statement). -/
theorem unramRoots_proved (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] : G15Ram.UnramRoots p ℓ :=
  _root_.UnramRootsTask.unramRoots

end HSyn

#print axioms HSyn.unramRoots_proved

end G0A3_z94b_unramroots

section G0A3_z95_bundle4
/-! ## g0-assemble3: `ResearchLeaves4`, `GluePieces4`, `sixContactMin_of_leaves4`

Task g0-assemble3, 2026-11-13. g0-assemble2's `GluePieces3` (part z90, 40 fields) with every later result applied
(parts b10-e30, z92). Each field of `GluePieces4` is a named `def … : Prop` of its source task, copied verbatim in that
task's part; kinds and sources are in `docs/research/g0-assemble3.md` §2 (LEAF = published theorem, LEAF? = leaf
candidate, GLUE = to be proved by the project). `ResearchLeaves4` is `ResearchLeaves3` with r10-amend's amended R10
(`DeRhamComparisonHT` = old R10 + the Hodge–Tate vanishing clause, which was `GluePieces3.g9R10Weights`). -/

noncomputable section

namespace HSyn

open G0Split

/-- **The research leaves after g0-assemble3**: `ResearchLeaves3` (part z80) with `r10` amended (r10-amend). -/
structure ResearchLeaves4 : Prop where
  r1r2 : LeafAdopt.R1R2fpRep
  r1rec : LeafQM.AV.R1rec
  r3 : ZInQ.LeafPush2.R03_LinYang
  r4 : PkgI1.ThetaModularity
  r5 : LeafQM.AV.R5fp
  r5count : LeafQM.AV.R5fpCount
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
  r8 : PkgI2.GrothendieckMonodromy.{0}
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  /-- R10 amended (r10-amend, `ZInQKernel/Contrib/R10/Amend.lean`): the de Rham comparison with the full
  Hodge–Tate weight multiset (Faltings 1988; Fontaine 1982; Tate 1967 §3.3; locators UNVERIFIED);
  `deRhamComparisonHT_iff : DeRhamComparisonHT ↔ PkgI4.DeRhamComparison ∧ G9Bridge.R10Weights`. -/
  r10 : ZInQ.Contrib.R10.DeRhamComparisonHT
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
  r14 : EigenformRepExists
  r15 : DeligneSerreConseq
  r16 : LeafModCurves.R16_EichlerShimuraJ1'
  r18 : ZInQ.LeafPush2.R18_Javanpeykar
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
  r20 : ZInQ.DefFaltings.R20_FaltingsLemma5
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  h5fin : ZInQ.DefFaltings.StableHeightFinite

/-- `ResearchLeaves4` gives `ResearchLeaves3` (the old R10 is a projection of the amended one). -/
theorem ResearchLeaves4.toR3 (r : ResearchLeaves4) : ResearchLeaves3 :=
  { r1r2 := r.r1r2, r1rec := r.r1rec, r3 := r.r3, r4 := r.r4, r5 := r.r5, r5count := r.r5count,
    r6 := r.r6, r7a := r.r7a, r7b := r.r7b, r8 := r.r8, r9a := r.r9a, r9b := r.r9b,
    r10 := ZInQ.Contrib.R10.deRhamComparison_of_HT r.r10, r11r12 := r.r11r12, r13 := r.r13,
    r14 := r.r14, r15 := r.r15, r16 := r.r16, r18 := r.r18, r19 := r.r19, r20 := r.r20,
    r21 := r.r21, r22 := r.r22, h5fin := r.h5fin }

/-- `ResearchLeaves3` together with g9-derham's `R10Weights` (the old field 28b of `GluePieces3`) gives
`ResearchLeaves4` (`deRhamComparisonHT_iff`). -/
theorem researchLeaves4_of (r : ResearchLeaves3) (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights) :
    ResearchLeaves4 :=
  { r1r2 := r.r1r2, r1rec := r.r1rec, r3 := r.r3, r4 := r.r4, r5 := r.r5, r5count := r.r5count,
    r6 := r.r6, r7a := r.r7a, r7b := r.r7b, r8 := r.r8, r9a := r.r9a, r9b := r.r9b,
    r10 := ZInQ.Contrib.R10.deRhamComparisonHT_iff.mpr ⟨r.r10, hW⟩, r11r12 := r.r11r12,
    r13 := r.r13, r14 := r.r14, r15 := r.r15, r16 := r.r16, r18 := r.r18, r19 := r.r19,
    r20 := r.r20, r21 := r.r21, r22 := r.r22, h5fin := r.h5fin }

/-- **The named Props left after g0-assemble3.** -/
structure GluePieces4 : Prop where
  -- FibreSimple: FS5 (NoCM on the fibre)
  /-- fs5-nocm, LEAF (N1b′: CM points via optimal embeddings; Shimura 1967, Jordan, González–Rotger). -/
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  /-- x6-kummer, LEAF (N2-L′: `X₆` is the conic `Y² + 3X² + 3Z² = 0` with `π₆ = −16(X² + Z²)/(27Z²)` on
  `ℚ̄`-points of one witness of the leaf bundle; Elkies 1998 §3, Kurihara 1979; a consequence of the published model,
  x6-kummer §3.6). fs5-nocm's glue N2 `X6KummerFibre` is proved from it and `MobiusGlue`. -/
  x6ConicModel : X6Kummer.X6ConicModel
  -- ProductModelHeight (unif-dims, product-unif, infra-smooth-dim)
  /-- metrization (via unif-dims), LEAF (the uniformization theorem with its dimension: `𝒢(ℂ)_τ ≅ ℂ^g/Λ`,
  Mumford §1, §4; GAGA). -/
  analyticUniformizationOfDim : ZInQ.Metrization.AnalyticUniformizationOfDim
  -- StableHeightBaseChange (height-bc; infra-stalks proved the other two)
  /-- height-bc, GLUE (BC-alg: `ψ` is injective on the Hodge line). -/
  hodgeBCInjective : ZInQ.HeightBC.HodgeBCInjective
  /-- height-bc, GLUE (`ω` base-changes along `𝓞_L → 𝓞_{L'}`). -/
  omegaBaseChange : ZInQ.HeightBC.OmegaBaseChange
  -- ThetaPoint (g0-thetapoint, fibre-qm-period, period-map)
  /-- g0-thetapoint, LEAF? (theta-constant ratios at a period matrix are algebraic; Shimura 1976). -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- pkg-I1 (via fibre-qm-period), LEAF? (the theta-quotient Hauptmodul of `Γ*`). -/
  qmHauptmodul : PkgI1.QMHauptmodul
  /-- fibre-qm-period, LEAF (Eichler class number one for `𝒪`, lattice form). -/
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  /-- fibre-qm-period, LEAF (R1(b) in family form; Shimura 1967 Main Thm I). -/
  r1bFamily : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.R1bFamily (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- period-map, GLUE (base change of QM classes is unique). -/
  baseChangeClassUnique : G0Split.FibreQM.PeriodMapH.BaseChangeClassUnique
  /-- period-map, GLUE (`π` is invariant under the QM twist, complex form), for the leaf's own triple. -/
  piTwistC : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.PeriodMapH.PiTwistC (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- period-map, GLUE (the QM twist acts on the period lattice). -/
  qmTwistLattice : G0Split.FibreQM.PeriodMapH.QMTwistLattice
  /-- period-map, LEAF? (CM points descend; Shimura's theory of CM). -/
  cmDescends : G0Split.FibreQM.PeriodMapH.CMDescends
  /-- period-map, GLUE (numerical: `Σθ⁸(Ω(√2 + i)) ≠ 0`). -/
  s8Nonzero : G0Split.FibreQM.PeriodMap.S8Nonzero
  /-- period-map, GLUE (textbook complex analysis: a holomorphic map of the sphere factoring affinely). -/
  sphereFactorAffine : G0Split.FibreQM.PeriodMap.SphereFactorAffine
  /-- period-map, GLUE (`Σθ⁸∘Ω` has exact weight 8). -/
  s8WeightExact : G0Split.FibreQM.PeriodMap.S8WeightExact
  /-- period-map, LEAF (the valence formula for `Γ*`). -/
  valenceBoundGammaStar : G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar
  /-- fibre-qm-period, GLUE (transport of complex points along base change). -/
  cPtsTransport : G0Split.FibreQM.CPtsTransport
  -- ModularConstituent: G2 (fibre-cover; Prop. TS by prop-ts, prop-ts-glue)
  /-- prop-ts-glue, GLUE. -/ verticalResidueSeparable : PropTSGlue.VerticalResidueSeparable
  /-- prop-ts-glue, GLUE. -/ snSpecialize : PropTSGlue.SNSpecialize
  /-- prop-ts-glue, GLUE. -/ kummerCompositum : PropTSGlue.KummerCompositum
  /-- prop-ts-glue, GLUE (`AbhyankarDVR → …`). -/ kummerAbhyankarFinGlue : PropTSGlue.KummerAbhyankarFinGlue
  /-- prop-ts-glue, GLUE. -/ kummerOtherBranchFin : PropTSGlue.KummerOtherBranchFin
  /-- prop-ts-glue, GLUE. -/ kummerVerticalFin : PropTSGlue.KummerVerticalFin
  /-- prop-ts-glue, GLUE (`AbhyankarDVR → …`). -/ kummerAbhyankarInfGlue : PropTSGlue.KummerAbhyankarInfGlue
  /-- prop-ts-glue, GLUE. -/ kummerOtherBranchInf : PropTSGlue.KummerOtherBranchInf
  /-- prop-ts-glue, GLUE. -/ kummerVerticalInf : PropTSGlue.KummerVerticalInf
  /-- prop-ts-glue, GLUE (truth SPECULATIVE per its report). -/ heckeIrreducible : PropTSGlue.HeckeIrreducible
  /-- prop-ts-glue, GLUE. -/ heckeNormalizationIrr : PropTSGlue.HeckeNormalizationIrr
  /-- prop-ts-glue, GLUE. -/ heckeDegree : PropTSGlue.HeckeDegree
  /-- prop-ts-glue, GLUE. -/ heckeBranch : PropTSGlue.HeckeBranch
  /-- prop-ts-glue, GLUE (Lemma NV). -/ heckeNoVertRam : PropTSGlue.HeckeNoVertRam
  -- ModularConstituent: G4 (kernel-field, kf-glue)
  /-- kf-glue, GLUE (Galois descent of the twisted isomorphisms). -/
  twistDescent : G0ModField.KernelField.TwistDescent
  -- ModularConstituent: G8-G12
  /-- g0-mod-galois, LEAF (R14 with its determinant clause; Shimura 1971 Thm 7.14; Deligne 1971). -/
  r14Det : G0Galois.R14Det
  /-- conj-twist, LEAF (N2: homomorphisms lift to `ℂ`-linear maps of uniformizations; Birkenhake–Lange 1.2.1). -/
  homLinearLift : G0Galois.HomLinearLift
  /-- g12-det, LEAF (HT weights of a twist shift by a constant; Sen 1980). -/
  senTwist : G0Galois.SenTwist
  /-- g12-det, LEAF (finite image ⇒ HT with weights 0; Tate 1967; Ax–Sen–Tate). -/
  finiteImageHT : G0Galois.FiniteImageHT
  /-- weil-pairing (used by g12-det), LEAF (T9 restated; Mumford §§6, 8, 20, 23). -/
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  /-- weil-pairing, LEAF (Mumford §7-8). -/
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  /-- weil-pairing, LEAF (Mumford §4 Appl. 2). -/
  divisiblePoints : WeilPairing.DivisiblePoints
  -- ModularConstituent: G13-G16
  /-- R17 concretely, LEAF (Carayol 1986, Thm (A)). -/
  carayolR17 : LadicCond.CarayolR17'
  -- ModularConstituent: joint glue on G7's data (linked-tate)
  /-- linked-tate, GLUE (G3 on the QM model: inertia above `p ∉ {3, ℓ}` fixes `ℓⁿ`-torsion, given NOS). -/
  goodRedTorsion : LinkedTate.GoodRedTorsion
  /-- linked-tate, GLUE (literature-backed: `rank End = 4` for a QM model with `EndDivision`). -/
  qmEndRank : LinkedTate.QMEndRank
  /-- linked-tate, GLUE (g14-trace's Frobenius link for the canonical operators). -/
  linkedFrob : UnramTate.LinkedFrob
  /-- linked-tate, GLUE (the upper breaks of the kernel field `L'`; usable since `G7Data` now carries
  `[L:ℚ] ≤ D`). -/
  kernelFieldBreaks : UnramTate.KernelFieldBreaks
  /-- linked-tate, GLUE (D1-D2 at `p = 3` for `ρ₅`). -/
  tateRamAtThree : UnramTate.TateRamAtThree

/-- `MobiusGlue` from T5 alone (image-plane). -/
theorem mobiusGlue_of_t5' (t : TextbookLeaves) : LeafQM.AV.Pin.MobiusGlue :=
  LeafQM.AV.CurveGlue.mobiusGlue_of_t5 t.t5

/-- FS5 (NoCM on the fibre) from `GluePieces4` (fs5-nocm). -/
theorem fibreComTrivial_of_gp4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    G0FibreSimple.FibreComTrivial :=
  fibreComTrivial_of_full (FS5NoCM.fibreComTrivialFull_of_leaves'' (r1r2fpFull_of r.toR3)
    (mobiusGlue_of_t5' t) t.t27 t.t6 gp.cmOptimalEmbedding
    (X6Kummer.x6KummerFibre_of_conic (mobiusGlue_of_t5' t) gp.x6ConicModel) r.r5count)

/-- `FibreSimple` from `GluePieces4` (fs1-descend, mul-rigidity, infra-stalks' `MulIsogeny`, fs5-nocm). -/
theorem fibreSimple_of_gp4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    G0Split.FibreSimple :=
  G0FibreSimple.fibreSimple_of_leaves t MulRigidity.mulIsogeny G0FibreSimple.rigidityHom
    ⟨G0FibreSimple.finiteDescends_proof, fibreComTrivial_of_gp4 r t gp⟩

/-- G3 for `QML3` objects (linked-tate). -/
theorem qmModelG3_of_gp4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    LinkedTate.QMModelG3 :=
  LinkedTate.qmModelG3_of r.r7a r.r6 t.t5 (LinkedTate.goodRedG3Bridge_of_torsion gp.goodRedTorsion)

/-- Prop. TS for every admissible cover (prop-ts, prop-ts-glue). -/
theorem propTSAll_of_gp4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    G0ModField.PropTSAll :=
  PropTSGlue.propTSAll_of_pieces'' t2_proved (LeafAdopt.R1R2fp_of_rep r.r1r2) (mobiusGlue_of_t5' t)
    gp.verticalResidueSeparable gp.snSpecialize gp.kummerCompositum gp.kummerAbhyankarFinGlue
    gp.kummerOtherBranchFin gp.kummerVerticalFin gp.kummerAbhyankarInfGlue gp.kummerOtherBranchInf
    gp.kummerVerticalInf gp.heckeIrreducible gp.heckeNormalizationIrr gp.heckeDegree gp.heckeBranch
    gp.heckeNoVertRam

/-- The period map's glue for the leaf's own triple (period-map). -/
theorem periodMapGlue_of_gp4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep r.r1r2))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep r.r1r2))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep r.r1r2)) :=
  G0Split.FibreQM.PeriodMapH.periodMapGlue_own _ gp.baseChangeClassUnique (gp.piTwistC r.r1r2)
    gp.qmTwistLattice
    (G0Split.FibreQM.PeriodMapH.piCMC_of _ _ _ (G0Split.FibreQM.own_spec _).1
      (G0Split.FibreQM.own_spec _).2.2 gp.baseChangeClassUnique (gp.piTwistC r.r1r2) gp.cmDescends)
    (G0Split.FibreQM.PeriodMapH.cmFixedHasCM_of t.t11a)

/-- **`GluePieces` from `GluePieces4` and the leaf bundles** (g0-assemble3). -/
theorem gluePieces_of_gluePieces4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    GluePieces where
  dimFinite := G0Split.dimFinite
  dimBaseChange := G0Split.dimBaseChange
  fibreSimple := fibreSimple_of_gp4 r t gp
  productModelHeight := ZInQ.UnifDims.productModelHeight_of_unifOfDim gp.analyticUniformizationOfDim
  stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
    (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_two
      gp.hodgeBCInjective gp.omegaBaseChange))
  productExists := G0Product.productExists
  reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r.toR3 G0Split.dimFinite
  thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
    (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 (mobiusGlue_of_t5' t) gp.qmHauptmodul
      t.t35 t.t11a gp.qmClassNumberOne (gp.r1bFamily r.r1r2) (periodMapGlue_of_gp4 r t gp)
      (G0Split.FibreQM.PeriodMap.hauptmodulUnique_of' gp.s8Nonzero gp.sphereFactorAffine)
      (G0Split.FibreQM.PeriodMap.qmDenZeroCM3_of'' gp.s8Nonzero gp.s8WeightExact
        gp.valenceBoundGammaStar)
      gp.cPtsTransport)
    gp.thetaRatiosAlgebraic
  modularConstituent := modularConstituent_of_field t
    (G0ModField.fibreCoverExists_of_propTSAll' t.t5 (propTSAll_of_gp4 r t gp)
      G0ModField.unramifiedConjugates)
    (G0ModField.KernelField.kernelFieldExists_of_descent t.t6 r.r7a r.r6 t.t5 t.t27
      (fibreComTrivial_of_gp4 r t gp) MulRigidity.mulIsogeny gp.twistDescent)
    UnramTate.unramifiedSup_mf
    (G0AssembleMod.afterG7_of3 r.toR3 t
      ⟨RvGP2.burnsideAbsIrred, gp.r14Det,
        ZInQ.Contrib.R10.g9Glue_of_deRhamComparisonHT r.r10,
        G0Galois.g10Glue_of_conjTwist
          (G0Galois.conjTwistNontrivial_of_leaves t.t5 t.t26 t.t35 gp.homLinearLift),
        G0Galois.g12Weight_of_senTwist gp.senTwist gp.finiteImageHT,
        G0Galois.detTate_of_leaves gp.t09SymmIsogenyExists gp.isogenyQuasiInverse
          gp.divisiblePoints t.t26,
        G0AssembleMod.resQFiniteIndex⟩
      (G0ModNewform.dirichletOfFinite_of_t17 t.t17) gp.carayolR17
      Swan.swanIndependent_proved Swan.swanIntegral_proved
      Swan.adaptedExists_proved
      (LinkedTate.modelG3G6_of (fibreSimple_of_gp4 r t gp) (qmModelG3_of_gp4 r t gp))
      (LinkedTate.linkedTateData_of_frobRam t.t7 t.t26 (fibreSimple_of_gp4 r t gp) gp.qmEndRank
        (UnramTate.linkedFrobRam_of gp.linkedFrob
          (UnramTate.linkedRam_of (qmModelG3_of_gp4 r t gp) gp.kernelFieldBreaks
            UnramTate.localInertiaGlobal UnramTate.upperAbsInertia gp.tateRamAtThree))))
  heightCopies := G0HeightCopies.heightCopiesAgree

/-- **G0 after g0-assemble3**: the leaf bundles (`ResearchLeaves4`, `TextbookLeaves`) and `GluePieces4` imply
`ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leavesR3 r.toR3 t (gluePieces_of_gluePieces4 r t gp)

/-- The same with g0-assemble2's `ResearchLeaves3` and the weight clause `R10Weights`. -/
theorem sixContactMin_of_leaves4' (r : ResearchLeaves3) (hW : ZInQ.Contrib.G9.G9Bridge.R10Weights)
    (t : TextbookLeaves) (gp : GluePieces4) : ZInQ.SixContactMin :=
  sixContactMin_of_leaves4 (researchLeaves4_of r hW) t gp

end HSyn

end

#print axioms HSyn.gluePieces_of_gluePieces4
#print axioms HSyn.sixContactMin_of_leaves4
#print axioms HSyn.sixContactMin_of_leaves4'
#print axioms HSyn.ResearchLeaves4.toR3
#print axioms ZInQ.UnifDims.productModelHeight_of_unifOfDim
#print axioms G0ModField.unramifiedConjugates
#print axioms X6Kummer.x6KummerFibre_of_conic
#print axioms MulRigidity.mulIsogeny
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_t5
#print axioms RvGP2.burnsideAbsIrred
#print axioms G0ModField.KernelField.endTransport
#print axioms G0ModField.KernelField.oMaximal
#print axioms ZInQ.Contrib.R10.g9Glue_of_deRhamComparisonHT
#print axioms G0Galois.conjTwistNontrivial_of_leaves
#print axioms ZInQ.HeightBC.cotangentSpanBC
#print axioms ZInQ.HeightBC.uniformizationLiftAnalytic
#print axioms ZInQ.ProductUnif.productUnifSplits
#print axioms ZInQ.DefFaltings.HodgeLattice.tangentDimAtOrigin
#print axioms PropTSGlue.propTSAll_of_pieces''
#print axioms HSyn.LinkedTate.linkedTateData_of_frobRam

end G0A3_z95_bundle4

section G0A3_z95b_homunify
/-! ## assemble-port: hom-unify's leaf `HomLatticeCorr` (mk/mk_z95b.py) -/

section HomUnifySec

namespace HomUnify

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3
open ZInQ.LeafPush2 (CPts IsUniformization)

/-- **The analytic representation of homomorphisms (textbook LEAF; the single leaf proposed by
hom-unify for T11(a) in `Hom` form).** Let `A`, `B` be abelian varieties over a field `K`,
`σ : K → ℂ`, and `Φ_A : ℂ^g → A(ℂ)_σ`, `Φ_B : ℂ^h → B(ℂ)_σ` analytic uniformizations with kernels
`Λ_A`, `Λ_B` (`g = dim A`, `h = dim B`).
1. (lifting) every homomorphism `f : A → B` lifts to a `ℂ`-linear `M : ℂ^g → ℂ^h` with
   `Φ_B(Mz) = f(Φ_A(z))`;
2. (realization, over `ℂ`) if `K = ℂ` and `σ = id`, every `ℂ`-linear `M : ℂ^g → ℂ^h` with
   `MΛ_A ⊆ Λ_B` is induced in this way by a unique homomorphism `f : A → B`.

Together: `Hom(A_ℂ, B_ℂ) ≅ {M ∈ Hom_ℂ(ℂ^g, ℂ^h) : MΛ_A ⊆ Λ_B}`, `f ↦ ρ_a(f)`, and for general `K`
the analytic representation of `f` is that of `f_ℂ`. Sources (all UNVERIFIED numbers):
Birkenhake–Lange, *Complex abelian varieties*, §1.2 (Prop. 1.2.1: homomorphisms of complex tori
`ℂ^g/Λ → ℂ^h/Λ'` are exactly the maps induced by `ℂ`-linear `M` with `MΛ ⊆ Λ'`, and the analytic
representation is injective); Mumford, *Abelian varieties*, §1 (the complex torus `A(ℂ)`) and
§3 (`A ↦ A^an` is fully faithful on abelian varieties); Serre, GAGA (1956) / Chow, for
"holomorphic ⇒ algebraic" in 2.; holomorphy of algebraic morphisms for 1. -/
def HomLatticeCorr : Prop :=
  (∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∀ f : PkgI3.AbVar.Hom A B, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ),
      ∀ z, ΦB (M z) = ΦA z ≫ f.hom) ∧
  (∀ (A B : PkgI3.AbVar ℂ) (g h : ℕ) (ΛA : Submodule ℤ (Fin g → ℂ))
    (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (ΦB : (Fin h → ℂ) → CPts B (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) ΛA ΦA → IsUniformization (RingHom.id ℂ) ΛB ΦB →
    ∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), (∀ z ∈ ΛA, M z ∈ ΛB) →
      ∃! f : PkgI3.AbVar.Hom A B, ∀ z, ΦB (M z) = ΦA z ≫ f.hom)

/-- **`HomLinearLift` from `HomLatticeCorr` (proved):** its first clause. -/
theorem homLinearLift_of_corr (h : HomLatticeCorr) : G0Galois.HomLinearLift := h.1

theorem t11a_riemannEnd_of_corr (h : HomLatticeCorr) : ZInQ.LeafPush2.T11a_RiemannEnd :=
  fun A g Λ Φ hA hU =>
    ⟨fun M hM => h.2 A A g g Λ Λ Φ Φ hA hA hU hU M hM,
     fun f => h.1 ℂ A A (RingHom.id ℂ) g g Λ Λ Φ Φ hA hA hU hU f⟩

/-- **`T11aRiemannHom` (period-glue's T11(a) in `Hom` form) from `HomLatticeCorr` (proved):** the realization clause at
`h = g` and the lifting clause at `K = ℂ`, `σ = id`. -/
theorem t11aRiemannHom_of_corr (h : HomLatticeCorr) : HSyn.G0Split.FibreQM.PeriodGlue.T11aRiemannHom :=
  fun A A' g Λ Λ' Φ Φ' hA hA' hU hU' =>
    ⟨fun M hM => h.2 A A' g g Λ Λ' Φ Φ' hA hA' hU hU' M hM,
     fun f => h.1 ℂ A A' (RingHom.id ℂ) g g Λ Λ' Φ Φ' hA hA' hU hU' f⟩

end HomUnify

end HomUnifySec

#print axioms HomUnify.t11a_riemannEnd_of_corr
#print axioms HomUnify.t11aRiemannHom_of_corr

end G0A3_z95b_homunify

section G0A3_z96_ltgoodred
/-! ## assemble-port: lt-goodred, `scratch/lt-goodred/integ/99d_proofs.lean` verbatim minus `#print` (mk/mk_z96.py) -/

/-! ## lt-goodred (integration copy): neron-lg's DVR classification (from parts/10_copies.lean) -/

section LTGoodRedNLGSec

noncomputable section

namespace LTGoodRed.NLG

open NumberField

/-- The discrete valuation ring `𝓞_{L,v}` of a nonzero prime `v` of `𝓞_L`, as a valuation subring
of `L` (the ring of the `v`-adic valuation). -/
noncomputable def dvrAt {L : Type} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : ValuationSubring L :=
  (v.valuation L).valuationSubring

instance {L : Type} [Field L] [NumberField L] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    IsDiscreteValuationRing (dvrAt v) := by
  unfold dvrAt; infer_instance

section Restrict

variable {K : Type} [Field K] [NumberField K]

/-- Every valuation subring of a number field contains `𝓞_K` (it is integrally closed). -/
theorem ringOfIntegers_mem (O : ValuationSubring K) (x : 𝓞 K) : (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral O (x : K) from x.isIntegral_coe.tower_top)
  exact hy ▸ y.2

/-- The inclusion `𝓞_K → O`. -/
def toO (O : ValuationSubring K) : 𝓞 K →+* O :=
  (algebraMap (𝓞 K) K).codRestrict O.toSubring (ringOfIntegers_mem O)

theorem toO_coe (O : ValuationSubring K) (x : 𝓞 K) : ((toO O x : O) : K) = algebraMap (𝓞 K) K x :=
  rfl

/-- The center of a valuation subring `O ≠ ⊤` of a number field on `𝓞_K`: a nonzero prime. -/
def center' (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := (IsLocalRing.maximalIdeal O).comap (toO O)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy⟩ : ∃ y : K, y ∉ O := by
      by_contra h
      push_neg at h
      exact hO (eq_top_iff.2 fun y _ => h y)
    have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
    have hyi : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hy
    let x : O := ⟨y⁻¹, hyi⟩
    have hx : x ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu'⟩ := hu
      apply hy
      have : ((u⁻¹ : Oˣ) : O) * x = 1 := by rw [← hu']; exact u.inv_mul
      have h2 : ((((u⁻¹ : Oˣ) : O) : K)) * y⁻¹ = 1 := congrArg Subtype.val this
      have h3 : y = (((u⁻¹ : Oˣ) : O) : K) := by
        field_simp at h2
        exact h2.symm
      rw [h3]; exact (((u⁻¹ : Oˣ) : O)).2
    have hx0 : x ≠ 0 := fun h => inv_ne_zero hy0 (congrArg Subtype.val h)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (x : K)
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero hb
    have ha : toO O a = x * toO O b := by
      apply Subtype.ext
      rw [toO_coe, Subring.coe_mul, toO_coe, ← hab, div_mul_cancel₀ _ hb0]
    intro hbot
    have hmem : a ∈ (IsLocalRing.maximalIdeal O).comap (toO O) := by
      rw [Ideal.mem_comap, ha]; exact Ideal.mul_mem_right _ _ hx
    rw [hbot, Ideal.mem_bot] at hmem
    apply hx0
    apply Subtype.ext
    rw [← hab, hmem, map_zero, zero_div]; rfl

/-- **Every valuation subring `O ≠ ⊤` of a number field is `𝓞_{K,v}` (proved).** -/
theorem dvrAt_center' (O : ValuationSubring K) (hO : O ≠ ⊤) : dvrAt (center' O hO) = O := by
  apply ValuationSubring.eq_of_le_of_ne_top _ _ hO
  intro x hx
  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (center' O hO) x hx
  have hd : IsUnit (toO O d) := by
    by_contra h
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hvd : O.valuation (algebraMap (𝓞 K) K d) = 1 := (O.valuation_eq_one_iff _).1 hd
  apply O.mem_of_valuation_le_one
  have h2 := congrArg O.valuation hnd
  rw [map_mul, hvd, _root_.mul_one] at h2
  rw [h2]
  exact O.valuation_le_one (toO O n)

/-- Every valuation subring `O ≠ ⊤` of a number field is a DVR. -/
theorem isDiscreteValuationRing_of_ne_top (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by
  rw [← dvrAt_center' O hO]
  infer_instance

end Restrict

end LTGoodRed.NLG

end

end LTGoodRedNLGSec

/-! ## lt-goodred §2: `GoodRedTorsion` (copied verbatim) and its proof

`GoodRedTorsion` is copied verbatim from `scratch/linked-tate/parts/98_g3tate.lean` (L33-62).
Proof (`goodRedTorsion`): with `Ω = \bar{L'}`,
* `g = qEmbRing L' : ℚ̄ → Ω` is bijective and `g ∘ resQ σ' = σ' ∘ g` (`resQ_spec`);
* `τ : Ω ≃ₐ[K] \bar K` (both are algebraic closures of `K`); `ψ = g⁻¹ ∘ τ⁻¹ : \bar K ≃ ℚ̄`;
* `w = ψ^*(v)`, a valuation ring of `\bar K`, and `O = w ∩ K`, a valuation ring of the number field
  `K` with `p ∈ 𝔪_O`, hence `≠ K` and a DVR (neron-lg's classification); `3` and `ℓⁿ` are units
  in `O` because they are prime to `p`;
* `σ_K = τ σ' τ⁻¹` lies in the inertia group of `w` (transport of the inertia condition of
  `resQ σ'` at `v` along `ψ`, using `ψ ∘ σ_K = resQ σ' ∘ ψ`);
* NOS (a) ⇒ (b) at `(O, w)` makes `σ_K` fix `A(\bar K)[ℓⁿ]`;
* the points: `E = trPt τ ∘ bcPt ∘ bcPt : A_{L,L'}(Ω) ≃* A(\bar K)` is multiplicative and carries the
  action of `σ'` to that of `σ_K` (`bcPt_galAct` twice, `trPt_galAct`). -/

section LTGoodRedSec

set_option linter.style.haveILetI false

noncomputable section

open scoped Pointwise

-- (`HSyn.LinkedTate.GoodRedTorsion` is linked-tate's own definition here)

namespace LTGoodRed

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-! ### Valuation rings: nonunits, coprime integers, inertia (Mathlib only) -/

section Val

variable {F₁ F₂ : Type} [Field F₁] [Field F₂]

/-- Nonunits of a pulled-back valuation ring. -/
theorem mem_nonunits_comap (A : ValuationSubring F₂) (ψ : F₁ ≃+* F₂) (x : F₁) :
    x ∈ (A.comap (ψ : F₁ →+* F₂)).nonunits ↔ ψ x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap]
  have h0 : x = 0 ↔ ψ x = 0 := (map_eq_zero_iff ψ ψ.injective).symm
  have h1 : (ψ : F₁ →+* F₂) x⁻¹ = (ψ x)⁻¹ := map_inv₀ ψ x
  rw [h1, h0]

/-- An integer prime to `p` is a unit in a valuation ring in which `p` is not. -/
theorem natCast_notMem_nonunits (A : ValuationSubring F₁) {p m : ℕ}
    (hp : (p : F₁) ∈ A.nonunits) (hm : Nat.Coprime m p) : (m : F₁) ∉ A.nonunits := by
  intro hmn
  have hp' : (p : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; simpa using hp
  have hm' : (m : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; simpa using hmn
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hm
  have hsum : (u : A) * (m : A) + (w : A) * (p : A) = 1 := by
    have := congrArg (Int.cast : ℤ → A) huw
    push_cast at this
    exact this
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hsum]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm') (Ideal.mul_mem_left _ _ hp')
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- The inverse of a nonzero element outside the nonunits lies in the ring. -/
theorem inv_mem_of_notMem_nonunits (A : ValuationSubring F₁) {x : F₁} (hx : x ∉ A.nonunits) :
    x ≠ 0 ∧ x⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hx
  exact hx

variable (K : Type) [Field K] {L : Type} [Field L] [Algebra K L]

/-- The concrete form of an inertia element: it preserves `A` and acts trivially modulo the
maximal ideal. -/
theorem of_mem_inertia (A : ValuationSubring L) (σ : A.decompositionSubgroup K)
    (hσ : σ ∈ A.inertiaSubgroup K) :
    (∀ x, (σ : L ≃ₐ[K] L) x ∈ A ↔ x ∈ A) ∧
      ∀ a ∈ A, (σ : L ≃ₐ[K] L) a - a ∈ A.nonunits := by
  have hs : (σ : L ≃ₐ[K] L) • A = A := σ.2
  constructor
  · intro x
    have key : ∀ y, y ∈ A ↔ ((σ : L ≃ₐ[K] L)⁻¹ • y) ∈ A := fun y => by
      conv_lhs => rw [← hs]
      exact ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
    rw [key ((σ : L ≃ₐ[K] L) x)]
    rw [show ((σ : L ≃ₐ[K] L)⁻¹ • (σ : L ≃ₐ[K] L) x) = x by
      rw [AlgEquiv.smul_def, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]]
  · intro a ha
    have h0 : (σ • IsLocalRing.residue A ⟨a, ha⟩ : IsLocalRing.ResidueField A) =
        IsLocalRing.residue A ⟨a, ha⟩ :=
      DFunLike.congr_fun (MonoidHom.mem_ker.mp hσ) (IsLocalRing.residue A ⟨a, ha⟩)
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff] at h0
    exact h0

/-- Conversely, the concrete conditions give PkgI2's `IsInertia`. -/
theorem isInertia_of (A : ValuationSubring L) (σ : L ≃ₐ[K] L)
    (h1 : ∀ x, σ x ∈ A ↔ x ∈ A) (h2 : ∀ a ∈ A, σ a - a ∈ A.nonunits) :
    PkgI2.IsInertia A σ := by
  have hd : σ ∈ A.decompositionSubgroup K := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h1 (σ⁻¹ • x)]
    rw [show σ (σ⁻¹ • x) = x by
      rw [AlgEquiv.smul_def, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]]
  refine ⟨hd, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  ext r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨σ, hd⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a =
    IsLocalRing.residue A a
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  exact h2 a a.2

end Val

/-! ### The proof of `GoodRedTorsion` -/

set_option maxHeartbeats 1000000 in
/-- **`GoodRedTorsion`, proved** (Mathlib, the copied `bcPt`/`trPt` and neron-lg's DVR
classification; NOS enters as the hypothesis of the Prop). -/
theorem goodRedTorsion : HSyn.LinkedTate.GoodRedTorsion := by
  intro hNOS K L L' _ hKL hLL' A hA ℓ _
  letI hNF : NumberField L' := numberField_of_fd L'
  intro p hp hp3 hpl v hv σ' hσ n x hx
  -- `K` is a number field
  haveI hKfd : FiniteDimensional ℚ K := FiniteDimensional.of_injective
    (IntermediateField.inclusion (hKL.trans hLL')).toLinearMap
    (IntermediateField.inclusion (hKL.trans hLL')).toRingHom.injective
  haveI hKNF : NumberField K := numberField_of_fd K
  letI iKL : Algebra K L := incAlg hKL
  letI iLL' : Algebra L L' := incAlg hLL'
  letI iKL' : Algebra K L' := incAlg (hKL.trans hLL')
  haveI tKLL' : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tLΩ : IsScalarTower L L' (AlgebraicClosure L') := inferInstance
  haveI tKL'Ω : IsScalarTower K L' (AlgebraicClosure L') := inferInstance
  haveI tKLΩ : IsScalarTower K L (AlgebraicClosure L') := IsScalarTower.of_algebraMap_eq
    (fun y => by
      rw [IsScalarTower.algebraMap_apply K L' (AlgebraicClosure L'),
        IsScalarTower.algebraMap_apply L L' (AlgebraicClosure L'),
        IsScalarTower.algebraMap_apply K L L'])
  -- `Ω = \bar{L'}` is an algebraic closure of `K`
  haveI tQKL' : IsScalarTower ℚ K L' := IsScalarTower.of_algebraMap_eq (fun q => by
    rw [eq_ratCast (algebraMap ℚ L') q, eq_ratCast (algebraMap ℚ K) q, map_ratCast])
  haveI : Algebra.IsAlgebraic ℚ L' := Algebra.IsAlgebraic.of_finite ℚ L'
  haveI : Algebra.IsAlgebraic K L' := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : Algebra.IsAlgebraic L' (AlgebraicClosure L') := AlgebraicClosure.isAlgebraic L'
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure L') :=
    Algebra.IsAlgebraic.trans K L' (AlgebraicClosure L')
  haveI : IsAlgClosure K (AlgebraicClosure L') := ⟨inferInstance, inferInstance⟩
  let τ : AlgebraicClosure L' ≃ₐ[K] AlgebraicClosure K :=
    IsAlgClosure.equiv K (AlgebraicClosure L') (AlgebraicClosure K)
  -- `g : ℚ̄ → Ω` is bijective
  let g : PkgI4.Qbar →ₐ[ℚ] AlgebraicClosure L' := (G0Galois.qEmbRing L').toRatAlgHom
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L') :=
    Algebra.IsAlgebraic.trans ℚ L' (AlgebraicClosure L')
  have hgbij : Function.Bijective g := by
    letI : Algebra PkgI4.Qbar (AlgebraicClosure L') := g.toAlgebra
    haveI : IsScalarTower ℚ PkgI4.Qbar (AlgebraicClosure L') :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L') := inferInstance
    haveI : Algebra.IsIntegral PkgI4.Qbar (AlgebraicClosure L') := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ge : PkgI4.Qbar ≃+* AlgebraicClosure L' := RingEquiv.ofBijective (G0Galois.qEmbRing L') hgbij
  have hge : ∀ z, ge z = G0Galois.qEmbRing L' z := fun _ => rfl
  -- the transport `ψ : \bar K ≃ ℚ̄`, the place `w` of `\bar K` and `O = w ∩ K`
  let ψ : AlgebraicClosure K ≃+* PkgI4.Qbar := τ.symm.toRingEquiv.trans ge.symm
  have hψ : ∀ y, ψ y = ge.symm (τ.symm y) := fun _ => rfl
  let w : ValuationSubring (AlgebraicClosure K) := v.comap (ψ : AlgebraicClosure K →+* PkgI4.Qbar)
  let O : ValuationSubring K := w.comap (algebraMap K (AlgebraicClosure K))
  -- `p ∈ 𝔪_w`
  have hpw : ((p : ℕ) : AlgebraicClosure K) ∈ w.nonunits := by
    rw [mem_nonunits_comap v ψ, map_natCast]; exact hv
  -- integers prime to `p` are units of `O`
  have hunit : ∀ m : ℕ, Nat.Coprime m p → IsUnit (m : O) := by
    intro m hm
    obtain ⟨hm0, hmi⟩ := inv_mem_of_notMem_nonunits w (natCast_notMem_nonunits w hpw hm)
    have hm0K : (m : K) ≠ 0 := by
      intro h; apply hm0
      rw [← map_natCast (algebraMap K (AlgebraicClosure K)), h, map_zero]
    have hmO : (m : K)⁻¹ ∈ O := by
      rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]; exact hmi
    refine isUnit_iff_exists_inv.mpr ⟨⟨(m : K)⁻¹, hmO⟩, Subtype.ext ?_⟩
    push_cast
    exact mul_inv_cancel₀ hm0K
  -- `O ≠ K`: `p⁻¹ ∉ O`
  have hOtop : O ≠ ⊤ := by
    intro htop
    have hpi : ((p : K))⁻¹ ∈ O := by rw [htop]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at hpi
    rw [ValuationSubring.mem_nonunits_iff_or] at hpw
    rcases hpw with h | h
    · exact hp.ne_zero (by exact_mod_cast h)
    · exact h hpi
  haveI hODVR : IsDiscreteValuationRing O := NLG.isDiscreteValuationRing_of_ne_top O hOtop
  -- `3` and `ℓⁿ` are units in `O`
  have hp3' : p ≠ 3 := fun h => hp3 (by rw [h]; exact Finset.mem_singleton_self 3)
  have h3 : IsUnit (3 : O) := by
    have := hunit 3 ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3'))
    exact_mod_cast this
  have hℓp : Nat.Coprime (ℓ ^ n) p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes (Fact.out : ℓ.Prime) hp).mpr (Ne.symm hpl))
  -- NOS (a) ⇒ (b) at `(O, w)`
  have htriv := ((hNOS K O w rfl (ObjBridge.toGrp A)).1.mp (hA O h3)) (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (by exact_mod_cast hunit (ℓ ^ n) hℓp)
  -- the inertia element `σ_K = τ σ' τ⁻¹` at `w`
  obtain ⟨σ, hσI, hσeq⟩ := hσ
  obtain ⟨hv1, hv2⟩ := of_mem_inertia ℚ v σ hσI
  rw [hσeq] at hv1 hv2
  let s' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L' := σ'
  let σK : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    (τ.symm.trans (s'.restrictScalars K)).trans τ
  have hσK : ∀ y, σK y = τ (s' (τ.symm y)) := fun _ => rfl
  have hres : ∀ y, ψ (σK y) = (G0Galois.resQ L' σ') (ψ y) := by
    intro y
    apply ge.injective
    show ge (ge.symm (τ.symm (σK y))) = ge ((G0Galois.resQ L' σ') (ge.symm (τ.symm y)))
    rw [RingEquiv.apply_symm_apply, hσK, AlgEquiv.symm_apply_apply]
    have hspec := G0Galois.resQ_spec L' σ' (ge.symm (τ.symm y))
    rw [← hge, ← hge, RingEquiv.apply_symm_apply] at hspec
    exact hspec.symm
  have hI : PkgI2.IsInertia w σK := by
    refine isInertia_of K w σK (fun y => ?_) (fun a ha => ?_)
    · show ψ (σK y) ∈ v ↔ ψ y ∈ v
      rw [hres]; exact hv1 (ψ y)
    · rw [mem_nonunits_comap v ψ, map_sub, hres]
      exact hv2 (ψ a) ha
  -- the points
  let E := (UnramTate.bcPt (K := L) (L := L') (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL))
    (AlgebraicClosure L')).trans ((UnramTate.bcPt (K := K) (L := L) A (AlgebraicClosure L')).trans
      (UnramTate.trPt A τ))
  have hE : ∀ y, E ((@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct s' y) =
      A.galAct σK (E y) := by
    intro y
    show UnramTate.trPt A τ (UnramTate.bcPt (K := K) (L := L) A (AlgebraicClosure L')
        (UnramTate.bcPt (K := L) (L := L') (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL))
          (AlgebraicClosure L')
          ((@PkgI3.AbVar.baseChange L _
            (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct s' y))) = _
    rw [UnramTate.bcPt_galAct, UnramTate.bcPt_galAct]
    exact UnramTate.trPt_galAct A τ _ σK (fun z => by rw [hσK, AlgEquiv.symm_apply_apply]; rfl) _
  have hEx : E x ^ (ℓ ^ n) = 1 := by rw [← map_pow, hx, map_one]
  have hfix : A.galAct σK (E x) = E x := htriv σK hI (E x) hEx
  apply E.injective
  exact (hE x).trans hfix

end LTGoodRed

end

end LTGoodRedSec


/-! ## lt-goodred §4: `QMEndRank` reduced to I3.M1, T27 and one algebraic glue Prop

* `rank ≥ 4` (proved, `four_le_finrank`): `𝒪 ≅ ℤ⁴` (`ofIntHom`) and `endBC ∘ endBC ∘ ι` is an
  injective ring map `𝒪 → End(A')`; `End(A')` is finite over `ℤ` by I3.M1.
* `rank ≤ rank End(A'_Ω)` (proved, `finrank_le_baseChange`): `endBC` is injective, I3.M1.
* T27 at `A'' = A'_Ω`, `Ω = \bar{L'}`: its hypotheses are proved here: `dim A'' = 2`
  (`pkgI3_dim_baseChange`, three times), `B = (2,−3)` is a division algebra (`quatB6_isUnit`: the
  norm form `x₀² − 2x₁² + 3x₂² − 6x₃²` is anisotropic over `ℚ`, 3-adic descent), and
  `B →ₐ[ℚ] End⁰(A'')` (`quatEmbed`, from `ι` and base change).
* Case `End⁰(A'') ≅ B`: `rank End(A'') = dim_ℚ End⁰(A'') = 4` (proved).
* Case `End⁰(A'') ≅ M₂(ℚ(√d))`, `d < 0`: the named glue Prop `QMSplitCaseRank`. -/

section LTQMRankSec

set_option linter.style.haveILetI false

noncomputable section

namespace LTGoodRed.QM

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField LeafQM
open scoped Quaternion TensorProduct

/-! ### `𝒪 ≅ ℤ⁴` and the lower bound -/

theorem ofInt_injective : Function.Injective ofInt := by
  intro n m h
  have h0 := congrArg QuaternionAlgebra.re h
  have h1 := congrArg QuaternionAlgebra.imI h
  have h2 := congrArg QuaternionAlgebra.imJ h
  have h3 := congrArg QuaternionAlgebra.imK h
  simp only [ofInt] at h0 h1 h2 h3
  have e2 : (n 2 : ℚ) = m 2 := by linarith
  have e3 : (n 3 : ℚ) = m 3 := by linarith
  have e0 : (n 0 : ℚ) = m 0 := by linarith
  have e1 : (n 1 : ℚ) = m 1 := by linarith
  funext i
  fin_cases i
  · exact_mod_cast e0
  · exact_mod_cast e1
  · exact_mod_cast e2
  · exact_mod_cast e3

/-- `n ↦ ofInt n`, an additive bijection `ℤ⁴ → 𝒪`. -/
def ofIntHom : (Fin 4 → ℤ) →+ O where
  toFun n := ⟨ofInt n, n, rfl⟩
  map_zero' := Subtype.ext ofInt_zero
  map_add' n m := Subtype.ext (ofInt_add n m).symm

theorem ofIntHom_injective : Function.Injective ofIntHom :=
  fun n m h => ofInt_injective (congrArg Subtype.val h)

/-- **`rank End(A) ≥ 4` for a QM abelian variety** (proved; I3.M1 for finiteness). -/
theorem four_le_finrank (hM1 : PkgI3.HomFreeFinite) {k : Type} [Field k] (A : PkgI3.AbVar k)
    (φ : O →+* PkgI3.AbVar.End A) (hφ : Function.Injective φ) :
    4 ≤ Module.finrank ℤ (PkgI3.AbVar.End A) := by
  obtain ⟨-, hfin, -, -⟩ := hM1 k A A
  let F : (Fin 4 → ℤ) →+ PkgI3.AbVar.End A := φ.toAddMonoidHom.comp ofIntHom
  have hF : Function.Injective F := hφ.comp ofIntHom_injective
  have := LinearMap.finrank_le_finrank_of_injective (f := F.toIntLinearMap) hF
  rwa [Module.finrank_fin_fun] at this

/-- **`rank End(A) ≤ rank End(A_Ω)`** (proved; `endBC` is injective, I3.M1). -/
theorem finrank_le_baseChange (hM1 : PkgI3.HomFreeFinite) {k : Type} [Field k]
    (A : PkgI3.AbVar k) (Ω : Type) [Field Ω] [Algebra k Ω] :
    Module.finrank ℤ (PkgI3.AbVar.End A) ≤
      Module.finrank ℤ (PkgI3.AbVar.End (A.baseChange Ω)) := by
  obtain ⟨-, hfin, -, -⟩ := hM1 Ω (A.baseChange Ω) (A.baseChange Ω)
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (HSyn.LinkedTate.endBC A Ω).toAddMonoidHom.toIntLinearMap)
    (HSyn.LinkedTate.endBC_injective A Ω)

/-- `rank_ℤ End(A) = dim_ℚ End⁰(A)` (I3.M1: `End(A)` is free). -/
theorem finrank_end0 (hM1 : PkgI3.HomFreeFinite) {k : Type} [Field k] (A : PkgI3.AbVar k) :
    Module.finrank ℚ (PkgI3.AbVar.End0 A) = Module.finrank ℤ (PkgI3.AbVar.End A) := by
  obtain ⟨hfree, -, -, -⟩ := hM1 k A A
  exact Module.finrank_baseChange

/-! ### `B = (2, −3)` is a division algebra -/

theorem mod3_step (a b e : ℤ) (h : a ^ 2 - 2 * b ^ 2 + 3 * e = 0) : 3 ∣ a ∧ 3 ∣ b := by
  have h3 : (3 : ZMod 3) = 0 := rfl
  have hc := congrArg (Int.cast : ℤ → ZMod 3) h
  push_cast at hc
  have h' : ((a : ZMod 3)) ^ 2 + ((b : ZMod 3)) ^ 2 = 0 := by
    linear_combination hc + ((b : ZMod 3) ^ 2 - (e : ZMod 3)) * h3
  have key : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
  obtain ⟨ha, hb⟩ := key _ _ h'
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha, (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hb⟩

theorem pow3_dvd (k : ℕ) : ∀ a b c d : ℤ, a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 →
    3 ^ k ∣ a ∧ 3 ^ k ∣ b ∧ 3 ^ k ∣ c ∧ 3 ^ k ∣ d := by
  induction k with
  | zero => intro a b c d _; simp
  | succ k ih =>
    intro a b c d h
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := mod3_step a b (c ^ 2 - 2 * d ^ 2) (by linear_combination h)
    have h' : (3 : ℤ) * (c ^ 2 - 2 * d ^ 2 + 3 * (a' ^ 2 - 2 * b' ^ 2)) = 0 := by
      linear_combination h
    obtain ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩ := mod3_step c d (a' ^ 2 - 2 * b' ^ 2)
      ((mul_eq_zero.mp h').resolve_left (by norm_num))
    have h'' : (9 : ℤ) * (a' ^ 2 - 2 * b' ^ 2 + 3 * c' ^ 2 - 6 * d' ^ 2) = 0 := by
      linear_combination h
    obtain ⟨h1, h2, h3, h4⟩ := ih a' b' c' d' ((mul_eq_zero.mp h'').resolve_left (by norm_num))
    rw [pow_succ']
    exact ⟨mul_dvd_mul_left 3 h1, mul_dvd_mul_left 3 h2, mul_dvd_mul_left 3 h3,
      mul_dvd_mul_left 3 h4⟩

theorem eq_zero_of_pow3_dvd (a : ℤ) (h : ∀ k : ℕ, 3 ^ k ∣ a) : a = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h a.natAbs)
  rw [Int.natAbs_pow]
  exact Nat.lt_pow_self (by norm_num)

/-- The norm form of `B` is anisotropic over `ℤ`. -/
theorem norm6_int (a b c d : ℤ) (h : a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 :=
  ⟨eq_zero_of_pow3_dvd a fun k => (pow3_dvd k a b c d h).1,
    eq_zero_of_pow3_dvd b fun k => (pow3_dvd k a b c d h).2.1,
    eq_zero_of_pow3_dvd c fun k => (pow3_dvd k a b c d h).2.2.1,
    eq_zero_of_pow3_dvd d fun k => (pow3_dvd k a b c d h).2.2.2⟩

/-- The norm form of `B` is anisotropic over `ℚ`. -/
theorem norm6_rat (q0 q1 q2 q3 : ℚ) (h : q0 ^ 2 - 2 * q1 ^ 2 + 3 * q2 ^ 2 - 6 * q3 ^ 2 = 0) :
    q0 = 0 ∧ q1 = 0 ∧ q2 = 0 ∧ q3 = 0 := by
  have hd0 : (q0.den : ℚ) ≠ 0 := by exact_mod_cast q0.den_nz
  have hd1 : (q1.den : ℚ) ≠ 0 := by exact_mod_cast q1.den_nz
  have hd2 : (q2.den : ℚ) ≠ 0 := by exact_mod_cast q2.den_nz
  have hd3 : (q3.den : ℚ) ≠ 0 := by exact_mod_cast q3.den_nz
  set D : ℚ := q0.den * q1.den * q2.den * q3.den with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hd0 hd1) hd2) hd3
  have e0 : ((q0.num * q1.den * q2.den * q3.den : ℤ) : ℚ) = q0 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q0]; ring
  have e1 : ((q1.num * q0.den * q2.den * q3.den : ℤ) : ℚ) = q1 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q1]; ring
  have e2 : ((q2.num * q0.den * q1.den * q3.den : ℤ) : ℚ) = q2 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q2]; ring
  have e3 : ((q3.num * q0.den * q1.den * q2.den : ℤ) : ℚ) = q3 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q3]; ring
  have hZ := norm6_int (q0.num * q1.den * q2.den * q3.den) (q1.num * q0.den * q2.den * q3.den)
    (q2.num * q0.den * q1.den * q3.den) (q3.num * q0.den * q1.den * q2.den) (by
      have : (((q0.num * q1.den * q2.den * q3.den : ℤ) : ℚ)) ^ 2
          - 2 * (((q1.num * q0.den * q2.den * q3.den : ℤ) : ℚ)) ^ 2
          + 3 * (((q2.num * q0.den * q1.den * q3.den : ℤ) : ℚ)) ^ 2
          - 6 * (((q3.num * q0.den * q1.den * q2.den : ℤ) : ℚ)) ^ 2 = 0 := by
        rw [e0, e1, e2, e3]; linear_combination D ^ 2 * h
      exact_mod_cast this)
  obtain ⟨z0, z1, z2, z3⟩ := hZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := e0; rw [z0, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0
  · have := e1; rw [z1, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0
  · have := e2; rw [z2, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0
  · have := e3; rw [z3, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0

/-- **`B = (2,−3)_ℚ` is a division algebra** (proved): `x · x̄ = n(x)` with `n` anisotropic. -/
theorem quatB6_isUnit : ∀ x : ℍ[ℚ, 2, -3], x ≠ 0 → IsUnit x := by
  intro x hx
  have hn : (x * star x).re = x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 := by
    simp [QuaternionAlgebra.re_mul]; ring
  have hn0 : (x * star x).re ≠ 0 := by
    intro h0
    rw [hn] at h0
    obtain ⟨z0, z1, z2, z3⟩ := norm6_rat _ _ _ _ h0
    exact hx (QuaternionAlgebra.ext z0 z1 z2 z3)
  set n := (x * star x).re with hndef
  have hxs : x * star x = (n : ℍ[ℚ, 2, -3]) := QuaternionAlgebra.mul_star_eq_coe x
  have hsx : star x * x = (n : ℍ[ℚ, 2, -3]) := by rw [← hxs]; exact (star_comm_self' x)
  have hinv : (n⁻¹ : ℚ) • (n : ℍ[ℚ, 2, -3]) = 1 := by
    rw [← QuaternionAlgebra.coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul, inv_mul_cancel₀ hn0,
      QuaternionAlgebra.coe_one]
  refine isUnit_iff_exists.mpr ⟨n⁻¹ • star x, ?_, ?_⟩
  · rw [mul_smul_comm, hxs, hinv]
  · rw [smul_mul_assoc, hsx, hinv]

/-! ### `B →ₐ[ℚ] End⁰(A)` from a QM structure -/

/-- `i ∈ 𝒪`. -/
def oI' : O := ⟨ofInt ![0, 1, 0, 0], _, rfl⟩
/-- `j = 2·(1+j)/2 − 1 ∈ 𝒪`. -/
def oJ' : O := ⟨ofInt ![-1, 0, 2, 0], _, rfl⟩

theorem oI'_mul_oI' : oI' * oI' = 2 := by
  apply Subtype.ext
  show ofInt ![0, 1, 0, 0] * ofInt ![0, 1, 0, 0] = 2
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem oJ'_mul_oJ' : oJ' * oJ' = -3 := by
  apply Subtype.ext
  show ofInt ![-1, 0, 2, 0] * ofInt ![-1, 0, 2, 0] = -3
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem oJ'_mul_oI' : oJ' * oI' = -(oI' * oJ') := by
  apply Subtype.ext
  show ofInt ![-1, 0, 2, 0] * ofInt ![0, 1, 0, 0] = -(ofInt ![0, 1, 0, 0] * ofInt ![-1, 0, 2, 0])
  ext <;> simp [ofInt] <;> norm_num

/-- **`B →ₐ[ℚ] End⁰(A)` from a ring map `𝒪 → End(A)`** (proved: `i ↦ 1 ⊗ φ(i)`, `j ↦ 1 ⊗ φ(j)`,
Mathlib's `QuaternionAlgebra.Basis.liftHom`). -/
theorem quatEmbed {k : Type} [Field k] (A : PkgI3.AbVar k) (φ : O →+* PkgI3.AbVar.End A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) := by
  let ψ : O →+* PkgI3.AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] PkgI3.AbVar.End0 A).toRingHom.comp φ
  refine ⟨QuaternionAlgebra.Basis.liftHom
    { i := ψ oI', j := ψ oJ', k := ψ oI' * ψ oJ',
      i_mul_i := ?_, j_mul_j := ?_, i_mul_j := rfl, j_mul_i := ?_ }⟩
  · rw [← map_mul, oI'_mul_oI', map_ofNat, zero_smul, add_zero, Algebra.smul_def, _root_.mul_one,
      map_ofNat]
  · rw [← map_mul, oJ'_mul_oJ', map_neg, map_ofNat, Algebra.smul_def, _root_.mul_one, map_neg,
      map_ofNat]
  · rw [← map_mul, oJ'_mul_oI', map_neg, map_mul, zero_smul, zero_sub]

/-! ### The reduction -/

/-- **Glue (algebra; Albert's classification for simple abelian surfaces in characteristic 0,
Mumford §21, numbering UNVERIFIED): the split geometric case.** For an abelian surface `A` over a
field `k` of characteristic `0` with an injective ring map `ι : 𝒪 → End_k(A)` and `EndDivision A`,
if `End⁰(A_Ω) ≅ M₂(ℚ(√d))` (`d < 0`) for an algebraically closed `Ω ⊇ k`, then
`rank_ℤ End_k(A) ≤ 4`. Route (STANDARD): `End⁰(A)` embeds in `End⁰(A_Ω)` (`endBC`, flatness of
`ℚ/ℤ`) as a subalgebra `S ⊇ ι(B)`; `S` is a left `B`-vector space, so `dim_ℚ S ∈ {4, 8}`; if
`dim S = 8` then `S = M₂(ℚ(√d))` contains a nonzero nilpotent, whose integer multiple in
`End(A)` is a nonzero nilpotent endomorphism; a nilpotent endomorphism of a positive-dimensional
abelian variety is not surjective, contradicting `EndDivision`. GLUE. -/
def QMSplitCaseRank : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] (φ : O →+* PkgI3.AbVar.End A), Function.Injective φ → A.dim = 2 →
    PkgI3.EndDivision A → ∀ d : ℚ, d < 0 →
    Nonempty (PkgI3.AbVar.End0 (A.baseChange Ω) ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) →
    Module.finrank ℤ (PkgI3.AbVar.End A) ≤ 4

/-- **`QMEndRank`, proved** from the leaves I3.M1 (`PkgI3.HomFreeFinite`, Mumford §19 Thm 3) and
T27 (`PkgI3.QMDichotomyYu`, Yu 2013 Thm 1.1) and the glue `QMSplitCaseRank`. -/
theorem qmEndRank_of (hM1 : PkgI3.HomFreeFinite) (hT27 : PkgI3.QMDichotomyYu)
    (hS : QMSplitCaseRank) : HSyn.LinkedTate.QMEndRank := by
  intro K L L' _ hKL hLL' PK hdiv
  letI iKL : Algebra K L := incAlg hKL
  letI iLL' : Algebra L L' := incAlg hLL'
  set A' : PkgI3.AbVar L' := @PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL') with hA'
  let φ : O →+* PkgI3.AbVar.End A' :=
    (HSyn.LinkedTate.endBC (PK.A.baseChange L) L').comp
      ((HSyn.LinkedTate.endBC PK.A L).comp PK.q.iota)
  have hφ : Function.Injective φ :=
    (HSyn.LinkedTate.endBC_injective _ L').comp
      ((HSyn.LinkedTate.endBC_injective _ L).comp PK.q.injective)
  have hdimA' : A'.dim = 2 := by
    rw [hA', G0Dim.pkgI3_dim_baseChange, G0Dim.pkgI3_dim_baseChange]
    exact PK.surface
  refine le_antisymm ?_ (four_le_finrank hM1 A' φ hφ)
  -- the geometric endomorphism algebra
  let Ω := AlgebraicClosure L'
  let A'' : PkgI3.AbVar Ω := A'.baseChange Ω
  have hdimA'' : A''.dim = 2 := by
    show (A'.baseChange Ω).dim = 2
    rw [G0Dim.pkgI3_dim_baseChange]; exact hdimA'
  let φ'' : O →+* PkgI3.AbVar.End A'' := (HSyn.LinkedTate.endBC A' Ω).comp φ
  rcases hT27 Ω A'' hdimA'' 2 (-3) PkgI3.quatIndefinite_two_neg_three quatB6_isUnit
      (quatEmbed A'' φ'') with he | ⟨d, hd, he⟩
  · obtain ⟨e⟩ := he
    calc Module.finrank ℤ (PkgI3.AbVar.End A')
        ≤ Module.finrank ℤ (PkgI3.AbVar.End A'') := finrank_le_baseChange hM1 A' Ω
      _ = Module.finrank ℚ (PkgI3.AbVar.End0 A'') := (finrank_end0 hM1 A'').symm
      _ = Module.finrank ℚ ℍ[ℚ, 2, -3] := e.toLinearEquiv.finrank_eq
      _ = 4 := QuaternionAlgebra.finrank_eq_four (R := ℚ) _ _ _
  · exact hS L' A' Ω φ hφ hdimA' hdiv d hd he

end LTGoodRed.QM

end

end LTQMRankSec


/-! ## lt-goodred §5: `QMSplitCaseRank`, proved from I3.M1

Suppose `rank End(A) > 4`. Then (all proved below):
* `End⁰(A) ↪ End⁰(A_Ω) ≅ M₂(ℚ(√d))`, a `ℚ`-algebra embedding (`endBC` injective, `ℚ` flat over
  `ℤ`); so `dim_ℚ End⁰(A) ≤ 8`;
* `B →ₐ[ℚ] End⁰(A)` (`quatEmbed`) and `B` is a division algebra, so for `s ∉ θ(B)` the map
  `(b, b') ↦ θ(b) + θ(b')·s` is injective: `dim End⁰(A) ≥ 8` (`eight_le_finrank`);
* hence `End⁰(A) ≅ M₂(ℚ(√d))`, and the preimage `x` of `E₁₂` is a nonzero element with `x² = 0`;
* clearing denominators, `n·x = 1 ⊗ m` with `m ∈ End(A)`, `m ≠ 0`, `m² = 0` (`End(A)` is free,
  I3.M1, so `m ↦ 1 ⊗ m` is injective);
* a nonzero `m` is an isogeny (`EndDivision`), so `m ∘ m = 0` is surjective; but the zero
  endomorphism factors through `Spec k`, a point, so `A` would be a point, against `dim A = 2`
  (`eq_zero_of_mul_self_eq_zero`). -/

section LTSplitSec

set_option linter.style.haveILetI false

noncomputable section

namespace LTGoodRed.QM

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM
open scoped Quaternion TensorProduct

/-! ### A square-zero endomorphism of an `EndDivision` surface is zero -/

/-- **A square-zero endomorphism of a positive-dimensional `EndDivision` abelian variety is zero**
(proved): otherwise it is surjective (an isogeny), so its square, the zero endomorphism, is
surjective; the zero endomorphism factors through `Spec k`, so `A` is a point, of dimension `≤ 0`. -/
theorem eq_zero_of_mul_self_eq_zero {k : Type} [Field k] (A : PkgI3.AbVar k)
    (hdiv : PkgI3.EndDivision A) (hdim : A.dim = 2) (m : PkgI3.AbVar.End A) (hm : m * m = 0) :
    m = 0 := by
  by_contra hm0
  obtain ⟨-, hsurj⟩ := hdiv m hm0
  have hcomp : (m * m).hom = m.hom ≫ m.hom := rfl
  have h1 : m.hom ≫ m.hom = (1 : A.X ⟶ A.X) := by rw [← hcomp, hm]; rfl
  have hs : Surjective (m.hom ≫ m.hom).left := by
    rw [Over.comp_left]; infer_instance
  rw [h1, Hom.one_def, Over.comp_left] at hs
  haveI hsub : Subsingleton A.X.left := by
    constructor
    intro y1 y2
    obtain ⟨x1, rfl⟩ := hs.surj y1
    obtain ⟨x2, rfl⟩ := hs.surj y2
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _
  have hle : A.dim ≤ 0 := topologicalKrullDim_zero_of_discreteTopology A.X.left
  rw [hdim] at hle
  exact absurd hle (by decide)

/-! ### `ℚ ⊗ M` for a free `ℤ`-module `M` -/

section Tensor

variable {M : Type} [Ring M]

theorem intCast_smul_one_tmul (c : ℤ) (m : M) :
    ((c : ℚ)) • ((1 : ℚ) ⊗ₜ[ℤ] m) = (1 : ℚ) ⊗ₜ[ℤ] (c • m) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
    show ((c : ℤ) : ℚ) = c • (1 : ℚ) by simp, TensorProduct.smul_tmul]

/-- Every element of `ℚ ⊗ M` has an integer multiple of the form `1 ⊗ m`. -/
theorem exists_smul_eq_tmul (x : ℚ ⊗[ℤ] M) :
    ∃ (n : ℤ) (m : M), n ≠ 0 ∧ (n : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] m := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q m =>
    refine ⟨q.den, q.num • m, by exact_mod_cast q.den_nz, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul,
      show ((q.den : ℤ) : ℚ) * q = ((q.num : ℤ) : ℚ) by
        rw [Int.cast_natCast, mul_comm]; exact Rat.mul_den_eq_num q,
      show ((q.num : ℤ) : ℚ) = q.num • (1 : ℚ) by simp, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨n, m, hn, h⟩ := hx
    obtain ⟨n', m', hn', h'⟩ := hy
    refine ⟨n * n', n' • m + n • m', mul_ne_zero hn hn', ?_⟩
    rw [smul_add, Int.cast_mul, mul_comm, mul_smul, h, mul_comm, mul_smul, h',
      intCast_smul_one_tmul, intCast_smul_one_tmul, TensorProduct.tmul_add]

/-- `m ↦ 1 ⊗ m` is injective for a free `ℤ`-module (flatness). -/
theorem one_tmul_injective [Module.Free ℤ M] :
    Function.Injective (fun m : M => (1 : ℚ) ⊗ₜ[ℤ] m) := by
  have hinj : Function.Injective ((Algebra.linearMap ℤ ℚ).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b h => by simpa using h)
  intro m m' h
  apply (TensorProduct.lid ℤ M).symm.injective
  apply hinj
  simpa [TensorProduct.lid_symm_apply] using h

end Tensor

/-! ### A copy of `B` and an element outside it give dimension `≥ 8` -/

theorem eight_le_finrank {R : Type} [Ring R] [Algebra ℚ R] [FiniteDimensional ℚ R]
    (θ : ℍ[ℚ, 2, -3] →ₐ[ℚ] R) (h4 : 4 < Module.finrank ℚ R) : 8 ≤ Module.finrank ℚ R := by
  haveI : Nontrivial R := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    rw [Module.finrank_zero_of_subsingleton] at h4
    omega
  have hr : Module.finrank ℚ (LinearMap.range θ.toLinearMap) ≤ 4 := by
    calc _ ≤ Module.finrank ℚ ℍ[ℚ, 2, -3] := LinearMap.finrank_range_le _
      _ = 4 := QuaternionAlgebra.finrank_eq_four (R := ℚ) _ _ _
  obtain ⟨s, hs⟩ : ∃ s, s ∉ LinearMap.range θ.toLinearMap := by
    by_contra h
    push_neg at h
    have htop : LinearMap.range θ.toLinearMap = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [htop, finrank_top] at hr
    omega
  have hunit : ∀ b : ℍ[ℚ, 2, -3], b ≠ 0 → ∃ c, θ c * θ b = 1 := by
    intro b hb
    obtain ⟨u, rfl⟩ := quatB6_isUnit b hb
    exact ⟨↑u⁻¹, by rw [← map_mul, Units.inv_mul, map_one]⟩
  let Lm : (ℍ[ℚ, 2, -3] × ℍ[ℚ, 2, -3]) →ₗ[ℚ] R :=
    θ.toLinearMap.comp (LinearMap.fst ℚ _ _) +
      ((LinearMap.mulRight ℚ s).comp θ.toLinearMap).comp (LinearMap.snd ℚ _ _)
  have hLm : ∀ b b', Lm (b, b') = θ b + θ b' * s := fun _ _ => rfl
  have hinj : Function.Injective Lm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨b, b'⟩ h
    rw [hLm] at h
    by_cases hb' : b' = 0
    · subst hb'
      rw [map_zero, zero_mul, add_zero] at h
      by_cases hb : b = 0
      · rw [hb]; rfl
      · obtain ⟨c, hc⟩ := hunit b hb
        rw [h, mul_zero] at hc
        exact absurd hc zero_ne_one
    · exfalso
      obtain ⟨c, hc⟩ := hunit b' hb'
      apply hs
      refine ⟨-(c * b), ?_⟩
      show θ (-(c * b)) = s
      have : s = θ c * (θ b' * s) := by rw [← _root_.mul_assoc, hc, _root_.one_mul]
      rw [this, eq_neg_of_add_eq_zero_right h, map_neg, map_mul, mul_neg]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, QuaternionAlgebra.finrank_eq_four (R := ℚ) 2 0 (-3)] at this

/-! ### The proof -/

/-- **`QMSplitCaseRank`, proved** from I3.M1 (`PkgI3.HomFreeFinite`). -/
theorem qmSplitCaseRank (hM1 : PkgI3.HomFreeFinite) : QMSplitCaseRank := by
  intro k _ _ A Ω _ _ _ φ _ hdim hdiv d _ he
  obtain ⟨e⟩ := he
  obtain ⟨hfreeM, hfinM, -, -⟩ := hM1 k A A
  obtain ⟨hfreeN, hfinN, -, -⟩ := hM1 Ω (A.baseChange Ω) (A.baseChange Ω)
  by_contra hlt
  push_neg at hlt
  -- `F = ℚ(√d)`, `dim_ℚ M₂(F) = 8`
  have hf : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by norm_num) d
  have hF : Module.finrank ℚ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) = 2 := by
    rw [(AdjoinRoot.powerBasis hf).finrank, AdjoinRoot.powerBasis_dim,
      Polynomial.natDegree_X_pow_sub_C]
  haveI : Module.Finite ℚ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) :=
    (AdjoinRoot.powerBasis hf).finite
  haveI : Nontrivial (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    rw [Module.finrank_zero_of_subsingleton] at hF
    omega
  have h8 : Module.finrank ℚ
      (Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) = 8 := by
    rw [Module.finrank_matrix, hF]; rfl
  -- `End⁰(A) ↪ End⁰(A_Ω)`
  let β : PkgI3.AbVar.End A →ₐ[ℤ] PkgI3.AbVar.End (A.baseChange Ω) :=
    (HSyn.LinkedTate.endBC A Ω).toIntAlgHom
  let Φ₀ : PkgI3.AbVar.End0 A →ₐ[ℚ] PkgI3.AbVar.End0 (A.baseChange Ω) :=
    Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) β
  haveI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have hΦ₀ : Function.Injective Φ₀ := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ) β.toLinearMap
      (HSyn.LinkedTate.endBC_injective A Ω)
    have heq : ⇑Φ₀ = ⇑(β.toLinearMap.lTensor ℚ) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul q m => simp [Φ₀, Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    rw [heq]; exact h
  let Φ := e.toAlgHom.comp Φ₀
  have hΦ : Function.Injective Φ := e.injective.comp hΦ₀
  -- dimensions
  have hrank : Module.finrank ℚ (PkgI3.AbVar.End0 A) = Module.finrank ℤ (PkgI3.AbVar.End A) :=
    finrank_end0 hM1 A
  obtain ⟨θ⟩ := quatEmbed A φ
  have hge : 8 ≤ Module.finrank ℚ (PkgI3.AbVar.End0 A) :=
    eight_le_finrank θ (by rw [hrank]; exact hlt)
  have hle : Module.finrank ℚ (PkgI3.AbVar.End0 A) ≤ 8 := by
    rw [← h8]; exact LinearMap.finrank_le_finrank_of_injective (f := Φ.toLinearMap) hΦ
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Φ.toLinearMap)
      (by rw [h8]; omega)).mp hΦ
  -- the preimage of `E₁₂`
  let E : Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) := !![0, 1; 0, 0]
  have hE0 : E ≠ 0 := by
    intro h
    have := congrFun (congrFun h 0) 1
    simp [E] at this
  have hEE : E * E = 0 := by
    simp only [E, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  obtain ⟨x, hx⟩ := hsurj E
  have hx0 : x ≠ 0 := by rintro rfl; exact hE0 (by rw [← hx, map_zero])
  have hxx : x * x = 0 := hΦ (by rw [map_mul, hx, hEE, map_zero])
  -- clearing denominators
  obtain ⟨n, m, hn, hnm⟩ := exists_smul_eq_tmul x
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [TensorProduct.tmul_zero, smul_eq_zero] at hnm
    rcases hnm with h | h
    · exact hn (by exact_mod_cast h)
    · exact hx0 h
  have hmm : m * m = 0 := by
    apply one_tmul_injective (M := PkgI3.AbVar.End A)
    show (1 : ℚ) ⊗ₜ[ℤ] (m * m) = (1 : ℚ) ⊗ₜ[ℤ] (0 : PkgI3.AbVar.End A)
    rw [TensorProduct.tmul_zero, ← _root_.mul_one (1 : ℚ), ← Algebra.TensorProduct.tmul_mul_tmul,
      ← hnm, smul_mul_smul_comm, hxx, smul_zero]
  exact hm0 (eq_zero_of_mul_self_eq_zero A hdiv hdim m hmm)

/-- **`QMEndRank` from the leaves I3.M1 and T27 alone** (proved). -/
theorem qmEndRank_of_leaves (hM1 : PkgI3.HomFreeFinite) (hT27 : PkgI3.QMDichotomyYu) :
    HSyn.LinkedTate.QMEndRank :=
  qmEndRank_of hM1 hT27 (qmSplitCaseRank hM1)

end LTGoodRed.QM

end

end LTSplitSec



end G0A3_z96_ltgoodred

section G0A3_z97_linkedram
/-! ## assemble-port: linked-ram, `scratch/linked-ram/olean/Tail.lean` at 3cb898bf (its final state; copied to src/) L2-1668 verbatim minus `#print` (mk/mk_z96.py) -/

/-! # linked-ram (scratch/linked-ram/): `KernelFieldBreaks` (ii) proved; `TateRamAtThree` corrected

Section 1 (`LinkedRamWild`) is `scratch/linked-ram/test/Wild.lean` minus `import Mathlib` (Mathlib only). -/

section LinkedRamWildSec

noncomputable section

namespace LinkedRamWild

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

/-- `‖k‖ = 1` in `ℚ̄_p` for `p ∤ k`. -/
theorem norm_natCast_eq_one {k : ℕ} (hk : ¬ p ∣ k) : ‖(k : K)‖ = 1 := by
  have h1 : ‖((k : ℚ_[p]) : K)‖ = ‖(k : ℚ_[p])‖ := PadicAlgCl.norm_extends p _
  rw [map_natCast] at h1
  rw [h1, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hk

/-- A root of unity of order prime to `p` congruent to `1` is `1`. -/
theorem eq_one_of_pow_eq_one {ξ : K} {k : ℕ} (hk0 : 0 < k) (hk : ¬ p ∣ k) (hξ : ξ ^ k = 1)
    (h : ‖ξ - 1‖ < 1) : ξ = 1 := by
  by_contra hne
  have hgeom : ∑ i ∈ Finset.range k, ξ ^ i = 0 := by
    have h2 := geom_sum_mul ξ k
    rw [hξ, sub_self] at h2
    exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hne)
  have hξn : ‖ξ‖ = 1 := by
    have : ‖ξ‖ ^ k = 1 := by rw [← norm_pow, hξ, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk0.ne').mp this
  have hterm : ∀ i, ‖1 - ξ ^ i‖ < 1 := by
    intro i
    have : 1 - ξ ^ i = (1 - ξ) * ∑ j ∈ Finset.range i, ξ ^ j := by
      rw [mul_comm, geom_sum_mul_neg]
    rw [this, norm_mul, norm_sub_rev]
    have hs : ‖∑ j ∈ Finset.range i, ξ ^ j‖ ≤ 1 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
        (fun j _ => by rw [norm_pow, hξn, one_pow])
    calc ‖ξ - 1‖ * ‖∑ j ∈ Finset.range i, ξ ^ j‖ ≤ ‖ξ - 1‖ * 1 :=
          mul_le_mul_of_nonneg_left hs (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact h
  have hk' : (k : K) = ∑ i ∈ Finset.range k, (1 - ξ ^ i) := by
    rw [Finset.sum_sub_distrib, hgeom, sub_zero]; simp
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.nonempty_range_iff.mpr hk0.ne') (fun i => 1 - ξ ^ i)
  have := norm_natCast_eq_one (p := p) hk
  rw [hk'] at this
  linarith [hterm i]

/-- The wild set (as in `LadicCond.wildSet`). -/
def IsWild (σ : K ≃ₐ[ℚ_[p]] K) : Prop := ∀ x : K, x ≠ 0 → ‖σ x - x‖ < ‖x‖

theorem norm_apply (σ : K ≃ₐ[ℚ_[p]] K) (x : K) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

/-- W1: a wild element fixes the roots of unity of order prime to `p`. -/
theorem wild_fix_root {σ : K ≃ₐ[ℚ_[p]] K} (hσ : IsWild σ) {ζ : K} {k : ℕ} (hk0 : 0 < k)
    (hk : ¬ p ∣ k) (hζ : ζ ^ k = 1) : σ ζ = ζ := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow hk0.ne'] at hζ; exact zero_ne_one hζ
  have hξ : (σ ζ * ζ⁻¹) ^ k = 1 := by rw [mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ]; simp
  have hlt : ‖σ ζ * ζ⁻¹ - 1‖ < 1 := by
    have h1 := hσ ζ hζ0
    have : σ ζ * ζ⁻¹ - 1 = (σ ζ - ζ) * ζ⁻¹ := by field_simp
    rw [this, norm_mul, norm_inv]
    have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
    rw [mul_inv_lt_iff₀ hn, one_mul]; exact h1
  have := eq_one_of_pow_eq_one hk0 hk hξ hlt
  field_simp at this
  exact this

/-- `‖c − 1‖ ≥ 1` for a root of unity `c ≠ 1` of order prime to `p`. -/
theorem one_le_norm_sub_one {c : K} {k : ℕ} (hk0 : 0 < k) (hk : ¬ p ∣ k) (hc : c ^ k = 1)
    (hne : c ≠ 1) : 1 ≤ ‖c - 1‖ := by
  by_contra h
  exact hne (eq_one_of_pow_eq_one hk0 hk hc (lt_of_not_ge h))

/-- W2: if `σ` is wild and `σ^k y = y` with `p ∤ k`, then `σ y = y`. -/
theorem wild_fix_of_pow {σ : K ≃ₐ[ℚ_[p]] K} (hσ : IsWild σ) {k : ℕ} (hk0 : 0 < k)
    (hk : ¬ p ∣ k) {y : K} (hy : (σ ^ k) y = y) : σ y = y := by
  classical
  have : NeZero (k : K) := ⟨by exact_mod_cast hk0.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K k
  have hζfix : σ ζ = ζ := wild_fix_root hσ hk0 hk hζ.pow_eq_one
  -- the fixed field of `σ`
  let F : Subfield K := RingHom.eqLocusField σ.toAlgHom.toRingHom (RingHom.id K)
  have hF : ∀ x : F, σ (x : K) = x := fun x => x.2
  let ζF : F := ⟨ζ, hζfix⟩
  have hζF : IsPrimitiveRoot ζF k :=
    IsPrimitiveRoot.of_map_of_injective (f := F.subtype) (by exact hζ) Subtype.val_injective
  -- `σ` as an `F`-linear endomorphism of `K`
  let S : Module.End F K :=
    { toFun := σ
      map_add' := map_add σ
      map_smul' := fun c v => by
        show σ ((c : K) * v) = (c : K) * σ v
        rw [map_mul, hF c] }
  have hS : ∀ v, S v = σ v := fun _ => rfl
  have hSpow : ∀ n v, (S ^ n) v = (σ ^ n) v := by
    intro n v
    rw [Module.End.pow_apply, AlgEquiv.coe_pow]
    rfl
  have hprod := Polynomial.X_pow_sub_one_eq_prod hk0 hζF
  have h1mem : (1 : F) ∈ Polynomial.nthRootsFinset k (1 : F) :=
    (Polynomial.mem_nthRootsFinset hk0 (1 : F)).mpr (one_pow _)
  rw [← Finset.prod_erase_mul _ _ h1mem] at hprod
  have heval := congrArg (fun q => Polynomial.aeval S q) hprod
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, Polynomial.aeval_C] at heval
  have hzero : (Polynomial.aeval S (∏ c ∈ (Polynomial.nthRootsFinset k (1 : F)).erase 1,
      (Polynomial.X - Polynomial.C c))) ((S - 1) y) = 0 := by
    rw [← Module.End.mul_apply, ← heval]
    show (S ^ k) y - y = 0
    rw [hSpow, hy, sub_self]
  -- the other factors are injective
  have hfac : ∀ c ∈ (Polynomial.nthRootsFinset k (1 : F)).erase 1,
      Function.Injective (Polynomial.aeval S (Polynomial.X - Polynomial.C c)) := by
    intro c hc
    obtain ⟨hc1, hc⟩ := Finset.mem_erase.mp hc
    have hck : c ^ k = 1 := (Polynomial.mem_nthRootsFinset hk0 (1 : F)).mp hc
    have hck' : (c : K) ^ k = 1 := by rw [← SubmonoidClass.coe_pow, hck]; rfl
    have hcne : (c : K) ≠ 1 := fun h => hc1 (Subtype.ext h)
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : σ v = (c : K) * v := by
      have : S v - c • v = 0 := hv
      rw [hS, sub_eq_zero] at this
      exact this
    by_contra hv0
    have h1 := hσ v hv0
    rw [hv', ← sub_one_mul, norm_mul] at h1
    have := one_le_norm_sub_one hk0 hk hck' hcne
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    nlinarith
  have hinj : Function.Injective (Polynomial.aeval S
      (∏ c ∈ (Polynomial.nthRootsFinset k (1 : F)).erase 1, (Polynomial.X - Polynomial.C c))) := by
    refine Finset.prod_induction _ (fun q : Polynomial F => Function.Injective (Polynomial.aeval S q))
      ?_ ?_ hfac
    · intro f g hf hg
      rw [map_mul, Module.End.coe_mul]
      exact hf.comp hg
    · rw [map_one, Module.End.coe_one]; exact Function.injective_id
  have h2 : (S - 1) y = 0 := by
    apply hinj
    rw [map_zero]
    exact hzero
  rw [LinearMap.sub_apply, Module.End.one_apply, hS, sub_eq_zero] at h2
  exact h2

/-- Powers of a wild element are wild. -/
theorem IsWild.pow {σ : K ≃ₐ[ℚ_[p]] K} (hσ : IsWild σ) (n : ℕ) : IsWild (σ ^ n) := by
  induction n with
  | zero => intro x hx; simpa using norm_pos_iff.mpr hx
  | succ n ih =>
    intro x hx
    rw [pow_succ, AlgEquiv.mul_apply]
    have h1 := ih x hx
    have hx' : σ x ≠ 0 := by simpa using hx
    have h2 := ih (σ x) hx'
    rw [norm_apply] at h2
    have : (σ ^ n) (σ x) - x = ((σ ^ n) (σ x) - σ x) + (σ x - x) := by ring
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2 (hσ x hx))

/-- W4: a wild element fixes every root of a nonzero `ℚ`-polynomial of degree `< p`. -/
theorem wild_fix_of_aeval {σ : K ≃ₐ[ℚ_[p]] K} (hσ : IsWild σ) {q : Polynomial ℚ} (hq : q ≠ 0)
    (hdeg : q.natDegree < p) {y : K} (hy : Polynomial.aeval y q = 0) : σ y = y := by
  classical
  let qK := q.map (algebraMap ℚ K)
  have hqK : qK ≠ 0 := Polynomial.map_ne_zero hq
  let R := qK.roots.toFinset
  have hR : R.card < (Finset.range (q.natDegree + 1)).card := by
    rw [Finset.card_range]
    calc R.card ≤ Multiset.card qK.roots := Multiset.toFinset_card_le _
      _ ≤ qK.natDegree := Polynomial.card_roots' _
      _ = q.natDegree := Polynomial.natDegree_map _
      _ < q.natDegree + 1 := Nat.lt_succ_self _
  have hmaps : ∀ i ∈ Finset.range (q.natDegree + 1), (σ ^ i) y ∈ R := by
    intro i _
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hqK, Polynomial.IsRoot,
      Polynomial.eval_map_algebraMap]
    have : Polynomial.aeval ((σ ^ i) y) q = (σ ^ i) (Polynomial.aeval y q) :=
      Polynomial.aeval_algHom_apply (((σ ^ i).toAlgHom).restrictScalars ℚ) y q
    rw [this, hy, map_zero]
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hR hmaps
  rw [Finset.mem_range] at hi hj
  -- reduce to `i < j`
  have key : ∀ i j : ℕ, i < j → j < q.natDegree + 1 → (σ ^ i) y = (σ ^ j) y → σ y = y := by
    intro i j hlt hj heq
    have hk : (σ ^ (j - i)) y = y := by
      have : σ ^ j = σ ^ i * σ ^ (j - i) := by rw [← pow_add]; congr 1; omega
      rw [this, AlgEquiv.mul_apply] at heq
      exact ((σ ^ i).injective heq).symm
    refine wild_fix_of_pow hσ (k := j - i) (by omega) ?_ hk
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hj heq
  · exact key j i h hi heq.symm

/-- W5: a wild element fixes `y` with `y ^ N = 1` when `p² ∤ N`. -/
theorem wild_fix_of_pow_eq_one {σ : K ≃ₐ[ℚ_[p]] K} (hσ : IsWild σ) {N : ℕ} (hN : 0 < N)
    (hN2 : ¬ p ^ 2 ∣ N) {y : K} (hy : y ^ N = 1) : σ y = y := by
  obtain ⟨b, N', hN', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.out.one_lt.ne'
  have hb : b ≤ 1 := by
    by_contra hb
    exact hN2 (Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) _)
  have hN'0 : 0 < N' := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow hN.ne'] at hy; exact zero_ne_one hy
  -- `y1 = y ^ N'` is fixed
  have hy1 : σ (y ^ N') = y ^ N' := by
    have hp1 : (y ^ N') ^ p = 1 := by
      interval_cases b
      · simp at hy; rw [hy, one_pow]
      · rw [← pow_mul, mul_comm]; simpa using hy
    by_cases h1 : y ^ N' = 1
    · rw [h1, map_one]
    · refine wild_fix_of_aeval hσ (q := ∑ i ∈ Finset.range p, Polynomial.X ^ i) ?_ ?_ ?_
      · intro h0
        have := congrArg (Polynomial.eval (1 : ℚ)) h0
        simp [Polynomial.eval_finsetSum] at this
        exact hp.out.ne_zero this
      · have h := Polynomial.natDegree_sum_le_of_forall_le (Finset.range p)
          (fun i => (Polynomial.X : Polynomial ℚ) ^ i) (n := p - 1) (fun i hi => by
            rw [Polynomial.natDegree_X_pow]; have := Finset.mem_range.mp hi; omega)
        have := hp.out.one_lt
        omega
      · simp only [map_sum, map_pow, Polynomial.aeval_X]
        have h2 := geom_sum_mul (y ^ N') p
        rw [hp1, sub_self] at h2
        exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr h1)
  have hξ : (σ y * y⁻¹) ^ N' = 1 := by
    rw [mul_pow, ← map_pow, hy1, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hy0)]
  have hlt : ‖σ y * y⁻¹ - 1‖ < 1 := by
    have h1 := hσ y hy0
    have : σ y * y⁻¹ - 1 = (σ y - y) * y⁻¹ := by field_simp
    rw [this, norm_mul, norm_inv]
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    rw [mul_inv_lt_iff₀ hn, one_mul]; exact h1
  have := eq_one_of_pow_eq_one hN'0 hN' hξ hlt
  field_simp at this
  exact this

/-! ### Transfer to `G_ℚ` along an embedding -/

section Global



theorem pow_compat {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (e : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (he : ∀ x : AlgebraicClosure ℚ, e (g x) = σ (e x)) (n : ℕ) (x : AlgebraicClosure ℚ) :
    e ((g ^ n) x) = (σ ^ n) (e x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ g n, AlgEquiv.mul_apply, ih, he, ← AlgEquiv.mul_apply, ← pow_succ]

/-- `g` fixes every element whose minimal polynomial has degree `< p`. -/
theorem fix_of_minpoly {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (e : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : IsWild σ) (he : ∀ x : AlgebraicClosure ℚ, e (g x) = σ (e x)) {x : AlgebraicClosure ℚ}
    (hx : (minpoly ℚ x).natDegree < p) : g x = x := by
  apply e.injective
  rw [he]
  refine wild_fix_of_aeval hσ (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)) hx ?_
  rw [show Polynomial.aeval (e x) (minpoly ℚ x) = e.toRatAlgHom (Polynomial.aeval x (minpoly ℚ x))
    from (Polynomial.aeval_algHom_apply e.toRatAlgHom x _), minpoly.aeval, map_zero]

/-- `g` fixes a finite-dimensional `L` with `[L:ℚ] < p`. -/
theorem fix_of_finrank {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (e : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : IsWild σ) (he : ∀ x : AlgebraicClosure ℚ, e (g x) = σ (e x))
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] (hL : Module.finrank ℚ L < p) :
    g ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  refine fix_of_minpoly e g hσ he (lt_of_le_of_lt ?_ hL)
  rw [show x = ((⟨x, hx⟩ : L) : AlgebraicClosure ℚ) from rfl, ← IntermediateField.minpoly_eq]
  exact minpoly.natDegree_le _

/-- `g` fixes every `N`-th root of unity when `p² ∤ N`. -/
theorem fix_of_pow_eq_one {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (e : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : IsWild σ) (he : ∀ x : AlgebraicClosure ℚ, e (g x) = σ (e x)) {N : ℕ} (hN : 0 < N)
    (hN2 : ¬ p ^ 2 ∣ N) {y : AlgebraicClosure ℚ} (hy : y ^ N = 1) : g y = y := by
  apply e.injective
  rw [he]
  exact wild_fix_of_pow_eq_one hσ hN hN2 (by rw [← map_pow, hy, map_one])

/-- Some `p`-power of `g` fixes a finite Galois `L'`. -/
theorem pow_mem_fixing {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (e : AlgebraicClosure ℚ →+* PadicAlgCl p)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : IsWild σ) (he : ∀ x : AlgebraicClosure ℚ, e (g x) = σ (e x))
    (L' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L'] [Normal ℚ L'] :
    ∃ a : ℕ, g ^ (p ^ a) ∈ L'.fixingSubgroup := by
  let r := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) L'
  have hn : 0 < orderOf (r g) := orderOf_pos (r g)
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.one_lt.ne'
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hfix : g ^ orderOf (r g) ∈ L'.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  refine ⟨a, ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hfix ⊢
  intro x hx
  apply e.injective
  rw [pow_compat e g he]
  refine wild_fix_of_pow (hσ.pow (p ^ a)) hm0 hm ?_
  rw [← pow_mul, ← hnm, ← pow_compat e g he, hfix x hx]

end Global

end LinkedRamWild

end

end LinkedRamWildSec

section LinkedRamMain

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace UnramTate

open G0ModField

/-- For an odd prime `p` and a set `Tm` of primes, `p² ∤ chiLevel Tm` (`lev q ∈ {q, 4}`). -/
theorem not_sq_dvd_chiLevel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ Tm : Finset ℕ, (∀ q ∈ Tm, q.Prime) →
      (p ∉ Tm → ¬ p ∣ chiLevel Tm) ∧ ¬ p ^ 2 ∣ chiLevel Tm := by
  intro Tm
  induction Tm using Finset.induction_on with
  | empty =>
    intro _
    simp only [chiLevel, Finset.prod_empty, Nat.dvd_one]
    refine ⟨fun _ => hp.one_lt.ne', fun h => ?_⟩
    have := Nat.pow_eq_one.mp h
    rcases this with h | h
    · exact hp.one_lt.ne' h
    · omega
  | @insert a s ha ih =>
    intro hTm
    have ih' := ih (fun q hq => hTm q (Finset.mem_insert_of_mem hq))
    have haP : a.Prime := hTm a (Finset.mem_insert_self a s)
    have hcl : chiLevel (insert a s) = lev a * chiLevel s := Finset.prod_insert ha
    rw [hcl]
    by_cases hap : a = p
    · subst hap
      have hlev : lev a = a := by unfold lev; simp [hp2]
      rw [hlev]
      have hns : ¬ a ∣ chiLevel s := ih'.1 ha
      refine ⟨fun h => absurd (Finset.mem_insert_self a s) h, fun h => ?_⟩
      rw [pow_two] at h
      exact hns (Nat.dvd_of_mul_dvd_mul_left hp.pos h)
    · have hlev : ¬ p ∣ lev a := by
        unfold lev
        split_ifs with h2
        · intro h
          have : p ∣ 2 ^ 2 := by norm_num; exact h
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
        · intro h
          exact hap ((Nat.prime_dvd_prime_iff_eq hp haP).mp h).symm
      have hcop : Nat.Coprime (p ^ 2) (lev a) :=
        Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hlev)
      refine ⟨fun hnot h => ?_, fun h => ih'.2 (hcop.dvd_of_dvd_mul_left h)⟩
      have hps : p ∉ s := fun h' => hnot (Finset.mem_insert_of_mem h')
      rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact hlev h
      · exact ih'.1 hps h

/-- `T u` consists of primes. -/
theorem prime_of_mem_T {u : ℚ} {q : ℕ} (hq : q ∈ T u) : q.Prime := by
  obtain ⟨hS, -, -⟩ := admissible_S_mul
  rcases Finset.mem_union.mp hq with h | h
  · exact hS q h
  · exact Nat.prime_of_mem_primeFactors h

/-- A wild `σ` makes `decomp p σ` act trivially on `μ_N` when `p² ∤ N`, so `cyc N` is trivial. -/
theorem cyc_decomp_eq_one {p : ℕ} [Fact p.Prime] {σ : PkgI4.GQp p}
    (hσ : σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p))) {N : ℕ} [NeZero N]
    (hN2 : ¬ p ^ 2 ∣ N) : cyc N (PkgI4.decomp p σ) = 1 := by
  have hw : LinkedRamWild.IsWild σ := hσ
  have he : ∀ x, embP p (PkgI4.decomp p σ x) = σ (embP p x) := embP_decomp p σ
  have : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hc := modularCyclotomicCharacter.unique (L := AlgebraicClosure ℚ) (n := N)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
    (toRingAut (PkgI4.decomp p σ)) (c := 1) (fun (t : (AlgebraicClosure ℚ)ˣ) ht => by
      have ht' : (t : AlgebraicClosure ℚ) ^ N = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N t).mp ht, Units.val_one]
      have hfix := LinkedRamWild.fix_of_pow_eq_one (embP p) (PkgI4.decomp p σ) hw he
        (Nat.pos_of_ne_zero (NeZero.ne N)) hN2 ht'
      show (PkgI4.decomp p σ) (t : AlgebraicClosure ℚ) = _
      rw [hfix]
      rcases Nat.lt_or_ge 1 N with h1 | h1
      · haveI : Fact (1 < N) := ⟨h1⟩
        rw [ZMod.val_one, pow_one]
      · have hN1 : N = 1 := by have := NeZero.ne N; omega
        subst hN1
        have : t = 1 := by
          have := (mem_rootsOfUnity 1 t).mp ht
          simpa using this
        subst this
        simp)
  apply Units.ext
  rw [Units.val_one]
  exact hc.symm

/-- **The tame half of `KernelFieldBreaks`** (its clause for `p > D`). -/
def KernelFieldBreaksHigh : Prop :=
  ∀ (u : ℚ) (P : LeafQM.AV.QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      (ZInQ.heightD : ℝ) < p → ∀ σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)),
          PkgI4.decomp p σ ∈ GQL L'

/-- **The wild half of `KernelFieldBreaks`** (its clause for `p ≤ D`); GLUE, unchanged. -/
def KernelFieldBreaksLow : Prop :=
  ∀ (u : ℚ) (P : LeafQM.AV.QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      (p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∀ t : ℝ, G0ModNewform.U0 < t →
          ∀ σ ∈ LadicCond.upperAbs p t, PkgI4.decomp p σ ∈ GQL L'

/-- `KernelFieldBreaks` is the conjunction of its two halves. -/
theorem kernelFieldBreaks_of_halves (hL : KernelFieldBreaksLow) (hH : KernelFieldBreaksHigh) :
    KernelFieldBreaks := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD p hp
  exact ⟨hL u P L A ε N χ β L' hLL' hD p hp, hH u P L A ε N χ β L' hLL' hD p hp⟩

/-- **The `β`-step for a wild element at an odd prime** (shared by both halves): for G7 data, an
odd prime `p` and a wild `σ ∈ G_{ℚ_p}` with `decomp p σ ∈ G_L`, `decomp p σ ∈ G_{L'}`. -/
theorem mem_GQL'_of_wild {u : ℚ} {P : LeafQM.AV.QML3 Qbar} {L : IF} [FiniteDimensional ℚ L]
    [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L'] [IsGalois ℚ L']
    {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL') {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {σ : PkgI4.GQp p} (hσ : σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)))
    (hgL : PkgI4.decomp p σ ∈ GQL L) : PkgI4.decomp p σ ∈ GQL L' := by
  have hp : p.Prime := Fact.out
  have hw : LinkedRamWild.IsWild σ := hσ
  have he : ∀ x, embP p (PkgI4.decomp p σ x) = σ (embP p x) := embP_decomp p σ
  obtain ⟨_, hDD, -, -, ⟨Tm, hTm, hNlev⟩, -, hβsq, hβmul, hL', -, -, -, -⟩ := hD
  obtain ⟨-, hinf, h11, -⟩ := hDD
  set g := PkgI4.decomp p σ with hg
  -- `β` is multiplicative on `G_L`
  have hε1 : ∀ x y : GQ, x ∈ GQL L → y ∈ GQL L → ε x y = 1 := by
    intro x y hx hy
    rw [hinf x 1 y 1 (fun z hz => (mem_GQL.mp hx z hz)) (fun z hz => (mem_GQL.mp hy z hz)), h11]
  have hβ1 : β 1 = 1 := by
    have := hβmul 1 1
    rw [h11, _root_.one_mul, _root_.mul_one] at this
    exact mul_left_cancel (this.trans (_root_.mul_one _).symm)
  have hβpow : ∀ n : ℕ, β (g ^ n) = β g ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact hβ1
    | succ n ih =>
      have h1 := hβmul (g ^ n) g
      have hx : ε (g ^ n) g = 1 := hε1 _ _ (Subgroup.pow_mem _ hgL n) hgL
      rw [hx, _root_.one_mul] at h1
      calc β (g ^ (n + 1)) = β (g ^ n * g) := congrArg β (pow_succ g n)
        _ = β (g ^ n) * β g := h1.symm
        _ = β g ^ n * β g := by rw [ih]
        _ = β g ^ (n + 1) := (pow_succ _ _).symm
  -- `χ(g) = 1`
  have hN2 : ¬ p ^ 2 ∣ N := by
    rw [hNlev]
    exact (not_sq_dvd_chiLevel hp hp2 Tm (fun q hq => prime_of_mem_T (hTm hq))).2
  have hχ : galChar χ g = 1 := by
    show χ.toUnitHom (cyc N g) = 1
    rw [cyc_decomp_eq_one hσ hN2, map_one]
  have hsq : β g ^ 2 = 1 := (hβsq g).trans hχ
  -- a `p`-power of `g` fixes `L'`
  obtain ⟨a, ha⟩ := LinkedRamWild.pow_mem_fixing (embP p) g hw he L'
  have hpa : β g ^ (p ^ a) = 1 := by
    rw [← hβpow]; exact ((hL' _).mp ha).2
  have hcop : Nat.Coprime (p ^ a) 2 := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hβg : β g = 1 := by
    have := (pow_gcd_eq_one (a := β g)).mpr ⟨hpa, hsq⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  exact (hL' g).mpr ⟨hgL, hβg⟩

/-- **`KernelFieldBreaksHigh`, proved.** For `p > D ≥ [L:ℚ]`, a wild `σ` fixes `L` (orbits of
size `< p`), acts trivially on `μ_N` (`p² ∤ N`), so `β(decomp σ)² = χ(decomp σ) = 1`; and some
`p`-power of `decomp σ` fixes `L'`, so `β(decomp σ)^{p^a} = 1`; `p` is odd, so `β(decomp σ) = 1`. -/
theorem kernelFieldBreaksHigh : KernelFieldBreaksHigh := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro hpD σ hσ
  have hw : LinkedRamWild.IsWild σ := hσ
  have he : ∀ x, embP p (PkgI4.decomp p σ x) = σ (embP p x) := embP_decomp p σ
  have h3 := three_le_heightD
  have hp2 : p ≠ 2 := by
    rintro rfl; push_cast at hpD; linarith
  have hLp : Module.finrank ℚ L < p := by
    have : (Module.finrank ℚ L : ℝ) < p := lt_of_le_of_lt (by exact_mod_cast hD.2.2.2.2.2.2.2.2.2.2.2.2) hpD
    exact_mod_cast this
  exact mem_GQL'_of_wild hD hp2 hσ (LinkedRamWild.fix_of_finrank (embP p) _ hw he L hLp)

/-! ### The wild half: reduced to a local break bound, wildness of upper groups, and `p = 2` -/

/-- **Leaf candidate (LEAF?, textbook composite): the absolute break bound** (Glazer's
manuscript L796-811, from Serre, *Local Fields*, Ch. III §6 (different bound
`δ ≤ e − 1 + e·v_p(e)`) and Ch. IV §1-§3 (Hilbert's formula `δ = Σ_{i≥0}(|G_i| − 1)`, Herbrand's
function); numbering UNVERIFIED): for a finite extension `F/ℚ_p` of degree `a` inside `ℚ̄_p`, every
element of the absolute upper ramification group `G_{ℚ_p}^u` with `u > 4a²` fixes `F` pointwise.
(The normal closure has degree `≤ a!`; its last upper break is `≤ 2δ/e ≤ 2(1 + log₂ a!) ≤ 4a²`.)
Stated over `LadicCond`'s definitions of `G_{ℚ_p}^u` (Serre IV §3). -/
def UpperBreakBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : LadicCond.Fld p) [FiniteDimensional ℚ_[p] F] (u : ℝ),
    4 * (Module.finrank ℚ_[p] F : ℝ) ^ 2 < u →
      ∀ σ ∈ LadicCond.upperAbs p u, ∀ x ∈ F, σ x = x

/-- **Glue (definitions): positive upper groups are wild.** For `u > 0`, `G_{ℚ_p}^u ⊆ P_p`
(`ψ(u) ≥ u > 0`, so `G^u(M) ⊆ G_1(M)` at every finite Galois level `M`; Serre IV §3). -/
def UpperAbsWild : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (u : ℝ), 0 < u →
    LadicCond.upperAbs p u ⊆ (LadicCond.wildSet : Set (PkgI4.GQp p))

/-- **Glue: `β` on high upper groups at `2`** (Glazer L826-843: local reciprocity, the
`2`-primary factor of `χ` has conductor `≤ 4`, the logarithm on `U_F^{e+1}`, and
`ψ_{F/ℚ_2}(u) ≥ u`). For G7 data and `u > U₀`, `β(decomp₂ σ) = 1` for `σ ∈ G_{ℚ_2}^u` with
`decomp₂ σ ∈ G_L`. GLUE (truth: STANDARD route, Glazer's argument). -/
def BetaTrivialAtTwo : Prop :=
  ∀ (u : ℚ) (P : LeafQM.AV.QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
    ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs 2 t,
      PkgI4.decomp 2 σ ∈ GQL L → β (PkgI4.decomp 2 σ) = 1

/-- `4 D² < U₀ = 4 (D G₀)²`. -/
theorem four_D_sq_lt_U0 : 4 * ((ZInQ.heightD : ℕ) : ℝ) ^ 2 < G0ModNewform.U0 := by
  unfold G0ModNewform.U0
  have hD : (1 : ℝ) ≤ (ZInQ.heightD : ℝ) := by
    have := three_le_heightD; linarith
  have hG : (2 : ℝ) ≤ (ZInQ.heightG0 : ℝ) := by
    unfold ZInQ.heightG0; norm_num
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hG (show (0 : ℝ) ≤ ZInQ.heightD by linarith)]

/-- **High upper groups fix a number field of degree `≤ D`** (from `UpperBreakBound`): for
`x ∈ L`, `F = ℚ_p(embP x)` has degree `≤ deg minpoly_ℚ x ≤ [L:ℚ] ≤ D`, and `4D² < U₀`. -/
theorem decomp_mem_GQL_of_breaks (hB : UpperBreakBound) {p : ℕ} [Fact p.Prime] (L : IF)
    [FiniteDimensional ℚ L] (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) {t : ℝ}
    (ht : G0ModNewform.U0 < t) {σ : PkgI4.GQp p} (hσ : σ ∈ LadicCond.upperAbs p t) :
    PkgI4.decomp p σ ∈ GQL L := by
  refine (mem_GQL (σ := PkgI4.decomp p σ)).mpr ?_
  intro x hx
  apply (embP p).injective
  rw [show act (PkgI4.decomp p σ) x = PkgI4.decomp p σ x from rfl, embP_decomp]
  let y : PadicAlgCl p := embP p x
  have hyint : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  let F : LadicCond.Fld p := IntermediateField.adjoin ℚ_[p] {y}
  haveI : FiniteDimensional ℚ_[p] F := IntermediateField.adjoin.finiteDimensional hyint
  have hdeg : Module.finrank ℚ_[p] F ≤ ZInQ.heightD := by
    have h1 : Module.finrank ℚ_[p] F = (minpoly ℚ_[p] y).natDegree :=
      IntermediateField.adjoin.finrank hyint
    have hq0 : (minpoly ℚ x).map (algebraMap ℚ ℚ_[p]) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x))
    have h2 : minpoly ℚ_[p] y ∣ (minpoly ℚ x).map (algebraMap ℚ ℚ_[p]) := by
      apply minpoly.dvd
      rw [Polynomial.aeval_map_algebraMap]
      rw [show Polynomial.aeval y (minpoly ℚ x) = (embP p).toRatAlgHom (Polynomial.aeval x (minpoly ℚ x))
        from Polynomial.aeval_algHom_apply (embP p).toRatAlgHom x _, minpoly.aeval, map_zero]
    have h3 : (minpoly ℚ x).natDegree ≤ Module.finrank ℚ L := by
      rw [show x = ((⟨x, hx⟩ : L) : Qbar) from rfl, ← IntermediateField.minpoly_eq]
      exact minpoly.natDegree_le _
    rw [h1]
    calc (minpoly ℚ_[p] y).natDegree ≤ ((minpoly ℚ x).map (algebraMap ℚ ℚ_[p])).natDegree :=
          Polynomial.natDegree_le_of_dvd h2 hq0
      _ = (minpoly ℚ x).natDegree := Polynomial.natDegree_map _
      _ ≤ Module.finrank ℚ L := h3
      _ ≤ ZInQ.heightD := hLD
  have hlt : 4 * (Module.finrank ℚ_[p] F : ℝ) ^ 2 < t := by
    refine lt_of_le_of_lt ?_ (lt_trans four_D_sq_lt_U0 ht)
    have : (Module.finrank ℚ_[p] F : ℝ) ≤ (ZInQ.heightD : ℝ) := by exact_mod_cast hdeg
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) this 2) (by norm_num)
  exact hB p F t hlt σ hσ y (IntermediateField.mem_adjoin_simple_self ℚ_[p] y)

/-- **`KernelFieldBreaksLow` from the break bound, wildness of positive upper groups, and the
prime `2`.** -/
theorem kernelFieldBreaksLow_of (hB : UpperBreakBound) (hW : UpperAbsWild)
    (h2 : BetaTrivialAtTwo) : KernelFieldBreaksLow := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD p hp
  letI : Fact p.Prime := ⟨hp⟩
  intro _ t ht σ hσ
  have hgL : PkgI4.decomp p σ ∈ GQL L :=
    decomp_mem_GQL_of_breaks hB L hD.2.2.2.2.2.2.2.2.2.2.2.2 ht hσ
  by_cases hp2 : p = 2
  · subst hp2
    have hβ := h2 u P L A ε N χ β L' hLL' hD t ht σ hσ hgL
    exact (hD.2.2.2.2.2.2.2.2.1 _).mpr ⟨hgL, hβ⟩
  · have hU0 : 0 < t := lt_of_le_of_lt U0_nonneg ht
    exact mem_GQL'_of_wild hD hp2 (hW p t hU0 hσ) hgL

/-- **`KernelFieldBreaks` from `UpperBreakBound`, `UpperAbsWild`, `BetaTrivialAtTwo`.** -/
theorem kernelFieldBreaks_of (hB : UpperBreakBound) (hW : UpperAbsWild)
    (h2 : BetaTrivialAtTwo) : KernelFieldBreaks :=
  kernelFieldBreaks_of_halves (kernelFieldBreaksLow_of hB hW h2) kernelFieldBreaksHigh

/-! ### `UpperAbsWild`, proved -/

section UpperWild

open LadicCond

variable {p : ℕ} [Fact p.Prime]

theorem restr_image_finite (M : Fld p) [FiniteDimensional ℚ_[p] M] (S : Set (PkgI4.GQp p)) :
    (restr M '' S).Finite := by
  apply Set.Finite.subset (Set.finite_range (fun f : M →ₐ[ℚ_[p]] Kbar p => (f : M → Kbar p)))
  rintro _ ⟨σ, -, rfl⟩
  exact ⟨(σ.toAlgHom).comp M.val, rfl⟩

theorem ramSet_anti (M : Fld p) {i j : ℕ} (hij : i ≤ j) : ramSet M j ⊆ ramSet M i := by
  rintro σ ⟨ϖ, hϖ, h⟩
  refine ⟨ϖ, hϖ, fun x hx hx1 => (h x hx hx1).trans ?_⟩
  exact pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega)

theorem ramSetR_anti (M : Fld p) {s t : ℝ} (hst : s ≤ t) : ramSetR M t ⊆ ramSetR M s := by
  unfold ramSetR
  split_ifs with ht hs hs
  · exact le_rfl
  · exact absurd (hst.trans ht) hs
  · exact Set.subset_univ _
  · exact ramSet_anti M (Int.toNat_le_toNat (Int.ceil_mono hst))

theorem ramSetR_sub_zero (M : Fld p) {t : ℝ} (ht : -1 < t) : ramSetR M t ⊆ ramSet M 0 := by
  unfold ramSetR
  rw [if_neg (by linarith)]
  exact ramSet_anti M (Nat.zero_le _)

theorem one_mem_ramSetR (M : Fld p) {ϖ : Kbar p} (hϖ : IsUnif M ϖ) (t : ℝ) :
    (1 : PkgI4.GQp p) ∈ ramSetR M t := by
  unfold ramSetR
  split_ifs
  · exact Set.mem_univ _
  · exact ⟨ϖ, hϖ, fun x _ _ => by simp⟩

theorem one_le_ramCardR (M : Fld p) [FiniteDimensional ℚ_[p] M] {ϖ : Kbar p} (hϖ : IsUnif M ϖ)
    (t : ℝ) : 1 ≤ ramCardR M t := by
  have hfin := restr_image_finite M (ramSetR M t)
  have hne : (restr M '' ramSetR M t).Nonempty := ⟨restr M 1, 1, one_mem_ramSetR M hϖ t, rfl⟩
  haveI := hfin.to_subtype
  haveI := hne.to_subtype
  exact Nat.card_pos

theorem ramCardR_le (M : Fld p) [FiniteDimensional ℚ_[p] M] {t : ℝ} (ht : -1 < t) :
    ramCardR M t ≤ ramCard M 0 :=
  Nat.card_mono (restr_image_finite M _) (Set.image_mono (ramSetR_sub_zero M ht))

theorem ramCardR_zero (M : Fld p) : ramCardR M 0 = ramCard M 0 := by
  unfold ramCardR ramCard ramSetR
  rw [if_neg (by norm_num)]
  simp

theorem integrand_anti (M : Fld p) [FiniteDimensional ℚ_[p] M] :
    Antitone (fun t : ℝ => (ramCardR M t : ℝ) / (ramCard M 0 : ℝ)) := by
  intro s t hst
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.card_mono (restr_image_finite M _) (Set.image_mono (ramSetR_anti M hst))

theorem phiAt_le_self (M : Fld p) [FiniteDimensional ℚ_[p] M] {ϖ : Kbar p} (hϖ : IsUnif M ϖ)
    {v : ℝ} (hv : 0 ≤ v) : phiAt M v ≤ v := by
  have hg0 : 0 < (ramCard M 0 : ℝ) := by
    rw [← ramCardR_zero]; exact_mod_cast one_le_ramCardR M hϖ 0
  unfold phiAt
  calc ∫ t in (0 : ℝ)..v, (ramCardR M t : ℝ) / (ramCard M 0 : ℝ)
      ≤ ∫ t in (0 : ℝ)..v, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hv ((integrand_anti M).intervalIntegrable)
          intervalIntegrable_const
        intro t ht
        rw [div_le_one hg0]
        exact_mod_cast ramCardR_le M (by linarith [ht.1])
    _ = v := by simp

theorem le_phiAt (M : Fld p) [FiniteDimensional ℚ_[p] M] {ϖ : Kbar p} (hϖ : IsUnif M ϖ)
    {v : ℝ} (hv : 0 ≤ v) : v / (ramCard M 0 : ℝ) ≤ phiAt M v := by
  have hg0 : 0 < (ramCard M 0 : ℝ) := by
    rw [← ramCardR_zero]; exact_mod_cast one_le_ramCardR M hϖ 0
  unfold phiAt
  calc v / (ramCard M 0 : ℝ) = ∫ t in (0 : ℝ)..v, (1 : ℝ) / (ramCard M 0 : ℝ) := by simp [div_eq_mul_inv]
    _ ≤ ∫ t in (0 : ℝ)..v, (ramCardR M t : ℝ) / (ramCard M 0 : ℝ) := by
        apply intervalIntegral.integral_mono_on hv intervalIntegrable_const
          ((integrand_anti M).intervalIntegrable)
        intro t _
        apply div_le_div_of_nonneg_right _ hg0.le
        exact_mod_cast one_le_ramCardR M hϖ t

/-- Elements `z` with `‖z − 1‖ < 1` are closed under products and integer powers. -/
theorem norm_mul_sub_one_lt {a b : Kbar p} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) :
    ‖a * b - 1‖ < 1 := by
  have hna : ‖a‖ = 1 := by
    have : a = (a - 1) + 1 := by ring
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact ha.ne)]
    simp [ha.le]
  have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [this]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ha)
  rw [norm_mul, hna, _root_.one_mul]; exact hb

theorem norm_pow_sub_one_lt {a : Kbar p} (ha : ‖a - 1‖ < 1) (n : ℕ) : ‖a ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact norm_mul_sub_one_lt ih ha

theorem norm_inv_sub_one_lt {a : Kbar p} (ha : ‖a - 1‖ < 1) : ‖a⁻¹ - 1‖ < 1 := by
  have hna : ‖a‖ = 1 := by
    have : a = (a - 1) + 1 := by ring
    rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact ha.ne)]
    simp [ha.le]
  have ha0 : a ≠ 0 := by rintro rfl; simp at hna
  have : a⁻¹ - 1 = (1 - a) * a⁻¹ := by field_simp
  rw [this, norm_mul, norm_inv, hna, inv_one, _root_.mul_one, norm_sub_rev]; exact ha

theorem norm_zpow_sub_one_lt {a : Kbar p} (ha : ‖a - 1‖ < 1) (k : ℤ) : ‖a ^ k - 1‖ < 1 := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact norm_pow_sub_one_lt ha n
  · rw [zpow_neg, zpow_natCast]; exact norm_inv_sub_one_lt (norm_pow_sub_one_lt ha n)

/-- In `M` with uniformizer `ϖ`, every nonzero absolute value is a power of `‖ϖ‖`. -/
theorem norm_eq_zpow (M : Fld p) {ϖ : Kbar p} (hϖ : IsUnif M ϖ) (hr0 : 0 < ‖ϖ‖) {x : Kbar p}
    (hx : x ∈ M) (hx0 : x ≠ 0) : ∃ k : ℤ, ‖x‖ = ‖ϖ‖ ^ k := by
  set r := ‖ϖ‖ with hr
  have hr1 : r < 1 := hϖ.2.1
  have hϖ0 : ϖ ≠ 0 := norm_pos_iff.mp hr0
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow (norm_pos_iff.mpr hx0) (one_lt_inv_iff₀.mpr ⟨hr0, hr1⟩)
  refine ⟨-(n + 1), ?_⟩
  have h1 : r ^ (-n) < ‖x‖ := by rw [← inv_zpow']; exact hn1
  have h2 : ‖x‖ ≤ r ^ (-(n + 1)) := by rw [← inv_zpow']; exact hn2
  by_contra hne
  have hlt : ‖x‖ < r ^ (-(n + 1)) := lt_of_le_of_ne h2 hne
  let z := x * ϖ ^ (n + 1)
  have hz : z ∈ M := M.mul_mem hx (zpow_mem hϖ.1 _)
  have hzn : ‖z‖ = ‖x‖ * r ^ (n + 1) := by rw [norm_mul, norm_zpow]
  have hpos : 0 < r ^ (n + 1) := zpow_pos hr0 _
  have hz1 : ‖z‖ < 1 := by
    rw [hzn]
    calc ‖x‖ * r ^ (n + 1) < r ^ (-(n + 1)) * r ^ (n + 1) := mul_lt_mul_of_pos_right hlt hpos
      _ = 1 := by rw [← zpow_add₀ hr0.ne']; simp
  have hzr : r < ‖z‖ := by
    rw [hzn]
    calc r = r ^ (-n) * r ^ (n + 1) := by rw [← zpow_add₀ hr0.ne']; simp
      _ < ‖x‖ * r ^ (n + 1) := mul_lt_mul_of_pos_right h1 hpos
  exact absurd (hϖ.2.2 z hz hz1) (not_le.mpr hzr)

/-- At a level `M` with `σ ∈ G_1(M)`, `σ` is wild on `M`. -/
theorem wild_on_of_ramSet (M : Fld p) {ϖ : Kbar p} (hϖ : IsUnif M ϖ) {σ : PkgI4.GQp p}
    (hle : ∀ y ∈ M, ‖y‖ ≤ 1 → ‖σ y - y‖ ≤ ‖ϖ‖ ^ 2) :
    ∀ x ∈ M, x ≠ 0 → ‖σ x - x‖ < ‖x‖ := by
  set r := ‖ϖ‖ with hr
  have hr1 : r < 1 := hϖ.2.1
  have hr0 : 0 < r := by
    have hpM : ((p : ℚ_[p]) : Kbar p) ∈ M := M.algebraMap_mem _
    have hpn : ‖((p : ℚ_[p]) : Kbar p)‖ = (p : ℝ)⁻¹ := by
      rw [PadicAlgCl.norm_extends, Padic.norm_p]
    have hp1 : ‖((p : ℚ_[p]) : Kbar p)‖ < 1 := by
      rw [hpn]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    have := hϖ.2.2 _ hpM hp1
    rw [hpn] at this
    exact lt_of_lt_of_le (inv_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)) this
  have hϖ0 : ϖ ≠ 0 := norm_pos_iff.mp hr0
  intro x hx hx0
  obtain ⟨k, hk⟩ := norm_eq_zpow M hϖ hr0 hx hx0
  let w := x * ϖ ^ (-k)
  have hwM : w ∈ M := M.mul_mem hx (zpow_mem hϖ.1 _)
  have hw1 : ‖w‖ = 1 := by
    rw [norm_mul, norm_zpow, hk, ← zpow_add₀ hr0.ne']; simp
  have hw0 : w ≠ 0 := by rintro h; rw [h, norm_zero] at hw1; exact zero_ne_one hw1
  have hxw : x = w * ϖ ^ k := by
    show x = x * ϖ ^ (-k) * ϖ ^ k
    rw [_root_.mul_assoc, ← zpow_add₀ hϖ0]; simp
  have hb : ‖σ w * w⁻¹ - 1‖ < 1 := by
    have : σ w * w⁻¹ - 1 = (σ w - w) * w⁻¹ := by field_simp
    rw [this, norm_mul, norm_inv, hw1, inv_one, _root_.mul_one]
    exact lt_of_le_of_lt (hle w hwM hw1.le) (pow_lt_one₀ hr0.le hr1 (by norm_num))
  have ha : ‖σ ϖ * ϖ⁻¹ - 1‖ < 1 := by
    have : σ ϖ * ϖ⁻¹ - 1 = (σ ϖ - ϖ) * ϖ⁻¹ := by field_simp
    rw [this, norm_mul, norm_inv, ← hr]
    have h := hle ϖ hϖ.1 hr1.le
    calc ‖σ ϖ - ϖ‖ * r⁻¹ ≤ r ^ 2 * r⁻¹ := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hr0.le)
      _ = r := by field_simp
      _ < 1 := hr1
  have hq : σ x * x⁻¹ = (σ w * w⁻¹) * (σ ϖ * ϖ⁻¹) ^ k := by
    rw [hxw, map_mul, map_zpow₀, mul_zpow, mul_inv, inv_zpow]
    field_simp
  have hlt : ‖σ x * x⁻¹ - 1‖ < 1 := by
    rw [hq]; exact norm_mul_sub_one_lt hb (norm_zpow_sub_one_lt ha k)
  have : σ x - x = (σ x * x⁻¹ - 1) * x := by field_simp
  rw [this, norm_mul]
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  calc ‖σ x * x⁻¹ - 1‖ * ‖x‖ < 1 * ‖x‖ := mul_lt_mul_of_pos_right hlt hxn
    _ = ‖x‖ := _root_.one_mul _

/-- Positive upper groups lie in `G_1` at every finite level, hence act wildly there. -/
theorem upperSet_wild (M : Fld p) [FiniteDimensional ℚ_[p] M] {u : ℝ} (hu : 0 < u)
    {σ : PkgI4.GQp p} (hσ : σ ∈ upperSet M u) : ∀ x ∈ M, x ≠ 0 → ‖σ x - x‖ < ‖x‖ := by
  have h0 := sInf_nonneg_of_pos M hu
  unfold upperSet ramSetR at hσ
  rw [if_neg (show ¬ _ ≤ (-1 : ℝ) by linarith)] at hσ
  obtain ⟨ϖ, hϖ, hle⟩ := hσ
  have hg0 : 0 < (ramCard M 0 : ℝ) := by
    rw [← ramCardR_zero]; exact_mod_cast one_le_ramCardR M hϖ 0
  have hne : {v : ℝ | -1 ≤ v ∧ u ≤ phiAt M v}.Nonempty := by
    refine ⟨u * ramCard M 0, by nlinarith, ?_⟩
    have := le_phiAt M hϖ (v := u * ramCard M 0) (by positivity)
    rwa [mul_div_assoc, div_self hg0.ne', _root_.mul_one] at this
  have hS : u ≤ sInf {v : ℝ | -1 ≤ v ∧ u ≤ phiAt M v} := by
    apply le_csInf hne
    rintro v ⟨-, hv⟩
    by_cases hv0 : v ≤ 0
    · have := phiAt_nonpos M hv0; linarith
    · exact hv.trans (phiAt_le_self M hϖ (le_of_lt (not_le.mp hv0)))
  have hn : 1 ≤ ⌈sInf {v : ℝ | -1 ≤ v ∧ u ≤ phiAt M v}⌉.toNat := by
    have : (0 : ℝ) < sInf {v : ℝ | -1 ≤ v ∧ u ≤ phiAt M v} := lt_of_lt_of_le hu hS
    have : (0 : ℤ) < ⌈sInf {v : ℝ | -1 ≤ v ∧ u ≤ phiAt M v}⌉ := Int.ceil_pos.mpr this
    omega
  apply wild_on_of_ramSet M hϖ
  intro y hy hy1
  refine (hle y hy hy1).trans ?_
  exact pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega)

end UpperWild

/-- **`UpperAbsWild`, proved.** -/
theorem upperAbsWild : UpperAbsWild := by
  intro p _ u hu σ hσ x hx
  let K : LadicCond.Fld p := IntermediateField.adjoin ℚ_[p] {x}
  haveI hKfin : FiniteDimensional ℚ_[p] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let M : LadicCond.Fld p := IntermediateField.normalClosure ℚ_[p] K (LadicCond.Kbar p)
  have hM : LadicCond.IsFinGal M := ⟨inferInstance, inferInstance⟩
  have hxM : x ∈ M :=
    IntermediateField.le_normalClosure K (IntermediateField.mem_adjoin_simple_self ℚ_[p] x)
  haveI : FiniteDimensional ℚ_[p] M := hM.1
  exact upperSet_wild M hu (hσ M hM) x hxM hx

/-- **`KernelFieldBreaks` from `UpperBreakBound` and `BetaTrivialAtTwo`** (`UpperAbsWild` proved). -/
theorem kernelFieldBreaks_of' (hB : UpperBreakBound) (h2 : BetaTrivialAtTwo) : KernelFieldBreaks :=
  kernelFieldBreaks_of_halves (kernelFieldBreaksLow_of hB upperAbsWild h2) kernelFieldBreaksHigh

/-! ### `BetaTrivialAtTwo` reduced to its sign -/

/-- **Glue: the sign of `β` on high upper groups at `2`.** `BetaTrivialAtTwo` with the extra
hypothesis `β(decomp₂ σ)² = 1`, which is proved (`betaTrivialAtTwo_of_sign`). The remaining content
is that `β(decomp₂ σ) ≠ −1`: the manuscript's local-reciprocity argument at 2 (L826-843). GLUE. -/
def BetaSignAtTwo : Prop :=
  ∀ (u : ℚ) (P : LeafQM.AV.QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
    ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs 2 t,
      PkgI4.decomp 2 σ ∈ GQL L → β (PkgI4.decomp 2 σ) ^ 2 = 1 → β (PkgI4.decomp 2 σ) = 1

/-- `8 ∤ chiLevel Tm` for a set of primes (`lev 2 = 4`, `lev q = q` odd). -/
theorem not_eight_dvd_chiLevel :
    ∀ Tm : Finset ℕ, (∀ q ∈ Tm, q.Prime) →
      (2 ∉ Tm → ¬ 2 ∣ chiLevel Tm) ∧ ¬ 8 ∣ chiLevel Tm := by
  intro Tm
  induction Tm using Finset.induction_on with
  | empty => intro _; simp [chiLevel]
  | @insert a s ha ih =>
    intro hTm
    have ih' := ih (fun q hq => hTm q (Finset.mem_insert_of_mem hq))
    have haP : a.Prime := hTm a (Finset.mem_insert_self a s)
    have hcl : chiLevel (insert a s) = lev a * chiLevel s := Finset.prod_insert ha
    rw [hcl]
    by_cases ha2 : a = 2
    · subst ha2
      have hlev : lev 2 = 4 := by unfold lev; simp
      rw [hlev]
      have hns : ¬ 2 ∣ chiLevel s := ih'.1 ha
      refine ⟨fun h => absurd (Finset.mem_insert_self 2 s) h, fun h => ?_⟩
      have : 2 ∣ chiLevel s := by
        have h8 : 4 * 2 ∣ 4 * chiLevel s := by simpa using h
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h8
      exact hns this
    · have hlev : lev a = a := by unfold lev; simp [ha2]
      rw [hlev]
      have hodd : ¬ 2 ∣ a := fun h => ha2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two haP).mp h).symm
      have hcop : Nat.Coprime 8 a :=
        Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
      refine ⟨fun hnot h => ?_, fun h => ih'.2 (hcop.dvd_of_dvd_mul_left h)⟩
      have hs : 2 ∉ s := fun h' => hnot (Finset.mem_insert_of_mem h')
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
      · exact hodd h
      · exact ih'.1 hs h

/-- At `2`, a high upper element acts trivially on `μ_N` when `8 ∤ N` (the `4`-part through
`UpperBreakBound` for `ℚ_2(i)`, the odd part by wildness). -/
theorem cyc_decomp_two_eq_one (hB : UpperBreakBound) {t : ℝ} (ht : G0ModNewform.U0 < t)
    {σ : PkgI4.GQp 2} (hσ : σ ∈ LadicCond.upperAbs 2 t) {N : ℕ} [NeZero N] (hN8 : ¬ 8 ∣ N) :
    cyc N (PkgI4.decomp 2 σ) = 1 := by
  have ht0 : 0 < t := lt_of_le_of_lt U0_nonneg ht
  have hw : LinkedRamWild.IsWild σ := upperAbsWild 2 t ht0 hσ
  have he : ∀ x, embP 2 (PkgI4.decomp 2 σ x) = σ (embP 2 x) := embP_decomp 2 σ
  obtain ⟨b, N', hN', hNeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne N) 2 (by norm_num)
  have hb : b ≤ 2 := by
    by_contra hb
    exact hN8 (hNeq ▸ Dvd.dvd.mul_right (show 8 ∣ 2 ^ b from
      (pow_dvd_pow 2 (by omega : 3 ≤ b))) _)
  have hN'0 : 0 < N' := Nat.pos_of_ne_zero (by rintro rfl; simp at hNeq; exact NeZero.ne N hNeq)
  -- `g` fixes every `N`-th root of unity
  have hfix : ∀ y : AlgebraicClosure ℚ, y ^ N = 1 → PkgI4.decomp 2 σ y = y := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl; rw [zero_pow (NeZero.ne N)] at hy; exact zero_ne_one hy
    -- `z = y^{N'}` has `z^4 = 1`, hence degree `≤ 4`, hence is fixed
    have hz4 : (y ^ N') ^ 4 = 1 := by
      have : (y ^ N') ^ (2 ^ b) = 1 := by rw [← pow_mul, mul_comm, ← hNeq, hy]
      have h4 : 2 ^ b ∣ 4 := by
        interval_cases b <;> norm_num
      obtain ⟨c, hc⟩ := h4
      rw [hc, pow_mul, this, one_pow]
    have hzfix : PkgI4.decomp 2 σ (y ^ N') = y ^ N' := by
      apply (embP 2).injective
      rw [he]
      set z := y ^ N'
      let yz : PadicAlgCl 2 := embP 2 z
      have hyint : IsIntegral ℚ_[2] yz := Algebra.IsIntegral.isIntegral yz
      let F : LadicCond.Fld 2 := IntermediateField.adjoin ℚ_[2] {yz}
      haveI : FiniteDimensional ℚ_[2] F := IntermediateField.adjoin.finiteDimensional hyint
      have hq : (Polynomial.X ^ 4 - 1 : Polynomial ℚ_[2]) ≠ 0 := by
        intro h
        have := congrArg (Polynomial.eval 0) h
        simp at this
      have hdeg : Module.finrank ℚ_[2] F ≤ 4 := by
        rw [IntermediateField.adjoin.finrank hyint]
        have hdvd : minpoly ℚ_[2] yz ∣ (Polynomial.X ^ 4 - 1 : Polynomial ℚ_[2]) := by
          apply minpoly.dvd
          simp only [map_sub, map_pow, Polynomial.aeval_X, map_one]
          rw [show yz ^ 4 = embP 2 (z ^ 4) by rw [map_pow], hz4, map_one, sub_self]
        calc (minpoly ℚ_[2] yz).natDegree ≤ (Polynomial.X ^ 4 - 1 : Polynomial ℚ_[2]).natDegree :=
              Polynomial.natDegree_le_of_dvd hdvd hq
          _ = 4 := by
            rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp
      have hlt : 4 * (Module.finrank ℚ_[2] F : ℝ) ^ 2 < t := by
        refine lt_of_le_of_lt ?_ (lt_trans four_D_sq_lt_U0 ht)
        have h1 : (Module.finrank ℚ_[2] F : ℝ) ≤ 4 := by exact_mod_cast hdeg
        have h2 : (4 : ℝ) ≤ (ZInQ.heightD : ℝ) := by
          have := admissible_S_mul.2.2; nlinarith
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) (h1.trans h2) 2) (by norm_num)
      exact hB 2 F t hlt σ hσ yz (IntermediateField.mem_adjoin_simple_self ℚ_[2] yz)
    -- `ξ = σY/Y` has `ξ^{N'} = 1` and `‖ξ − 1‖ < 1`
    apply (embP 2).injective
    rw [he]
    set Y := embP 2 y
    have hY0 : Y ≠ 0 := (map_ne_zero _).mpr hy0
    have hξ : (σ Y * Y⁻¹) ^ N' = 1 := by
      have h1 : σ (Y ^ N') = Y ^ N' := by
        have := congrArg (embP 2) hzfix
        rw [he, map_pow] at this
        exact this
      rw [mul_pow, ← map_pow, h1, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hY0)]
    have hlt : ‖σ Y * Y⁻¹ - 1‖ < 1 := by
      have h1 := hw Y hY0
      have : σ Y * Y⁻¹ - 1 = (σ Y - Y) * Y⁻¹ := by field_simp
      rw [this, norm_mul, norm_inv]
      have hn : 0 < ‖Y‖ := norm_pos_iff.mpr hY0
      rw [mul_inv_lt_iff₀ hn, _root_.one_mul]; exact h1
    have := LinkedRamWild.eq_one_of_pow_eq_one (p := 2) hN'0 hN' hξ hlt
    field_simp at this
    exact this
  have : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hc := modularCyclotomicCharacter.unique (L := AlgebraicClosure ℚ) (n := N)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
    (toRingAut (PkgI4.decomp 2 σ)) (c := 1) (fun (t : (AlgebraicClosure ℚ)ˣ) ht => by
      have ht' : (t : AlgebraicClosure ℚ) ^ N = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N t).mp ht, Units.val_one]
      show (PkgI4.decomp 2 σ) (t : AlgebraicClosure ℚ) = _
      rw [hfix _ ht']
      rcases Nat.lt_or_ge 1 N with h1 | h1
      · haveI : Fact (1 < N) := ⟨h1⟩
        rw [ZMod.val_one, pow_one]
      · have hN1 : N = 1 := by have := NeZero.ne N; omega
        subst hN1
        have : t = 1 := by
          have := (mem_rootsOfUnity 1 t).mp ht
          simpa using this
        subst this
        simp)
  apply Units.ext
  rw [Units.val_one]
  exact hc.symm

/-- **`BetaTrivialAtTwo` from `UpperBreakBound` and `BetaSignAtTwo`**: `β(g)² = χ(g) = 1`. -/
theorem betaTrivialAtTwo_of_sign (hB : UpperBreakBound) (h : BetaSignAtTwo) : BetaTrivialAtTwo := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD t ht σ hσ hgL
  obtain ⟨_, -, -, -, ⟨Tm, hTm, hNlev⟩, -, hβsq, -, -, -, -, -, -⟩ := id hD
  have hN8 : ¬ 8 ∣ N := by
    rw [hNlev]
    exact (not_eight_dvd_chiLevel Tm (fun q hq => prime_of_mem_T (hTm hq))).2
  have hχ : galChar χ (PkgI4.decomp 2 σ) = 1 := by
    show χ.toUnitHom (cyc N (PkgI4.decomp 2 σ)) = 1
    rw [cyc_decomp_two_eq_one hB ht hσ hN8, map_one]
  exact h u P L A ε N χ β L' hLL' hD t ht σ hσ hgL ((hβsq _).trans hχ)

/-! ### `TateRamAtThree`, corrected -/

/-- **Glue: the Tate module of the QM model at `p = 3`, with `[L:ℚ] ≤ D`** (linked-tate's
`TateRamAtThree` with the degree bound that `G7Data` carries; Glazer L814-821: over
`F = L_v(A[5])`, of degree `≤ D·|GL₄(𝔽₅)| = D G₀`, Raynaud's criterion gives semistable reduction,
wild inertia acts trivially on `V₅`, and `G_{ℚ_3}^t ⊆ G_F ∩ P_3` for `t > U₀ = 4(DG₀)²`). GLUE. -/
def TateRamAtThreeD : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L')
    (PK : LeafQM.AV.QML3 K), Module.finrank ℚ L ≤ ZInQ.heightD →
    letI : NumberField L' := numberField_of_fd L'
    ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs 3 t,
      ∀ σ' : Field.absoluteGaloisGroup L', G0Galois.resQ L' σ' = PkgI4.decomp 3 σ →
        G0Galois.tate (@PkgI3.AbVar.baseChange L _
          (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) 5 σ' = 1

/-- The old form implies the corrected one. -/
theorem tateRamAtThreeD_of (h : TateRamAtThree) : TateRamAtThreeD :=
  fun K L L' _ _ hKL hLL' PK _ => h K L L' hKL hLL' PK

/-- **`LinkedRam`, proved** from G3, `KernelFieldBreaks`, the two proved Mathlib Props and the
corrected `TateRamAtThreeD` (linked-tate's `linkedRam_of`, with `[L:ℚ] ≤ D` taken from `G7Data`). -/
theorem linkedRam_of' (hG3 : HSyn.LinkedTate.QMModelG3) (hK : KernelFieldBreaks)
    (hLI : LocalInertiaGlobal) (hUI : UpperAbsInertia) (h3 : TateRamAtThreeD) : LinkedRam := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD Θ h hΘ m a n d h1 h2 hmL h4 h5 h6 h7 h8
    gam g0 g1 g2 g3 hgam1 j5 j3
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hK' := hK u P L A ε N χ β L' hLL' hD
  have hLD : Module.finrank ℚ L ≤ ZInQ.heightD := hD.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨K, hKL, PK, -, rfl⟩ := hD.1
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  -- on `G_{L'}`, `ρ` is the Tate action
  have hρ : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (g : PkgI4.GQ),
      g ∈ GQL L' →
      (∀ σ'' : Field.absoluteGaloisGroup L', G0Galois.resQ L' σ'' = g →
        G0Galois.tate (@PkgI3.AbVar.baseChange L _
          (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ σ'' = 1) →
      GlueDescent.rho (tmOf hLL' _ Θ h m ℓ) (fun _ => j 1) (fun g => j (gam (h * g * h⁻¹))) g
        = 1 := by
    intro ℓ _ j g hg ht
    obtain ⟨σ'', hσ''⟩ : g ∈ (@GaloisCopy.resQ L' _ hNF).range := by
      rw [resQRange L']; exact hg
    subst hσ''
    have hcj : h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹ ∈ GQL L' := hnorm.conj_mem _ hg h
    unfold GlueDescent.rho
    rw [tmOf_resQ hLL' _ Θ h hΘ m hmL ℓ σ'']
    have ht' : GaloisCopy.tate (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ σ'' = 1 :=
      ht σ'' rfl
    have hγ : gam (h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹) = 1 := hgam1 _ hcj
    rw [ht']
    show ((j (gam (h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹)))⁻¹ * j 1) • (1 : Module.End _ _) = 1
    rw [hγ, map_one, inv_one, _root_.one_mul, one_smul]
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hG5 := hG3 K L L' hKL hLL' PK 5
  have hG3' := hG3 K L L' hKL hLL' PK 3
  refine ⟨fun hp5 => ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩,
    fun hp5 => ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩⟩
  · -- `ρ₅`, `p ≠ 5`, `p ≤ D`
    have hσI := hUI p t (lt_of_le_of_lt U0_nonneg ht) hσ
    refine hρ 5 j5 _ ((hK' p hp).1 hpD t ht σ hσ) (fun σ'' hσ'' => ?_)
    by_cases hp3 : p = 3
    · subst hp3
      exact h3 K L L' hKL hLL' PK hLD t ht σ hσ σ'' hσ''
    · exact tate_trivial_of_g3 hLI hG5 p hp3 hp5 σ hσI σ'' hσ''
  · -- `ρ₅`, `p ≠ 5`, `p > D`
    have hσI := LadicCond.wildSet_subset_inertiaSet hσ
    have hp3 : p ≠ 3 := by
      intro h3'
      subst h3'
      have := three_le_heightD
      push_cast at hpD
      linarith
    exact hρ 5 j5 _ ((hK' p hp).2 hpD σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG5 p hp3 hp5 σ hσI σ'' hσ'')
  · -- `ρ₃`, `p = 5`, `p ≤ D`
    have hσI := hUI p t (lt_of_le_of_lt U0_nonneg ht) hσ
    have hp3 : p ≠ 3 := by omega
    exact hρ 3 j3 _ ((hK' p hp).1 hpD t ht σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG3' p hp3 hp3 σ hσI σ'' hσ'')
  · -- `ρ₃`, `p = 5`, `p > D`
    have hσI := LadicCond.wildSet_subset_inertiaSet hσ
    have hp3 : p ≠ 3 := by omega
    exact hρ 3 j3 _ ((hK' p hp).2 hpD σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG3' p hp3 hp3 σ hσI σ'' hσ'')

/-! ### `TateRamAtThreeD` reduced to Raynaud's criterion at `3` on the model -/

section TateRam

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- The Galois action on points is an action (`galHom_mul`). -/
theorem galAct_mul' {K : Type} [Field K] (A : PkgI3.AbVar K)
    (a b : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (P : A.Pt (AlgebraicClosure K)) :
    A.galAct (a * b) P = A.galAct a (A.galAct b P) := by
  show PkgI3.AbVar.galHom (a * b) ≫ P = PkgI3.AbVar.galHom a ≫ PkgI3.AbVar.galHom b ≫ P
  rw [PkgI3.AbVar.galHom_mul, Category.assoc]

/-- Compatibility with an isomorphism `ψ : K̄ ≅ ℚ̄` passes to powers. -/
theorem psi_pow_compat {K : Type} [Field K] (ψ : AlgebraicClosure K ≃+* PkgI4.Qbar)
    (σK : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (h : ∀ y, ψ (σK y) = g (ψ y)) (n : ℕ) (y : AlgebraicClosure K) :
    ψ ((σK ^ n) y) = (g ^ n) (ψ y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => rw [pow_succ σK n, AlgEquiv.mul_apply, ih, h, ← AlgEquiv.mul_apply, ← pow_succ]

/-- **Points: a `k`-th power with `p ∤ k` fixing a point forces the element itself to fix it**,
for `σK ∈ G_K` matching a wild `σ ∈ G_{ℚ_p}` under some `ψ : K̄ ≅ ℚ̄`. The stabilizer `S` of the
point is open (`PkgI3.RhoCont`), hence closed, so `S = G_{K̄^S}`; `σK^k` fixes `K̄^S`, and W2 moves
this to `σK`. -/
theorem fix_of_pow_fix {K : Type} [Field K] [CharZero K] (A : PkgI3.AbVar K)
    (ψ : AlgebraicClosure K ≃+* PkgI4.Qbar) (σK : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    {p : ℕ} [Fact p.Prime] (σ : PkgI4.GQp p) (hσ : σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)))
    (hc : ∀ y, ψ (σK y) = PkgI4.decomp p σ (ψ y)) {k : ℕ} (hk0 : 0 < k) (hk : ¬ p ∣ k)
    (x : A.Pt (AlgebraicClosure K)) (hx : A.galAct (σK ^ k) x = x) : A.galAct σK x = x := by
  haveI : IsGalois K (AlgebraicClosure K) := {}
  have hone : A.galAct (1 : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) x = x := by
    show PkgI3.AbVar.galHom 1 ≫ x = x
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  obtain ⟨U, hU⟩ := PkgI3.RhoCont.exists_openSubgroup_galAct_eq A x
  let S : Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
    { carrier := {g | A.galAct g x = x}
      mul_mem' := fun {a b} ha hb => by
        show A.galAct (a * b) x = x
        rw [galAct_mul', show A.galAct b x = x from hb, show A.galAct a x = x from ha]
      one_mem' := hone
      inv_mem' := fun {a} ha => by
        show A.galAct a⁻¹ x = x
        have ha' : A.galAct a x = x := ha
        conv_lhs => rw [← ha']
        rw [← galAct_mul', inv_mul_cancel, hone] }
  have hSopen : IsOpen (S : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isOpen_mono (H₁ := U.toSubgroup) (fun g hg => hU g hg) U.isOpen
  have hSclosed : IsClosed (S : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isClosed_of_isOpen S hSopen
  have hfix := InfiniteGalois.fixingSubgroup_fixedField (⟨S, hSclosed⟩ : ClosedSubgroup _)
  have hk' : σK ^ k ∈ S := hx
  have hmem : σK ∈ (IntermediateField.fixedField S).fixingSubgroup := by
    refine (IntermediateField.mem_fixingSubgroup_iff _ σK).mpr ?_
    intro y hy
    have hyk : (σK ^ k) y = y := (IntermediateField.mem_fixedField_iff S y).mp hy _ hk'
    apply ψ.injective
    rw [hc]
    have he : ∀ z, embP p (PkgI4.decomp p σ z) = σ (embP p z) := embP_decomp p σ
    have h1 : (PkgI4.decomp p σ ^ k) (ψ y) = ψ y := by
      rw [← psi_pow_compat ψ σK (PkgI4.decomp p σ) hc k y, hyk]
    apply (embP p).injective
    rw [he]
    refine LinkedRamWild.wild_fix_of_pow hσ hk0 hk ?_
    rw [← LinkedRamWild.pow_compat (embP p) (PkgI4.decomp p σ) he k, h1]
  rw [hfix] at hmem
  exact hmem

/-- **Glue: Raynaud's criterion at `3` for high upper ramification on the QM model.** For a
`QML3` object over `K` with `[K:ℚ] ≤ D`, an isomorphism `ψ : K̄ ≅ ℚ̄` and `σK ∈ G_K` matching
`σ ∈ G_{ℚ_3}^t` (`t > U₀`), `σK` acts unipotently, `(σK − 1)² = 0`, on `A(K̄)[5ⁿ]`.
Route (STANDARD; Glazer L814-821): `K₁ = K(A[5])` has `[K₁:ℚ] ≤ D·|GL₄(𝔽₅)| = DG₀` (T5, open
stabilizers), so `σK` fixes `K₁` (`UpperBreakBound`, `4(DG₀)² = U₀ < t`); `σK` is in the inertia
group of the place `ψ^*(v)` above `3` (`UpperAbsInertia`, `LocalInertiaGlobal`); Raynaud's
criterion (R6, `PkgI2.RaynaudCriterion`, with `m = 5`) over `K₁` at that place. GLUE (the
transport of R6 along `K ⊆ K₁`, as lt-goodred transported NOS). -/
def RaynaudAtThree : Prop :=
  ∀ (K : IF) [FiniteDimensional ℚ K] (PK : LeafQM.AV.QML3 K), Module.finrank ℚ K ≤ ZInQ.heightD →
    ∀ (ψ : AlgebraicClosure K ≃+* PkgI4.Qbar) (σK : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (t : ℝ), G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs 3 t,
      (∀ y, ψ (σK y) = PkgI4.decomp 3 σ (ψ y)) →
      ∀ (n : ℕ) (x : PK.A.Pt (AlgebraicClosure K)), x ^ (5 ^ n) = 1 →
        PK.A.galAct σK (PK.A.galAct σK x) * (PK.A.galAct σK x)⁻¹ * (PK.A.galAct σK x)⁻¹ * x = 1

/-- **The model statement at `3`** (over `K` itself): the same `σK` fixes `A(K̄)[5ⁿ]`. -/
def TateRamCore : Prop :=
  ∀ (K : IF) [FiniteDimensional ℚ K] (PK : LeafQM.AV.QML3 K), Module.finrank ℚ K ≤ ZInQ.heightD →
    ∀ (ψ : AlgebraicClosure K ≃+* PkgI4.Qbar) (σK : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (t : ℝ), G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs 3 t,
      (∀ y, ψ (σK y) = PkgI4.decomp 3 σ (ψ y)) →
      ∀ (n : ℕ) (x : PK.A.Pt (AlgebraicClosure K)), x ^ (5 ^ n) = 1 → PK.A.galAct σK x = x

/-- **`TateRamCore` from `RaynaudAtThree`**: unipotence gives `σK^{5ⁿ} x = x` (with
`y = σK x · x⁻¹` fixed, `σK^m x = y^m x` and `y^{5ⁿ} = 1`), `σ` is wild (`upperAbsWild`), and
`3 ∤ 5ⁿ` (`fix_of_pow_fix`). -/
theorem tateRamCore_of (hR : RaynaudAtThree) : TateRamCore := by
  intro K _ PK hK ψ σK t ht σ hσ hc n x hx
  have hu := hR K PK hK ψ σK t ht σ hσ hc n x hx
  set s := PK.A.galAct σK with hs
  set y := s x * x⁻¹ with hy
  have hsy : s y = y := by
    rw [hy, map_mul, map_inv]
    have h2 : s (s x) * (s x)⁻¹ = ((s x)⁻¹ * x)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hu]; group
    rw [h2, mul_inv_rev, inv_inv, mul_comm]
  have hsx : y * x = s x := by simp only [hy, inv_mul_cancel_right]
  have hiter : ∀ m : ℕ, PK.A.galAct (σK ^ m) x = y ^ m * x := by
    intro m
    induction m with
    | zero =>
      show PkgI3.AbVar.galHom 1 ≫ x = 1 * x
      rw [PkgI3.AbVar.galHom_one, Category.id_comp, _root_.one_mul]
    | succ m ih =>
      rw [pow_succ', galAct_mul', ih, map_mul, map_pow, hsy]
      show y ^ m * s x = y ^ (m + 1) * x
      rw [pow_succ, _root_.mul_assoc, hsx]
  have hy5 : y ^ (5 ^ n) = 1 := by
    rw [hy, mul_pow, ← map_pow, hx, map_one, inv_pow, hx, inv_one, _root_.mul_one]
  have hfix5 : PK.A.galAct (σK ^ (5 ^ n)) x = x := by rw [hiter, hy5, _root_.one_mul]
  have hw : σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp 3)) :=
    upperAbsWild 3 t (lt_of_le_of_lt U0_nonneg ht) hσ
  have h35 : ¬ 3 ∣ 5 ^ n := by
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  exact fix_of_pow_fix PK.A ψ σK σ hw hc (pow_pos (by norm_num) n) h35 x hfix5

set_option maxHeartbeats 1000000 in
/-- **`TateRamAtThreeD` from `TateRamCore`**: transport along `\bar{L'} ≅ K̄` over `K` and
`A_{L,L'}(\bar{L'}) ≅ A(K̄)`, exactly as in lt-goodred's `goodRedTorsion`. -/
theorem tateRamAtThreeD_of_core (hC : TateRamCore) : TateRamAtThreeD := by
  intro K L L' _ _ hKL hLL' PK hLD
  letI hNF : NumberField L' := numberField_of_fd L'
  intro t ht σ hσ σ' hσ'
  haveI hLfd : FiniteDimensional ℚ L := FiniteDimensional.of_injective
    (IntermediateField.inclusion hLL').toLinearMap
    (IntermediateField.inclusion hLL').toRingHom.injective
  haveI hKfd : FiniteDimensional ℚ K := FiniteDimensional.of_injective
    (IntermediateField.inclusion (hKL.trans hLL')).toLinearMap
    (IntermediateField.inclusion (hKL.trans hLL')).toRingHom.injective
  have hKD : Module.finrank ℚ K ≤ ZInQ.heightD :=
    (IntermediateField.finrank_le_of_le_right hKL).trans hLD
  apply HSyn.LinkedTate.tate_eq_one_of_torsion
  intro n x hx
  letI iKL : Algebra K L := incAlg hKL
  letI iLL' : Algebra L L' := incAlg hLL'
  letI iKL' : Algebra K L' := incAlg (hKL.trans hLL')
  haveI tKLL' : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tLΩ : IsScalarTower L L' (AlgebraicClosure L') := inferInstance
  haveI tKL'Ω : IsScalarTower K L' (AlgebraicClosure L') := inferInstance
  haveI tKLΩ : IsScalarTower K L (AlgebraicClosure L') := IsScalarTower.of_algebraMap_eq
    (fun y => by
      rw [IsScalarTower.algebraMap_apply K L' (AlgebraicClosure L'),
        IsScalarTower.algebraMap_apply L L' (AlgebraicClosure L'),
        IsScalarTower.algebraMap_apply K L L'])
  haveI tQKL' : IsScalarTower ℚ K L' := IsScalarTower.of_algebraMap_eq (fun q => by
    rw [eq_ratCast (algebraMap ℚ L') q, eq_ratCast (algebraMap ℚ K) q, map_ratCast])
  haveI : Algebra.IsAlgebraic ℚ L' := Algebra.IsAlgebraic.of_finite ℚ L'
  haveI : Algebra.IsAlgebraic K L' := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : Algebra.IsAlgebraic L' (AlgebraicClosure L') := AlgebraicClosure.isAlgebraic L'
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure L') :=
    Algebra.IsAlgebraic.trans K L' (AlgebraicClosure L')
  haveI : IsAlgClosure K (AlgebraicClosure L') := ⟨inferInstance, inferInstance⟩
  let τ : AlgebraicClosure L' ≃ₐ[K] AlgebraicClosure K :=
    IsAlgClosure.equiv K (AlgebraicClosure L') (AlgebraicClosure K)
  let g : PkgI4.Qbar →ₐ[ℚ] AlgebraicClosure L' := (G0Galois.qEmbRing L').toRatAlgHom
  haveI hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L') :=
    Algebra.IsAlgebraic.trans ℚ L' (AlgebraicClosure L')
  have hgbij : Function.Bijective g := by
    letI : Algebra PkgI4.Qbar (AlgebraicClosure L') := g.toAlgebra
    haveI : IsScalarTower ℚ PkgI4.Qbar (AlgebraicClosure L') :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L') := inferInstance
    haveI : Algebra.IsIntegral PkgI4.Qbar (AlgebraicClosure L') := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ge : PkgI4.Qbar ≃+* AlgebraicClosure L' := RingEquiv.ofBijective (G0Galois.qEmbRing L') hgbij
  have hge : ∀ z, ge z = G0Galois.qEmbRing L' z := fun _ => rfl
  let ψ : AlgebraicClosure K ≃+* PkgI4.Qbar := τ.symm.toRingEquiv.trans ge.symm
  let s' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L' := σ'
  let σK : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    (τ.symm.trans (s'.restrictScalars K)).trans τ
  have hσK : ∀ y, σK y = τ (s' (τ.symm y)) := fun _ => rfl
  have hres : ∀ y, ψ (σK y) = (G0Galois.resQ L' σ') (ψ y) := by
    intro y
    apply ge.injective
    show ge (ge.symm (τ.symm (σK y))) = ge ((G0Galois.resQ L' σ') (ge.symm (τ.symm y)))
    rw [RingEquiv.apply_symm_apply, hσK, AlgEquiv.symm_apply_apply]
    have hspec := G0Galois.resQ_spec L' σ' (ge.symm (τ.symm y))
    rw [← hge, ← hge, RingEquiv.apply_symm_apply] at hspec
    exact hspec.symm
  have hcomp : ∀ y, ψ (σK y) = PkgI4.decomp 3 σ (ψ y) := by
    intro y; rw [hres, hσ']
  let E := (UnramTate.bcPt (K := L) (L := L') (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
    (AlgebraicClosure L')).trans ((UnramTate.bcPt (K := K) (L := L) PK.A (AlgebraicClosure L')).trans
      (UnramTate.trPt PK.A τ))
  have hE : ∀ y, E ((@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct s' y) =
      PK.A.galAct σK (E y) := by
    intro y
    show UnramTate.trPt PK.A τ (UnramTate.bcPt (K := K) (L := L) PK.A (AlgebraicClosure L')
        (UnramTate.bcPt (K := L) (L := L') (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
          (AlgebraicClosure L')
          ((@PkgI3.AbVar.baseChange L _
            (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct s' y))) = _
    rw [UnramTate.bcPt_galAct, UnramTate.bcPt_galAct]
    exact UnramTate.trPt_galAct PK.A τ _ σK (fun z => by rw [hσK, AlgEquiv.symm_apply_apply]; rfl) _
  have hEx : E x ^ (5 ^ n) = 1 := by rw [← map_pow, hx, map_one]
  have hfix : PK.A.galAct σK (E x) = E x := hC K PK hKD ψ σK t ht σ hσ hcomp n (E x) hEx
  apply E.injective
  exact (hE x).trans hfix

/-- **`TateRamAtThreeD` from `RaynaudAtThree`.** -/
theorem tateRamAtThreeD_of_raynaud (hR : RaynaudAtThree) : TateRamAtThreeD :=
  tateRamAtThreeD_of_core (tateRamCore_of hR)

/-! #### `RaynaudAtThree` from R6, `UpperBreakBound` and the `5`-torsion field -/

/-- **Glue: the `5`-torsion field of a QM surface has degree `≤ |GL₄(𝔽₅)| = G₀`.** For a `QML3`
object over a number field `K ⊆ ℚ̄`, there is a finite `K₁/K` inside `K̄` with `[K₁:K] ≤ G₀` such
that every `g ∈ G_K` fixing `K₁` fixes `A(K̄)[5]`. Route (STANDARD): `A(K̄)[5] ≅ (ℤ/5)⁴` (T5); the
stabilizer of `A[5]` is open (`PkgI3.RhoCont`), its fixed field `K₁` has `[K₁:K]` = its index =
the order of the image of `G_K` in `Aut(A[5]) ≅ GL₄(𝔽₅)`. GLUE (Galois theory and counting). -/
def TorsionFieldFive : Prop :=
  ∀ (K : IF) [FiniteDimensional ℚ K] (PK : LeafQM.AV.QML3 K),
    ∃ K₁ : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K₁ ∧
      Module.finrank K K₁ ≤ ZInQ.heightG0 ∧
      ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ K₁, g y = y) →
        ∀ x : PK.A.Pt (AlgebraicClosure K), x ^ 5 = 1 → PK.A.galAct g x = x

/-- `4 (D G₀)² = U₀`. -/
theorem U0_eq : G0ModNewform.U0 = 4 * (((ZInQ.heightD * ZInQ.heightG0 : ℕ) : ℝ)) ^ 2 := rfl

set_option maxHeartbeats 1000000 in
/-- **`RaynaudAtThree`, proved** from R6 (`PkgI2.RaynaudCriterion`), `UpperBreakBound` and
`TorsionFieldFive`: `σK` fixes `K₁` (each `y ∈ K₁` has degree `≤ D G₀` over `ℚ`, so the break bound
applies to `ℚ_3(embP (ψ y))`), lies in the inertia group of `ψ^*(v)` (`upperAbsInertia`,
`localInertiaGlobal`), and Raynaud's criterion over `K₁` with `m = 5` gives `(σK − 1)² = 0` on
`A(K̄)[5ⁿ]`, transported along `A_{K₁}(K̄₁) ≅ A(K̄)`. -/
theorem raynaudAtThree_of (hRay : PkgI2.RaynaudCriterion.{0}) (hB : UpperBreakBound)
    (hT : TorsionFieldFive) : RaynaudAtThree := by
  intro K _ PK hK ψ σK t ht σ hσ hc n x hx
  obtain ⟨K₁, hK₁fd, hK₁deg, hK₁fix⟩ := hT K PK
  haveI := hK₁fd
  have ht0 : 0 < t := lt_of_le_of_lt U0_nonneg ht
  -- (1) `σK` fixes `K₁`
  have hfixK₁ : ∀ y ∈ K₁, σK y = y := by
    intro y hy
    apply ψ.injective
    rw [hc]
    set z := ψ y
    -- degree of `z` over `ℚ`
    haveI : FiniteDimensional ℚ K₁ := Module.Finite.trans K K₁
    have hdegz : (minpoly ℚ z).natDegree ≤ ZInQ.heightD * ZInQ.heightG0 := by
      have h1 : minpoly ℚ z = minpoly ℚ y := minpoly.algEquiv_eq ψ.toRatAlgEquiv y
      have h2 : minpoly ℚ y = minpoly ℚ (⟨y, hy⟩ : K₁) :=
        minpoly.algebraMap_eq (A := ℚ) (algebraMap K₁ (AlgebraicClosure K)).injective (⟨y, hy⟩ : K₁)
      have h3 : (minpoly ℚ (⟨y, hy⟩ : K₁)).natDegree ≤ Module.finrank ℚ K₁ := minpoly.natDegree_le _
      have h4 : Module.finrank ℚ K₁ = Module.finrank ℚ K * Module.finrank K K₁ :=
        (Module.finrank_mul_finrank ℚ K K₁).symm
      rw [h1, h2]
      calc _ ≤ Module.finrank ℚ K₁ := h3
        _ = Module.finrank ℚ K * Module.finrank K K₁ := h4
        _ ≤ ZInQ.heightD * ZInQ.heightG0 := Nat.mul_le_mul hK hK₁deg
    -- the break bound at `ℚ_3(embP z)`
    have he : ∀ w, embP 3 (PkgI4.decomp 3 σ w) = σ (embP 3 w) := embP_decomp 3 σ
    apply (embP 3).injective
    rw [he]
    let yz : PadicAlgCl 3 := embP 3 z
    have hyint : IsIntegral ℚ_[3] yz := Algebra.IsIntegral.isIntegral yz
    let F : LadicCond.Fld 3 := IntermediateField.adjoin ℚ_[3] {yz}
    haveI : FiniteDimensional ℚ_[3] F := IntermediateField.adjoin.finiteDimensional hyint
    have hdeg : Module.finrank ℚ_[3] F ≤ ZInQ.heightD * ZInQ.heightG0 := by
      have h1 : Module.finrank ℚ_[3] F = (minpoly ℚ_[3] yz).natDegree :=
        IntermediateField.adjoin.finrank hyint
      have hq0 : (minpoly ℚ z).map (algebraMap ℚ ℚ_[3]) ≠ 0 :=
        Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral z))
      have h2 : minpoly ℚ_[3] yz ∣ (minpoly ℚ z).map (algebraMap ℚ ℚ_[3]) := by
        apply minpoly.dvd
        rw [Polynomial.aeval_map_algebraMap]
        rw [show Polynomial.aeval yz (minpoly ℚ z) =
            (embP 3).toRatAlgHom (Polynomial.aeval z (minpoly ℚ z))
          from Polynomial.aeval_algHom_apply (embP 3).toRatAlgHom z _, minpoly.aeval, map_zero]
      rw [h1]
      calc (minpoly ℚ_[3] yz).natDegree ≤ ((minpoly ℚ z).map (algebraMap ℚ ℚ_[3])).natDegree :=
            Polynomial.natDegree_le_of_dvd h2 hq0
        _ = (minpoly ℚ z).natDegree := Polynomial.natDegree_map _
        _ ≤ _ := hdegz
    have hlt : 4 * (Module.finrank ℚ_[3] F : ℝ) ^ 2 < t := by
      refine lt_of_le_of_lt ?_ ht
      rw [U0_eq]
      have : (Module.finrank ℚ_[3] F : ℝ) ≤ ((ZInQ.heightD * ZInQ.heightG0 : ℕ) : ℝ) := by
        exact_mod_cast hdeg
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) this 2) (by norm_num)
    exact hB 3 F t hlt σ hσ yz (IntermediateField.mem_adjoin_simple_self ℚ_[3] yz)
  -- (2) the inertia data at a place above `3`
  have hσI := upperAbsInertia 3 t ht0 hσ
  obtain ⟨v, hv, τv, hτv, hτveq⟩ := localInertiaGlobal 3 σ hσI
  obtain ⟨hv1, hv2⟩ := LTGoodRed.of_mem_inertia ℚ v τv hτv
  rw [hτveq] at hv1 hv2
  -- (3) `K₁`, its algebraic closure `K̄₁ ≅ K̄`, `σ₁`, `ψ₁`
  haveI hK₁NF : NumberField K₁ :=
    { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans K K₁ }
  haveI : Algebra.IsAlgebraic K₁ (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) K₁
  haveI : IsAlgClosure K₁ (AlgebraicClosure K) := ⟨inferInstance, inferInstance⟩
  let τ₁ : AlgebraicClosure K₁ ≃ₐ[K₁] AlgebraicClosure K :=
    IsAlgClosure.equiv K₁ (AlgebraicClosure K₁) (AlgebraicClosure K)
  let σK₁ : AlgebraicClosure K ≃ₐ[K₁] AlgebraicClosure K :=
    AlgEquiv.ofRingEquiv (f := σK.toRingEquiv) (fun k => hfixK₁ k k.2)
  let σ₁ : AlgebraicClosure K₁ ≃ₐ[K₁] AlgebraicClosure K₁ := (τ₁.trans σK₁).trans τ₁.symm
  have hσ₁ : ∀ y, τ₁ (σ₁ y) = σK₁ (τ₁ y) := fun y => by
    show τ₁ (τ₁.symm (σK₁ (τ₁ y))) = _
    rw [AlgEquiv.apply_symm_apply]
  have hrs : σK₁.restrictScalars K = σK := AlgEquiv.ext fun _ => rfl
  let ψ₁ : AlgebraicClosure K₁ ≃+* PkgI4.Qbar := τ₁.toRingEquiv.trans ψ
  have hc₁ : ∀ y, ψ₁ (σ₁ y) = PkgI4.decomp 3 σ (ψ₁ y) := fun y => by
    show ψ (τ₁ (σ₁ y)) = _
    rw [hσ₁]
    exact hc (τ₁ y)
  let w₁ : ValuationSubring (AlgebraicClosure K₁) := v.comap (ψ₁ : AlgebraicClosure K₁ →+* PkgI4.Qbar)
  let O₁ : ValuationSubring K₁ := w₁.comap (algebraMap K₁ (AlgebraicClosure K₁))
  have h3w : ((3 : ℕ) : AlgebraicClosure K₁) ∈ w₁.nonunits := by
    rw [LTGoodRed.mem_nonunits_comap v ψ₁, map_natCast]; exact hv
  have hunit : ∀ m : ℕ, Nat.Coprime m 3 → IsUnit (m : O₁) := by
    intro m hm
    obtain ⟨hm0, hmi⟩ := LTGoodRed.inv_mem_of_notMem_nonunits w₁
      (LTGoodRed.natCast_notMem_nonunits w₁ h3w hm)
    have hm0K : (m : K₁) ≠ 0 := by
      intro h; apply hm0
      rw [← map_natCast (algebraMap K₁ (AlgebraicClosure K₁)), h, map_zero]
    have hmO : (m : K₁)⁻¹ ∈ O₁ := by
      rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]; exact hmi
    refine isUnit_iff_exists_inv.mpr ⟨⟨(m : K₁)⁻¹, hmO⟩, Subtype.ext ?_⟩
    push_cast
    exact mul_inv_cancel₀ hm0K
  have hOtop : O₁ ≠ ⊤ := by
    intro htop
    have hpi : ((3 : ℕ) : K₁)⁻¹ ∈ O₁ := by rw [htop]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at hpi
    rw [ValuationSubring.mem_nonunits_iff_or] at h3w
    rcases h3w with h | h
    · exact (by norm_num : (3 : ℕ) ≠ 0) (by exact_mod_cast h)
    · exact h hpi
  haveI hODVR : IsDiscreteValuationRing O₁ := LTGoodRed.NLG.isDiscreteValuationRing_of_ne_top O₁ hOtop
  have h5 : IsUnit ((5 : ℕ) : O₁) := hunit 5 (by norm_num)
  have hI₁ : PkgI2.IsInertia w₁ σ₁ := by
    refine LTGoodRed.isInertia_of K₁ w₁ σ₁ (fun y => ?_) (fun a ha => ?_)
    · show ψ₁ (σ₁ y) ∈ v ↔ ψ₁ y ∈ v
      rw [hc₁]; exact hv1 (ψ₁ y)
    · rw [LTGoodRed.mem_nonunits_comap v ψ₁, map_sub, hc₁]
      exact hv2 (ψ₁ a) ha
  -- (4) the points: `E₁ : A_{K₁}(K̄₁) ≃* PK.A(K̄)`
  let A₁ : PkgI3.AbVar K₁ := PK.A.baseChange K₁
  let E₁ := (UnramTate.trPt A₁ τ₁).trans (UnramTate.bcPt (K := K) (L := K₁) PK.A (AlgebraicClosure K))
  have hE₁ : ∀ (g : AlgebraicClosure K₁ ≃ₐ[K₁] AlgebraicClosure K₁)
      (g' : AlgebraicClosure K ≃ₐ[K₁] AlgebraicClosure K), (∀ y, τ₁ (g y) = g' (τ₁ y)) →
      ∀ p, E₁ (A₁.galAct g p) = PK.A.galAct (g'.restrictScalars K) (E₁ p) := by
    intro g g' hg p
    show UnramTate.bcPt (K := K) (L := K₁) PK.A (AlgebraicClosure K)
        (UnramTate.trPt A₁ τ₁ (A₁.galAct g p)) = _
    rw [UnramTate.trPt_galAct A₁ τ₁ g g' (fun y => (hg y).symm) p, UnramTate.bcPt_galAct]
    rfl
  -- (5) `A_{K₁}[5]` is rational over `K₁`
  have hrat : ∀ g : AlgebraicClosure K₁ ≃ₐ[K₁] AlgebraicClosure K₁,
      ∀ p ∈ PkgI2.torsion (ObjBridge.toGrp A₁) (AlgebraicClosure K₁) 5,
        PkgI2.galAct (ObjBridge.toGrp A₁) g p = p := by
    intro g p hp
    let g' : AlgebraicClosure K ≃ₐ[K₁] AlgebraicClosure K := (τ₁.symm.trans g).trans τ₁
    have hg : ∀ y, τ₁ (g y) = g' (τ₁ y) := fun y => by
      show τ₁ (g y) = τ₁ (g (τ₁.symm (τ₁ y))); rw [AlgEquiv.symm_apply_apply]
    have hp5 : (E₁ p) ^ 5 = 1 := by
      have : p ^ 5 = 1 := hp
      exact (map_pow E₁ p 5).symm.trans ((congrArg E₁ this).trans (map_one E₁))
    have hfix := hK₁fix (g'.restrictScalars K) (fun y hy => g'.commutes ⟨y, hy⟩) (E₁ p) hp5
    apply E₁.injective
    exact (hE₁ g g' hg p).trans hfix
  -- (6) Raynaud
  have hx₁ : E₁.symm x ∈ PkgI2.torsion (ObjBridge.toGrp A₁) (AlgebraicClosure K₁) (5 ^ n) := by
    show (E₁.symm x) ^ (5 ^ n) = 1
    exact (map_pow E₁.symm x (5 ^ n)).symm.trans ((congrArg E₁.symm hx).trans (map_one E₁.symm))
  have hu := hRay K₁ O₁ w₁ rfl (ObjBridge.toGrp A₁) 5 (by norm_num) h5 hrat σ₁ hI₁ 5
    Nat.prime_five (by exact_mod_cast h5) n (E₁.symm x) hx₁
  -- (7) transport `(σ₁ − 1)² = 0` back
  have hσ' : ∀ p, E₁ (A₁.galAct σ₁ p) = PK.A.galAct σK (E₁ p) := fun p => by
    rw [hE₁ σ₁ σK₁ hσ₁ p, hrs]
  have hu' : A₁.galAct σ₁ (A₁.galAct σ₁ (E₁.symm x)) * (A₁.galAct σ₁ (E₁.symm x))⁻¹ *
      (A₁.galAct σ₁ (E₁.symm x))⁻¹ * E₁.symm x = 1 := hu
  have := congrArg E₁ hu'
  rw [map_mul, map_mul, map_mul, map_inv, map_one, hσ', hσ', MulEquiv.apply_symm_apply] at this
  exact this

/-! #### `TorsionFieldFive`, proved from T5 -/

/-- `|GL₄(𝔽₅)| = (5⁴−1)(5⁴−5)(5⁴−25)(5⁴−125) = G₀`. -/
theorem card_GL4_F5 : Nat.card (GL (Fin 4) (ZMod 5)) = ZInQ.heightG0 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  unfold ZInQ.heightG0
  norm_num

/-- Additive automorphisms of `𝔽₅⁴` number at most `G₀`. -/
theorem card_addAut_le : Nat.card ((Fin 4 → ZMod 5) ≃+ (Fin 4 → ZMod 5)) ≤ ZInQ.heightG0 := by
  rw [← card_GL4_F5, ← Nat.card_congr (Matrix.GeneralLinearGroup.toLin (n := Fin 4)
    (R := ZMod 5)).symm.toEquiv]
  let toGL : ((Fin 4 → ZMod 5) ≃+ (Fin 4 → ZMod 5)) →
      LinearMap.GeneralLinearGroup (ZMod 5) (Fin 4 → ZMod 5) := fun f =>
    Units.mk (f.toAddMonoidHom.toZModLinearMap 5) (f.symm.toAddMonoidHom.toZModLinearMap 5)
      (LinearMap.ext fun v => by simp) (LinearMap.ext fun v => by simp)
  have htoGL : Function.Injective toGL := by
    intro f g h
    apply AddEquiv.ext
    intro v
    exact congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 5) (Fin 4 → ZMod 5) =>
      (u : (Fin 4 → ZMod 5) →ₗ[ZMod 5] (Fin 4 → ZMod 5)) v) h
  haveI : Finite (LinearMap.GeneralLinearGroup (ZMod 5) (Fin 4 → ZMod 5)) :=
    Finite.of_equiv _ (Matrix.GeneralLinearGroup.toLin (n := Fin 4) (R := ZMod 5)).toEquiv
  exact Nat.card_le_card_of_injective toGL htoGL

set_option maxHeartbeats 1000000 in
/-- **`TorsionFieldFive`, proved from T5** (`PkgI2.TorsionStructure`): the stabilizer `S` of
`A(K̄)[5] ≅ 𝔽₅⁴` is open (finitely many open point stabilizers), `K₁ = K̄^S` is finite with
`[K₁:K] = [G_K : S]`, and `G_K/S` embeds in `Aut(𝔽₅⁴)`, of order `G₀`. Worked on the `PkgI2`
side (`PkgI2.Pts`, `PkgI2.galAct`), which is definitionally `PkgI3`'s. -/
theorem torsionFieldFive_of (hTors : PkgI2.TorsionStructure.{0}) : TorsionFieldFive := by
  intro K _ PK
  haveI : IsGalois K (AlgebraicClosure K) := {}
  let G := ObjBridge.toGrp PK.A
  obtain ⟨e, he⟩ := hTors K G 2 5
    (by have h := PK.surface; simp only [PkgI3.AbVar.dim] at h; rw [h]; norm_cast) (by norm_num)
    (by norm_num)
  let ga : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →
      PkgI2.Pts G (AlgebraicClosure K) → PkgI2.Pts G (AlgebraicClosure K) :=
    fun g p => PkgI2.galAct G g p
  have ga_mul : ∀ a b p, ga (a * b) p = ga a (ga b p) := fun a b p => galAct_mul' PK.A a b p
  have ga_one : ∀ p, ga 1 p = p := fun p => by
    show PkgI3.AbVar.galHom 1 ≫ p = p
    rw [PkgI3.AbVar.galHom_one]
    exact Category.id_comp _
  have ga_hmul : ∀ g p q, ga g (p * q) = ga g p * ga g q := fun g p q => PkgI2.galAct_mul G g p q
  have ga_pow : ∀ g p (k : ℕ), ga g (p ^ k) = ga g p ^ k := fun g p k => PkgI2.galAct_pow G g p k
  have ga_1 : ∀ g, ga g 1 = 1 := fun g => PkgI2.galAct_one G g
  let T := PkgI2.torsion G (AlgebraicClosure K) 5
  have hmem : ∀ g, ∀ p ∈ T, ga g p ∈ T := by
    intro g p hp
    have hp' : p ^ 5 = 1 := hp
    show (ga g p) ^ 5 = 1
    rw [← ga_pow, hp', ga_1]
  haveI hTfin : Finite T := Finite.of_equiv _ e.symm
  -- the stabilizer `S` of `A[5]`
  let S : Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
    { carrier := {g | ∀ p ∈ T, ga g p = p}
      mul_mem' := fun {a b} ha hb p hp => by
        rw [ga_mul, hb p hp, ha p hp]
      one_mem' := fun p _ => ga_one p
      inv_mem' := fun {a} ha p hp => by
        have h1 := ha (ga a⁻¹ p) (hmem _ p hp)
        rw [← ga_mul, mul_inv_cancel, ga_one] at h1
        exact h1.symm }
  -- `S` is open
  choose U hU using fun x : PK.A.Pt (AlgebraicClosure K) =>
    PkgI3.RhoCont.exists_openSubgroup_galAct_eq PK.A x
  have hSnhds : (S : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) ∈ nhds 1 := by
    have hfinT : (T : Set (PkgI2.Pts G (AlgebraicClosure K))).Finite := Set.toFinite T
    refine Filter.mem_of_superset ((Filter.biInter_mem hfinT).mpr
      (fun x _ => (U x).isOpen.mem_nhds (U x).one_mem)) ?_
    intro g hg x hx
    exact hU x g (Set.mem_iInter₂.mp hg x hx)
  have hSopen : IsOpen (S : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isOpen_of_mem_nhds S hSnhds
  have hSclosed : IsClosed (S : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isClosed_of_isOpen S hSopen
  let K₁ := IntermediateField.fixedField S
  have hfix : K₁.fixingSubgroup = S :=
    InfiniteGalois.fixingSubgroup_fixedField (⟨S, hSclosed⟩ : ClosedSubgroup _)
  have hfd : FiniteDimensional K K₁ := by
    rw [← InfiniteGalois.isOpen_iff_finite]
    show IsOpen (K₁.fixingSubgroup : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
    rw [hfix]; exact hSopen
  -- `G_K / S ↪ Aut(𝔽₅⁴)`
  have hesymm : ∀ v w : (Fin 4 → ZMod 5), (e.symm (v + w)).1 = (e.symm v).1 * (e.symm w).1 := by
    intro v w
    have h5 : (e.symm v).1 * (e.symm w).1 ∈ T := by
      have h1 : (e.symm v).1 ^ 5 = 1 := (e.symm v).2
      have h2 : (e.symm w).1 ^ 5 = 1 := (e.symm w).2
      show (_ * _) ^ 5 = 1
      rw [mul_pow, h1, h2, _root_.one_mul]
    have := he (e.symm v) (e.symm w) h5
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    rw [← this, Equiv.symm_apply_apply]
  let act : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) → (Fin 4 → ZMod 5) → (Fin 4 → ZMod 5) := fun g v =>
    e ⟨ga g (e.symm v).1, hmem g _ (e.symm v).2⟩
  have hact_add : ∀ g v w, act g (v + w) = act g v + act g w := by
    intro g v w
    have h5 : ga g (e.symm v).1 * ga g (e.symm w).1 ∈ T := by
      rw [← ga_hmul, ← hesymm]; exact hmem g _ (e.symm (v + w)).2
    show e ⟨ga g (e.symm (v + w)).1, _⟩ = e ⟨ga g (e.symm v).1, _⟩ + e ⟨ga g (e.symm w).1, _⟩
    rw [← he ⟨ga g (e.symm v).1, hmem g _ (e.symm v).2⟩ ⟨ga g (e.symm w).1, hmem g _ (e.symm w).2⟩ h5]
    congr 2
    rw [hesymm, ga_hmul]
  have hact_mul : ∀ g h v, act (g * h) v = act g (act h v) := by
    intro g h v
    show e ⟨ga (g * h) (e.symm v).1, _⟩ = e ⟨ga g (e.symm (e ⟨ga h (e.symm v).1, _⟩)).1, _⟩
    congr 2
    rw [Equiv.symm_apply_apply, ga_mul]
  have hact_one : ∀ v, act 1 v = v := by
    intro v
    show e ⟨ga 1 (e.symm v).1, _⟩ = v
    rw [show (⟨ga 1 (e.symm v).1, hmem 1 _ (e.symm v).2⟩ : T) = e.symm v from
      Subtype.ext (ga_one _)]
    exact e.apply_symm_apply v
  let F : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) → AddAut (Fin 4 → ZMod 5) := fun g =>
    { toFun := act g
      invFun := act g⁻¹
      left_inv := fun v => by rw [← hact_mul, inv_mul_cancel, hact_one]
      right_inv := fun v => by rw [← hact_mul, mul_inv_cancel, hact_one]
      map_add' := hact_add g }
  let φ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Multiplicative (AddAut (Fin 4 → ZMod 5)) :=
    { toFun := fun g => Multiplicative.ofAdd (F g)
      map_one' := by
        apply congrArg Multiplicative.ofAdd
        exact AddEquiv.ext hact_one
      map_mul' := fun g h => by
        apply congrArg Multiplicative.ofAdd
        exact AddEquiv.ext (hact_mul g h) }
  have hker : φ.ker = S := by
    ext g
    rw [MonoidHom.mem_ker]
    constructor
    · intro hg p hp
      have h3 : act g (e ⟨p, hp⟩) = e ⟨p, hp⟩ :=
        DFunLike.congr_fun (congrArg Multiplicative.toAdd hg) (e ⟨p, hp⟩)
      have h4 : e ⟨ga g p, hmem g p hp⟩ = e ⟨p, hp⟩ := by
        rw [← h3]
        show e ⟨ga g p, _⟩ = e ⟨ga g (e.symm (e ⟨p, hp⟩)).1, _⟩
        congr 2
        rw [Equiv.symm_apply_apply]
      exact congrArg Subtype.val (e.injective h4)
    · intro hg
      apply congrArg Multiplicative.ofAdd
      apply AddEquiv.ext
      intro v
      show e ⟨ga g (e.symm v).1, _⟩ = v
      rw [show (⟨ga g (e.symm v).1, hmem g _ (e.symm v).2⟩ : T) = e.symm v from
        Subtype.ext (hg _ (e.symm v).2)]
      exact e.apply_symm_apply v
  haveI : Finite (Multiplicative (AddAut (Fin 4 → ZMod 5))) :=
    Finite.of_injective (fun f : Multiplicative (AddAut (Fin 4 → ZMod 5)) =>
      ((Multiplicative.toAdd f : AddAut (Fin 4 → ZMod 5)) : (Fin 4 → ZMod 5) → (Fin 4 → ZMod 5)))
      (fun f g h => Multiplicative.toAdd.injective (AddEquiv.ext (congrFun h)))
  have hidx : S.index ≤ ZInQ.heightG0 := by
    rw [← hker, Subgroup.index_ker]
    exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans card_addAut_le
  refine ⟨K₁, hfd, ?_, fun g hg x hx => ?_⟩
  · rw [IntermediateField.finrank_eq_fixingSubgroup_index, hfix]; exact hidx
  · have : g ∈ K₁.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff K₁ g).mpr hg
    rw [hfix] at this
    exact this x hx

/-- **`TateRamAtThreeD` from the leaves R6, T5 and `UpperBreakBound`.** -/
theorem tateRamAtThreeD_of_leaves (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hB : UpperBreakBound) : TateRamAtThreeD :=
  tateRamAtThreeD_of_raynaud (raynaudAtThree_of hRay hB (torsionFieldFive_of hTors))

end TateRam

end UnramTate

end

end LinkedRamMain

end G0A3_z97_linkedram

section G0A3_z98_fold2
/-! ## assemble-port: leaf-fold2's textbook folds and open leaf bundles

Verbatim slices of `scratch/leaf-fold2/parts/b20_fold.lean` (leaf-fold2, 5a41b70a), generated by `mk/mk_z98.py`: the
textbook leaves closed since leaf-fold (imports `ZInQKernel.Contrib.T14.Main`, `ZInQKernel.Contrib.T28.Assemble`,
`ZInQKernel.Contrib.RLeaf.X1ConstantField`), `OpenResearchLeaves2`, `OpenTextbookLeaves2`, `researchLeaves3_of_open2`,
`x1Leaves_of_open2`, `textbookLeaves_of_open2`. leaf-fold2's other proofs (image-plane, infra-stalks, AbVarBC,
unif-dims, conj-twist, inner-twist) are not copied: g0-assemble3's parts b10-f20 fold the same results. -/

noncomputable section

namespace HSyn

open CategoryTheory AlgebraicGeometry G0Split

/-! ### Textbook leaves closed since leaf-fold -/

/-- **T14(a′) proved** (task t1415-tc / `ZInQKernel/Contrib/T14/Main.lean`). -/
theorem t14a_proved : PkgI6.BrauerHasse2C := _root_.ZInQ.Contrib.T14.brauerHasse2C

/-- **T14(b′) proved** (`ZInQKernel/Contrib/T14/Main.lean`). -/
theorem t14b_proved : PkgI6.BrauerReciprocity2C := _root_.ZInQ.Contrib.T14.brauerReciprocity2C

/-- **T28 proved** (`ZInQKernel/Contrib/T28/Assemble.lean`). T28 is not used by the proof (its
field was deleted from `TextbookLeaves`, see `mk_prefix.py`); recorded for completeness. -/
theorem t28_proved : PkgI1.IgusaClebschSeparation :=
  _root_.T28.igusaClebschSeparation_proved

/-- **T36 proved** (`ZInQKernel/Contrib/RLeaf/T36Torsion.lean`). -/
theorem t36_proved : X1Belyi.TorsionStructure := _root_.ZInQ.RLeaf.t36_torsionStructure

/-- **T37 proved** (`ZInQKernel/Contrib/RLeaf/T37GoodReduction.lean`). -/
theorem t37_proved : X1Belyi.GoodReductionUnramified :=
  _root_.ZInQ.RLeaf.T37.t37_goodReductionUnramified

/-- **T39 from T40** (`ZInQKernel/Contrib/RLeaf/X1ConstantField.lean`): a degree-one place of
`K_N` makes `ℚ` algebraically closed in `K_N`. -/
theorem t39_of_t40 (h : X1Belyi.X1RationalCusp) : X1Belyi.X1ConstantField :=
  _root_.ZInQ.RLeaf.x1ConstantField_of_x1RationalCusp h

/-- **The research-level leaves still open** (leaf-fold2). `ResearchLeaves3` (g0-assemble2: no
`opaque` placeholder) with four fields in their published, corrected or concrete form:
* `r1b`: R1(b) concretely, in family form (fibre-qm-period's `R1bFamily`; was `GluePieces3.r1bFamily`
  and, before that, the `opaque` `r1an`);
* `r10`: R10 corrected (`PkgI4.DeRhamComparisonHT`, with the multiplicity-0 clause; g9-derham,
  r10-amend);
* `r14`: R14 corrected (`G0Galois.R14Det`, with the determinant clause; was also
  `GluePieces3.r14Det`);
* `r17`: R17 concretely (`LadicCond.CarayolR17'`, Carayol 1986 Thm (A); was
  `GluePieces3.carayolR17` and, before that, the `opaque` `r17`). -/
structure OpenResearchLeaves2 : Prop where
  r1r2 : LeafAdopt.R1R2fpRep
  /-- R1(b), concrete (family form), for the triple of the leaf bundle. -/
  r1b : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.R1bFamily (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  r1rec : LeafQM.AV.R1rec
  r3 : ZInQ.LeafPush2.R03_LinYang
  r4 : PkgI1.ThetaModularity
  r5 : LeafQM.AV.R5fp
  r5count : LeafQM.AV.R5fpCount
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
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
  r20 : ZInQ.DefFaltings.R20_FaltingsLemma5
  r21 : ZInQ.DefFaltings.R21_Bost
  r22 : ZInQ.LeafPush2.R22_Pazuki
  /-- H5's finiteness half (its `NeronModelMinimal` half is proved, h5-glue). -/
  h5fin : ZInQ.DefFaltings.StableHeightFinite

/-- **The textbook leaves still open** (leaf-fold2): `TextbookLeaves` without the ten fields no
proof uses (deleted, `mk_prefix.py`), without the eight proved fields (`t14a`, `t14b` here;
`t15`, `t16a`, `t17`, `t18`, `t25`, `t31` by leaf-fold), and with `x1` (T36-T40) cut to T38 and
T40 (T36, T37 proved; T39 follows from T40). -/
structure OpenTextbookLeaves2 : Prop where
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : LeafPush.T09_WeilPairing.{0}
  t10 : T10Etale.T10_TateDuality
  t11a : ZInQ.LeafPush2.T11a_RiemannEnd
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomyYu
  t33 : LeafModCurves.JacobianExists ℚ
  t34 : LeafModCurves.DimJ1Genus
  t35 : ZInQ.LeafPush2.UniformizationExists
  /-- T38 (x1-belyi): a function field over `ℚ` with constant field `ℚ` is that of a smooth
  proper curve. -/
  t38 : X1Belyi.CurveOfFunctionFieldQ
  /-- T40 (x1-belyi): `K_N` has a degree-one place. -/
  t40 : X1Belyi.X1RationalCusp
  t41 : ZInQ.H5Neron.NeronModelExists

theorem researchLeaves3_of_open2 (r : OpenResearchLeaves2) : ResearchLeaves3 where
  r1r2 := r.r1r2
  r1rec := r.r1rec
  r3 := r.r3
  r4 := r.r4
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r7a := r.r7a
  r7b := r.r7b
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
  r20 := r.r20
  r21 := r.r21
  r22 := r.r22
  h5fin := r.h5fin

theorem x1Leaves_of_open2 (t : OpenTextbookLeaves2) : X1Belyi.X1Leaves where
  torsion := t36_proved
  goodRed := t37_proved
  curve := t.t38
  constants := t39_of_t40 t.t40
  cusp := t.t40

theorem textbookLeaves_of_open2 (t : OpenTextbookLeaves2) : TextbookLeaves where
  t5 := t.t5
  t6 := t.t6
  t7 := t.t7
  t8 := t.t8
  t9 := t.t9
  t10 := t.t10
  t11a := t.t11a
  t11b := t.t11b
  t14a := t14a_proved
  t14b := t14b_proved
  t15 := t15_proved
  t16a := t16a_proved
  t17 := t17_proved
  t18 := t18_proved
  t23 := t.t23
  t24 := t.t24
  t25 := t25_proved
  t26 := t.t26
  t27 := t.t27
  t31 := t31_proved
  t33 := t.t33
  t34 := t.t34
  t35 := t.t35
  x1 := x1Leaves_of_open2 t
  t41 := t.t41

end HSyn

end

end G0A3_z98_fold2

section G0A3_z99_bundle5
/-! ## assemble-port: `GluePieces5`, `gluePieces_of_gluePieces5`, `sixContactMin_of_leaves5`

Task assemble-port, 2026-11-13. g0-assemble3's `sixContactMin_of_leaves4` (part z95), ported onto leaf-fold2's base
(`scratch/h-decomposition/Leaves.lean` with the ten unused `TextbookLeaves` fields deleted, every part inside `namespace
HDec`; leaf-fold2's bundles `OpenResearchLeaves2`, `OpenTextbookLeaves2`, part z98), with the results proved since
g0-assemble3 folded in: prop-ts-glue's `SpecNonMeeting` (part e10), ts-kummer (e12), hodge-bc2 (b15), leaf-fold2's T35
transport (e40), cpts-transport (e45), lt-goodred (z96), linked-ram (z97). -/

noncomputable section

namespace HSyn

open G0Split

/-- leaf-fold2's research bundle gives g0-assemble3's `ResearchLeaves4`: R14 without its determinant clause
(`eigenformRepExists_of_r14Det`); leaf-fold's `PkgI4.DeRhamComparisonHT` is accepted as r10-amend's
`ZInQ.Contrib.R10.DeRhamComparisonHT` (the same statement, two copies; definitional unfolding). -/
theorem researchLeaves4_of_open2 (r : OpenResearchLeaves2) : ResearchLeaves4 :=
  { r1r2 := r.r1r2, r1rec := r.r1rec, r3 := r.r3, r4 := r.r4, r5 := r.r5, r5count := r.r5count, r6 := r.r6,
    r7a := r.r7a, r7b := r.r7b, r8 := r.r8, r9a := r.r9a, r9b := r.r9b, r10 := r.r10, r11r12 := r.r11r12,
    r13 := r.r13, r14 := eigenformRepExists_of_r14Det r.r14, r15 := r.r15, r16 := r.r16, r18 := r.r18,
    r19 := r.r19, r20 := r.r20, r21 := r.r21, r22 := r.r22, h5fin := r.h5fin }

/-- **The named Props left after assemble-port** (27 fields). g0-assemble3's `GluePieces4` (46 fields) without the 29
fields proved or moved since (table: docs/research/assemble-port.md §2); `LinkedTateData` now comes from lt-local's proof of
g0-assemble2's `LinkedTateLocal` (part z93z; `UnramRoots` proved by frob-contrib, part z94b; `TateBridge35` from
frob-pieces' leaves), so linked-tate's `linkedFrob`, `kernelFieldBreaks`, `tateRamAtThree` (the last likely false as
stated, linked-ram F1) are not needed;
period-glue's leaves `gammaStarGen` (LEAF?) and `t11aRiemannHom` (LEAF), which replace `s8WeightExact` and
`qmTwistLattice`, ts-hecke's `y3Connected` (LEAF) and hecke-rest's `qmAutCard`, `serreRigidity3`, `alFixedPoints` (leaves) and
`heckeVertWitness` (GLUE), which replace the five Hecke Props (`heckeDegree` proved from T5, the curve charts proved), and
linked-frob's and spread-out's three EGA IV leaves, `properSmoothGenConnected` (LEAF?), T4, T3 (LEAF), which replace
`linkedFrob`. -/
structure GluePieces5 : Prop where
  -- FibreSimple: FS5 (NoCM on the fibre)
  /-- fs5-nocm, LEAF (N1b′: CM points via optimal embeddings; Shimura 1967, Jordan, González–Rotger). -/
  cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding
  /-- x6-kummer, LEAF (N2-L′: `X₆` is the conic `Y² + 3X² + 3Z² = 0` with `π₆ = −16(X² + Z²)/(27Z²)` on
  `ℚ̄`-points of one witness of the leaf bundle; Elkies 1998 §3, Kurihara 1979; a consequence of the published model,
  x6-kummer §3.6). fs5-nocm's glue N2 `X6KummerFibre` is proved from it and `MobiusGlue`. -/
  x6ConicModel : X6Kummer.X6ConicModel
  -- ProductModelHeight (unif-dims, product-unif, infra-smooth-dim)
  -- StableHeightBaseChange (height-bc; infra-stalks proved the other two)
  -- ThetaPoint (g0-thetapoint, fibre-qm-period, period-map)
  /-- g0-thetapoint, LEAF? (theta-constant ratios at a period matrix are algebraic; Shimura 1976). -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- pkg-I1 (via fibre-qm-period), LEAF? (the theta-quotient Hauptmodul of `Γ*`). -/
  qmHauptmodul : PkgI1.QMHauptmodul
  /-- fibre-qm-period, LEAF (Eichler class number one for `𝒪`, lattice form). -/
  qmClassNumberOne : G0Split.FibreQM.QMClassNumberOne
  /-- period-map, GLUE (`π` is invariant under the QM twist, complex form), for the leaf's own triple. -/
  piTwistC : ∀ h : LeafAdopt.R1R2fpRep,
    G0Split.FibreQM.PeriodMapH.PiTwistC (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h))
  /-- period-map, LEAF? (CM points descend; Shimura's theory of CM). -/
  cmDescends : G0Split.FibreQM.PeriodMapH.CMDescends
  /-- period-map, GLUE (textbook complex analysis: a holomorphic map of the sphere factoring affinely). -/
  sphereFactorAffine : G0Split.FibreQM.PeriodMap.SphereFactorAffine
  /-- period-map, LEAF (the valence formula for `Γ*`). -/
  valenceBoundGammaStar : G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar
  -- ModularConstituent: G2 (fibre-cover; Prop. TS by prop-ts, prop-ts-glue)
  -- ModularConstituent: G4 (kernel-field, kf-glue)
  -- ModularConstituent: G8-G12
  /-- g12-det, LEAF (HT weights of a twist shift by a constant; Sen 1980). -/
  senTwist : G0Galois.SenTwist
  /-- g12-det, LEAF (finite image ⇒ HT with weights 0; Tate 1967; Ax–Sen–Tate). -/
  finiteImageHT : G0Galois.FiniteImageHT
  /-- weil-pairing (used by g12-det), LEAF (T9 restated; Mumford §§6, 8, 20, 23). -/
  t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists
  /-- weil-pairing, LEAF (Mumford §7-8). -/
  isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse
  /-- weil-pairing, LEAF (Mumford §4 Appl. 2). -/
  divisiblePoints : WeilPairing.DivisiblePoints
  -- ModularConstituent: G13-G16
  -- ModularConstituent: joint glue on G7's data (linked-tate)
  /-- period-glue, LEAF? (`Γ*/ℚ^×` is the `(2,4,6)` triangle group generated by `ι(1+i+j)`, `ι((j−3)/2)`: Takeuchi 1977,
  Elkies 1998 §3, Poincaré's polygon theorem; with R4 it gives period-map's `S8WeightExact`, `s8WeightExact_of`). -/
  gammaStarGen : G0Split.FibreQM.PeriodGlue.GammaStarGen
  /-- ts-hecke, LEAF (R1conn: the canonical model `Y₃` is connected over `ℚ`, witness form; Shimura, Deligne (Bourbaki 389,
  PSPM 33 §2), Milne §5, §13 for `π₀(Sh_K)` with its Galois action; the two geometric components computed in
  `scratch/ts-hecke/pi0_check.py`). Gives prop-ts-glue's `HeckeIrreducible` (`heckeIrreducible_of_connected`). -/
  y3Connected : TSHecke.Y3Connected
  /-- hecke-rest, LEAF? (Shimura's classification of `com(ι)` for QM abelian surfaces, with the unit counts of
  `ℤ[i]`, `ℤ[ζ₃]`: `|Aut(A, ι)| = 4, 6, 2` by CM type; Shimura 1963, Rotger 2003 §2). -/
  qmAutCard : HeckeRest.QMAutCard
  /-- hecke-rest, LEAF (Serre's lemma at level 3: a finite-order endomorphism fixing `A[3]` is the identity; Serre 1960/61,
  Silverberg–Zarhin 1996). -/
  serreRigidity3 : HeckeRest.SerreRigidity3
  /-- hecke-rest, LEAF? (fixed points of `w₂, w₃, w₆` on `X₆` are CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`: Rotger 2004, Ogg 1983,
  with the embedding check of `scratch/hecke-rest/fibre_sizes.py`). With T5 and the two above it gives ts-hecke's
  `HeckeFibreSizes` (`heckeFibreSizes_of`). -/
  alFixedPoints : HeckeRest.ALFixedPoints
  /-- hecke-rest, GLUE (one unramified vertical prime of the Hecke cover at every `p > 324`: Lemma NV of h-b1 §3, or good
  reduction of `Y₃`, Morita 1981, Carayol 1986; equivalent in content to `HeckeNoVertRam`, which it gives,
  `heckeNoVertRam_of_witness`). -/
  heckeVertWitness : HeckeRestNV.HeckeVertWitness
  /-- spread-out, LEAF (EGA IV₃ 8.8.2 (ii): descent of schemes of finite presentation along a cofiltered limit with affine
  transition maps; Stacks 01ZM; locators UNVERIFIED). With the next two it gives neron-lg's N1-g1 `AbVarSpreadsOut`
  (`abVarSpreadsOut_of_ega`, part z94), which with the following fields gives `LinkedFrob`
  (`LinkedFrobRed.linkedFrob_of_neron_nmp`). -/
  egaIV_8_8_2_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii
  /-- spread-out, LEAF (EGA IV₃ 8.10.5 (xii): descent of properness; Stacks 081F; UNVERIFIED). -/
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  /-- spread-out, LEAF (EGA IV₄ 17.7.8 (ii): descent of smoothness; Stacks 07RP; UNVERIFIED). -/
  egaIV_17_7_8_ii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii
  /-- frob-pieces, LEAF? (Zariski's connectedness theorem in the form used: a smooth proper `𝓞_L[1/f]`-scheme with
  geometrically connected generic fibre is geometrically connected; EGA III₁ 4.3). -/
  properSmoothGenConnected : FrobPiecesNeron.ProperSmoothGenConnected
  /-- textbook LEAF I2-Red (T4; `TextbookLeaves.t4`, deleted by leaf-fold2 as unused and used again here): reduction is
  bijective on prime-to-`p` torsion at good reduction. -/
  reductionTorsionBijective : PkgI2.ReductionTorsionBijective.{0}
  /-- textbook LEAF I2-NMP (T3; `TextbookLeaves.t3`, likewise): the Néron mapping property of abelian schemes. -/
  neronMappingAbelianScheme : PkgI2.NeronMappingAbelianScheme.{0}
  /-- hom-unify, LEAF (the analytic representation of homomorphisms, both directions: every homomorphism lifts to a
  `ℂ`-linear map of uniformizations, and over `ℂ` every lattice-preserving `ℂ`-linear map is induced by a unique
  homomorphism; Birkenhake–Lange §1.2, Prop. 1.2.1; Mumford §1, §3; GAGA). It replaces three leaves: T11(a)
  (`OpenTextbookLeaves2.t11a`, `t11a_riemannEnd_of_corr`), conj-twist's `HomLinearLift` (`homLinearLift_of_corr`) and
  period-glue's `T11aRiemannHom` (`t11aRiemannHom_of_corr`). -/
  homLatticeCorr : HomUnify.HomLatticeCorr

/-- **`GluePieces` from `GluePieces5` and leaf-fold2's open leaf bundles.** g0-assemble3's `gluePieces_of_gluePieces4`
(part z95), with every field proved since replaced by its proof: `analyticUniformizationOfDim` by T35's transport,
`hodgeBCInjective`, `omegaBaseChange` (hodge-bc2), `baseChangeClassUnique`, `cPtsTransport` (cpts-transport),
`SpecNonMeeting` and six Kummer pieces inside `propTSAll_final''` (prop-ts-glue, ts-kummer), `goodRedTorsion`,
`qmEndRank` (lt-goodred), `KernelFieldBreaks` (linked-ram, from `upperBreakBound`, `betaTrivialAtTwo`), `twistDescent` (twist-descent), `s8Nonzero`
(period-glue), `s8WeightExact`, `qmTwistLattice` (period-glue, from `gammaStarGen`, `t11aRiemannHom` and the proved
Skolem–Noether), linked-tate's
`LinkedRam` through linked-ram's `linkedRam_of'` with the corrected `tateRamAtThreeD`; `r1bFamily`, `r14Det`, `carayolR17` are the fields `r1b`, `r14`, `r17` of
`OpenResearchLeaves2`. -/
theorem gluePieces_of_gluePieces5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5) :
    GluePieces :=
  let r4 := researchLeaves4_of_open2 r
  let t3 := textbookLeaves_of_open2 t
  have hMob : LeafQM.AV.Pin.MobiusGlue := mobiusGlue_of_t5' t3
  have hFS5 : G0FibreSimple.FibreComTrivial :=
    fibreComTrivial_of_full (FS5NoCM.fibreComTrivialFull_of_leaves'' (r1r2fpFull_of r4.toR3)
      hMob t.t27 t.t6 gp.cmOptimalEmbedding
      (X6Kummer.x6KummerFibre_of_conic hMob gp.x6ConicModel) r.r5count)
  have hFS : G0Split.FibreSimple :=
    G0FibreSimple.fibreSimple_of_leaves t3 MulRigidity.mulIsogeny G0FibreSimple.rigidityHom
      ⟨G0FibreSimple.finiteDescends_proof, hFS5⟩
  have hG3 : LinkedTate.QMModelG3 :=
    LinkedTate.qmModelG3_of r.r7a r.r6 t.t5 (LinkedTate.goodRedG3Bridge_of_torsion LTGoodRed.goodRedTorsion)
  have hTS : G0ModField.PropTSAll :=
    PropTSGlue.propTSAll_final'' t2_proved (LeafAdopt.R1R2fp_of_rep r.r1r2) hMob KummerComp.kummerCompositum_final
      TsKummer.kummerAbhyankarFinGlue TsKummer.kummerOtherBranchFin TsKummer.kummerVerticalFin
      TsKummer.kummerAbhyankarInfGlue TsKummer.kummerOtherBranchInf TsKummer.kummerVerticalInf
      (TSHecke.heckeIrreducible_of_connected gp.y3Connected)
      (TSHecke.heckeNormalizationIrr_of HeckeRestAll.curveGaloisChart t.t5)
      (TSHecke.heckeDegree_of_torsion t.t5)
      (TSHecke.heckeBranch_of' (LeafAdopt.R1R2fp_of_rep r.r1r2) HeckeRestCurve.curveChartInf
        (HeckeRest.heckeFibreSizes_of' t.t5 gp.qmAutCard gp.serreRigidity3 gp.alFixedPoints) t.t5)
      (HeckeRestNV.heckeNoVertRam_of_witness gp.heckeVertWitness)
  have hPM : G0Split.FibreQM.PeriodMapGlue (G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep r.r1r2))
      (G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep r.r1r2))
      (G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep r.r1r2)) :=
    G0Split.FibreQM.PeriodMapH.periodMapGlue_own _ G0Split.FibreQM.PeriodMapH.baseChangeClassUnique_proof
      (gp.piTwistC r.r1r2) (G0Split.FibreQM.PeriodGlue.qmTwistLattice_of' (HomUnify.t11aRiemannHom_of_corr gp.homLatticeCorr) TSkolemKW.glueDescent_leafSkolemNoether)
      (G0Split.FibreQM.PeriodMapH.piCMC_of _ _ _ (G0Split.FibreQM.own_spec _).1
        (G0Split.FibreQM.own_spec _).2.2 G0Split.FibreQM.PeriodMapH.baseChangeClassUnique_proof
        (gp.piTwistC r.r1r2) gp.cmDescends)
      (G0Split.FibreQM.PeriodMapH.cmFixedHasCM_of t.t11a)
  { dimFinite := G0Split.dimFinite
    dimBaseChange := G0Split.dimBaseChange
    fibreSimple := hFS
    productModelHeight := ZInQ.UnifDims.productModelHeight_of_unifOfDim
      (ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists t.t35)
    stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine
      (ZInQ.HeightBC.g0_hodgeLine_iff.mpr (ZInQ.HeightBC.hodgeLineBaseChange_of_two
        ZInQ.HeightBC.hodgeBCInjective ZInQ.HeightBC.omegaBaseChange))
    productExists := G0Product.productExists
    reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves3 r4.toR3 G0Split.dimFinite
    thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios
      (G0Split.FibreQM.fibreQMPeriod_main_rep r.r1r2 hMob gp.qmHauptmodul
        t.t35 t.t11a gp.qmClassNumberOne (r.r1b r.r1r2) hPM
        (G0Split.FibreQM.PeriodMap.hauptmodulUnique_of' G0Split.FibreQM.PeriodGlue.s8Nonzero_proof gp.sphereFactorAffine)
        (G0Split.FibreQM.PeriodMap.qmDenZeroCM3_of'' G0Split.FibreQM.PeriodGlue.s8Nonzero_proof (G0Split.FibreQM.PeriodGlue.s8WeightExact_of r.r4 gp.gammaStarGen)
          gp.valenceBoundGammaStar)
        G0Split.FibreQM.cPtsTransport_proof)
      gp.thetaRatiosAlgebraic
    modularConstituent := modularConstituent_of_field t3
      (G0ModField.fibreCoverExists_of_propTSAll' t.t5 hTS G0ModField.unramifiedConjugates)
      (G0ModField.KernelField.kernelFieldExists_of_descent t.t6 r.r7a r.r6 t.t5 t.t27
        hFS5 MulRigidity.mulIsogeny G0ModField.KernelField.twistDescent)
      UnramTate.unramifiedSup_mf
      (G0AssembleMod.afterG7_of3 r4.toR3 t3
        ⟨RvGP2.burnsideAbsIrred, r.r14,
          ZInQ.Contrib.R10.g9Glue_of_deRhamComparisonHT r4.r10,
          G0Galois.g10Glue_of_conjTwist
            (G0Galois.conjTwistNontrivial_of_leaves t.t5 t.t26 t.t35 (HomUnify.homLinearLift_of_corr gp.homLatticeCorr)),
          G0Galois.g12Weight_of_senTwist gp.senTwist gp.finiteImageHT,
          G0Galois.detTate_of_leaves gp.t09SymmIsogenyExists gp.isogenyQuasiInverse
            gp.divisiblePoints t.t26,
          G0AssembleMod.resQFiniteIndex⟩
        (G0ModNewform.dirichletOfFinite_of_t17 t17_proved) r.r17
        Swan.swanIndependent_proved Swan.swanIntegral_proved
        Swan.adaptedExists_proved
        (LinkedTate.modelG3G6_of hFS hG3)
        (G0AssembleMod.linkedTateData_of_local t.t7
          (LTLocal.linkedTateLocal_of_tateBridge35 r.r6 t.t5 (unramRoots_proved 2 5) (unramRoots_proved 2 3)
            (FrobPiecesGood.tateBridge35_of_neron_nmp t.t26
              (abVarSpreadsOut_of_ega gp.egaIV_8_8_2_ii gp.egaIV_8_10_5_xii gp.egaIV_17_7_8_ii)
              gp.properSmoothGenConnected gp.reductionTorsionBijective gp.neronMappingAbelianScheme)
            hFS (LTGoodRed.QM.qmEndRank_of_leaves t.t6 t.t27))))
    heightCopies := G0HeightCopies.heightCopiesAgree }

/-- **The open textbook leaves after assemble-port** (17 fields): leaf-fold2's `OpenTextbookLeaves2` without `t11a`
(T11(a), implied by hom-unify's leaf `HomLatticeCorr`, a field of `GluePieces5`). -/
structure OpenTextbookLeaves5 : Prop where
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : LeafPush.T09_WeilPairing.{0}
  t10 : T10Etale.T10_TateDuality
  t11b : ZInQ.LeafPush2.T11b_Rigidity
  t23 : ∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p
  t24 : EigenformTwist
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomyYu
  t33 : LeafModCurves.JacobianExists ℚ
  t34 : LeafModCurves.DimJ1Genus
  t35 : ZInQ.LeafPush2.UniformizationExists
  /-- T38 (x1-belyi): a function field over `ℚ` with constant field `ℚ` is that of a smooth
  proper curve. -/
  t38 : X1Belyi.CurveOfFunctionFieldQ
  /-- T40 (x1-belyi): `K_N` has a degree-one place. -/
  t40 : X1Belyi.X1RationalCusp
  t41 : ZInQ.H5Neron.NeronModelExists

/-- `OpenTextbookLeaves2` from `OpenTextbookLeaves5` and `HomLatticeCorr`. -/
theorem openTextbookLeaves2_of_5 (t : OpenTextbookLeaves5) (h : HomUnify.HomLatticeCorr) : OpenTextbookLeaves2 :=
  { t5 := t.t5,
    t6 := t.t6,
    t7 := t.t7,
    t8 := t.t8,
    t9 := t.t9,
    t10 := t.t10,
    t11a := HomUnify.t11a_riemannEnd_of_corr h,
    t11b := t.t11b,
    t23 := t.t23,
    t24 := t.t24,
    t26 := t.t26,
    t27 := t.t27,
    t33 := t.t33,
    t34 := t.t34,
    t35 := t.t35,
    t38 := t.t38,
    t40 := t.t40,
    t41 := t.t41 }

/-- **G0 after assemble-port** (no `sorry`, standard axioms): leaf-fold2's open research leaves (`OpenResearchLeaves2`,
26 fields), the open textbook leaves (`OpenTextbookLeaves5`, 17 fields) and `GluePieces5` (27 fields: 17 LEAF, 7 LEAF?,
3 GLUE; table in docs/research/assemble-port.md §2) imply `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves5) (gp : GluePieces5) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leavesR3 (researchLeaves4_of_open2 r).toR3
    (textbookLeaves_of_open2 (openTextbookLeaves2_of_5 t gp.homLatticeCorr))
    (gluePieces_of_gluePieces5 r (openTextbookLeaves2_of_5 t gp.homLatticeCorr) gp)

end HSyn

end

#print axioms HSyn.researchLeaves4_of_open2
#print axioms HSyn.gluePieces_of_gluePieces5
#print axioms HSyn.sixContactMin_of_leaves5
#print axioms HSyn.textbookLeaves_of_open2
#print axioms HSyn.openTextbookLeaves2_of_5
#print axioms HSyn.t14a_proved
#print axioms HSyn.t14b_proved
#print axioms HSyn.t36_proved
#print axioms HSyn.t37_proved
#print axioms HSyn.t39_of_t40
#print axioms PropTSGlue.specNonMeeting
#print axioms PropTSGlue.propTSAll_final''
#print axioms ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists
#print axioms ZInQ.HeightBC.hodgeBCInjective
#print axioms ZInQ.HeightBC.omegaBaseChange
#print axioms HSyn.G0Split.FibreQM.cPtsTransport_proof
#print axioms HSyn.G0Split.FibreQM.PeriodMapH.baseChangeClassUnique_proof
#print axioms TsKummer.kummerAbhyankarFinGlue
#print axioms TsKummer.kummerOtherBranchFin
#print axioms TsKummer.kummerVerticalFin
#print axioms TsKummer.kummerAbhyankarInfGlue
#print axioms TsKummer.kummerOtherBranchInf
#print axioms TsKummer.kummerVerticalInf
#print axioms LTGoodRed.goodRedTorsion
#print axioms LTGoodRed.QM.qmEndRank_of_leaves
#print axioms UnramTate.kernelFieldBreaks_of'
#print axioms UnramTate.linkedRam_of'
#print axioms UnramTate.kernelFieldBreaksHigh
#print axioms UnramTate.betaTrivialAtTwo_of_sign
#print axioms UnramTate.tateRamAtThreeD_of_leaves
#print axioms G0ModField.KernelField.twistDescent
#print axioms KummerComp.kummerCompositum_final
#print axioms LTLocal.linkedTateLocal_of_tateBridge35
#print axioms FrobPiecesGood.tateBridge35_of_neron_nmp
#print axioms HSyn.unramRoots_proved
#print axioms LinkedFrobRed.linkedFrob_of_neron_nmp
#print axioms HSyn.abVarSpreadsOut_of_ega
#print axioms TSHecke.heckeIrreducible_of_connected
#print axioms HeckeRestAll.curveGaloisChart
#print axioms HeckeRestCurve.curveChartInf
#print axioms HeckeRest.heckeFibreSizes_of
#print axioms HeckeRestNV.heckeNoVertRam_of_witness
#print axioms TSHecke.heckeNormalizationIrr_of
#print axioms TSHecke.heckeDegree_of_torsion
#print axioms TSHecke.heckeBranch_of'
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.s8Nonzero_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.s8WeightExact_of
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.qmTwistLattice_of'
#print axioms UnramTate.upperAbsWild

end G0A3_z99_bundle5

end HDec

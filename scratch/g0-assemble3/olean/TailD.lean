import TailF

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
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

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
  /-- fs5-nocm, GLUE (N2: the Kummer fibre of `X₆ → P¹` over `t(u)`). -/
  x6KummerFibre : FS5NoCM.X6KummerFibre
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
  /-- fibre-cover, GLUE (a compositum of conjugates of a field unramified at `p` is unramified at `p`). -/
  unramifiedConjugates : G0ModField.UnramifiedConjugates
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
    (mobiusGlue_of_t5' t) t.t27 t.t6 gp.cmOptimalEmbedding gp.x6KummerFibre r.r5count)

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
  PropTSGlue.propTSAll_of_pieces'' t.t2 (LeafAdopt.R1R2fp_of_rep r.r1r2) (mobiusGlue_of_t5' t)
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
      gp.unramifiedConjugates)
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


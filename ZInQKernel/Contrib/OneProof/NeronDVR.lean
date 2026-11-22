import ZInQKernel.Contrib.OneProof.BLRLocalizes

/-! # neron-dvr: Néron models over the discrete valuation rings of a number field

Task neron-dvr (docs/research/neron-dvr.md; gap-triage A8).

The research field `neronSchemeModelExistsDVR` (`ReductSplit.NeronSchemeModelExistsDVR`, TailZ7 L238; BLR §1.4
Thm. 3 over an arbitrary discrete valuation ring) is proved here **for `K` a number field**
(`GapNeron.NeronSchemeModelExistsDVRNF`, the field with `[NumberField K]` added) from the textbook field
`neronSchemeExtensionExists` (N1, `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists`: BLR §1.4 Thm. 3 over the
Dedekind ring `𝓞_L`) alone. BLR §1.2 Prop. 4 is not a hypothesis: gt-blr proved it
(`GapBLR.neronLocalizesDVR_proved : ReductGlue.NeronLocalizesDVR`, no hypotheses).

Proof: N1 at `L = K` gives a Néron group model `𝒩` of `A_K` over `𝓞_K` (neron-c's
`neronModelExists_of_extension`); `GapBLR.neronLocalizesDVR_proved` makes `𝒩 ×_{𝓞_K} O`
(`ReductGlue.toO 𝒩 O`) a Néron model over `O`; compose its generic-fibre identification with `A_K ≅ A`
(`bcSelfIso`, base change along `id : K → K`).

The consumers of the field are restated over number fields where the chain uses them only there:
* SS1 and SS3 (`ss1_ss3_of14`, TailZ23 L763, through `ReductB.ss1_ss3_of_cp`): `ss1_ss3_of_cpNF` etc.;
  these use the field only through `hasSemistableReduction_of`, at number fields.
* r6 (`raynaudCriterion_leaves`, TailZ14 L243) and r8 (`grothendieckMonodromy_final'`, TailZ7 L1496) conclude
  `PkgI2.RaynaudCriterion` and `PkgI2.GrothendieckMonodromy`, which quantify over every field. From the
  number-field form of the Néron field they give only the number-field restrictions `RaynaudCriterionNF`,
  `GrothendieckMonodromyNF` (`raynaudCriterion_leavesNF`, `grothendieckMonodromy_final'NF`). Whether the chain
  can consume these is recorded in the report (§ fold).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety Pts torsion galAct IsInertia UnipSq HasGoodReduction)

namespace GapNeron

open ReductSplit

/-! ## §1 The statement and its implication from the field -/

/-- **`NeronSchemeModelExistsDVR` at number fields**: the research field `ReductSplit.NeronSchemeModelExistsDVR`
(TailZ7 L238, copied verbatim) with `[NumberField K]` added. BLR §1.4 Thm. 3 with §1.2 Def. 1 for an abelian
variety over a number field `K` and a discrete valuation ring `O` of `K`. -/
def NeronSchemeModelExistsDVRNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K),
    ∃ (N : Over (Spec (CommRingCat.of O))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (e : (Over.pullback (jO O)).obj N ≅ A.X),
      ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
        Function.Bijective fun f : Y ⟶ N => (Over.pullback (jO O)).map f ≫ e.hom

/-- The restriction is implied by the field. -/
theorem neronSchemeModelExistsDVRNF_of_field (h : ReductSplit.NeronSchemeModelExistsDVR) :
    NeronSchemeModelExistsDVRNF :=
  fun K _ _ O _ A => h K O A

/-! ## §2 The proof from N1 -/

/-- `A_K ≅ A` for the base change along `id : K → K`. (Irreducible: unfolding the `eqToIso` makes the kernel
time out in `neronSchemeModelExistsNF`.) -/
noncomputable irreducible_def bcSelfIso {K : Type} [Field K] (A : PkgI3.AbVar K) :
    (A.baseChange K).X ≅ A.X :=
  eqToIso (by
    show (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K K)))).obj A.X =
      (Over.pullback (𝟙 _)).obj A.X
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]) ≪≫ Over.pullbackId.app A.X

/-- Postcomposition with an isomorphism does not change bijectivity (any domain). -/
theorem bijective_comp_iso' {α : Type*} {C : Type*} [Category C] {Z W W' : C} (F : α → (Z ⟶ W))
    (e : W ≅ W') : Function.Bijective (fun f => F f ≫ e.hom) ↔ Function.Bijective F := by
  have : (fun f => F f ≫ e.hom) = (fun g : Z ⟶ W => g ≫ e.hom) ∘ F := rfl
  rw [this]
  have hb : Function.Bijective (fun g : Z ⟶ W => g ≫ e.hom) :=
    ⟨fun g₁ g₂ h => by simpa using congrArg (· ≫ e.inv) h,
      fun g => ⟨g ≫ e.inv, by simp⟩⟩
  exact ⟨fun h => (Function.Bijective.of_comp_iff' hb F).mp h, fun h => hb.comp h⟩

theorem bijective_trans {K : Type} [Field K] (O : ValuationSubring K) {B B' : PkgI3.AbVar K}
    (G : Over (Spec (CommRingCat.of O))) (g : (Over.pullback (jO O)).obj G ≅ B.X) (e : B.X ≅ B'.X)
    (Y : Over (Spec (CommRingCat.of O)))
    (hb : Function.Bijective fun f : Y ⟶ G => (Over.pullback (jO O)).map f ≫ g.hom) :
    Function.Bijective fun f : Y ⟶ G => (Over.pullback (jO O)).map f ≫ (g ≪≫ e).hom := by
  have h2 := (bijective_comp_iso' _ e).mpr hb
  simpa only [Iso.trans_hom, Category.assoc] using h2

/-- **Néron models over the discrete valuation rings of a number field, from N1** (BLR §1.4 Thm. 3 over `𝓞_K`;
BLR §1.2 Prop. 4 is gt-blr's theorem `GapBLR.neronLocalizesDVR_proved`). -/
theorem neronSchemeModelExistsNF (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists) :
    NeronSchemeModelExistsDVRNF := by
  intro K _ _ O _ A
  obtain ⟨𝒩, h𝒩⟩ := ZInQ.Contrib.NeronC.neronModelExists_of_extension hN1 K A K
  have h := GapBLR.neronLocalizesDVR_proved K A K 𝒩 h𝒩 O
  exact ⟨(ReductGlue.toO 𝒩 O).G, inferInstance, inferInstance, inferInstance,
    (ReductGlue.toO 𝒩 O).gen ≪≫ bcSelfIso A,
    fun Y _ => bijective_trans O (ReductGlue.toO 𝒩 O).G _ (bcSelfIso A) Y (h Y)⟩

/-- The same with BLR §1.2 Prop. 4 as a hypothesis (the signature of gap-triage A8; `hB` is not needed). -/
theorem neronSchemeModelExistsNF' (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists)
    (_hB : CToPrinted.BLR_1_2_4) : NeronSchemeModelExistsDVRNF :=
  neronSchemeModelExistsNF hN1

/-! ## §3 Common lemmas at number fields (TailZ7 §4, `hN` retyped) -/

section Common

variable {K : Type} [Field K] [NumberField K]

/-- `ReductSplit.exists_neron_groupModel` (TailZ7 L315) with `hN` at number fields (proof unchanged). -/
theorem exists_neron_groupModelNF (hN : NeronSchemeModelExistsDVRNF) (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (A : PkgI3.AbVar K) :
    ∃ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel := by
  obtain ⟨N, hS, hSep, hQC, e, hN⟩ := hN K O A
  let F := Over.pullback (jO O)
  let P : Over (Spec (CommRingCat.of O)) → Prop := fun Y => Smooth Y.hom
  have hP1 : P (𝟙_ _) := ZInQ.Contrib.NeronC.smooth_tensorUnit _
  have hP2 : ∀ X Y, P X → P Y → P (X ⊗ Y) := fun X Y hX hY =>
    ZInQ.Contrib.NeronC.smooth_tensor X Y hX hY
  have hB : ∀ Y, P Y → Function.Bijective fun f : Y ⟶ N => F.map f ≫ e.hom :=
    fun Y hY => @hN Y hY
  letI : GrpObj N := ZInQ.Contrib.NeronC.grpObjOfNeron F P hP1 hP2 N hS _ e hB
  let 𝒩 : GroupModelO A O :=
    { G := N
      gen := e
      gen_hom := ZInQ.Contrib.NeronC.isMonHom_of_neron F P hP1 hP2 N hS _ e hB }
  exact ⟨𝒩, fun Y _ => hN Y⟩

/-- `ReductSplit.hasSemistableReduction_of` (TailZ7 L333) with `hN` at number fields. -/
theorem hasSemistableReduction_ofNF (hN : NeronSchemeModelExistsDVRNF) (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (A : PkgI3.AbVar K) (h : SemistableNeronModels A O) :
    HasSemistableReduction A O := by
  obtain ⟨𝒩, h𝒩⟩ := exists_neron_groupModelNF hN O A
  exact ⟨𝒩, h𝒩, h 𝒩 h𝒩⟩

end Common

/-! ## §4 SS1 and SS3 (TailZ23 `ReductB`, `hN` retyped; proofs unchanged) -/

section SS

open ReductGlue ReductB ZInQ.Contrib.AbVarBC

/-- `ReductB.semistablePersists_of_leaves_nf` (TailZ23 L441) with `hN` at number fields. -/
theorem semistablePersists_of_leaves_nfNF (h33 : SemistablePersistsDVRnf)
    (hN : NeronSchemeModelExistsDVRNF) (hLG : SemistableLocalGlobal) (hDown : DVRComapFinite) :
    ZInQ.HeightSplit.SemistablePersists := by
  intro K _ _ A L _ _ _ 𝒩 h𝒩 hss L' _ _ _ _ _ 𝒩' h𝒩'
  rw [hLG K A L 𝒩 h𝒩] at hss
  rw [hLG K A L' 𝒩' h𝒩']
  intro O' hO'
  haveI := hO'
  haveI : IsDiscreteValuationRing (O'.comap (algebraMap L L')) := hDown L L' O' hO'
  haveI : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite ℚ L L'
  have h1 := h33 L (O'.comap (algebraMap L L')) L' O' rfl (A.baseChange L)
    (hss _ inferInstance)
  exact hasSemistableReduction_ofNF hN O' _
    (semistableNeronModels_transport (bcbcIso A L L') (bcbcIso_isMonHom A L L') h1)

/-- `ReductB.semistableReductionThm_of_leaves_nf` (TailZ23 L509) with `hN` at number fields. -/
theorem semistableReductionThm_of_leaves_nfNF (h36 : SemistableReductionDVRnf)
    (h33 : SemistablePersistsDVRnf) (hN : NeronSchemeModelExistsDVRNF) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) (hDown : DVRComapFinite) :
    ZInQ.HeightSplit.SemistableReductionThm := by
  classical
  intro K _ _ A
  set S := {O : ValuationSubring K | IsDiscreteValuationRing O ∧ ¬ HasSemistableReduction A O}
  have hS : S.Finite := hAA K A
  have hch : ∀ O : ValuationSubring K, ∃ K' : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K K' ∧ (IsDiscreteValuationRing O →
        ∀ O' : ValuationSubring K', IsDiscreteValuationRing O' →
          O'.comap (algebraMap K K') = O → SemistableNeronModels (A.baseChange K') O') := by
    intro O
    by_cases hO : IsDiscreteValuationRing O
    · obtain ⟨K', h1, h2⟩ := h36 K O A
      exact ⟨K', h1, fun _ => h2⟩
    · exact ⟨⊥, inferInstance, fun h => absurd h hO⟩
  choose F hFfin hF using hch
  let L₀ : IntermediateField K (AlgebraicClosure K) := ⨆ O ∈ hS.toFinset, F O
  haveI : FiniteDimensional K L₀ :=
    IntermediateField.finiteDimensional_iSup_of_finset' (fun O _ => hFfin O)
  haveI : NumberField L₀ := NumberField.of_module_finite K L₀
  refine ⟨L₀, inferInstance, inferInstance, inferInstance, fun 𝒩 h𝒩 => ?_⟩
  rw [hLG K A L₀ 𝒩 h𝒩]
  intro O'' hO''
  haveI := hO''
  haveI hO : IsDiscreteValuationRing (O''.comap (algebraMap K L₀)) := hDown K L₀ O'' hO''
  by_cases hOS : O''.comap (algebraMap K L₀) ∈ S
  · -- a place of bad reduction: go through `F O ≤ L₀`
    set O := O''.comap (algebraMap K L₀) with hOdef
    have hle : F O ≤ L₀ := le_iSup₂ (f := fun O _ => F O) O (hS.mem_toFinset.mpr hOS)
    letI : Algebra (F O) L₀ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    haveI : IsScalarTower K (F O) L₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : FiniteDimensional (F O) L₀ := by
      haveI := hFfin O
      exact FiniteDimensional.right K (F O) L₀
    haveI : NumberField (F O) := by
      haveI := hFfin O
      exact NumberField.of_module_finite K (F O)
    haveI hOi : IsDiscreteValuationRing (O''.comap (algebraMap (F O) L₀)) :=
      hDown (F O) L₀ O'' hO''
    have hc : (O''.comap (algebraMap (F O) L₀)).comap (algebraMap K (F O)) = O := by
      rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq]
    have h1 : SemistableNeronModels (A.baseChange (F O)) (O''.comap (algebraMap (F O) L₀)) :=
      hF O hO _ hOi hc
    have h2 := hasSemistableReduction_ofNF hN _ _ h1
    have h3 := h33 (F O) (O''.comap (algebraMap (F O) L₀)) L₀ O'' rfl (A.baseChange (F O)) h2
    exact hasSemistableReduction_ofNF hN O'' _
      (semistableNeronModels_transport (bcbcIso A (F O) L₀) (bcbcIso_isMonHom A (F O) L₀) h3)
  · -- a place of semistable reduction of `A`
    have hgood : HasSemistableReduction A (O''.comap (algebraMap K L₀)) := by
      by_contra hc
      exact hOS ⟨hO, hc⟩
    exact hasSemistableReduction_ofNF hN O'' _ (h33 K _ L₀ O'' rfl A hgood)

/-- `ReductB.semistablePersists_final_nf` (TailZ23 L566) with `hN` at number fields. -/
theorem semistablePersists_final_nfNF (h33 : SemistablePersistsDVRnf)
    (hN : NeronSchemeModelExistsDVRNF) (hLG : SemistableLocalGlobal) :
    ZInQ.HeightSplit.SemistablePersists :=
  semistablePersists_of_leaves_nfNF h33 hN hLG dvrComapFinite

/-- `ReductB.semistableReductionThm_final_nf` (TailZ23 L573) with `hN` at number fields. -/
theorem semistableReductionThm_final_nfNF (h36 : SemistableReductionDVRnf)
    (h33 : SemistablePersistsDVRnf) (hN : NeronSchemeModelExistsDVRNF) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) : ZInQ.HeightSplit.SemistableReductionThm :=
  semistableReductionThm_of_leaves_nfNF h36 h33 hN hLG hAA dvrComapFinite

/-- **`ReductB.ss1_ss3_of_cp` (TailZ23 L580) with `hN` at number fields** (the consumer used by `ss1_ss3_of14`,
TailZ23 L763). -/
theorem ss1_ss3_of_cpNF (hSH : SemistablePersistsSHcp) (hPair : StrictHenselizationPair)
    (h36 : SemistableReductionDVR) (hN : NeronSchemeModelExistsDVRNF) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists :=
  ⟨semistableReductionThm_final_nfNF (reductionNF_of_general h36)
      (persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair)) hN hLG hAA,
    semistablePersists_final_nfNF (persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair)) hN hLG⟩

/-- `ReductB.ss1_ss3_of_cp_full` (TailZ23 L591) with `hN` at number fields. -/
theorem ss1_ss3_of_cp_fullNF (hR : RaynaudSemistableSHcp) (hSH : SemistablePersistsSHcp)
    (hPair : StrictHenselizationPair) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) (hN : NeronSchemeModelExistsDVRNF)
    (hLG : SemistableLocalGlobal) (hAA : SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists :=
  ⟨semistableReductionThm_final_nfNF
      (semistableReductionDVRnf_of_raynaudCP (raynaudSemistableCP_of_SH hR hPair hE) hM hE)
      (persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair)) hN hLG hAA,
    semistablePersists_final_nfNF (persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair)) hN hLG⟩

/-- The restated consumer agrees with the original on the field (sanity: same conclusion, same hypotheses
up to `neronSchemeModelExistsDVRNF_of_field`). -/
theorem ss1_ss3_of_cp_eq (hSH : SemistablePersistsSHcp) (hPair : StrictHenselizationPair)
    (h36 : SemistableReductionDVR) (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists :=
  ss1_ss3_of_cpNF hSH hPair h36 (neronSchemeModelExistsDVRNF_of_field hN) hLG hAA

end SS

/-! ## §5 r6 and r8 at number fields

`PkgI2.RaynaudCriterion` (r6) and `PkgI2.GrothendieckMonodromy` (r8) quantify over every field `K`; from the
number-field form of the Néron field the chain's proofs (TailZ7 §5, §6) give their restrictions to number
fields, stated here verbatim with `[NumberField K]` added. -/

/-- `PkgI2.RaynaudCriterion` (HDecomp/Objects.lean L1436, verbatim) with `[NumberField K]` added. -/
def RaynaudCriterionNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ), 3 ≤ m → IsUnit (m : O) →
      (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
        ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
          ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

/-- `PkgI2.GrothendieckMonodromy` (HDecomp/Objects.lean L1416, verbatim) with `[NumberField K]` added. -/
def GrothendieckMonodromyNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
        ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
          (∀ x ∈ K', σ x = x) →
          ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

theorem raynaudCriterionNF_of_general (h : PkgI2.RaynaudCriterion.{0}) : RaynaudCriterionNF :=
  fun K _ _ O _ w hw A _ m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx =>
    h K O w hw A m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx

theorem grothendieckMonodromyNF_of_general (h : PkgI2.GrothendieckMonodromy.{0}) :
    GrothendieckMonodromyNF :=
  fun K _ _ O _ w hw A _ => h K O w hw A

/-- `ReductSplit.raynaudCriterion_of_leaves` (TailZ7 L395) at number fields, `hN` retyped (proof unchanged). -/
theorem raynaudCriterion_of_leavesNF (hR : RaynaudSemistable) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVRNF) (hT : PkgI2.TorsionStructure.{0})
    (hF : FixedTorsionRational) : RaynaudCriterionNF := by
  intro K _ _ O _ w hw A _ m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let B := ObjBridge.ofGrp A
  have hss : SemistableNeronModels B O :=
    hR K O B m hm hmO (hF K B m (natCast_ne_zero_of_isUnit O hmO) (fun σ x hx => hrat σ x hx))
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ (natCast_ne_zero_of_isUnit O hℓO) n x hx
  exact unipSq_of_tate B ℓ σ t n x ht
    (hU K O (AlgebraicClosure K) w hw B (hasSemistableReduction_ofNF hN O B hss) ℓ hℓO σ hσ t)

/-- **r6 consumer restated**: `ReductGlue.raynaudCriterion_leaves` (TailZ14 L243) with `hN` at number fields;
the conclusion is the number-field restriction of r6. -/
theorem raynaudCriterion_leavesNF (hR : RaynaudSemistable) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVRNF) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudCriterionNF :=
  raynaudCriterion_of_leavesNF hR hU hN (AvSplit.torsionStructure_of_mumford hM)
    (ReductGlue.fixedTorsionRational_of_mulEtale hE)

/-- `ReductSplit.grothendieckMonodromy_of_leaves` (TailZ7 L425) at number fields, `hN` retyped; the only
addition is the `NumberField K'` instance at the one use of `hN`. -/
theorem grothendieckMonodromy_of_leavesNF (hS : SemistableReductionDVR)
    (hU : SemistableUnipotent) (hN : NeronSchemeModelExistsDVRNF) (hT : PkgI2.TorsionStructure.{0})
    (hD : DVRFiniteExtension) : GrothendieckMonodromyNF := by
  intro K _ _ O _ w hw A _
  let B := ObjBridge.ofGrp A
  obtain ⟨K', hK', hss'⟩ := hS K O B
  refine ⟨K', hK', fun σ hσ hfix ℓ hℓ hℓO n x hx => ?_⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI := hD K O w hw K' hK'
  haveI : NumberField K' := by
    haveI := hK'
    exact NumberField.of_module_finite K K'
  have hss := hss' (w.comap (algebraMap K' (AlgebraicClosure K))) inferInstance (by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw])
  haveI : IsAlgClosure K' (AlgebraicClosure K) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) (L := K') (A := AlgebraicClosure K)⟩
  let σ' : AlgebraicClosure K ≃ₐ[K'] AlgebraicClosure K :=
    AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun y => hfix _ y.2)
  have hσ' : IsInertia w σ' := isInertia_restrict K' w σ σ' (fun _ => rfl) hσ
  have hℓO' : IsUnit (ℓ : w.comap (algebraMap K' (AlgebraicClosure K))) := by
    have := hℓO.map (toO' O w hw K')
    rwa [map_natCast] at this
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ (natCast_ne_zero_of_isUnit O hℓO) n x hx
  let e := ZInQ.Contrib.AbVarBC.bcPt (L := K') B (AlgebraicClosure K)
  let t' : TΩ (B.baseChange K') (AlgebraicClosure K) ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive e.symm.toMonoidHom) t
  have ht' : t'.1 n = Additive.ofMul (e.symm x) := by
    show MonoidHom.toAdditive e.symm.toMonoidHom (t.1 n) = _
    rw [ht]; rfl
  have h := hU K' (w.comap (algebraMap K' (AlgebraicClosure K))) (AlgebraicClosure K) w rfl
    (B.baseChange K') (hasSemistableReduction_ofNF hN _ _ hss) ℓ hℓO' σ' hσ' t'
  have hu := unipSq_of_tate (B.baseChange K') ℓ σ' t' n (e.symm x) ht' h
  have key : ∀ q, e ((B.baseChange K').galAct σ' q) = B.galAct σ (e q) := fun q => by
    rw [ZInQ.Contrib.AbVarBC.bcPt_galAct]
    congr 2
  have := congrArg e hu
  simp only [map_mul, map_inv, key, map_one] at this
  have hx' : e (e.symm x) = x := e.apply_symm_apply x
  erw [hx'] at this
  exact this

/-- **r8 consumer restated**: `ReductSplit.grothendieckMonodromy_final'` (TailZ7 L1496) with `hN` at number
fields; the conclusion is the number-field restriction of r8. -/
theorem grothendieckMonodromy_final'NF (hS : SemistableReductionDVR) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVRNF) (hM : AvSplit.MumfordTorsionAlgClosed) :
    GrothendieckMonodromyNF :=
  grothendieckMonodromy_of_leavesNF hS hU hN (AvSplit.torsionStructure_of_mumford hM) dvrFiniteExtension

/-- **r6 and r8 at number fields from N1** and the other leaves of their consumers (no Néron field). -/
theorem r6_r8_NF_of_N1 (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists) (hR : RaynaudSemistable)
    (hU : SemistableUnipotent) (hS : SemistableReductionDVR) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudCriterionNF ∧ GrothendieckMonodromyNF :=
  ⟨raynaudCriterion_leavesNF hR hU (neronSchemeModelExistsNF hN1) hM hE,
    grothendieckMonodromy_final'NF hS hU (neronSchemeModelExistsNF hN1) hM⟩

end GapNeron

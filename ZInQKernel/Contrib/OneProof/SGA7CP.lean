import ZInQKernel.OneProof.H.TailZ34

/-! # sga7-cp: the two SGA 7 IX strictly henselian leaves used only in characteristic 0, perfect residue field

Task sga7-cp (docs/research/sga7-cp.md). The research fields
* `raynaudSemistableSH : ReductGlue.RaynaudSemistableSH` (SGA 7 I Exp. IX Prop. 4.7 over every strictly henselian
  DVR), and
* `sga7_IX_3_5_ForwardGeom : UnipotentForward.SGA7_IX_3_5_ForwardGeom` (SGA 7 I Exp. IX Prop. 3.5, forward direction,
  over every strictly henselian DVR)

of `HDec.HSyn.OpenResearchLeaves21` are consumed by the chain only through r6 at number fields
(`PkgI2.RaynaudCriterionNF`) and SS1/SS3 (`HDec.HSyn.raynaudCriterionNF_of14`, `HDec.HSyn.ss1_ss3_of14NF`, TailZ26).
There, the strictly henselian DVRs they are applied at are strict henselizations of DVRs of number fields: their
fraction field has characteristic `0` and their residue field is algebraic over a finite field, hence perfect (and,
being separably closed, algebraically closed).

This file proves r6 at number fields and SS1/SS3 from the **restrictions** of the two leaves to characteristic `0`
and perfect residue field:
* `ReductB.RaynaudSemistableSHcp` (TailZ23, already in the tree; a specialization of `RaynaudSemistableSH`);
* `SGA7CP.SGA7_IX_3_5_ForwardGeomCP` (new, below; a specialization of `SGA7_IX_3_5_ForwardGeom`, and also a
  consequence of the reading-robust `UnipotentForward.SGA7_IX_3_5_Forward` with no glue, since the two readings of
  semistability agree for perfect residue fields: `forwardGeomCP_of_forward`).

No other new hypothesis: everything else comes from fields of the current bundles and proved glue. The generation
module `ZInQKernel/Contrib/OneProof/SGA7CPFold.lean` uses these theorems to replace the two fields by their
restrictions (`HDec.HSyn.OpenResearchLeaves22`, `HDec.HSyn.sixContactMin_of_open29`).
-/

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety Pts torsion galAct IsInertia UnipSq HasGoodReduction)
open ReductSplit ReductGlue ZInQ.HeightSplit

namespace SGA7CP

/-! ## §1 The new leaf: SGA 7 IX 3.5 (forward) in characteristic `0` with perfect residue field -/

/-- **LEAF `SGA7_IX_3_5_ForwardGeomCP`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.5, the direction "semistable ⇒
unipotent of echelon `≤ 2`", one `σ` at a time; number UNVERIFIED). `UnipotentForward.SGA7_IX_3_5_ForwardGeom`
(Contrib/OneProof/UnipotentForward.lean, verbatim) with `[CharZero K]` and `[PerfectField (ResidueField O)]` added:
`O` a strictly henselian DVR of a field `K` of characteristic `0` whose residue field is perfect (hence algebraically
closed), `Ω = K^s`, `w` the valuation ring of `Ω` over `O`, `ℓ` a prime invertible in `O`. If `A` has semistable
reduction at `O`, every `σ` in the inertia group satisfies `(σ - 1)² = 0` on `T_ℓ(A)`.

A specialization of the chain's field (`forwardGeomCP_of_forwardGeom`). For perfect residue fields semistability
over `k(s)` and on the geometric special fibre agree, so this form is also a consequence of the reading-robust
`SGA7_IX_3_5_Forward` (`forwardGeomCP_of_forward`, no glue): the `k(s)` reading risk of the field disappears. -/
def SGA7_IX_3_5_ForwardGeomCP : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)], IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → HasSemistableReduction A O →
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → (galTΩ A ℓ σ - 1) * (galTΩ A ℓ σ - 1) = 0

/-- The restriction is a specialization of the chain's field (so it is not stronger). -/
theorem forwardGeomCP_of_forwardGeom (h : UnipotentForward.SGA7_IX_3_5_ForwardGeom) :
    SGA7_IX_3_5_ForwardGeomCP :=
  fun K _ _ O _ _ hO Ω _ _ _ w hw A ℓ _ hℓ hA σ hσ => h K O hO Ω w hw A ℓ hℓ hA σ hσ

/-- **The restriction follows from the reading-robust form with no glue**: for a perfect, separably closed
residue field, `UnipotentForward.semiAbelianDescends_of_perfect` gives semistability over `k(s)`. -/
theorem forwardGeomCP_of_forward (h : UnipotentForward.SGA7_IX_3_5_Forward) : SGA7_IX_3_5_ForwardGeomCP := by
  intro K _ _ O _ _ hO Ω _ _ _ w hw A ℓ _ hℓ hA σ hσ
  refine h K O hO Ω w hw A ℓ hℓ ?_ hA σ hσ
  obtain ⟨𝒩, h1, h2⟩ := hA
  exact ⟨𝒩, h1, UnipotentForward.semiAbelianDescends_of_perfect K O hO.2.2 A 𝒩 h2⟩

/-- `ReductB.RaynaudSemistableSHcp` is a specialization of the chain's field `RaynaudSemistableSH`. -/
theorem raynaudSemistableSHcp_of_SH (h : ReductGlue.RaynaudSemistableSH) : ReductB.RaynaudSemistableSHcp :=
  fun K _ _ O _ _ hO A m hm hmu ht => h K O hO A m hm hmu ht

/-! ## §2 Unipotence at number fields (the only use of the field, through r6) -/

/-- `ReductGlue.SemistableUnipotentSH` (TailZ14) with `[CharZero K]` and `[PerfectField (ResidueField O)]`. -/
def SemistableUnipotentSHcp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)], IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

/-- `ReductSplit.SemistableUnipotent` (TailZ7, the field `semistableUnipotent` of the old bundles) with
`[NumberField K]` added: the form r6 uses. -/
def SemistableUnipotentNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

/-- `UnipotentForward.semistableUnipotentSH_of_forwardGeom` with the two instances (proof unchanged). -/
theorem semistableUnipotentSHcp_of_forwardGeomCP (hP : SGA7_IX_3_5_ForwardGeomCP)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : SemistableUnipotentSHcp := by
  intro K _ _ O _ _ hO Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isUnit O hℓ
  obtain ⟨σs, hσs, φ, hφ, hcomm⟩ := UnipotentForward.sepClosure_tate hE K Ω w A ℓ hℓK σ hσ
  have hws : (w.comap (algebraMap (separableClosure K Ω) Ω)).comap
      (algebraMap K (separableClosure K Ω)) = O := by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw]
  have key := hP K O hO (separableClosure K Ω) _ hws A ℓ hℓ hA σs hσs
  obtain ⟨s, rfl⟩ := hφ t
  have h2 := congrArg φ (UnipotentForward.sq_form _ key s)
  simp only [map_add, map_sub, map_nsmul, map_zero, hcomm] at h2
  exact h2

open ZInQ.Contrib.AbVarBC in
/-- **Unipotence at number fields from the restricted strictly henselian form**: `ReductGlue.unipotentFromSH_of`
(TailZ14), applied over the inertia field `E` of `w`, whose valuation ring `w ∩ E` is a strict henselization of `O`
(`StrictHenselizationInside`). `E ⊇ K` has characteristic `0`, and the residue field of `w ∩ E` is algebraic over the
finite residue field of `O`, hence perfect (`ReductB.perfectField_residue_nf`, `ReductB.perfectField_of_isSHNeronExt`).
Proof otherwise unchanged. -/
theorem semistableUnipotentNF_of_SHcp (hIn : StrictHenselizationInside) (hSH : SemistableUnipotentSHcp) :
    SemistableUnipotentNF := by
  intro K _ _ O _ Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  obtain ⟨E, hE, hSHN, hfix⟩ := hIn K O Ω w hw
  haveI : PerfectField (IsLocalRing.ResidueField O) := ReductB.perfectField_residue_nf O
  haveI : PerfectField (IsLocalRing.ResidueField (w.comap (algebraMap E Ω))) :=
    ReductB.perfectField_of_isSHNeronExt hSHN
  haveI : CharZero E := ReductB.charZero_of_algebra K E
  obtain ⟨hSHP, halg, hbc⟩ := hSHN
  haveI : IsDiscreteValuationRing (w.comap (algebraMap E Ω)) := hSHP.1
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) E⟩
  have hAE : HasSemistableReduction (A.baseChange E) (w.comap (algebraMap E Ω)) := by
    obtain ⟨𝒩, h𝒩, hs⟩ := hA
    exact ⟨bcDVR hE 𝒩, hbc A 𝒩 h𝒩, (isSemistable_bcDVR_iff hE halg 𝒩).mp hs⟩
  have hℓP : IsUnit (ℓ : w.comap (algebraMap E Ω)) := by
    have := hℓ.map (comapHom hE)
    rwa [map_natCast] at this
  let σ₁ := toE E σ (hfix σ hσ)
  have hσ₁ : IsInertia w σ₁ := isInertia_toE E w σ (hfix σ hσ) hσ
  let φ : TΩ (A.baseChange E) Ω ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (bcPt A Ω).toMonoidHom)
  let ψ : TΩ A Ω ℓ →ₗ[ℤ_[ℓ]] TΩ (A.baseChange E) Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (bcPt A Ω).symm.toMonoidHom)
  have hφψ : φ (ψ t) = t := by
    apply Subtype.ext
    funext n
    change Additive.ofMul (bcPt A Ω ((bcPt A Ω).symm (Additive.toMul (t.1 n)))) = t.1 n
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hcomm : ∀ s, φ (galTΩ (A.baseChange E) ℓ σ₁ s) = galTΩ A ℓ σ (φ s) := by
    intro s
    apply Subtype.ext
    funext n
    change Additive.ofMul (bcPt A Ω ((A.baseChange E).galAct σ₁ (Additive.toMul (s.1 n)))) =
      Additive.ofMul (A.galAct σ (bcPt A Ω (Additive.toMul (s.1 n))))
    rw [bcPt_galAct, toE_restrictScalars]
  have key := hSH E (w.comap (algebraMap E Ω)) hSHP Ω w rfl (A.baseChange E) hAE ℓ hℓP σ₁ hσ₁
    (ψ t)
  have := congrArg φ key
  simp only [map_add, map_sub, map_nsmul, map_zero, hcomm, hφψ] at this
  exact this

/-- **Unipotence at number fields from the new leaf** and two leaves of the current bundles:
`MulEtaleAbelianScheme` (proved, `ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof`) and
`NeronBaseChangeStrictHenselization` (BLR §1.2 Prop. 2). The cp analogue of
`UnipotentForward.semistableUnipotent_of_forwardGeom`. -/
theorem semistableUnipotentNF_of_forwardGeomCP (hP : SGA7_IX_3_5_ForwardGeomCP)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) (hN : GapSHPair.NeronBaseChangeStrictHenselization) :
    SemistableUnipotentNF :=
  semistableUnipotentNF_of_SHcp (UnipotentForward.strictHenselizationInside_of_neron hN)
    (semistableUnipotentSHcp_of_forwardGeomCP hP hE)

/-! ## §3 r6 at number fields from the restricted leaves -/

/-- `GapNeron.raynaudCriterion_of_leavesNF` (NeronDVR.lean) with `hR` restricted to characteristic `0` and perfect
residue field (`ReductB.RaynaudSemistableCP`) and `hU` to number fields; the residue field of a DVR of a number field
is finite (`ReductB.perfectField_residue_nf`). Proof otherwise unchanged. -/
theorem raynaudCriterionNF_of_cp (hR : ReductB.RaynaudSemistableCP) (hU : SemistableUnipotentNF)
    (hN : GapNeron.NeronSchemeModelExistsDVRNF) (hT : PkgI2.TorsionStructure.{0})
    (hF : FixedTorsionRational) : GapNeron.RaynaudCriterionNF := by
  intro K _ _ O _ w hw A _ m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : PerfectField (IsLocalRing.ResidueField O) := ReductB.perfectField_residue_nf O
  let B := ObjBridge.ofGrp A
  have hss : SemistableNeronModels B O :=
    hR K O B m hm hmO (hF K B m (natCast_ne_zero_of_isUnit O hmO) (fun σ x hx => hrat σ x hx))
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ (natCast_ne_zero_of_isUnit O hℓO) n x hx
  exact unipSq_of_tate B ℓ σ t n x ht
    (hU K O (AlgebraicClosure K) w hw B (GapNeron.hasSemistableReduction_ofNF hN O B hss) ℓ hℓO σ hσ t)

/-- **r6 at number fields from the two restricted SGA 7 leaves** and leaves of the current bundles
(`StrictHenselizationPair` from `NeronBaseChangeStrictHenselization`, N1, Mumford's torsion count) and proved glue.
Replaces `HDec.HSyn.raynaudCriterionNF_of14` (TailZ26), which used `RaynaudSemistableSH` and `SemistableUnipotent`. -/
theorem raynaudCriterionNF_of_cpLeaves (hR : ReductB.RaynaudSemistableSHcp) (hP : SGA7_IX_3_5_ForwardGeomCP)
    (hNB : GapSHPair.NeronBaseChangeStrictHenselization) (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    GapNeron.RaynaudCriterionNF :=
  raynaudCriterionNF_of_cp
    (ReductB.raynaudSemistableCP_of_SH hR (GapSHPair.strictHenselizationPair_of_neron hNB) hE)
    (semistableUnipotentNF_of_forwardGeomCP hP hE hNB) (GapNeron.neronSchemeModelExistsNF hN1)
    (AvSplit.torsionStructure_of_mumford hM) (ReductGlue.fixedTorsionRational_of_mulEtale hE)

/-! ## §4 SS1 and SS3 from the restricted Raynaud leaf -/

/-- **SS1 and SS3 from `RaynaudSemistableSHcp`** (in place of `RaynaudSemistableSH`): neron-dvr's
`GapNeron.ss1_ss3_of_cp_fullNF` with the pair from `NeronBaseChangeStrictHenselization` and the Néron field at number
fields from N1. Replaces `HDec.HSyn.ss1_ss3_of14NF` (TailZ26). -/
theorem ss1_ss3_of_cpLeaves (hR : ReductB.RaynaudSemistableSHcp) (hSH : ReductB.SemistablePersistsSHcp)
    (hNB : GapSHPair.NeronBaseChangeStrictHenselization) (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme)
    (hLG : SemistableLocalGlobal) (hAA : SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists :=
  GapNeron.ss1_ss3_of_cp_fullNF hR hSH (GapSHPair.strictHenselizationPair_of_neron hNB) hM hE
    (GapNeron.neronSchemeModelExistsNF hN1) hLG hAA

end SGA7CP

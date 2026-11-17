import ZInQKernel.Contrib.OneProof.UnipotentForward
import ZInQKernel.Contrib.OneProof.NeronDVR

/-!
# sga735-narrow: `sga7_IX_3_5_ForwardGeom` restricted to algebraically closed residue fields

Task sga735-narrow (docs/research/sga735-narrow.md). The research field
`sga7_IX_3_5_ForwardGeom : UnipotentForward.SGA7_IX_3_5_ForwardGeom` (SGA 7 I, Exp. IX, Prop. 3.5, forward
direction at `σ = τ`, over a strictly henselian DVR) carries the reading risk "SGA 7 IX reads semistability on
`𝒩 ×_O k(s)`, not on the geometric special fibre" (`UnipotentForward.SemiAbelianDescendsSepClosed`, proved only for
perfect `k(s)`). Its only use in the chain (`UnipotentForward.semistableUnipotent_of_forwardGeom`, TailZ33 and its
`_hf` copy) feeds `semistableUnipotent : ReductSplit.SemistableUnipotent`, whose only reader on the route is r6 at
number fields (`raynaudCriterionNF_of14`, TailZ26 and its `_hf` copy). There the DVR is a localization of a number
field, so its residue field is finite, hence perfect, and after strict henselization inside `K̄` (the inertia field
of `w`) the residue field is algebraically closed.

This file:
* states the restricted leaf `SGA7_IX_3_5_ForwardGeomAC` (the field word for word, with
  `[IsAlgClosed (IsLocalRing.ResidueField O)]` added) and proves it from the field (`forwardGeomAC_of_forwardGeom`)
  and from the `k(s)` reading (`forwardGeomAC_of_forwardRes`), so it is a consequence of the print under either
  reading of "semistable";
* proves `SemistableUnipotentCP` (the chain's `ReductSplit.SemistableUnipotent` with `[PerfectField k(s)]` added)
  from the restricted leaf and the two bundle leaves the old proof used (`MulEtaleAbelianScheme`,
  `NeronBaseChangeStrictHenselization`);
* proves r6 at number fields (`GapNeron.RaynaudCriterionNF`) from `SemistableUnipotentCP` with the other
  hypotheses of `GapNeron.raynaudCriterion_leavesNF` unchanged.

No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction Pts torsion galAct UnipSq)
open ReductSplit ReductGlue ZInQ.HeightSplit

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SGA735AC

/-! ## §1. The restricted leaf -/

/-- **LEAF `SGA7_IX_3_5_ForwardGeomAC`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.5, the direction "semistable ⇒
unipotent", one `σ` at a time; number and wording UNVERIFIED), over a strictly henselian discrete valuation ring
**with algebraically closed residue field**. This is `UnipotentForward.SGA7_IX_3_5_ForwardGeom` word for word with
`[IsAlgClosed (IsLocalRing.ResidueField O)]` added: `O` strictly henselian with `k(s)` algebraically closed, `Ω = K^s`,
`w` over `O`, `ℓ` invertible in `O`; if `A` has semistable reduction at `O`, every `σ` in the inertia group satisfies
`(σ - 1)² = 0` on `T_ℓ(A) = lim A(K^s)[ℓⁿ]`.

Since `k(s) = κ̄`, semistability over `k(s)` and on the geometric special fibre coincide
(`UnipotentForward.hasSemistableReductionRes_iff`), so this is a specialization of the print whichever of the two
SGA 7 IX uses (`forwardGeomAC_of_forwardGeom`, `forwardGeomAC_of_forwardRes`). -/
def SGA7_IX_3_5_ForwardGeomAC : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAlgClosed (IsLocalRing.ResidueField O)],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → HasSemistableReduction A O →
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
        (galTΩ A ℓ σ - 1) * (galTΩ A ℓ σ - 1) = 0

/-- The restricted leaf is a specialization of the field (never stronger). -/
theorem forwardGeomAC_of_forwardGeom (h : UnipotentForward.SGA7_IX_3_5_ForwardGeom) :
    SGA7_IX_3_5_ForwardGeomAC :=
  fun K _ O _ _ hO Ω _ _ _ w hw A ℓ _ hℓ hA σ hσ => h K O hO Ω w hw A ℓ hℓ hA σ hσ

/-- The `k(s)` reading of SGA 7 IX 3.5 (semistability over the residue field itself), over the same bases. -/
def SGA7_IX_3_5_ForwardRes : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → UnipotentForward.HasSemistableReductionRes A O →
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
        (galTΩ A ℓ σ - 1) * (galTΩ A ℓ σ - 1) = 0

/-- The restricted leaf also follows from the `k(s)` reading: for algebraically closed `k(s)` the two notions of
semistable reduction agree (`UnipotentForward.hasSemistableReductionRes_iff`, proved). -/
theorem forwardGeomAC_of_forwardRes (h : SGA7_IX_3_5_ForwardRes) : SGA7_IX_3_5_ForwardGeomAC :=
  fun K _ O _ _ hO Ω _ _ _ w hw A ℓ _ hℓ hA σ hσ =>
    h K O hO Ω w hw A ℓ hℓ ((UnipotentForward.hasSemistableReductionRes_iff O A).mpr hA) σ hσ

/-- The restricted leaf also follows from gt-unip's reading-robust form `SGA7_IX_3_5_Forward`. -/
theorem forwardGeomAC_of_forward (h : UnipotentForward.SGA7_IX_3_5_Forward) : SGA7_IX_3_5_ForwardGeomAC :=
  fun K _ O _ _ hO Ω _ _ _ w hw A ℓ _ hℓ hA σ hσ =>
    h K O hO Ω w hw A ℓ hℓ ((UnipotentForward.hasSemistableReductionRes_iff O A).mpr hA) hA σ hσ

/-! ## §2. `SemistableUnipotent` for perfect residue fields -/

/-- **GLUE (proved below) `SemistableUnipotentCP`**: the chain's `ReductSplit.SemistableUnipotent` (TailZ7) with
`[PerfectField (IsLocalRing.ResidueField O)]` added. -/
def SemistableUnipotentCP : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

/-- `SemistableUnipotentCP` is a specialization of `ReductSplit.SemistableUnipotent`. -/
theorem semistableUnipotentCP_of_general (h : ReductSplit.SemistableUnipotent) : SemistableUnipotentCP :=
  fun K _ O _ _ Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t => h K O Ω w hw A hA ℓ hℓ σ hσ t

/-- `ReductGlue.SemistableUnipotentSH` with `[IsAlgClosed k(s)]` added. -/
def SemistableUnipotentSHAC : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAlgClosed (IsLocalRing.ResidueField O)],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

/-- gt-unip's `semistableUnipotentSH_of_forwardGeom`, with the residue-field instance carried along. -/
theorem semistableUnipotentSHAC_of_forwardGeomAC (hP : SGA7_IX_3_5_ForwardGeomAC)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : SemistableUnipotentSHAC := by
  intro K _ O _ _ hO Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
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

/-- The residue field of a strict henselization (in the sense of `IsSHNeronExt`) of a DVR with perfect residue
field is perfect (it is algebraic over `k(s)`). -/
theorem perfectField_of_isSHNeronExt {K E : Type} [Field K] [Field E] [Algebra K E]
    {O : ValuationSubring K} {P : ValuationSubring E} {hP : P.comap (algebraMap K E) = O}
    [PerfectField (IsLocalRing.ResidueField O)] (h : IsSHNeronExt O P hP) :
    PerfectField (IsLocalRing.ResidueField P) := by
  obtain ⟨-, halg, -⟩ := h
  letI := (resMap hP).toAlgebra
  exact Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField O)

/-- **`SemistableUnipotentCP` from the restricted leaf** (reduct-glue's `unipotentFromSH_of`, with the base
`StrictHenselizationInside` proved from the Néron leaf by gt-unip's `strictHenselizationInside_of_neron`): apply the
leaf to `A_E` over the inertia field `E` of `w`. The residue field of `w ∩ E` is algebraic over the perfect `k(s)`,
hence perfect, and separably closed, hence algebraically closed. -/
theorem semistableUnipotentCP_of_SHAC (hIn : StrictHenselizationInside) (hSH : SemistableUnipotentSHAC) :
    SemistableUnipotentCP := by
  intro K _ O _ _ Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  obtain ⟨E, hE, hSHPall, hfix⟩ := hIn K O Ω w hw
  haveI : PerfectField (IsLocalRing.ResidueField (w.comap (algebraMap E Ω))) :=
    perfectField_of_isSHNeronExt hSHPall
  obtain ⟨hSHP, halg, hbc⟩ := hSHPall
  haveI : IsDiscreteValuationRing (w.comap (algebraMap E Ω)) := hSHP.1
  haveI : IsSepClosed (IsLocalRing.ResidueField (w.comap (algebraMap E Ω))) := hSHP.2.2
  haveI : IsAlgClosed (IsLocalRing.ResidueField (w.comap (algebraMap E Ω))) :=
    IsSepClosed.isAlgClosed_of_perfectField _
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
    PkgI3.Tate.map (MonoidHom.toAdditive (ZInQ.Contrib.AbVarBC.bcPt A Ω).toMonoidHom)
  let ψ : TΩ A Ω ℓ →ₗ[ℤ_[ℓ]] TΩ (A.baseChange E) Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (ZInQ.Contrib.AbVarBC.bcPt A Ω).symm.toMonoidHom)
  have hφψ : φ (ψ t) = t := by
    apply Subtype.ext
    funext n
    change Additive.ofMul (ZInQ.Contrib.AbVarBC.bcPt A Ω
      ((ZInQ.Contrib.AbVarBC.bcPt A Ω).symm (Additive.toMul (t.1 n)))) = t.1 n
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hcomm : ∀ s, φ (galTΩ (A.baseChange E) ℓ σ₁ s) = galTΩ A ℓ σ (φ s) := by
    intro s
    apply Subtype.ext
    funext n
    change Additive.ofMul (ZInQ.Contrib.AbVarBC.bcPt A Ω ((A.baseChange E).galAct σ₁ (Additive.toMul (s.1 n)))) =
      Additive.ofMul (A.galAct σ (ZInQ.Contrib.AbVarBC.bcPt A Ω (Additive.toMul (s.1 n))))
    rw [ZInQ.Contrib.AbVarBC.bcPt_galAct, toE_restrictScalars]
  have key := hSH E (w.comap (algebraMap E Ω)) hSHP Ω w rfl (A.baseChange E) hAE ℓ hℓP σ₁ hσ₁
    (ψ t)
  have := congrArg φ key
  simp only [map_add, map_sub, map_nsmul, map_zero, hcomm, hφψ] at this
  exact this

/-- **`SemistableUnipotentCP` from the restricted leaf and the two bundle leaves of the old proof**
(`MulEtaleAbelianScheme`, BLR 7.3/2; `NeronBaseChangeStrictHenselization`, BLR §1.2 Prop. 2). This replaces
`UnipotentForward.semistableUnipotent_of_forwardGeom` at TailZ33. -/
theorem semistableUnipotentCP_of_forwardGeomAC (hP : SGA7_IX_3_5_ForwardGeomAC)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) (hN : GapSHPair.NeronBaseChangeStrictHenselization) :
    SemistableUnipotentCP :=
  semistableUnipotentCP_of_SHAC (UnipotentForward.strictHenselizationInside_of_neron hN)
    (semistableUnipotentSHAC_of_forwardGeomAC hP hE)

/-! ## §3. r6 at number fields from `SemistableUnipotentCP` -/

/-- The residue field of a DVR of a number field is finite, hence perfect (ReductB's `perfectField_residue_nf`,
TailZ23, reproved here from TailZ14's `center`). -/
theorem perfectField_residue_nf {L : Type} [Field L] [NumberField L] (O : ValuationSubring L)
    [IsDiscreteValuationRing O] : PerfectField (IsLocalRing.ResidueField O) := by
  haveI : (center O).IsMaximal := center_isMaximal O
  haveI : Finite (𝓞 L ⧸ center O) := Ideal.finiteQuotientOfFreeOfNeBot (center O) (center_ne_bot O)
  haveI : Finite (center O).ResidueField :=
    Finite.of_surjective _ (center O).bijective_algebraMap_quotient_residueField.2
  haveI : Finite (IsLocalRing.ResidueField O) := Finite.of_equiv _ (resIso O).toEquiv
  infer_instance

/-- neron-dvr's `GapNeron.raynaudCriterion_of_leavesNF` with `hU : SemistableUnipotentCP` (proof unchanged, plus
one `haveI` for `PerfectField k(s)`). -/
theorem raynaudCriterion_of_leavesNF_cp (hR : RaynaudSemistable) (hU : SemistableUnipotentCP)
    (hN : GapNeron.NeronSchemeModelExistsDVRNF) (hT : PkgI2.TorsionStructure.{0})
    (hF : FixedTorsionRational) : GapNeron.RaynaudCriterionNF := by
  intro K _ _ O _ w hw A _ m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : PerfectField (IsLocalRing.ResidueField O) := perfectField_residue_nf O
  let B := ObjBridge.ofGrp A
  have hss : SemistableNeronModels B O :=
    hR K O B m hm hmO (hF K B m (natCast_ne_zero_of_isUnit O hmO) (fun σ x hx => hrat σ x hx))
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ (natCast_ne_zero_of_isUnit O hℓO) n x hx
  exact unipSq_of_tate B ℓ σ t n x ht
    (hU K O (AlgebraicClosure K) w hw B (GapNeron.hasSemistableReduction_ofNF hN O B hss) ℓ hℓO σ hσ t)

/-- **r6 at number fields from `SemistableUnipotentCP`**: `GapNeron.raynaudCriterion_leavesNF` (NeronDVR) with
`hU : SemistableUnipotentCP` in place of `ReductSplit.SemistableUnipotent`. This replaces
`GapNeron.raynaudCriterion_leavesNF` at `raynaudCriterionNF_of14` (TailZ26). -/
theorem raynaudCriterion_leavesNF_cp (hR : RaynaudSemistable) (hU : SemistableUnipotentCP)
    (hN : GapNeron.NeronSchemeModelExistsDVRNF) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : GapNeron.RaynaudCriterionNF :=
  raynaudCriterion_of_leavesNF_cp hR hU hN (AvSplit.torsionStructure_of_mumford hM)
    (ReductGlue.fixedTorsionRational_of_mulEtale hE)

/-- The whole replacement at once: r6 at number fields from the restricted leaf (statement of the r6 field
unchanged). -/
theorem raynaudCriterionNF_of_forwardGeomAC (hR : RaynaudSemistable) (hP : SGA7_IX_3_5_ForwardGeomAC)
    (hNbc : GapSHPair.NeronBaseChangeStrictHenselization) (hN : GapNeron.NeronSchemeModelExistsDVRNF)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    GapNeron.RaynaudCriterionNF :=
  raynaudCriterion_leavesNF_cp hR (semistableUnipotentCP_of_forwardGeomAC hP hE hNbc) hN hM hE

end SGA735AC

end

#print axioms SGA735AC.forwardGeomAC_of_forwardGeom
#print axioms SGA735AC.forwardGeomAC_of_forwardRes
#print axioms SGA735AC.semistableUnipotentCP_of_forwardGeomAC
#print axioms SGA735AC.raynaudCriterionNF_of_forwardGeomAC

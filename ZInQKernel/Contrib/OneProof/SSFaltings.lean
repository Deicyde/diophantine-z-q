import ZInQKernel.Contrib.OneProof.NeronDVR

/-! # ss-faltings: the height rows off SGA 7 IX Cor. 3.3, through the stable Faltings height

Task ss-faltings (docs/research/ss-faltings.md). The bundle field `sga7_IX_Cor3_3_Def34` (SGA 7 IX Cor. 3.3) reaches the
proof only through height-split's SS2 (`ZInQ.HeightSplit.SemistableNeronBaseChange`), SS3
(`ZInQ.HeightSplit.SemistablePersists`) and the global form of SS1 (`ZInQ.HeightSplit.SemistableReductionThm`, whose
proof `GapNeron.ss1_ss3_of_cpNF` uses persistence twice). Their readers are the height rows R18, R19, R21, R22,
`StableHeightFinite` and the lower half of R20 (TailY's `r18_of_leaves`, `r19_of_leaves`, `r21_of_leaves'`,
`r22_of_upper`, `stableHeightFinite_of'`, `r20Lower_of_leaves'`). They use

* SS2 only through `stableFaltingsHeight_eq_of_semistable` (TailY): the kernel's stable height is the height of any
  semistable Néron model. That needs only the **invariance of the height of a semistable Néron model under finite
  extension**, which is Faltings' statement for semiabelian schemes (Faltings 1983 §3, p. 354; the manuscript
  uses it uncited at diophantine_zq.tex L596-598) read for Néron models: the leaf
  `FaltingsSemistableHeightBC` (§1 of this file), weaker than SS2
  (`faltingsSemistableHeightBC_of_ss2`);
* SS1 and SS3 only to find, for two abelian varieties, one field over which both are semistable (`r20Lower`), or one
  semistable field (identification). Raynaud's criterion (the bundle's Raynaud leaf, Silverberg–Zarhin Thm 3.5 as
  cited at L816) gives more: `A` is semistable over **every** number field containing `K(A[15])`
  (`semistableReductionThmIF_of_raynaud`, §2), with no persistence statement.

§3 re-proves the six rows from these. No `sorry`, no `axiom`. -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.SSFaltings

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.H5Neron ZInQ.HeightSplit

/-! ## §1. The leaf: Faltings' invariance of the semistable height -/

/-- **Leaf (Faltings 1983 §3, p. 354; page read 11-17 by the reading desk).** If `A_L` has semistable reduction
everywhere
(its Néron model `𝒩` over `𝓞_L` is semistable, height-split's `IsSemistable`), then for every finite extension `L'/L`
the Néron model `𝒩'` of `A_{L'}` has the same height (the kernel's `GroupModel.height`: the metrized Hodge line
`⋀^g ω`, metric `(i/2)^g ∫ η ∧ η̄`, degree normalized by `[L:ℚ]`, Faltings' normalization, p. 351). Faltings
prints, for a semiabelian scheme over the ring of integers, that its height is invariant under extension of the
base field (§3, p. 354, without a citation; see also p. 351 Bem. b) and p. 350 Lemma 1). The leaf is stated for
the Néron models `𝒩`, `𝒩'`, assuming semistability only of `𝒩`; linking it to the print needs
`𝒩'^0 ≅ (𝒩^0)_{𝓞_{L'}}` under semistability, which is SGA 7 IX Cor. 3.3 (or BLR 7.4/3), cited neither by
Faltings there nor by the manuscript: that content is part of this leaf (consequence, GLUE).
The manuscript uses it uncited at
diophantine_zq.tex L596-598 and cites Faltings 1983 (bibitem `faltings1983`, L11084-11086) at L621 and L733. Weaker
than SS2 (`faltingsSemistableHeightBC_of_ss2`). -/
def FaltingsSemistableHeightBC : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] (𝒩 : GroupModel A L), 𝒩.IsNeronModel → IsSemistable 𝒩 →
    ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
      (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel → 𝒩'.height = 𝒩.height

/-- **The leaf is a consequence of SS2** (with the kernel's proved base-change and open-subgroup height lemmas): it is
not stronger than the row it replaces. -/
theorem faltingsSemistableHeightBC_of_ss2 (hSS2 : SemistableNeronBaseChange) :
    FaltingsSemistableHeightBC := by
  intro K _ _ A L _ _ _ 𝒩 h𝒩 hss L' _ _ _ _ _ 𝒩' h𝒩'
  obtain ⟨𝒰, 𝒱, h𝒱, h𝒰𝒩, h𝒰𝒱⟩ := hSS2 K A L 𝒩 h𝒩 hss L' 𝒩' h𝒩'
  calc 𝒩'.height = 𝒰.height := (Contrib.HeightBC.openSubgroupHeight K A L' 𝒰 𝒩' h𝒰𝒩).symm
    _ = 𝒱.height := Contrib.HeightBC.openSubgroupHeight K A L' 𝒰 𝒱 h𝒰𝒱
    _ = 𝒩.height := Contrib.HeightBC.modelHeightBaseChange K A L L' 𝒩 𝒱 h𝒱

/-! ## §2. Semistability over every field containing `K(A[15])`, from Raynaud's criterion -/

/-- **Semistable reduction over every large field** (glue, proved below from Raynaud's criterion): for `A` over a
number field `K` there is a finite `K₀ ⊆ K̄` such that over every number field `K₀ ⊆ L ⊆ K̄` every Néron model of
`A_L` is semistable. It implies SS1 (`semistableReductionThm_of_IF`) and replaces SS1 + SS3 in the readers. -/
def SemistableReductionThmIF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K),
    ∃ K₀ : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K₀ ∧
      ∀ (L : IntermediateField K (AlgebraicClosure K)) [NumberField L], K₀ ≤ L →
        ∀ 𝒩 : GroupModel A L, 𝒩.IsNeronModel → IsSemistable 𝒩

/-- SS1 from the strong form. -/
theorem semistableReductionThm_of_IF (h : SemistableReductionThmIF) : SemistableReductionThm := by
  intro K _ _ A
  obtain ⟨K₀, hfin, hK₀⟩ := h K A
  haveI : NumberField K₀ := NumberField.of_module_finite K K₀
  exact ⟨K₀, inferInstance, inferInstance, inferInstance, hK₀ K₀ le_rfl⟩

/-- `3` or `5` is a unit in a local ring (`3 · 2 - 5 = 1`): the manuscript's choice `A[3]`, or `A[5]` when the
residue characteristic is `3` (diophantine_zq.tex L814). -/
theorem exists_three_or_five_isUnit {R : Type} [CommRing R] [IsLocalRing R] :
    ∃ m : ℕ, (m = 3 ∨ m = 5) ∧ IsUnit (m : R) := by
  by_cases h3 : IsUnit ((3 : ℕ) : R)
  · exact ⟨3, Or.inl rfl, h3⟩
  · refine ⟨5, Or.inr rfl, ?_⟩
    have h1 : IsUnit (((3 : ℕ) : R) * 2 + -((5 : ℕ) : R)) := by
      rw [show ((3 : ℕ) : R) * 2 + -((5 : ℕ) : R) = 1 by push_cast; ring]
      exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
    · exact absurd (isUnit_of_mul_isUnit_left h) h3
    · exact IsUnit.neg_iff _ |>.mp h

open ReductSplit ReductGlue ReductB ZInQ.Contrib.AbVarBC GapNeron in
/-- **`SemistableReductionThmIF` from Raynaud's criterion** (`ReductSplit.RaynaudSemistable`, the bundle's Raynaud
leaf through `ReductB.raynaudSemistable_of_SH_pair`), Mumford's torsion count and `[m]` étale (textbook fields),
Néron models over the DVRs of a number field (from N1) and the proved local-global glue. `K₀` is a finite field of
definition of `A(K̄)[15]`. Over `K₀ ⊆ L`, at a DVR `O` of `L` take `m ∈ {3, 5}` invertible in `O` (L814's choice); the points of
order `m ∣ 15` of `A_L` are `L`-rational (`torsion_descends_etale`, `fixedTorsionRational_inter`), so Raynaud's
criterion gives semistable reduction at `O`. The proof of `ReductB.semistableReductionDVRnf_of_raynaudCP` with one
`K₀` for all places and all `L ⊇ K₀`. -/
theorem semistableReductionThmIF_of_raynaud (hR : RaynaudSemistable)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme)
    (hN : NeronSchemeModelExistsDVRNF) (hLG : SemistableLocalGlobal) : SemistableReductionThmIF := by
  intro K _ _ A
  have h12 : ((15 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
  obtain ⟨K₀, hfin, hfix⟩ :=
    torsionFieldOfDefinition_of (AvSplit.torsionStructure_of_mumford hM) K A 15 h12
  refine ⟨K₀, hfin, fun L _ hle 𝒩 h𝒩 => ?_⟩
  rw [hLG K A L 𝒩 h𝒩]
  intro O hO
  haveI := hO
  obtain ⟨m, hm34, hmu⟩ := exists_three_or_five_isUnit (R := O)
  have hm3 : 3 ≤ m := by rcases hm34 with rfl | rfl <;> norm_num
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr (by rcases hm34 with rfl | rfl <;> norm_num)
  have hm12 : ∀ p : A.Pt (AlgebraicClosure K), p ^ m = 1 → p ^ 15 = 1 := by
    intro p hp
    rcases hm34 with rfl | rfl
    · rw [show (15 : ℕ) = 3 * 5 by norm_num, pow_mul, hp, one_pow]
    · rw [show (15 : ℕ) = 5 * 3 by norm_num, pow_mul, hp, one_pow]
  refine hasSemistableReduction_ofNF hN O _ (hR L O (A.baseChange L) m hm3 hmu ?_)
  intro x hx
  haveI : Algebra.IsAlgebraic L (AlgebraicClosure K) := Algebra.IsAlgebraic.tower_top (K := K) L
  haveI : Module.IsTorsionFree L (AlgebraicClosure L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap L (AlgebraicClosure L)).injective
  haveI : Module.IsTorsionFree L (AlgebraicClosure K) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap L (AlgebraicClosure K)).injective
  let κ' : AlgebraicClosure K →ₐ[L] AlgebraicClosure L := IsAlgClosed.lift
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := κ'.restrictScalars K
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A κ m hmK x hx
  obtain ⟨z, hz⟩ := fixedTorsionRational_inter hE L A m hmK p hp
    (fun σ hσ => hfix σ (fun y hy => hσ y (hle hy)) p (hm12 p hp))
  refine ⟨(bcPt A L).symm z, ?_⟩
  rw [← hpx, ← hz]
  apply (bcPt A (AlgebraicClosure L)).injective
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt]
  have hκ : AlgHom.restrictScalars K (Algebra.ofId L (AlgebraicClosure L)) = κ.comp L.val := by
    refine AlgHom.ext fun a => ?_
    exact (κ'.commutes a).symm
  rw [hκ]

/-! ## §3. The identification and the rows over the leaf -/

section Identification

variable (hN1 : NeronModelExists) (hF : FaltingsSemistableHeightBC)

include hN1 hF in
/-- **The kernel's stable height is the height of any semistable Néron model**, from N1 and Faltings' invariance
(TailY's `stableFaltingsHeight_eq_of_semistable` with `hF` in place of SS2 and the two open-subgroup steps). -/
theorem stableFaltingsHeight_eq_of_semistableF {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) {L₀ : Type} [Field L₀] [NumberField L₀] [Algebra K L₀]
    (𝒩₀ : GroupModel A L₀) (h𝒩₀ : 𝒩₀.IsNeronModel) (hss : IsSemistable 𝒩₀) :
    stableFaltingsHeight A = 𝒩₀.height := by
  rw [stableFaltingsHeight_eq_iInf_height]
  refine le_antisymm (iInf_le_of_le (FinExt.mk L₀) (iInf_le_of_le 𝒩₀ le_rfl)) ?_
  refine le_iInf fun E => le_iInf fun 𝒢 => ?_
  obtain ⟨L', j1, j2, j3, j4, j5, t1, t2⟩ := compositum K E.L L₀
  obtain ⟨𝒢', h𝒢'⟩ := groupModelBaseChangeExists K A E.L L' 𝒢
  obtain ⟨𝒩', h𝒩'⟩ := hN1 K A L'
  calc 𝒩₀.height = 𝒩'.height := (hF K A L₀ 𝒩₀ h𝒩₀ hss L' 𝒩' h𝒩').symm
    _ ≤ 𝒢'.height := Contrib.HeightBC.neronModelMinimal K A L' 𝒩' 𝒢' h𝒩'
    _ = 𝒢.height := Contrib.HeightBC.modelHeightBaseChange K A E.L L' 𝒢 𝒢' h𝒢'

include hN1 hF in
/-- Published height ⇒ kernel height. -/
theorem stableFaltingsHeight_eq_of_isStableFaltingsHeightF {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {x : ℝ} (h : IsStableFaltingsHeight A x) :
    stableFaltingsHeight A = (x : EReal) := by
  obtain ⟨L, i1, i2, i3, 𝒩, h𝒩, hss, hx⟩ := h
  rw [stableFaltingsHeight_eq_of_semistableF hN1 hF A 𝒩 h𝒩 hss, hx]

include hN1 hF in
/-- **Independence of the field** (the published definition is well posed). -/
theorem isStableFaltingsHeight_uniqueF {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {x y : ℝ} (hx : IsStableFaltingsHeight A x) (hy : IsStableFaltingsHeight A y) : x = y := by
  have := (stableFaltingsHeight_eq_of_isStableFaltingsHeightF hN1 hF hx).symm.trans
    (stableFaltingsHeight_eq_of_isStableFaltingsHeightF hN1 hF hy)
  exact_mod_cast this

variable (hSS1 : SemistableReductionThm)

include hN1 hF hSS1 in
/-- A semistable Néron model over some field, whose height is the kernel's stable height. -/
theorem exists_semistable_neronF {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ IsSemistable 𝒩₀ ∧ stableFaltingsHeight A = 𝒩₀.height := by
  obtain ⟨L₀, i1, i2, i3, hL₀⟩ := hSS1 K A
  obtain ⟨𝒩₀, h𝒩₀⟩ := hN1 K A L₀
  exact ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, hL₀ 𝒩₀ h𝒩₀,
    stableFaltingsHeight_eq_of_semistableF hN1 hF A 𝒩₀ h𝒩₀ (hL₀ 𝒩₀ h𝒩₀)⟩

include hN1 hF hSS1 in
/-- **H5 identification**: for a real `x`, the kernel's `stableFaltingsHeight A = x` iff `x` is Faltings'
(published) stable height of `A`. -/
theorem isStableFaltingsHeight_iffF {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (x : ℝ) : IsStableFaltingsHeight A x ↔ stableFaltingsHeight A = (x : EReal) := by
  refine ⟨stableFaltingsHeight_eq_of_isStableFaltingsHeightF hN1 hF, fun hx => ?_⟩
  obtain ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, hss, he⟩ := exists_semistable_neronF hN1 hF hSS1 A
  exact ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, hss, he.symm.trans hx⟩

end Identification

section Rows

variable {K : Type} [Field K]

/-- **`stableFaltingsHeight A ≠ ⊥`** (TailY's `stableFaltingsHeight_ne_bot`, `hF` for SS2). -/
theorem stableFaltingsHeight_ne_botF (hN1 : NeronModelExists) (hSS1 : SemistableReductionThm)
    (hF : FaltingsSemistableHeightBC) (hU : AnalyticUniformizationUnique)
    (hD : MetrizedDimUnique) [NumberField K] (A : PkgI3.AbVar K) : stableFaltingsHeight A ≠ ⊥ := by
  obtain ⟨L₀, i1, i2, i3, 𝒩₀, -, -, he⟩ := exists_semistable_neronF hN1 hF hSS1 A
  rw [he]
  by_cases hM : ∃ (g : ℕ) (M : MetrizedModel A L₀ g), M.model = 𝒩₀
  · obtain ⟨g, M, rfl⟩ := hM
    rw [groupModel_height_eq hU hD M]
    exact EReal.coe_ne_bot _
  · push Not at hM
    have htop : 𝒩₀.height = ⊤ :=
      le_antisymm le_top (le_iInf fun g => le_iInf fun M => le_iInf fun h => absurd h (hM g M))
    rw [htop]
    exact top_ne_bot

/-- **H-19: `StableHeightFinite`** (TailY's `stableHeightFinite_of'`, `hF` for SS2). -/
theorem stableHeightFinite_ofF (hN1 : NeronModelExists) (hSS1 : SemistableReductionThm)
    (hF : FaltingsSemistableHeightBC) (hMet : NeronMetrizable)
    (hU : AnalyticUniformizationUnique) : StableHeightFinite :=
  fun _ _ _ A => ⟨stableFaltingsHeight_ne_top hN1 hMet A,
    stableFaltingsHeight_ne_botF hN1 hSS1 hF hU metrizedDimUnique A⟩

/-- **H-17: R21** (TailY's `r21_of_leaves'`, `hF` for SS2). -/
theorem r21_of_leavesF (hB : BostLowerBound) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hF : FaltingsSemistableHeightBC)
    (hU : AnalyticUniformizationUnique) : R21_Bost := by
  intro K _ _ A g hg
  by_cases ht : stableFaltingsHeight A = ⊤
  · rw [ht]; exact le_top
  obtain ⟨x, hx⟩ := exists_real_of_ne _ ht
    (stableFaltingsHeight_ne_botF hN1 hSS1 hF hU metrizedDimUnique A)
  rw [hx]
  exact EReal.coe_le_coe_iff.mpr (by
    have := grBostBound_of_bost hB K A g hg x ((isStableFaltingsHeight_iffF hN1 hF hSS1 A x).mpr hx)
    linarith)

/-- **H-14: R18** (TailY's `r18_of_leaves`, `hF` for SS2). -/
theorem r18_of_leavesF (hJ : JavanpeykarBound) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hF : FaltingsSemistableHeightBC)
    (hMet : NeronMetrizable) : LeafPush2.R18_Javanpeykar := by
  intro K _ _ X _ _ P₀ J aj hJac g hg hg1 t ht d hd hd0
  by_cases hb : stableFaltingsHeight J = ⊥
  · rw [hb]; exact bot_le
  obtain ⟨x, hx⟩ := exists_real_of_ne _ (stableFaltingsHeight_ne_top hN1 hMet J) hb
  rw [hx]
  exact EReal.coe_le_coe_iff.mpr (hJ K X P₀ J aj hJac g hg hg1 t ht d hd hd0 x
    ((isStableFaltingsHeight_iffF hN1 hF hSS1 J x).mpr hx))

/-- **H-18: R22** (TailY's `r22_of_upper`, `hF` for SS2). -/
theorem r22_of_upperF (hP : PazukiCor13Upper) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hF : FaltingsSemistableHeightBC) :
    LeafPush2.R22_Pazuki := by
  intro K _ _ A hA x hx X hX σ Λ Φ hΦ Ω hΩ hPer F _ _ emb z c hc hz
  have h := hP K A hA x ((isStableFaltingsHeight_iffF hN1 hF hSS1 A x).mpr hx) σ Λ Φ hΦ Ω hΩ hPer
    F emb z c hc hz
  exact (absLogHeight_le_absLogHeightL2 z).trans
    (pazuki_upper_of_upper ZInQ.HeightSplit.pazukiC2_nonneg hX h)

/-- **H-15: R19** (TailY's `r19_of_leaves`, `hF` for SS2). -/
theorem r19_of_leavesF (hGR : GaudronRemondThm14) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hF : FaltingsSemistableHeightBC) : R19_GaudronRemond :=
  fun K _ _ A B g x hg hx hiso =>
    hGR K A B g x hg ((isStableFaltingsHeight_iffF hN1 hF hSS1 A x).mpr hx) hiso

/-- **The lower half of R20** (TailY's `r20Lower_of_leaves'`) from the lower half of Faltings' Lemma 5 for base
changes, N1, Faltings' invariance and `SemistableReductionThmIF`: both heights are computed on Néron models over
`K_A ⊔ K_B ⊆ K̄`, where `A` and `B` are semistable (no persistence statement). -/
theorem r20Lower_of_leavesF (hF5 : FaltingsLemma5BCLower) (hN1 : NeronModelExists)
    (hSS : SemistableReductionThmIF) (hF : FaltingsSemistableHeightBC) :
    ∀ (K : Type) [Field K] [NumberField K] (A B : _root_.ZInQ.DefFaltings.AbVar K) (φ : A.X ⟶ B.X),
      _root_.ZInQ.DefFaltings.IsIsogeny φ →
      ∀ x y : ℝ, _root_.ZInQ.DefFaltings.stableFaltingsHeight A = x →
        _root_.ZInQ.DefFaltings.stableFaltingsHeight B = y →
        -((1 / 2) * Real.log (_root_.ZInQ.DefFaltings.isogDeg φ)) ≤ x - y := by
  intro K _ _ A B φ hφ x y hx hy
  obtain ⟨KA, hA1, hKA⟩ := hSS K A
  obtain ⟨KB, hB1, hKB⟩ := hSS K B
  haveI := hA1
  haveI := hB1
  let L : IntermediateField K (AlgebraicClosure K) := KA ⊔ KB
  haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_sup KA KB
  haveI : NumberField L := NumberField.of_module_finite K L
  obtain ⟨𝒩A, hA⟩ := hN1 K A L
  obtain ⟨𝒩B, hB⟩ := hN1 K B L
  have sA : IsSemistable 𝒩A := hKA L le_sup_left 𝒩A hA
  have sB : IsSemistable 𝒩B := hKB L le_sup_right 𝒩B hB
  have hxA : 𝒩A.height = x := (stableFaltingsHeight_eq_of_semistableF hN1 hF A 𝒩A hA sA).symm.trans hx
  have hyB : 𝒩B.height = y := (stableFaltingsHeight_eq_of_semistableF hN1 hF B 𝒩B hB sB).symm.trans hy
  exact hF5 K A B φ hφ L 𝒩A 𝒩B hA hB sA sB x y hxA hyB

end Rows

end ZInQ.SSFaltings

import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.CoefResidualCounts
import ZInQKernel.Contrib.CloudB3RC53.ContBridge.Discrete

/-!
# Nonzero residual interfaces

The full local condition has an acyclic identity cone. Its genuine Selmer
complex therefore computes global continuous cohomology. A field-valued
complex admits an actual map from its cohomology with zero differential.
These two facts supply the cochain comparison, not just dimension equalities.

The small curve is y² = x(x − 11)(x + 33), at coefficient index zero.
Global finiteness and vanishing, when used, are the existing explicit
Milne inputs from manuscript lines 4525–4531, not additional axioms.
-/

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace ZInQ.Contrib.RC53Assist.ResidualWitness

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules
  ZInQ.Manuscript.RC.HeegnerAlgebra

section Formality

variable {k : Type} [Field k]

/-- The genuine cohomology of a complex, with zero differentials. -/
def homologyModel (C : CochainComplex (ModuleCat.{0} k) ℤ) : GCx k where
  X n := C.homology n
  d _ _ _ := 0
  d_d _ _ _ _ _ _ := rfl

private theorem homologyModel_d (C : CochainComplex (ModuleCat.{0} k) ℤ)
    (i j : ℤ) : (homologyModel C).toCC.d i j = 0 := by
  dsimp [GCx.toCC, homologyModel]
  split_ifs <;> rfl

/-- A linear section of the projection from genuine cycles to homology. -/
def cycleSection (C : CochainComplex (ModuleCat.{0} k) ℤ) (n : ℤ) :
    C.homology n ⟶ C.cycles n :=
  Projective.factorThru (𝟙 (C.homology n)) (C.homologyπ n)

private theorem cycleSection_π (C : CochainComplex (ModuleCat.{0} k) ℤ) (n : ℤ) :
    cycleSection C n ≫ C.homologyπ n = 𝟙 _ :=
  Projective.factorThru_comp _ _

/-- The actual cochain map obtained by choosing linear representatives of classes. -/
def homologyModelTo (C : CochainComplex (ModuleCat.{0} k) ℤ) :
    (homologyModel C).toCC ⟶ C where
  f n := cycleSection C n ≫ C.iCycles n
  comm' i j _ := by
    rw [homologyModel_d, zero_comp, Category.assoc, HomologicalComplex.iCycles_d,
      comp_zero]

/-- Field-valued formality, with an actual quasi-isomorphism into the complex. -/
theorem homologyModelTo_quasiIso (C : CochainComplex (ModuleCat.{0} k) ℤ) :
    QuasiIso (homologyModelTo C) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := (homologyModel C).toCC
  have : IsIso (H.iCycles n) :=
    H.isIso_iCycles n (n + 1) (by simp) (homologyModel_d C n (n + 1))
  have : IsIso (H.homologyπ n) :=
    H.isIso_homologyπ (n - 1) n (by simp) (homologyModel_d C (n - 1) n)
  have hcyc : HomologicalComplex.cyclesMap (homologyModelTo C) n =
      H.iCycles n ≫ cycleSection C n := by
    apply (cancel_mono (C.iCycles n)).1
    rw [HomologicalComplex.cyclesMap_i, Category.assoc]
    rfl
  have hmap : H.homologyπ n ≫
      HomologicalComplex.homologyMap (homologyModelTo C) n = H.iCycles n := by
    rw [HomologicalComplex.homologyπ_naturality, hcyc, Category.assoc, cycleSection_π]
    rfl
  have : IsIso (H.homologyπ n ≫
      HomologicalComplex.homologyMap (homologyModelTo C) n) := by
    rw [hmap]
    infer_instance
  exact IsIso.of_isIso_comp_left (H.homologyπ n) _

end Formality

section NaturalHomology

variable {k : Type} [CommRing k]

private theorem extension_d_neg (C : CochainComplex (ModuleCat.{0} k) ℕ) :
    (natCx C).toCC.d (-1) 0 = 0 := by
  ext x
  exact GCx.toCC_d_hom (natCx C) (-1) 0 (by omega) x

private def zeroScHom (C : CochainComplex (ModuleCat.{0} k) ℕ) :
    (natCx C).toCC.sc' (-1) 0 1 ⟶ C.sc' 0 0 1 where
  τ₁ := 0
  τ₂ := 𝟙 (C.X 0)
  τ₃ := 𝟙 (C.X 1)
  comm₁₂ := by
    rw [zero_comp]
    change 0 = (natCx C).toCC.d (-1) 0 ≫ 𝟙 _
    rw [Category.comp_id, extension_d_neg]
  comm₂₃ := by
    ext x
    exact (GCx.toCC_d_hom (natCx C) 0 1 rfl x).trans rfl

private def zeroCyclesMap (C : CochainComplex (ModuleCat.{0} k) ℕ) :
    (natCx C).toCC.cycles 0 ⟶ C.cycles 0 :=
  ((natCx C).toCC.cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).hom ≫
    ShortComplex.cyclesMap (zeroScHom C) ≫
    (C.cyclesIsoSc' 0 0 1 (by simp) (by simp)).inv

private def zeroHomologyIso (C : CochainComplex (ModuleCat.{0} k) ℕ) :
    (natCx C).toCC.homology 0 ≅ C.homology 0 := by
  have : IsIso (ShortComplex.cyclesMap (zeroScHom C)) :=
    ShortComplex.isIso_cyclesMap_of_isIso_of_mono' _
      (by change IsIso (𝟙 _); infer_instance) (by change Mono (𝟙 _); infer_instance)
  have : IsIso (zeroCyclesMap C) := by unfold zeroCyclesMap; infer_instance
  exact ((natCx C).toCC.isoHomologyπ (-1) 0 (by simp) (extension_d_neg C)).symm ≪≫
    asIso (zeroCyclesMap C) ≪≫ C.isoHomologyπ 0 0 (by simp) (C.shape 0 0 (by simp))

/-- Homology is unchanged by genuine extension of natural cochains by zero. -/
def natHomologyIso (C : CochainComplex (ModuleCat.{0} k) ℕ) (n : ℕ) :
    (natCx C).toCC.homology (n : ℤ) ≅ C.homology n := by
  cases n with
  | zero => exact zeroHomologyIso C
  | succ n =>
    let e : (natCx C).toCC.sc' (n : ℤ) ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ) ≅
        C.sc' n (n + 1) (n + 2) :=
      ShortComplex.isoMk (Iso.refl (C.X n)) (Iso.refl (C.X (n + 1)))
        (Iso.refl (C.X (n + 2)))
        (by
          ext x
          exact (GCx.toCC_d_hom (natCx C) (n : ℤ) ((n + 1 : ℕ) : ℤ)
            (by omega) x).trans rfl |>.symm)
        (by
          ext x
          exact (GCx.toCC_d_hom (natCx C) ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)
            (by omega) x).trans rfl |>.symm)
    exact (natCx C).toCC.homologyIsoSc' (n : ℤ) ((n + 1 : ℕ) : ℤ)
        ((n + 2 : ℕ) : ℤ) (by simp) (by simp; omega) ≪≫
      ShortComplex.homologyMapIso e ≪≫
      (C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).symm

private theorem natHomology_negative (C : CochainComplex (ModuleCat.{0} k) ℕ)
    (n : ℤ) (hn : n < 0) : Subsingleton ((natCx C).toCC.homology n) := by
  have : Subsingleton ((natCx C).toCC.X n) := by
    cases n with
    | ofNat m => simp only [Int.ofNat_eq_natCast] at hn; omega
    | negSucc m => exact inferInstanceAs (Subsingleton PUnit.{1})
  have : Subsingleton (((natCx C).toCC.sc n).X₂) :=
    inferInstanceAs (Subsingleton ((natCx C).toCC.X n))
  have hex : (natCx C).toCC.ExactAt n :=
    ((natCx C).toCC.sc n).exact_of_isZero_X₂ (ModuleCat.isZero_of_subsingleton _)
  exact ModuleCat.subsingleton_of_isZero
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hex)

end NaturalHomology

/-- The imaginary quadratic field Q(i). -/
abbrev SmallK := CyclotomicField 4 ℚ

local instance : IsCyclotomicExtension {4} ℚ SmallK := by
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  exact CyclotomicField.isCyclotomicExtension 4 ℚ

private theorem smallK_degree : Module.finrank ℚ SmallK = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 4) SmallK
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

private theorem smallK_complex : IsTotallyComplex SmallK :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) _ (by norm_num)

/-- An integral square root of minus one. -/
def smallAlpha : 𝓞 SmallK :=
  ⟨IsCyclotomicExtension.zeta 4 ℚ SmallK,
    (IsCyclotomicExtension.zeta_spec 4 ℚ SmallK).isIntegral (by norm_num)⟩

private theorem smallAlpha_sq : smallAlpha ^ 2 = (-1 : 𝓞 SmallK) := by
  apply Subtype.ext
  have h : IsPrimitiveRoot (IsCyclotomicExtension.zeta 4 ℚ SmallK ^ 2) 2 := by
    simpa using (IsCyclotomicExtension.zeta_spec 4 ℚ SmallK).pow_of_dvd
      (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (2 : ℕ) ∣ 4)
  exact h.eq_neg_one_of_two_right

private theorem smallAlpha_radicand : IsQuadraticRadicand SmallK (-1) smallAlpha :=
  ⟨smallK_degree, by simpa using smallAlpha_sq,
    IsCyclotomicExtension.adjoin_primitive_root_eq_top
      (IsCyclotomicExtension.zeta_spec 4 ℚ SmallK)⟩

/-- The least admissible positive curve parameter. -/
theorem eleven_admissible :
    0 < (11 : ℕ) ∧ Squarefree (11 : ℕ) ∧ 11 % 12 = 11 ∧
      ∀ ℓ : ℕ, ℓ % 12 = 11 → 11 ≤ ℓ := by
  refine ⟨by decide, (show Nat.Prime 11 by decide).squarefree, by decide, ?_⟩
  intro ℓ hℓ
  have := Nat.mod_le ℓ 12
  omega

/-- The actual curve E₁₁, not a replacement finite module. -/
def SmallE : WeierstrassCurve SmallK := cubicCurve 0 11 (-33)

private theorem smallE_roots :
    (0 : SmallK) ≠ 11 ∧ (0 : SmallK) ≠ -33 ∧ (11 : SmallK) ≠ -33 := by
  norm_num

private theorem smallE_elliptic : SmallE.IsElliptic :=
  isElliptic_cubicCurve smallE_roots.1 smallE_roots.2.1 smallE_roots.2.2

/-- At index zero every support has full required torsion and trivial genuine action. -/
theorem smallE_residual_hypotheses (S : Set (HeightOneSpectrum (𝓞 SmallK))) :
    FullTorsion SmallK S SmallE (2 ^ (0 + 1)) ∧
      FullTorsion SmallK S SmallE (2 ^ 0) ∧ FullTorsion SmallK S SmallE 2 ∧
      ∀ (σ : GKS SmallK S) (P : TorsS SmallK S SmallE ((2 : ℕ) : ℤ)), σ • P = P :=
  residualFin2_hyps_cubicCurve smallE_roots.1 smallE_roots.2.1 smallE_roots.2.2

open ZInQ.Manuscript.RC.Limits

/-- Charged support containing all bad primes of the displayed integral equation. -/
def SmallS : Set (HeightOneSpectrum (𝓞 SmallK)) :=
  primesAboveSet SmallK (chargedPrimes 66 5 ∅)

private theorem smallS_finite : SmallS.Finite :=
  primesAboveSet_finite SmallK _
    (ne_zero_of_mem_chargedPrimes (by decide) (by decide) (by simp))

private theorem smallS_above_two (v : HeightOneSpectrum (𝓞 SmallK))
    (hv : (2 : 𝓞 SmallK) ∈ v.asIdeal) : v ∈ SmallS :=
  two_mem_primesAboveSet SmallK (two_mem_chargedPrimes (by decide)) v hv

private theorem smallSetting : NekovarFiniteSetting SmallK SmallS 2 (ZMod 2) where
  prime := Nat.prime_two
  finite_S := smallS_finite
  above_p := smallS_above_two
  condP _ := smallK_complex
  finite_R := inferInstance
  nilpotent_p := ⟨1, by decide⟩
  selfInjective := Module.injective_of_isSemisimpleRing (ZMod 2) (ZMod 2)

/-- The trivial character at the first genuine coefficient stage. -/
def smallCharacter : GKS SmallK SmallS →* (Acoef (0 + 1))ˣ := 1

abbrev SmallM : Type := ResidualM SmallE 0 smallCharacter

private theorem smallTorsion :
    FullTorsion SmallK SmallS SmallE (2 ^ (0 + 1)) ∧
      FullTorsion SmallK SmallS SmallE (2 ^ 0) ∧ FullTorsion SmallK SmallS SmallE 2 ∧
      ∀ (σ : GKS SmallK SmallS) (P : TorsS SmallK SmallS SmallE ((2 : ℕ) : ℤ)), σ • P = P :=
  smallE_residual_hypotheses SmallS

instance : ContinuousSMul (GKS SmallK SmallS) SmallM :=
  continuousSMul_residualM SmallE 0 smallCharacter smallTorsion.1 smallTorsion.2.1
    smallTorsion.2.2.1 smallTorsion.2.2.2

instance : Finite SmallM :=
  finite_residualM SmallE 0 smallCharacter smallTorsion.1 smallTorsion.2.1 smallTorsion.2.2.1

/-- Actual residual coefficients identified with the trivial two-dimensional module. -/
def smallMEquiv : SmallM ≃ₗ[ZMod 2] Wgen SmallK SmallS :=
  residualMEquivWgen SmallE 0 smallCharacter smallTorsion.1 smallTorsion.2.1 smallTorsion.2.2.1

/-- The actual residual representation has four elements, dimension two, and trivial action. -/
theorem smallM_facts : Nat.card SmallM = 4 ∧ Module.finrank (ZMod 2) SmallM = 2 ∧
    ∀ (σ : GKS SmallK SmallS) (x : SmallM), σ • x = x := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_congr smallMEquiv.toEquiv]
    change Nat.card (ZMod 2 × ZMod 2) = 4
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
  · exact smallMEquiv.finrank_eq.trans (finrank_zmod2_sq)
  · exact smul_residualM_eq SmallE 0 smallCharacter smallTorsion.1 smallTorsion.2.1
      smallTorsion.2.2.1 smallTorsion.2.2.2

/-- The full conditions are actual local cochain complexes with the identity maps. -/
def smallConditions : GaloisLocalConditions SmallK SmallS (ZMod 2) SmallM :=
  relaxedConditions (ZMod 2) (GKS SmallK SmallS) (fun v : Places SmallK SmallS => Gloc SmallK v.1)
    (fun v => locMap SmallK SmallS v.1) SmallM

/-- Genuine support data, with equal supports and no new places. -/
def smallSupportData : SupportChangeData (ZMod 2) :=
  galoisSupportData SmallK (subset_refl SmallS) (ZMod 2) SmallM
    (fun q => absurd q.2.1 q.2.2) (fun q => absurd q.2.1 q.2.2) smallConditions

abbrev smallGlobal : GCx (ZMod 2) := globalCx (ZMod 2) (GKS SmallK SmallS) SmallM

/-- The residual diagram after cancellation of the genuine full-condition identity cone. -/
def smallResidualData : SelData (ZMod 2) :=
  ZInQ.Contrib.CloudB3RC53.Torsion.modelSel (homologyModel smallGlobal.toCC)

abbrev smallP : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ :=
  (selCx smallResidualData).toCC

/-- Every nonzero global degree is counted; this is not an empty-degree witness. -/
def smallDegrees : Finset ℤ := Finset.Icc 0 2

/-- The actual-coefficient identification of a global term in a natural degree. -/
def smallActualHEquiv (n : ℕ) : smallGlobal.toCC.homology (n : ℤ) ≃ₗ[ZMod 2]
    contCohomology (ZMod 2) (GKS SmallK SmallS) SmallM n :=
  (natHomologyIso (contCochains (ZMod 2) (GKS SmallK SmallS) SmallM) n).toLinearEquiv

/-- The genuine-coefficient identification of the same global term. -/
def smallGlobalHEquiv (n : ℕ) : smallGlobal.toCC.homology (n : ℤ) ≃ₗ[ZMod 2]
    genH SmallK SmallS n :=
  (smallActualHEquiv n).trans
    (residualCohIso SmallE 0 smallCharacter smallTorsion.1 smallTorsion.2.1
      smallTorsion.2.2.1 smallTorsion.2.2.2 n).toLinearEquiv

/-- The precise eGact argument of the actual-coefficient constructor. -/
def smallEGact (n : ℤ) (hn : n ∈ smallDegrees) : smallResidualData.G.X n ≃ₗ[ZMod 2]
    contCohomology (ZMod 2) (GKS SmallK SmallS) SmallM n.toNat := by
  change smallGlobal.toCC.homology n ≃ₗ[ZMod 2] _
  have h0 : 0 ≤ n := (Finset.mem_Icc.mp hn).1
  have hcast : (n.toNat : ℤ) = n := by omega
  rw [← hcast]
  exact smallActualHEquiv n.toNat

/-- The precise eG argument of the genuine-coefficient constructor. -/
def smallEG (n : ℤ) (hn : n ∈ smallDegrees) : smallResidualData.G.X n ≃ₗ[ZMod 2]
    genH SmallK SmallS n.toNat := by
  change smallGlobal.toCC.homology n ≃ₗ[ZMod 2] _
  have h0 : 0 ≤ n := (Finset.mem_Icc.mp hn).1
  have hcast : (n.toNat : ℤ) = n := by omega
  rw [← hcast]
  exact smallGlobalHEquiv n.toNat

private def allGenHEquiv (n : ℕ) : genH SmallK SmallS n ≃ₗ[ZMod 2]
    continuousCohomology n (Wrep SmallK SmallS) := by
  have : LocallyCompactSpace (GKS SmallK SmallS) := locallyCompactSpace_GS SmallK SmallS
  have : ContinuousSMul (ZMod 2) (Wgen SmallK SmallS) :=
    ZInQ.Contrib.CloudB3RC53.ContBridge.continuousSMul_of_discrete (ZMod 2) (Wgen SmallK SmallS)
  exact (ZInQ.Contrib.CloudB3RC53.ContBridge.contCohomologyLinearEquiv
    (ZMod 2) (GKS SmallK SmallS) (Wgen SmallK SmallS) n).symm

private theorem smallGenH_finite (h51 : MilneADT_I_5_1_totallyComplex) (n : ℕ) (hn : n ≤ 2) :
    Module.Finite (ZMod 2) (genH SmallK SmallS n) := by
  obtain ⟨h0, h1, h2, _⟩ := h51 SmallK smallK_complex SmallS smallS_finite smallS_above_two
    (Wrep SmallK SmallS) inferInstance inferInstance
    (continuous_trivialRepS_action (GaloisGroupS SmallK SmallS) (ZMod 2 × ZMod 2))
  have : Module.Finite (ZMod 2) (continuousCohomology n (Wrep SmallK SmallS)) := by
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  exact (genHEquiv SmallK SmallS n hn).symm.finiteDimensional

private theorem smallGenH_upper (h410 : MilneADT_I_4_10_totallyComplex) (n : ℕ) (hn : 2 < n) :
    Subsingleton (genH SmallK SmallS n) := by
  have := h410 SmallK smallK_complex SmallS smallS_finite smallS_above_two
    (Wrep SmallK SmallS) inferInstance inferInstance
    (continuous_trivialRepS_action (GaloisGroupS SmallK SmallS) (ZMod 2 × ZMod 2)) n hn
  exact ⟨fun x y => (allGenHEquiv n).injective (Subsingleton.elim _ _)⟩

private theorem smallGlobal_finite (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (n : ℤ) :
    Module.Finite (ZMod 2) (smallResidualData.G.X n) := by
  change Module.Finite (ZMod 2) (smallGlobal.toCC.homology n)
  cases n with
  | negSucc m =>
    have := natHomology_negative
      (contCochains (ZMod 2) (GKS SmallK SmallS) SmallM) (Int.negSucc m)
      (Int.negSucc_lt_zero m)
    infer_instance
  | ofNat m =>
    have : Module.Finite (ZMod 2) (genH SmallK SmallS m) := by
      by_cases hm : m ≤ 2
      · exact smallGenH_finite h51 m hm
      · have := smallGenH_upper h410 m (by omega)
        infer_instance
    exact (smallGlobalHEquiv m).symm.finiteDimensional

private theorem smallGlobal_off (h410 : MilneADT_I_4_10_totallyComplex)
    (n : ℤ) (hn : n < 0 ∨ 2 < n) : Subsingleton (smallResidualData.G.X n) := by
  change Subsingleton (smallGlobal.toCC.homology n)
  cases n with
  | negSucc m =>
    exact natHomology_negative (contCochains (ZMod 2) (GKS SmallK SmallS) SmallM)
      (Int.negSucc m) (Int.negSucc_lt_zero m)
  | ofNat m =>
    have hm : 2 < m := by simp only [Int.ofNat_eq_natCast] at hn; omega
    have := smallGenH_upper h410 m hm
    exact ⟨fun x y => (smallGlobalHEquiv m).injective (Subsingleton.elim _ _)⟩

private theorem smallP_ge (h410 : MilneADT_I_4_10_totallyComplex) : smallP.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have := smallGlobal_off h410 n (Or.inl hn)
  have : Subsingleton (smallP.X n) := by
    change Subsingleton (smallResidualData.G.X n × PUnit.{1} × PUnit.{1})
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

private theorem smallP_le (h410 : MilneADT_I_4_10_totallyComplex) : smallP.IsStrictlyLE 2 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have := smallGlobal_off h410 n (Or.inr hn)
  have : Subsingleton (smallP.X n) := by
    change Subsingleton (smallResidualData.G.X n × PUnit.{1} × PUnit.{1})
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

private theorem smallP_finite (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (n : ℤ) :
    Module.Finite (ZMod 2) (smallP.X n) := by
  have := smallGlobal_finite h410 h51 n
  change Module.Finite (ZMod 2) (smallResidualData.G.X n × PUnit.{1} × PUnit.{1})
  infer_instance

private theorem modelProj_quasiIso (G : GCx (ZMod 2)) :
    QuasiIso (GHom.toCC (ZInQ.Contrib.CloudB3RC53.Torsion.modelProj G)) := by
  have : IsIso (GHom.toCC (ZInQ.Contrib.CloudB3RC53.Torsion.modelProj G)) := by
    refine ⟨⟨GHom.toCC (ZInQ.Contrib.CloudB3RC53.Torsion.modelIncl G), ?_, ?_⟩⟩
    · ext n x
      obtain ⟨a, u, v⟩ := x
      exact Prod.ext rfl (Prod.ext rfl rfl)
    · ext n x
      rfl
  infer_instance

private theorem smallPP_exists (h410 : MilneADT_I_4_10_totallyComplex) :
    ∃ pP : smallP ⟶ (selCx smallSupportData.D).toCC, QuasiIso pP := by
  have := smallP_le h410
  have : smallP.IsKProjective := CochainComplex.isKProjective_of_projective smallP 2
  let l : smallP ⟶ smallGlobal.toCC :=
    GHom.toCC (ZInQ.Contrib.CloudB3RC53.Torsion.modelProj (homologyModel smallGlobal.toCC)) ≫
      homologyModelTo smallGlobal.toCC
  have := modelProj_quasiIso (homologyModel smallGlobal.toCC)
  have := homologyModelTo_quasiIso smallGlobal.toCC
  have : QuasiIso l := inferInstance
  let q : (selCx smallSupportData.D).toCC ⟶ smallGlobal.toCC :=
    GHom.toCC (projG smallSupportData.D)
  have : QuasiIso q := relaxed_quasiIso
    (k := ZMod 2) (GS := GKS SmallK SmallS)
    (Gv := fun v : Places SmallK SmallS => Gloc SmallK v.1)
    (loc := fun v => locMap SmallK SmallS v.1) (M := SmallM)
  exact exists_quasiIso_of_zigzag l q

private theorem smallP_d (i j : ℤ) : smallP.d i j = 0 := by
  by_cases h : i + 1 = j
  · ext x
    rw [GCx.toCC_d_hom _ i j h]
    change ((0, 0, (0 : PUnit.{1}) - 0 - 0) :
      smallResidualData.G.X j × PUnit.{1} × PUnit.{1}) = 0
    simp
  · exact smallP.shape i j h

private theorem smallP_minimal (i j : ℤ) (x : smallP.X i) :
    (smallP.d i j).hom x ∈
      IsLocalRing.maximalIdeal (ZMod 2) • (⊤ : Submodule (ZMod 2) (smallP.X j)) := by
  rw [smallP_d]
  exact Submodule.zero_mem _

private theorem smallGlobal_zero_rank : Module.finrank (ZMod 2) (smallResidualData.G.X 0) = 2 := by
  rw [((smallEG 0 (by decide)).trans (genHEquiv SmallK SmallS 0 (by decide))).finrank_eq]
  exact (finrank_H0_trivialRepS (GaloisGroupS SmallK SmallS) (ZMod 2 × ZMod 2)).trans
    finrank_zmod2_sq

private theorem smallP_positive (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) :
    6 ≤ ∑ n ∈ smallDegrees, Module.finrank (ZMod 2) (smallP.X n) := by
  have : Module.Finite (ZMod 2) (smallResidualData.G.X 0) := smallGlobal_finite h410 h51 0
  have : Module.Finite (ZMod 2) (smallResidualData.G.X 1) := smallGlobal_finite h410 h51 1
  have h0 : Module.finrank (ZMod 2) (smallP.X 0) = 2 := by
    change Module.finrank (ZMod 2) (smallResidualData.G.X 0 × PUnit.{1} × PUnit.{1}) = 2
    rw [Module.finrank_prod, Module.finrank_prod, smallGlobal_zero_rank,
      Module.finrank_zero_of_subsingleton]
  have h1 : Module.finrank (ZMod 2) (smallP.X 1) = hW SmallK SmallS 1 := by
    change Module.finrank (ZMod 2) (smallResidualData.G.X 1 × PUnit.{1} × PUnit.{1}) = _
    have hz : Module.finrank (ZMod 2) PUnit.{1} = 0 := Module.finrank_zero_of_subsingleton
    rw [Module.finrank_prod, Module.finrank_prod, hz]
    exact ((smallEG 1 (by decide)).trans (genHEquiv SmallK SmallS 1 (by decide))).finrank_eq
  obtain ⟨_, _, _, he⟩ := h51 SmallK smallK_complex SmallS smallS_finite smallS_above_two
    (Wrep SmallK SmallS) inferInstance inferInstance
    (continuous_trivialRepS_action (GaloisGroupS SmallK SmallS) (ZMod 2 × ZMod 2))
  have hc : InfinitePlace.nrComplexPlaces SmallK = 1 :=
    nrComplexPlaces_eq_one_of_imaginaryQuadratic SmallK smallK_degree smallK_complex
  have hd : Module.finrank (ZMod 2) (Wrep SmallK SmallS) = 2 := finrank_zmod2_sq
  have hh0 : hW SmallK SmallS 0 = 2 :=
    (finrank_H0_trivialRepS (GaloisGroupS SmallK SmallS) (ZMod 2 × ZMod 2)).trans finrank_zmod2_sq
  change (hW SmallK SmallS 0 : ℤ) - hW SmallK SmallS 1 + hW SmallK SmallS 2 =
    -((InfinitePlace.nrComplexPlaces SmallK : ℤ) * Module.finrank (ZMod 2) (Wrep SmallK SmallS)) at he
  rw [hh0, hc, hd] at he
  have hp : 4 ≤ hW SmallK SmallS 1 := by omega
  have h := Finset.sum_le_sum_of_subset
    (f := fun n : ℤ => Module.finrank (ZMod 2) (smallP.X n))
    (show ({0, 1} : Finset ℤ) ⊆ smallDegrees by decide)
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton, h0, h1] at h
  omega

/-- The integral equation of E₁₁ over any base ring. -/
def smallCurve (R : Type*) [CommRing R] : WeierstrassCurve R := ⟨0, 22, 0, -363, 0⟩

private theorem smallCurve_elliptic (F : Type*) [Field F] [CharZero F] :
    (smallCurve F).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  apply IsUnit.mk0
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, smallCurve]

private theorem smallCurve_eq_smallE : smallCurve SmallK = SmallE := by
  ext <;> norm_num [smallCurve, SmallE, cubicCurve]

/-- The same integral curve at every genuine finite place. -/
def smallLocalModels (w : HeightOneSpectrum (𝓞 SmallK)) :
    WeierstrassCurve (w.adicCompletionIntegers SmallK) :=
  smallCurve (w.adicCompletionIntegers SmallK)

private theorem smallCurve_map {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A) :
    (smallCurve R).map f = smallCurve A := by
  ext <;> simp [smallCurve, WeierstrassCurve.map]
  · exact map_ofNat f 22
  · exact map_ofNat f 363

private theorem smallLocal_baseChange (w : HeightOneSpectrum (𝓞 SmallK)) :
    (smallLocalModels w).baseChange (w.adicCompletion SmallK) =
      smallCurve (w.adicCompletion SmallK) :=
  smallCurve_map (algebraMap (w.adicCompletionIntegers SmallK) (w.adicCompletion SmallK))

instance (w : HeightOneSpectrum (𝓞 SmallK)) :
    ((smallLocalModels w).baseChange (w.adicCompletion SmallK)).IsElliptic := by
  rw [smallLocal_baseChange]
  have := ZInQ.Contrib.CloudB3RC53.Mattuck.charZero_adicCompletion SmallK w
  exact smallCurve_elliptic _

/-- The full row of the genuine local-condition table. -/
def smallCond : Ideal (𝓞 SmallK) → LocalCondition := fun _ => .full

private theorem smallCond_derivative : ∀ P : Ideal (𝓞 SmallK),
    smallCond P = .derivRelaxed → ∃ q ∈ (∅ : Finset ℕ), P ∈ primesAbove SmallK q := by
  intro P h
  cases h

/-- The discriminant of the actual integral equation, over any base ring. -/
theorem smallCurve_discriminant (R : Type*) [CommRing R] :
    (smallCurve R).Δ = 2304 * 11 ^ 6 := by
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, smallCurve]

/-- The local integral equations and the global actual curve have the same generic fiber. -/
theorem local_models_are_baseChanges (w : HeightOneSpectrum (𝓞 SmallK)) :
    (smallLocalModels w).baseChange (w.adicCompletion SmallK) =
      SmallE.baseChange (w.adicCompletion SmallK) := by
  rw [smallLocal_baseChange, ← smallCurve_eq_smallE]
  exact (smallCurve_map (algebraMap SmallK (w.adicCompletion SmallK))).symm

section ConcreteTorsion

open WeierstrassCurve

variable (F : Type*) [Field F] [CharZero F]

private theorem rootZero_nonsingular : (smallCurve F).toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  refine ⟨?_, Or.inl ?_⟩ <;> norm_num [smallCurve]

private theorem rootEleven_nonsingular : (smallCurve F).toAffine.Nonsingular 11 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  refine ⟨?_, Or.inl ?_⟩ <;> norm_num [smallCurve]

private theorem rootNegThirtyThree_nonsingular : (smallCurve F).toAffine.Nonsingular (-33) 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  refine ⟨?_, Or.inl ?_⟩ <;> norm_num [smallCurve]

private def fourTorsionPoints : Fin 4 → (smallCurve F).toAffine.Point
  | 0 => 0
  | 1 => .some 0 0 (rootZero_nonsingular F)
  | 2 => .some 11 0 (rootEleven_nonsingular F)
  | 3 => .some (-33) 0 (rootNegThirtyThree_nonsingular F)

private theorem two_zsmul_eq_zero_iff (P : (smallCurve F).toAffine.Point) :
    (2 : ℤ) • P = 0 ↔ ∃ i, fourTorsionPoints F i = P := by
  constructor
  · intro h
    rcases P with _ | ⟨x, y, hxy⟩
    · exact ⟨0, rfl⟩
    rw [two_zsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some,
      Affine.Point.some.injEq] at h
    have hy : y = 0 := by
      have hyy := h.2
      simp only [Affine.negY, smallCurve, zero_mul, sub_zero] at hyy
      have h2y : (2 : F) * y = 0 := by linear_combination hyy
      exact (mul_eq_zero.mp h2y).resolve_left two_ne_zero
    subst hy
    have he := hxy.1
    rw [Affine.equation_iff'] at he
    simp only [smallCurve] at he
    have hfac : x * (x - 11) * (x + 33) = 0 := by linear_combination -he
    rcases mul_eq_zero.mp hfac with h12 | h3
    · rcases mul_eq_zero.mp h12 with hx | hx
      · subst hx
        exact ⟨1, rfl⟩
      · have hx' : x = 11 := sub_eq_zero.mp hx
        subst hx'
        exact ⟨2, rfl⟩
    · have hx : x = -33 := eq_neg_of_add_eq_zero_left h3
      subst hx
      exact ⟨3, rfl⟩
  · rintro ⟨i, rfl⟩
    rw [two_zsmul, add_eq_zero_iff_eq_neg]
    fin_cases i <;> simp [fourTorsionPoints, Affine.Point.neg_some, Affine.negY, smallCurve]

private theorem fourTorsionPoints_injective : Function.Injective (fourTorsionPoints F) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [fourTorsionPoints] <;> norm_num at h

/-- Exactly four rational 2-torsion points on the actual integral equation of E₁₁. -/
theorem smallCurve_two_torsion :
    Nat.card (Submodule.torsionBy ℤ (smallCurve F).toAffine.Point 2) = 4 := by
  have hmem : ∀ i, fourTorsionPoints F i ∈ Submodule.torsionBy ℤ (smallCurve F).toAffine.Point 2 :=
    fun i => (Submodule.mem_torsionBy_iff _ _).mpr
      ((two_zsmul_eq_zero_iff F _).mpr ⟨i, rfl⟩)
  let f : Fin 4 → Submodule.torsionBy ℤ (smallCurve F).toAffine.Point 2 :=
    fun i => ⟨fourTorsionPoints F i, hmem i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact fourTorsionPoints_injective F (congrArg Subtype.val h)
    · intro P
      have hP : (2 : ℤ) • (P : (smallCurve F).toAffine.Point) = 0 :=
        (Submodule.mem_torsionBy_iff _ _).mp P.2
      obtain ⟨i, hi⟩ := (two_zsmul_eq_zero_iff F _).mp hP
      exact ⟨i, Subtype.ext hi⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_fin]

end ConcreteTorsion

/-- Stronger than hfull: the same local curve has full rational 2-torsion at every finite place. -/
theorem local_models_have_full_two_torsion (w : HeightOneSpectrum (𝓞 SmallK)) :
    Nat.card (Submodule.torsionBy ℤ
      ((smallLocalModels w).baseChange (w.adicCompletion SmallK)).toAffine.Point 2) = 4 := by
  rw [smallLocal_baseChange]
  have := ZInQ.Contrib.CloudB3RC53.Mattuck.charZero_adicCompletion SmallK w
  exact smallCurve_two_torsion _

private theorem smallCond_full : ∀ w : HeightOneSpectrum (𝓞 SmallK),
    smallCond w.asIdeal = .oldKummer →
      Nat.card (Submodule.torsionBy ℤ
        ((smallLocalModels w).baseChange (w.adicCompletion SmallK)).toAffine.Point 2) = 4 :=
  fun w _ => local_models_have_full_two_torsion w

private theorem smallUm : ∑ n ∈ smallDegrees, Module.finrank (ZMod 2) (smallResidualData.U.X n) ≤
    ∑ p ∈ chargedPrimes 66 5 ∅,
      condSum SmallK (genCondDimFun2 SmallK SmallS smallCond
        (ZInQ.Contrib.CloudB3RC53.Mattuck.kummerDimOfCurves SmallK smallLocalModels
          (ZInQ.Contrib.CloudB3RC53.Mattuck.kd2OfCurves SmallK smallLocalModels))) p := by
  have hz : (∑ n ∈ smallDegrees, Module.finrank (ZMod 2) (smallResidualData.U.X n)) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    change Module.finrank (ZMod 2) PUnit.{1} = 0
    exact Module.finrank_zero_of_subsingleton
  rw [hz]
  exact Nat.zero_le _

private theorem smallLm : ∑ n ∈ smallDegrees, Module.finrank (ZMod 2) (smallResidualData.L.X (n - 1)) ≤
    ∑ p ∈ chargedPrimes 66 5 ∅, genLocSum SmallK SmallS p := by
  have hz : (∑ n ∈ smallDegrees, Module.finrank (ZMod 2) (smallResidualData.L.X (n - 1))) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    change Module.finrank (ZMod 2) PUnit.{1} = 0
    exact Module.finrank_zero_of_subsingleton
  rw [hz]
  exact Nat.zero_le _

abbrev smallFullData : SelData (ZMod 2) := smallSupportData.Dp
abbrev smallQuotient : GCx (ZMod 2) := ZInQ.Contrib.CloudB3RC53.SelmerDuality.zeroCx (ZMod 2)

def smallF : GHom smallSupportData.Dp.U smallFullData.U := idGHom _
def smallG : GHom smallFullData.U smallQuotient := zeroGHom _ _

private theorem sameGHom {A B : GCx (ZMod 2)} (f g : GHom A B)
    (h : ∀ i (x : A.X i), f.f i i rfl x = g.f i i rfl x) : f = g := by
  obtain ⟨ff, hf⟩ := f
  obtain ⟨gg, hg⟩ := g
  have he : ff = gg := by
    funext i j hij
    subst hij
    ext x
    exact h i x
  subst he
  rfl

private theorem smallRestricted : smallSupportData.Dp = restrictData smallFullData smallF := by
  have hi : ghomComp smallF smallFullData.ι = smallFullData.ι :=
    sameGHom _ _ fun n x => rfl
  change smallFullData =
    (⟨smallFullData.G, smallFullData.U, smallFullData.L, smallFullData.res,
      ghomComp smallF smallFullData.ι⟩ : SelData (ZMod 2))
  rw [hi]

private theorem smallFg (n : ℤ) (u : smallSupportData.Dp.U.X n) :
    smallG.f n n rfl (smallF.f n n rfl u) = 0 := rfl

private theorem smallF_injective (n : ℤ) : Function.Injective (smallF.f n n rfl) := fun _ _ h => h

private theorem smallG_surjective (n : ℤ) : Function.Surjective (smallG.f n n rfl) :=
  fun _x => ⟨0, Subsingleton.elim _ _⟩

private theorem smallExact (n : ℤ) (u : smallFullData.U.X n)
    (_ : smallG.f n n rfl u = 0) : ∃ u', smallF.f n n rfl u' = u := ⟨u, rfl⟩

private theorem smallQuotient_acyclic : smallQuotient.toCC.Acyclic := by
  rw [acyclic_toCC_iff]
  intro i j k hij hjk x _
  exact ⟨0, Subsingleton.elim _ _⟩

/-- Jointly witnessed residual identifications, finite bounds, and actual comparison maps. -/
structure JointWitness where
  finiteG : ∀ n, Module.Finite (ZMod 2) (smallResidualData.G.X n)
  eG : ∀ n ∈ smallDegrees, smallResidualData.G.X n ≃ₗ[ZMod 2] genH SmallK SmallS n.toNat
  eGact : ∀ n ∈ smallDegrees, smallResidualData.G.X n ≃ₗ[ZMod 2]
    contCohomology (ZMod 2) (GKS SmallK SmallS) SmallM n.toNat
  hUm : ∑ n ∈ smallDegrees, Module.finrank (ZMod 2) (smallResidualData.U.X n) ≤
    ∑ p ∈ chargedPrimes 66 5 ∅,
      condSum SmallK (genCondDimFun2 SmallK SmallS smallCond
        (ZInQ.Contrib.CloudB3RC53.Mattuck.kummerDimOfCurves SmallK smallLocalModels
          (ZInQ.Contrib.CloudB3RC53.Mattuck.kd2OfCurves SmallK smallLocalModels))) p
  hLm : ∑ n ∈ smallDegrees, Module.finrank (ZMod 2) (smallResidualData.L.X (n - 1)) ≤
    ∑ p ∈ chargedPrimes 66 5 ∅, genLocSum SmallK SmallS p
  boundedGE : smallP.IsStrictlyGE 0
  boundedLE : smallP.IsStrictlyLE 2
  pP : smallP ⟶ (selCx smallSupportData.D).toCC
  quasiP : QuasiIso pP
  L : CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ
  Lge : L.IsStrictlyGE 0
  Lle : L.IsStrictlyLE 2
  finiteL : ∀ n, Module.Finite (ZMod 2) (L.X n)
  hLmin : ∀ i j x, (L.d i j).hom x ∈
    IsLocalRing.maximalIdeal (ZMod 2) • (⊤ : Submodule (ZMod 2) (L.X j))
  pL : L ⟶ (selCx smallFullData).toCC
  quasiL : QuasiIso pL
  positive : 6 ≤ ∑ n ∈ smallDegrees, Module.finrank (ZMod 2) (L.X n)

/-- All five model hypotheses coexist on genuine nonzero residual coefficients. -/
theorem jointWitness_nonempty (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h788 : NekovarProp788ii SmallK) :
    Nonempty JointWitness := by
  obtain ⟨pP, hpP⟩ := smallPP_exists h410
  have hq : QuasiIso (GHom.toCC (supportMap smallSupportData)) :=
    supportChange_of_print SmallK h788 (subset_refl SmallS) 2 smallSetting smallS_finite
      (fun q => absurd q.2.1 q.2.2) (fun q => absurd q.2.1 q.2.2) smallConditions
  let pL : smallP ⟶ (selCx smallFullData).toCC := pP ≫ GHom.toCC (supportMap smallSupportData)
  have hpL : QuasiIso pL := inferInstance
  exact ⟨{
    finiteG := smallGlobal_finite h410 h51
    eG := smallEG
    eGact := smallEGact
    hUm := smallUm
    hLm := smallLm
    boundedGE := smallP_ge h410
    boundedLE := smallP_le h410
    pP := pP
    quasiP := hpP
    L := smallP
    Lge := smallP_ge h410
    Lle := smallP_le h410
    finiteL := smallP_finite h410 h51
    hLmin := smallP_minimal
    pL := pL
    quasiL := hpL
    positive := smallP_positive h410 h51 }⟩

private theorem smallPrimeFactors : (2 * 66).primeFactors = {2, 3, 11} := by
  rw [show 2 * 66 = 2 * (2 * 3 * 11) by decide,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.prime_two.primeFactors, Nat.prime_three.primeFactors,
    (show Nat.Prime 11 by decide).primeFactors]
  decide

/-- The genuine moving prime is good for the displayed integral equation. -/
theorem smallSupport_facts : Nat.Prime 5 ∧ ¬ 5 ∣ 2304 * 11 ^ 6 ∧
    chargedPrimes 66 5 ∅ = {2, 3, 5, 11} := by
  refine ⟨by decide, by decide, ?_⟩
  simp only [chargedPrimes, smallPrimeFactors]
  decide

/-- A genuine complex infinite place. -/
def smallInfinitePlace : InfinitePlace SmallK := Classical.arbitrary _

private theorem smallInfinitePlace_complex : smallInfinitePlace.IsComplex := by
  apply InfinitePlace.not_isReal_iff_isComplex.mp
  intro hw
  let f : SmallK →+* ℝ := InfinitePlace.embedding_of_isReal hw
  have hs : (smallAlpha : SmallK) ^ 2 = -1 :=
    congrArg (fun x : 𝓞 SmallK => (x : SmallK)) smallAlpha_sq
  have h := congrArg f hs
  rw [map_pow, map_neg, map_one] at h
  have hpos := sq_nonneg (f (smallAlpha : SmallK))
  linarith

/-- The genuine constructor, applied to the jointly witnessed data. -/
def genuineCounts (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) (J : JointWitness) :
    ResidualRankCounts := by
  letI : ∀ n, Module.Finite (ZMod 2) (smallResidualData.G.X n) := J.finiteG
  letI : ∀ n, Module.Finite (ZMod 2) (smallResidualData.U.X n) := fun n => by
    change Module.Finite (ZMod 2) PUnit.{1}
    infer_instance
  letI : ∀ n, Module.Finite (ZMod 2) (smallResidualData.L.X n) := fun n => by
    change Module.Finite (ZMod 2) PUnit.{1}
    infer_instance
  letI : ∀ w, ((smallLocalModels w).baseChange (w.adicCompletion SmallK)).IsElliptic :=
    fun w => inferInstance
  letI : smallP.IsStrictlyGE 0 := J.boundedGE
  letI : smallP.IsStrictlyLE 2 := J.boundedLE
  letI : QuasiIso J.pP := J.quasiP
  letI : J.L.IsStrictlyGE 0 := J.Lge
  letI : J.L.IsStrictlyLE 2 := J.Lle
  letI : ∀ n, Module.Finite (ZMod 2) (J.L.X n) := J.finiteL
  letI : QuasiIso J.pL := J.quasiL
  exact ZInQ.Contrib.CloudB3RC53.Mattuck.residualRankCounts_genuine
    SmallK smallLocalModels h410 h51 h28 h23 h788 (-1) smallAlpha smallAlpha_radicand
    smallK_complex 66 (by decide) 0 (by simp) 5 (by decide) ∅ (by simp) (by simp)
    smallCond smallCond_derivative smallCond_full smallInfinitePlace smallInfinitePlace_complex
    SmallS smallResidualData smallDegrees (Finset.Subset.refl _) J.eG J.hUm J.hLm
    (subset_refl SmallS) 2 smallSetting smallS_finite SmallM
    (fun q => absurd q.2.1 q.2.2) (fun q => absurd q.2.1 q.2.2) smallConditions
    smallFullData smallQuotient smallF smallG smallRestricted smallFg smallF_injective
    smallG_surjective smallExact smallQuotient_acyclic 0 2 J.pP J.L J.hLmin J.pL

/-- The actual-coefficient constructor, applied to the same jointly witnessed data. -/
def actualCounts (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) (J : JointWitness) :
    ResidualRankCounts := by
  letI : ∀ n, Module.Finite (ZMod 2) (smallResidualData.G.X n) := J.finiteG
  letI : ∀ n, Module.Finite (ZMod 2) (smallResidualData.U.X n) := fun n => by
    change Module.Finite (ZMod 2) PUnit.{1}
    infer_instance
  letI : ∀ n, Module.Finite (ZMod 2) (smallResidualData.L.X n) := fun n => by
    change Module.Finite (ZMod 2) PUnit.{1}
    infer_instance
  letI : ∀ w, ((smallLocalModels w).baseChange (w.adicCompletion SmallK)).IsElliptic :=
    fun w => inferInstance
  letI : smallP.IsStrictlyGE 0 := J.boundedGE
  letI : smallP.IsStrictlyLE 2 := J.boundedLE
  letI : QuasiIso J.pP := J.quasiP
  letI : J.L.IsStrictlyGE 0 := J.Lge
  letI : J.L.IsStrictlyLE 2 := J.Lle
  letI : ∀ n, Module.Finite (ZMod 2) (J.L.X n) := J.finiteL
  letI : QuasiIso J.pL := J.quasiL
  exact residualRankCounts_actual SmallK smallLocalModels h410 h51 h28 h23 h788
    (-1) smallAlpha smallAlpha_radicand smallK_complex 66 (by decide) 0 (by simp)
    5 (by decide) ∅ (by simp) (by simp) smallCond smallCond_derivative smallCond_full
    smallInfinitePlace smallInfinitePlace_complex SmallE 0 smallCharacter smallTorsion.1
    smallTorsion.2.1 smallTorsion.2.2.1 smallTorsion.2.2.2 SmallS smallResidualData
    smallDegrees (Finset.Subset.refl _) J.eGact J.hUm J.hLm (subset_refl SmallS)
    2 smallSetting smallS_finite smallCharacter (fun q => absurd q.2.1 q.2.2)
    (fun q => absurd q.2.1 q.2.2) smallConditions smallFullData smallQuotient smallF smallG
    smallRestricted smallFg smallF_injective smallG_surjective smallExact
    smallQuotient_acyclic 0 2 J.pP J.L J.hLmin J.pL

/-- Non-vacuity of the genuine constructor, with a nonzero genuine minimal model. -/
theorem residualRankCounts_genuine_nonvacuous (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    ∃ J : JointWitness, 6 ≤ (genuineCounts h410 h51 h28 h23 h788 J).genericRank ∧
      (genuineCounts h410 h51 h28 h23 h788 J).genericRank ≤ 238 := by
  obtain ⟨J⟩ := jointWitness_nonempty h410 h51 h788
  have hb := (genuineCounts h410 h51 h28 h23 h788 J).genericRank_le
  change (genuineCounts h410 h51 h28 h23 h788 J).genericRank ≤
    residualBoundConstant (2 * 66).primeFactors.card 0 (∅ : Finset ℕ).card at hb
  rw [smallPrimeFactors] at hb
  norm_num [residualBoundConstant] at hb
  exact ⟨J, J.positive, hb⟩

/-- Non-vacuity of the actual-coefficient constructor, with the actual nonzero residual module. -/
theorem residualRankCounts_actual_nonvacuous (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) (h788 : NekovarProp788ii SmallK) :
    ∃ J : JointWitness, 6 ≤ (actualCounts h410 h51 h28 h23 h788 J).genericRank ∧
      (actualCounts h410 h51 h28 h23 h788 J).genericRank ≤ 238 := by
  obtain ⟨J⟩ := jointWitness_nonempty h410 h51 h788
  have hb := (actualCounts h410 h51 h28 h23 h788 J).genericRank_le
  change (actualCounts h410 h51 h28 h23 h788 J).genericRank ≤
    residualBoundConstant (2 * 66).primeFactors.card 0 (∅ : Finset ℕ).card at hb
  rw [smallPrimeFactors] at hb
  norm_num [residualBoundConstant] at hb
  exact ⟨J, J.positive, hb⟩

/-- The numerical upper bound supplied by both constructors in this test case. -/
theorem smallBound : residualBoundConstant (2 * 66).primeFactors.card 0 (∅ : Finset ℕ).card = 238 := by
  rw [smallPrimeFactors]
  decide

end ZInQ.Contrib.RC53Assist.ResidualWitness

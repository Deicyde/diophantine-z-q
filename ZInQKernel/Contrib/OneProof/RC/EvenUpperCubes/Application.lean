import ZInQKernel.Contrib.OneProof.RC.AuxInputs.Assembly
import ZInQKernel.Contrib.OneProof.RC.EvenUpperCubes.Level
import ZInQKernel.Contrib.OneProof.RC.EvenUpperCubes.Realize

/-! The auxiliary factor and even upper bound use the same alphabet,
source family, and installed contraction certificate. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenUpperCubes

open ZInQ.Manuscript SelmerTwoPower AddressGenuine AuxInputs EvenUpperText PrintsAnalytic Symbols Wiring
open ZInQ.Contrib.CloudB3RC53 CoefficientDictionary ZInQ.Contrib.RC53Assist.AuxFactor

attribute [local instance] Nat.fact_prime_two

variable {ℓ : ℕ} {W : WData ℓ} {C : Even.CentralNormalization (Ecurve ℓ)}

theorem partitionCertificate_iff (hS : SupportSpec W)
    (A : SqClass (conductor W.S) → Config (SqClass (conductor W.S)) → ZMod 2) (d : ℤ) :
    partitionCertificate W hS A d ↔ SourcePartitionable W (evenTypes W.S hS.1) A d := by
  constructor
  · rintro ⟨hd, hsf, havoid, hpart⟩
    exact ⟨⟨hd, hsf, havoid⟩, hpart⟩
  · rintro ⟨⟨hd, hsf, havoid⟩, hpart⟩
    exact ⟨hd, hsf, havoid, hpart⟩

/-- In the concrete squareclass alphabet, the class of residue one is zero.
This uses the class construction behind `TypeData.classes`. -/
theorem evenTypes_typ_one (hS : SupportSpec W) (q : ℕ)
    (hq : (q : ZMod (evenTypes W.S hS.1).m) = 1) :
    (evenTypes W.S hS.1).typ q = 0 := by
  change (q : ZMod (conductor W.S)) = 1 at hq
  change sqClassOf (conductor W.S) (q : ℤ) = 0
  rw [sqClassOf_eq_sqMk 1 (by simpa only [Int.cast_natCast, Units.val_one] using hq), sqMk_one]

/-- Construct a cube from the reading at the base total type. The rank
premise of the downstream scalar comparison is unnecessary here. -/
theorem sourceCubesAt_of_reading (hS : SupportSpec W) (P : SourceFamily W C)
    (hN : 0 < N₀ ℓ) (hlevel : ∀ p : ℕ, p.Prime → p ∣ N₀ ℓ → p ∈ W.S)
    {d : ℤ} (hd : SourcePartitionable (withPartitionCertificate W hS (symbolFamily P hS))
      (evenTypes W.S hS.1) (symbolFamily P hS) d)
    (a : ℕ → ℚ_[2]) (δ : ℤ) (F : ℕ → Prop)
    (hread : symbolFamily P hS (primeConfig d.natAbs.primeFactors (evenTypes W.S hS.1).typ).total =
      symb (evenTypes W.S hS.1) (coeffReading a δ F))
    (hfactor : ∀ B, FixedUFactorization (evenTypes W.S hS.1) (coeffReading a δ F) B)
    (hrules : CoefficientRules (evenSign W.S)
      (symb (evenTypes W.S hS.1) (coeffReading a δ F))) (b : ℕ) :
    ∃ fam : Even.BinaryFamily (N₀ ℓ), b ≤ fam.b ∧ fam.h 0 = d ∧
      (∀ x, ∀ p ∈ d.natAbs.primeFactors, (p : ℤ) ∣ fam.h x) ∧
      (∀ x, (primeConfig (fam.h x).natAbs.primeFactors (evenTypes W.S hS.1).typ).total =
        (primeConfig d.natAbs.primeFactors (evenTypes W.S hS.1).typ).total) ∧
      ∀ x, x ≠ 0 → SourceUnit (withPartitionCertificate W hS (symbolFamily P hS))
        (evenTypes W.S hS.1) (symbolFamily P hS) (fam.h x) := by
  obtain ⟨⟨hneg, hsf, havoid⟩, hpart⟩ := hd
  have hc : d.natAbs.Coprime (conductor W.S) :=
    (coprime_conductor hS.1 hS.2.1 _).2
      (fun p hp hpd => havoid p hp (Int.natCast_dvd.mpr hpd))
  have hgood : ∀ p ∈ d.natAbs.primeFactors, (evenTypes W.S hS.1).Good p ∧
      Nat.Coprime p (N₀ ℓ) := by
    intro p hp
    have hg := good_primeFactors hS.1 hc p hp
    exact ⟨hg, (Nat.Prime.coprime_iff_not_dvd hg.1).2 fun h =>
      havoid p (hlevel p hg.1 h) (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))⟩
  rw [hread] at hpart
  obtain ⟨fam, _, hb, hbase, _, hdiv, htotal, hunit⟩ :=
    realized_cubes_with_total (evenTypes W.S hS.1) a δ F hfactor hrules
      (fun q _ hq => evenTypes_typ_one hS q hq) W.S hS.1 hN d hneg hsf havoid hgood hpart
      (max b 1) (le_max_right _ _)
  refine ⟨fam, hb ▸ le_max_left _ _, hbase, hdiv, htotal, fun x hx => ?_⟩
  obtain ⟨hn, ha, hu⟩ := hunit x hx
  refine ⟨⟨hn, fam.sqfree x, ha⟩, ?_⟩
  rw [htotal x, hread]
  exact hu

/-- The missing cube premise of the prepared-source adapter, with its
explicit zero extension, for the installed certificate. -/
theorem sourceCubeInputs_of_genuineSources (hS : SupportSpec W) (P : SourceFamily W C)
    (hW : WaldspurgerCor2) (hE : (Ecurve ℓ).IsElliptic)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : Even.EvenLowerBound (Ecurve ℓ) C)
    (hG : PreparedGenuineEvenSource (withPartitionCertificate W hS (symbolFamily P hS))
      (evenTypes W.S hS.1) C hW hE hcont h9 (symbolFamily P hS))
    (hzero : ∀ τ, ¬ PreparedType (withPartitionCertificate W hS (symbolFamily P hS))
      (evenTypes W.S hS.1) τ → symbolFamily P hS τ = 0)
    (hrules : ∀ τ, PreparedType (withPartitionCertificate W hS (symbolFamily P hS))
      (evenTypes W.S hS.1) τ → CoefficientRules (evenSign W.S) (symbolFamily P hS τ))
    (hN : 0 < N₀ ℓ) (hlevel : ∀ p : ℕ, p.Prime → p ∣ N₀ ℓ → p ∈ W.S) :
    SourceCubeInputs (withPartitionCertificate W hS (symbolFamily P hS))
      (evenTypes W.S hS.1) (symbolFamily P hS) := by
  intro d hd _ b
  let τ := (primeConfig d.natAbs.primeFactors (evenTypes W.S hS.1).typ).total
  have hτ : PreparedType (withPartitionCertificate W hS (symbolFamily P hS))
      (evenTypes W.S hS.1) τ := by
    by_contra hn
    obtain ⟨_, S, _, hunit⟩ := hd.2
    change symbolFamily P hS τ ((primeConfig d.natAbs.primeFactors
      (evenTypes W.S hS.1).typ).contractBy S) = 1 at hunit
    rw [hzero τ hn] at hunit
    exact zero_ne_one hunit
  obtain ⟨D₀, Q, h₀, _, _, hf, hr⟩ := hG.2 τ hτ
  exact sourceCubesAt_of_reading hS P hN hlevel hd
    (genuineEvenCoefficient hW hE Q h₀ hcont h9)
    (genuineEvenNormalization hW hE Q h₀ hcont h9).2 (Even.S0Filter W.S D₀) hr hf
    (by
      change CoefficientRules (evenSign W.S)
        (genuineEvenSymbol (evenTypes W.S hS.1) hW hE Q h₀ hcont h9)
      rw [← hr]
      exact hrules τ hτ) b

/-- The prepared-source adapter at the text's level, without a cube input. -/
theorem rc11Inputs_of_genuineSources (hS : SupportSpec W) (P : SourceFamily W C)
    (hℓ : 0 < ℓ) (hM : ModularNewform) (hH : HasseConvergence)
    (hW : WaldspurgerCor2) (hE : (Ecurve ℓ).IsElliptic)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : Even.EvenLowerBound (Ecurve ℓ) C)
    (hG : PreparedGenuineEvenSource (withPartitionCertificate W hS (symbolFamily P hS))
      (evenTypes W.S hS.1) C hW hE hcont h9 (symbolFamily P hS))
    (hzero : ∀ τ, ¬ PreparedType (withPartitionCertificate W hS (symbolFamily P hS))
      (evenTypes W.S hS.1) τ → symbolFamily P hS τ = 0)
    (hrules : ∀ τ, PreparedType (withPartitionCertificate W hS (symbolFamily P hS))
      (evenTypes W.S hS.1) τ → CoefficientRules (evenSign W.S) (symbolFamily P hS τ))
    (hs : Even.EvenScalar32 (Ecurve ℓ) (N₀ ℓ) C) :
    EvenUpperRC11Inputs (withPartitionCertificate W hS (symbolFamily P hS)) := by
  let : NeZero (conductor W.S) := ⟨(conductor_pos hS.1).ne'⟩
  obtain ⟨hl, hlevel⟩ := curveLevel_and_support hS hℓ hM hH
  have hN := level_pos_of_bcdt (bcdtThmA_of_modularNewform hM) hℓ
  exact rc11Inputs_of_preparedGenuineSources (evenTypes W.S hS.1) C hW hE hcont h9
    (fun _ hp => (conductor_support hS.1 hS.2.1 hp).1) (symbolFamily P hS) hG
    (sourceUnit_type_prepared_of_zero_unprepared fun τ hτ Γ => congrFun (hzero τ hτ) Γ)
    hl hs (partitionCertificate_iff hS (symbolFamily P hS))
    (sourceCubeInputs_of_genuineSources hS P hW hE hcont h9 hG hzero hrules hN hlevel)

/-- The App F comparisons on each actual reference source. Both assertions
use the same reading as the auxiliary-factor assembly. -/
def SourceRules (hS : SupportSpec W) (P : SourceFamily W C) : Prop :=
  ∀ τ (h : HasReference W τ),
    (∀ B, FixedUFactorization (evenTypes W.S hS.1) (P τ h).reading B) ∧
    CoefficientRules (evenSign W.S) ((P τ h).symbol hS)

/-- The same bounded realizations used by the auxiliary factor give the
fixed-set comparison as well as the graph rules. -/
theorem sourceRules_of_realizations (hS : SupportSpec W) (P : SourceFamily W C)
    (hReal : ∀ τ h B, (P τ h).BudgetRealization hS B) : SourceRules hS P := by
  intro τ h
  have hgraph := ((P τ h).rules_and_seed hS (hReal τ h)).1
  refine ⟨fun B => ?_, hgraph⟩
  let : NeZero (conductor W.S) := ⟨(conductor_pos hS.1).ne'⟩
  obtain ⟨X, F, S, hchar, hlocal, _⟩ := hReal τ h B
  let : CharZero X.K := hchar
  have htyp : IsTypeChar (evenTypes W.S hS.1) (typChar (conductor W.S)) :=
    isTypeChar_typeData _ (conductor_pos hS.1) _
  exact X.fixedU_of_constituents (O12.inputs_of_theta S hlocal htyp) htyp

/-- The installed certificate itself guarantees that its base total type
has a reference. This applies across the merged family's entire filter. -/
theorem sourceCubeInputs_of_sourceFamily (hS : SupportSpec W) (P : SourceFamily W C)
    (hRules : SourceRules hS P) (hN : 0 < N₀ ℓ)
    (hlevel : ∀ p : ℕ, p.Prime → p ∣ N₀ ℓ → p ∈ W.S) :
    SourceCubeInputs (withPartitionCertificate W hS (symbolFamily P hS))
      (evenTypes W.S hS.1) (symbolFamily P hS) := by
  classical
  intro d hd _ b
  let τ := (primeConfig d.natAbs.primeFactors (evenTypes W.S hS.1).typ).total
  have hRef : HasReference W τ := by
    by_contra hn
    obtain ⟨_, S, _, hu⟩ := hd.2
    change symbolFamily P hS τ ((primeConfig d.natAbs.primeFactors
      (evenTypes W.S hS.1).typ).contractBy S) = 1 at hu
    rw [symbolFamily, dite_eq_right hn] at hu
    exact zero_ne_one hu
  have hr : symbolFamily P hS τ = (P τ hRef).symbol hS := by
    rw [symbolFamily, dite_eq_left hRef]
  exact sourceCubesAt_of_reading hS P hN hlevel hd
    (fun D => ((P τ hRef).r D : ℚ_[2])) (P τ hRef).δ (evenFilter W.S τ)
    hr (hRules τ hRef).1 (hRules τ hRef).2 b

/-- The square identity at the very same source and its chosen depth
gives (3.3a) at every observed unit of the merged family. -/
theorem units33a_of_sourceFamily (hS : SupportSpec W) (P : SourceFamily W C)
    (hCW : C.Lstar = W.Lstar) (hRules : SourceRules hS P) :
    ∃ C₀ : ℤ, Units33a (withPartitionCertificate W hS (symbolFamily P hS))
      (SourceUnit (withPartitionCertificate W hS (symbolFamily P hS))
        (evenTypes W.S hS.1) (symbolFamily P hS)) C₀ := by
  classical
  let : NeZero (conductor W.S) := ⟨(conductor_pos hS.1).ne'⟩
  let U : SqClass (conductor W.S) → ℤ → Prop := fun τ d =>
    SourceUnit (withPartitionCertificate W hS (symbolFamily P hS))
      (evenTypes W.S hS.1) (symbolFamily P hS) d ∧
    (primeConfig d.natAbs.primeFactors (evenTypes W.S hS.1).typ).total = τ
  have hbounds : ∀ τ, ∃ B, Units33a (withPartitionCertificate W hS (symbolFamily P hS)) (U τ) B := by
    intro τ
    by_cases hRef : HasReference W τ
    · let Q := P τ hRef
      refine ⟨2 * Q.δ + padicValRat 2 (W.Lstar (-(Q.D₀ : ℤ))), ?_⟩
      intro d ⟨hd, ht⟩
      have hsf := Int.squarefree_natAbs.mpr hd.1.2.1
      have hc := (coprime_conductor hS.1 hS.2.1 _).2
        (fun p hp hpd => hd.1.2.2 p hp (Int.natCast_dvd.mpr hpd))
      have hv := hd.2
      rw [ht, symbolFamily, dite_eq_left hRef, Q.symbol_primeFactors hS (hRules τ hRef).1 hsf hc] at hv
      unfold coeffSymbol at hv
      split_ifs at hv with hu
      · obtain ⟨hF, hne, hval⟩ := hu
        change (Q.r d.natAbs : ℚ_[2]) ≠ 0 at hne
        have hr : Q.r d.natAbs ≠ 0 := by exact_mod_cast hne
        have hvr : padicValRat 2 (Q.r d.natAbs) = Q.δ + (d.natAbs.primeFactors.card : ℤ) := by
          change Padic.valuation (Q.r d.natAbs : ℚ_[2]) = _ at hval
          rwa [Padic.valuation_ratCast] at hval
        have hneg := hd.1.1
        have he : -(d.natAbs : ℤ) = d := by
          rw [← Int.natAbs_neg, Int.natAbs_of_nonneg (by omega : 0 ≤ -d), neg_neg]
        have hsquare := (Q.coeff d.natAbs hF).2
        rw [hCW, he] at hsquare
        have hLd : W.Lstar d ≠ 0 := by
          intro h0
          exact (pow_ne_zero 2 hr) (by rw [hsquare, h0, zero_div])
        have hcal := congrArg (padicValRat 2) hsquare
        rw [padicValRat.pow, padicValRat.div hLd Q.nonzero] at hcal
        have hcal' : 2 * padicValRat 2 (Q.r d.natAbs) =
            padicValRat 2 (W.Lstar d) - padicValRat 2 (W.Lstar (-(Q.D₀ : ℤ))) := by
          exact_mod_cast hcal
        have hω : (d.natAbs.primeFactors.card : ℤ) = (omega d : ℤ) :=
          EvenUpper.even_omega_eq d
        exact ⟨hneg.ne, hLd, by dsimp only [withPartitionCertificate]; linarith⟩
      · exact (zero_ne_one hv).elim
    · refine ⟨0, fun d ⟨hd, ht⟩ => ?_⟩
      have hv := hd.2
      rw [ht, symbolFamily, dite_eq_right hRef] at hv
      exact (zero_ne_one hv).elim
  choose B hB using hbounds
  refine ⟨∑ τ, max (B τ) 0, fun d hd => ?_⟩
  exact units33a_of_finite_sources U B hB d
    ⟨(primeConfig d.natAbs.primeFactors (evenTypes W.S hS.1).typ).total, hd, rfl⟩

/-- The precise fixed-level consequences for the entire source family,
including its original central normalization and its actual units. -/
theorem sourceConsequences_of_sourceFamily (hS : SupportSpec W) (P : SourceFamily W C)
    (hCW : C.Lstar = W.Lstar) (hRules : SourceRules hS P)
    (hℓ : 0 < ℓ) (hM : ModularNewform) (hH : HasseConvergence)
    (hs : Even.EvenScalar32 (Ecurve ℓ) (N₀ ℓ) C) :
    SourceConsequenceInputs (withPartitionCertificate W hS (symbolFamily P hS))
      (evenTypes W.S hS.1) (symbolFamily P hS) := by
  obtain ⟨hl, hlevel⟩ := curveLevel_and_support hS hℓ hM hH
  have hN := level_pos_of_bcdt (bcdtThmA_of_modularNewform hM) hℓ
  exact ⟨hl, ⟨C, hCW⟩, partitionCertificate_iff hS (symbolFamily P hS),
    (scalar32_iff_even C hCW).mpr hs, units33a_of_sourceFamily hS P hCW hRules,
    sourceCubeInputs_of_sourceFamily hS P hRules hN hlevel⟩

/-- The RC11 input over the entire family used by the auxiliary factor.
Outside the prepared congruence branch it uses the genuine source of
each type admitting a reference. -/
theorem rc11Inputs_of_sourceFamily (hS : SupportSpec W) (P : SourceFamily W C)
    (hCW : C.Lstar = W.Lstar) (hRules : SourceRules hS P)
    (hℓ : 0 < ℓ) (hM : ModularNewform) (hH : HasseConvergence)
    (hs : Even.EvenScalar32 (Ecurve ℓ) (N₀ ℓ) C) :
    EvenUpperRC11Inputs (withPartitionCertificate W hS (symbolFamily P hS)) :=
  rc11Inputs_of_sourceConsequences (sourceConsequences_of_sourceFamily hS P hCW hRules hℓ hM hH hs)

/-- Formula (3.3b) on the installed partition predicate; App E's scalar
output and the actual same-source App F comparisons are the remaining
even upper inputs. -/
theorem evenUpper33b_of_sourceFamily (hS : SupportSpec W) (P : SourceFamily W C)
    (hCW : C.Lstar = W.Lstar) (hRules : SourceRules hS P)
    (hℓ : 0 < ℓ) (hM : ModularNewform) (hH : HasseConvergence)
    (hPrints : Prints) (hAppE : Even.AppEOutputs (Ecurve ℓ) (N₀ ℓ) C) :
    ∃ C₁ : ℤ, EvenUpper33b (withPartitionCertificate W hS (symbolFamily P hS)) C₁ := by
  have hB := bcdtThmA_of_modularNewform hM
  have hN := level_pos_of_bcdt hB hℓ
  exact evenUpper33b_of_RC11Inputs _ hPrints hℓ (lstarTarget_of_normalization hCW hℓ hB hH)
    ⟨C, hCW⟩
    (rc11Inputs_of_sourceFamily hS P hCW hRules hℓ hM hH
      (Even.evenScalar32_of_appE hN.ne' hAppE))

/-- Both assertions of the manuscript's (3.3b), using the existing
rank-zero forward implication and Boolean comparison. -/
theorem fullUpper33b_of_sourceFamily (hS : SupportSpec W) (P : SourceFamily W C)
    (hCW : C.Lstar = W.Lstar) (hRules : SourceRules hS P)
    (hℓ : 0 < ℓ) (hM : ModularNewform) (hH : HasseConvergence)
    (hK : KolyvaginThm1Printed) (hAppE : Even.AppEOutputs (Ecurve ℓ) (N₀ ℓ) C) :
    ∃ C₁ : ℤ, Upper33b (withPartitionCertificate W hS (symbolFamily P hS)) C₁ := by
  have hB := bcdtThmA_of_modularNewform hM
  have hN := level_pos_of_bcdt hB hℓ
  exact upper33b_of_sourceConsequences
    (forward_of_analytic_leaves hB hK hℓ (lstarTarget_of_normalization hCW hℓ hB hH))
    (sourceConsequences_of_sourceFamily hS P hCW hRules hℓ hM hH
      (Even.evenScalar32_of_appE hN.ne' hAppE))

end ZInQ.Manuscript.RC.EvenUpperCubes

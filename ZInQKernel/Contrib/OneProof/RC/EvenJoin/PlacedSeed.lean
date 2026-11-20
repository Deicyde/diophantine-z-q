import ZInQKernel.Contrib.OneProof.RC.EvenJoin.PlacedInventory
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.IntegersExtension

/-! The actual supported block vectors and the single seed at a tested
set. The divided series is still computed at the fixed place. -/

noncomputable section

set_option maxHeartbeats 1300000

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion HeckeRing.GL2
open IsDedekindDomain NumberField ModularForm ThetaCoeff UpperHalfPlane Wiring
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped AdicCompletionExtension MatrixGroups

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)} {P : EvenSource W L τ}
variable {hS : SupportSpec W} {i : Fin 2} {U : Finset ℕ}
variable (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p)

theorem evenBlockLevel_dvd (b : EvenBlock U) : evenBlockLevel P b ∣ movingLevel P U := by
  cases b with
  | none => exact dvd_rfl
  | some j => exact unaryLevel_dvd P U j

include hU in
theorem movingLevel_ne : movingLevel P U ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (mul_ne_zero (even_level_ne_zero P) (conductor_pos hS.1).ne'))
    (Finset.prod_ne_zero_iff.mpr fun p hp => (hU p hp).1.ne_zero)

include hU in
theorem movingLevel_test_coprime :
    ∀ q, Test (evenTypes W.S hS.1) U q → q.Coprime (movingLevel P U) := by
  intro q hq
  refine (Nat.Prime.coprime_iff_not_dvd hq.1.1).mpr ?_
  intro hd
  rcases hq.1.1.dvd_mul.mp hd with hd | hd
  · exact (Nat.Prime.coprime_iff_not_dvd hq.1.1).mp hq.1.2
      ((conductor_support hS.1 hS.2.1 hq.1.1).mpr ((evenMasked P hS).2.1 q hq.1.1 hd))
  · obtain ⟨p, hp, hpq⟩ := (hq.1.1.prime.dvd_finsetProd_iff id).mp hd
    exact hq.2 ((Nat.prime_dvd_prime_iff_eq hq.1.1 (hU p hp).1).mp hpq |>.symm ▸ hp)

section Series

variable {K : Type} [Field K]

/-- Evaluation before division, retaining the two kinds of actual block. -/
def blockSeriesAt (phase a : ℕ → K) (good : ℕ → Prop) (i : Fin 2)
    (b : EvenBlock U) : ℕ → K :=
  match b with
  | none => timesTheta (TL phase U.toList a)
  | some j => timesTheta (unaryCoeff good phase i j.val)

theorem timesTheta_map_ringHom {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (a : ℕ → R) (n : ℕ) :
    f (timesTheta a n) = timesTheta (fun k => f (a k)) n := by
  simp only [timesTheta, map_add, map_mul, map_ofNat, map_sum]

theorem unaryCoeff_map_ringHom {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (phase : ℕ → R) (good : ℕ → Prop) (i : Fin 2) (j n : ℕ) :
    f (unaryCoeff good phase i j n) = unaryCoeff good (f ∘ phase) i j n := by
  classical
  unfold unaryCoeff
  split_ifs <;> simp

theorem TL_map_scaled {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (phase a : ℕ → R) (a' : ℕ → S) (s : S)
    (ha : ∀ n, f (a n) = s * a' n) (J : List ℕ) (n : ℕ) :
    f (TL phase J a n) = s * TL (f ∘ phase) J a' n := by
  induction J generalizing n with
  | nil => exact ha n
  | cons p J ih =>
    have hd : f (divCoeff (TL phase J a) p n) = s * divCoeff (TL (f ∘ phase) J a') p n := by
      unfold divCoeff
      split_ifs <;> simp [ih]
    simp only [TL_cons, Odd.Top, map_sub, map_mul, ih, hd, Function.comp_apply]
    ring

theorem blockSeriesAt_map (κ : K →+* ℂ) (phase a : ℕ → K)
    (hη : ∀ n, κ (phase n) = P.phaseData.η n) (ha : ∀ n, κ (a n) = P.sievedCoeff n)
    (b : EvenBlock U) (n : ℕ) :
    κ (blockSeriesAt phase a (evenTypes W.S hS.1).Good i b n) = evenBlockSeries P hS i b n := by
  cases b with
  | none =>
    simp only [blockSeriesAt, evenBlockSeries, timesTheta_map_ringHom,
      TL_map_scaled κ phase a P.sievedCoeff 1 (fun j => (ha j).trans (one_mul _).symm),
      one_mul, show κ ∘ phase = _ from funext hη]
  | some j =>
    simp only [blockSeriesAt, evenBlockSeries, timesTheta_map_ringHom, unaryCoeff_map_ringHom,
      show κ ∘ phase = _ from funext hη]

end Series

variable {F : IntermediateField ℚ ℂ} [NumberField F]
variable {v : HeightOneSpectrum (𝓞 F)}
include hU in
/-- The placed lists of this row are the actual moving and unary lists. -/
theorem exists_actual_placed_lists (v : HeightOneSpectrum (𝓞 F))
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1) :
    letI : NeZero (movingLevel P U) := ⟨movingLevel_ne (P := P) (hS := hS) hU⟩
    ∃ (A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b) (evenBlockSeries P hS i b)),
      IsMovingCharacter P U (A none).χ ∧
      (∀ j : ↥(subscripts U), IsUnaryCharacter P i j.val (A (some j)).χ) ∧
      Nonempty (PlacedCuspLists A (evenBlockLevel_dvd (P := P)) v) := by
  letI : NeZero (movingLevel P U) := ⟨movingLevel_ne (P := P) (hS := hS) hU⟩
  obtain ⟨A, hB, hJ⟩ := exists_actual_cuspidal_inventory (P := P) hS i U hU hodd
  exact ⟨A, hB, hJ, exists_placedCuspLists A (evenBlockLevel_dvd (P := P)) v⟩

variable {A : ∀ b : EvenBlock U, CuspBlockExpansion (evenBlockLevel P b)
  (evenBlockSeries P hS i b)}
variable [NeZero (movingLevel P U)]
variable (D : PlacedCuspLists A (evenBlockLevel_dvd (P := P)) v)
variable (hLi : OldNewIndependenceWeightTwo)

abbrev PlacedCuspLists.fieldMap :
    FixedField v →+* FixedField D.w :=
  letI : Algebra F D.E := (IntermediateField.inclusion D.includes).toAlgebra
  letI := D.liesOver
  v.adicCompletionExtension F D.E D.w

abbrev PlacedCuspLists.ringMap : FixedRing v →+* FixedRing D.w :=
  letI : Algebra F D.E := (IntermediateField.inclusion D.includes).toAlgebra
  letI := D.liesOver
  v.adicCompletionIntegersExtension F D.E D.w

theorem PlacedCuspLists.fieldMap_complex (x : F) :
    D.κ (D.fieldMap (FinitePlace.embedding v x)) = (x : ℂ) := by
  letI : Algebra F D.E := (IntermediateField.inclusion D.includes).toAlgebra
  letI := D.liesOver
  exact constituentComplexEmbedding_fixed D.w v x

theorem PlacedCuspLists.fieldMap_source
    (C₀ : SourceAtPlace P (FixedRing v) (FixedField v)) (j : C₀.K₀ →+* F)
    (hK : (FinitePlace.embedding v).comp j = C₀.eK) (hC : F.subtype.comp j = C₀.eC) :
    D.κ.comp (D.fieldMap.comp C₀.eK) = C₀.eC := by
  apply RingHom.ext
  intro x
  change D.κ (D.fieldMap (C₀.eK x)) = C₀.eC x
  rw [← DFunLike.congr_fun hK x, ← DFunLike.congr_fun hC x]
  exact D.fieldMap_complex (j x)

abbrev PlacedCuspLists.evenBasis :=
  (D.inventory (evenTypes W.S hS.1) hLi).toBasis (movingLevel_test_coprime (P := P) (hS := hS) hU)

variable {phase a : ℕ → FixedField D.w}
variable (hη : ∀ n, D.κ (phase n) = P.phaseData.η n)
variable (ha : ∀ n, D.κ (a n) = P.sievedCoeff n)

include hη ha in
theorem exists_placed_block_vectors :
    ∃ z : EvenBlock U → ↥(distinctCuspColumns A (evenBlockLevel_dvd (P := P))) → FixedField D.w,
      (∀ b n, (D.evenBasis hU hLi).eval n (z b) =
        blockSeriesAt phase a (evenTypes W.S hS.1).Good i b n) ∧
      ∀ b x, z b x ≠ 0 →
        (D.inventory (evenTypes W.S hS.1) hLi).level x ∣ evenBlockLevel P b ∧
        (D.evenBasis hU hLi).χ x = D.blockChar b := by
  have hex (b : EvenBlock U) := coordinates_of_block_span
    (D.inventory (evenTypes W.S hS.1) hLi) (movingLevel_test_coprime (P := P) (hS := hS) hU) D.κ
    (evenBlockLevel P b) (D.blockChar b) (blockSeriesAt phase a (evenTypes W.S hS.1).Good i b)
    (by simpa only [blockSeriesAt_map (hS := hS) (i := i) D.κ phase a hη ha b] using
      D.block_span (evenTypes W.S hS.1) hLi b)
  choose z hval hs using hex
  exact ⟨z, hval, hs⟩

/-- The divided vector built from the individually supported blocks. -/
def placedEvenVector (z : EvenBlock U →
    ↥(distinctCuspColumns A (evenBlockLevel_dvd (P := P))) → FixedField D.w)
    (phase a : ℕ → FixedField D.w) :
    ↥(distinctCuspColumns A (evenBlockLevel_dvd (P := P))) → FixedField D.w := by
  classical
  exact (2 : FixedField D.w) ^ (-(P.δ + U.card + 1)) •
    (z none - ∑ j ∈ subscripts U, TL phase U.toList a j •
      (if hj : j ∈ subscripts U then z (some ⟨j, hj⟩) else 0))

include hη ha in
/-- The even vector is the same scalar combination as the actual joined
form. This is an identity on the very basis used for Hecke and diamonds. -/
theorem placed_evenVector_eval
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1)
    (z : EvenBlock U → ↥(distinctCuspColumns A (evenBlockLevel_dvd (P := P))) → FixedField D.w)
    (hz : ∀ b n, (D.evenBasis hU hLi).eval n (z b) =
      blockSeriesAt phase a (evenTypes W.S hS.1).Good i b n)
    (n : ℕ) :
    D.κ ((D.evenBasis hU hLi).eval n (placedEvenVector (D := D) z phase a)) =
      (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n := by
  classical
  let uz (j : ℕ) := if hj : j ∈ subscripts U then z (some ⟨j, hj⟩) else 0
  change D.κ ((D.evenBasis hU hLi).eval n
    ((2 : FixedField D.w) ^ (-(P.δ + U.card + 1)) •
      (z none - ∑ j ∈ subscripts U, TL phase U.toList a j • uz j))) = _
  rw [evenVector_eval _ (evenTypes W.S hS.1).Good phase a P.δ i U (z none) uz (hz none)
    (fun j hj k => by simpa only [uz, dite_eq_left hj, blockSeriesAt] using hz (some ⟨j, hj⟩) k) n,
    joinedForm_coeff, timesTheta_map_ringHom]
  congr 1
  funext k
  simp only [halfDivided, map_mul, map_zpow₀, map_ofNat,
    map_rawNumerator_scaled D.κ hη (fun k => (ha k).trans (one_mul _).symm), one_mul]

section FixedSource

variable (C₀ : SourceAtPlace P (FixedRing v) (FixedField v))
variable (hκ : D.κ.comp (D.fieldMap.comp C₀.eK) = C₀.eC)

abbrev PlacedCuspLists.phaseAt : ℕ → FixedField D.w := D.fieldMap ∘ C₀.eK ∘ C₀.η₀
abbrev PlacedCuspLists.rawSource : ℕ → FixedField D.w := D.fieldMap ∘ C₀.eK ∘ C₀.c

include hκ in
theorem PlacedCuspLists.phase_complex (n : ℕ) :
    D.κ (D.phaseAt C₀ n) = P.phaseData.η n :=
  (DFunLike.congr_fun hκ (C₀.η₀ n)).trans (C₀.complex_eta n)

include hκ in
theorem PlacedCuspLists.rawSource_complex (n : ℕ) :
    D.κ (D.rawSource C₀ n) = P.sievedCoeff n :=
  (DFunLike.congr_fun hκ (C₀.c n)).trans (C₀.complex_coeff n)

def PlacedCuspLists.vectors :=
  (exists_placed_block_vectors hU D hLi (D.phase_complex C₀ hκ) (D.rawSource_complex C₀ hκ)).choose

theorem PlacedCuspLists.vectors_spec :
    (∀ b n, (D.evenBasis hU hLi).eval n (D.vectors hU hLi C₀ hκ b) =
      blockSeriesAt (D.phaseAt C₀) (D.rawSource C₀) (evenTypes W.S hS.1).Good i b n) ∧
    ∀ b x, D.vectors hU hLi C₀ hκ b x ≠ 0 →
      (D.inventory (evenTypes W.S hS.1) hLi).level x ∣ evenBlockLevel P b ∧
      (D.evenBasis hU hLi).χ x = D.blockChar b :=
  (exists_placed_block_vectors hU D hLi (D.phase_complex C₀ hκ) (D.rawSource_complex C₀ hκ)).choose_spec

def PlacedCuspLists.seed :=
  placedEvenVector (D := D) (D.vectors hU hLi C₀ hκ) (D.phaseAt C₀) (D.rawSource C₀)

/-- A nonzero seed coordinate comes from at least one of the separately
supported actual blocks. -/
theorem PlacedCuspLists.seed_support
    (x : ↥(distinctCuspColumns A (evenBlockLevel_dvd (P := P))))
    (hx : D.seed hU hLi C₀ hκ x ≠ 0) :
    ∃ b, D.vectors hU hLi C₀ hκ b x ≠ 0 ∧
      (D.inventory (evenTypes W.S hS.1) hLi).level x ∣ evenBlockLevel P b ∧
      (D.evenBasis hU hLi).χ x = D.blockChar b := by
  classical
  by_contra hn
  apply hx
  have hzero (b : EvenBlock U) : D.vectors hU hLi C₀ hκ b x = 0 := by
    by_contra he
    exact hn ⟨b, he, (D.vectors_spec hU hLi C₀ hκ).2 b x he⟩
  unfold PlacedCuspLists.seed placedEvenVector
  simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, hzero]
  have hs :
      (∑ j ∈ subscripts U, TL (D.phaseAt C₀) U.toList (D.rawSource C₀) j •
        (if hj : j ∈ subscripts U then D.vectors hU hLi C₀ hκ (some ⟨j, hj⟩)
          else 0) x) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [dite_eq_left hj, hzero, smul_zero]
  rw [hs, sub_zero, smul_zero]

theorem PlacedCuspLists.seed_complex
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1) (n : ℕ) :
    D.κ ((D.evenBasis hU hLi).eval n (D.seed hU hLi C₀ hκ)) =
      (qExpansion 1 (joinedForm hS i U hU hodd)).coeff n :=
  placed_evenVector_eval hU D hLi (D.phase_complex C₀ hκ) (D.rawSource_complex C₀ hκ)
    hodd _ (D.vectors_spec hU hLi C₀ hκ).1 n

theorem PlacedCuspLists.ringMap_agrees (x : FixedRing v) :
    algebraMap (FixedRing D.w) (FixedField D.w) (D.ringMap x) =
      D.fieldMap (algebraMap (FixedRing v) (FixedField v) x) := by
  letI : Algebra F D.E := (IntermediateField.inclusion D.includes).toAlgebra
  letI := D.liesOver
  rfl

theorem PlacedCuspLists.seed_integral
    (hodd : P.phaseData.η (-1 : ZMod P.phaseData.N) * (-1 : ℂ) ^ i.val = -1) (n : ℕ) :
    (D.evenBasis hU hLi).eval n (D.seed hU hLi C₀ hκ) =
      algebraMap (FixedRing D.w) (FixedField D.w)
        (D.ringMap (timesTheta (fixedH (hS := hS) C₀ i U hU) n)) := by
  apply D.κ.injective
  rw [D.seed_complex hU hLi C₀ hκ hodd, D.ringMap_agrees, joinedForm_coeff]
  have h₀ := commonCoeff_place C₀ hS Subtype.val_injective i U.toList
    U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp)) n
  change _ = D.κ (D.fieldMap (algebraMap (FixedRing v) (FixedField v)
    (timesTheta (dividedCoeff (source_at_place C₀ hS Subtype.val_injective) i U.toList
      U.nodup_toList (fun p hp => hU p (Finset.mem_toList.mp hp))) n)))
  rw [h₀, ← RingHom.comp_apply D.fieldMap C₀.eK, ← RingHom.comp_apply D.κ, hκ,
    commonCoeff_complex C₀ hS i U.toList n]

end FixedSource

end ZInQ.Manuscript.RC.EvenJoin

import ZInQKernel.Contrib.RC53Assist.AuxFactor.PreparedClauseFour
import ZInQKernel.Contrib.OneProof.RC.Even.EvenPhase

/-!
# The genuine even source behind the prepared prime-unit certificate

The source is the actual fixed `EvenPhaseData` for the original elliptic curve,
with sign minus one and its original `S0Filter`. Its phase-removed rational
coefficients and depth are read from the existing `minimum_sieved` theorem with
empty extra sieve. No coefficient function or index predicate is freely chosen,
and no even minimization argument is re-proved here.

The central normalization is tied to the fixed central values. The printed
Corollary 2 of Waldspurger, the genuine even lower bound, and the actual twist
continuations remain explicit inputs of the existing minimum theorem. The
source's type-filter dictionary, fixed-`U` factorization, and equality of the
specified symbol with the actual normalized source symbol remain explicit.
None of these inputs asserts a unit or a seed.

The certificate bridge uses the already attained even depth. The direct seed
bridge also uses that same attained index; it does not invoke the abstract
certificate's generic minimization helper. All preparation precedes the varying
companion parameter and its exclusions.
-/

set_option maxHeartbeats 600000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AuxFactor

open ZInQ.Manuscript ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Wiring
  ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.PrintsAnalytic
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset

attribute [local instance] Nat.fact_prime_two

variable {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- The coefficient function and depth supplied by the existing even minimum
on the whole original squareclass filter, with no extra sieve. -/
noncomputable def genuineEvenNormalization (hW : WaldspurgerCor2)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) {C : CentralNormalization E}
    {S₀ : Finset ℕ} {D₀ : ℕ} (P : EvenPhaseData E C (-1) S₀ D₀)
    (h₀ : C.Lstar (-1 * (D₀ : ℤ)) ≠ 0)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist E h) F)
    (h9 : EvenLowerBound E C) : (ℕ → ℚ) × ℤ :=
  let H := P.minimum_sieved hW hE (Or.inr rfl) h₀ hcont h9 ∅ (by simp)
  (H.choose, H.choose_spec.2.choose)

/-- The actual phase-removed coefficients, embedded in the two-adic field. -/
noncomputable def genuineEvenCoefficient (hW : WaldspurgerCor2)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) {C : CentralNormalization E}
    {S₀ : Finset ℕ} {D₀ : ℕ} (P : EvenPhaseData E C (-1) S₀ D₀)
    (h₀ : C.Lstar (-1 * (D₀ : ℤ)) ≠ 0)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist E h) F)
    (h9 : EvenLowerBound E C) : ℕ → ℚ_[2] :=
  fun D => ((genuineEvenNormalization hW hE P h₀ hcont h9).1 D : ℚ_[2])

/-- The actual dictionary symbol of the fixed even form at its existing
minimum, read on the original squareclass filter. -/
noncomputable def genuineEvenSymbol (T : TypeData L ε) (hW : WaldspurgerCor2)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) {C : CentralNormalization E}
    {S₀ : Finset ℕ} {D₀ : ℕ} (P : EvenPhaseData E C (-1) S₀ D₀)
    (h₀ : C.Lstar (-1 * (D₀ : ℤ)) ≠ 0)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist E h) F)
    (h9 : EvenLowerBound E C) : Config L → ZMod 2 :=
  symb T (coeffReading (genuineEvenCoefficient hW hE P h₀ hcont h9)
    (genuineEvenNormalization hW hE P h₀ hcont h9).2 (S0Filter S₀ D₀))

/-- The selected coefficients are exactly the phase-removed coefficients of
`P.g`, satisfy its same-source square identity, and attain the existing even
minimum on the whole original filter. This is a projection and field-embedding
bridge from `EvenPhaseData.minimum_sieved`, not a new minimum theorem. -/
theorem genuineEvenNormalization_spec (hW : WaldspurgerCor2)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) {C : CentralNormalization E}
    {S₀ : Finset ℕ} {D₀ : ℕ} (P : EvenPhaseData E C (-1) S₀ D₀)
    (h₀ : C.Lstar (-1 * (D₀ : ℤ)) ≠ 0)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist E h) F)
    (h9 : EvenLowerBound E C) :
    let M := genuineEvenNormalization hW hE P h₀ hcont h9
    (∀ D ∈ P.retained, hiwCoeff P.g D / hiwCoeff P.g D₀ = P.z D * (M.1 D : ℂ) ∧
      M.1 D ^ 2 = C.Lstar (-1 * (D : ℤ)) / C.Lstar (-1 * (D₀ : ℤ))) ∧
    LeastCoefficientDepth (genuineEvenCoefficient hW hE P h₀ hcont h9)
      (S0Filter S₀ D₀) M.2 := by
  let H := P.minimum_sieved hW hE (Or.inr rfl) h₀ hcont h9 ∅ (by simp)
  have hr := H.choose_spec.1
  have hmin := H.choose_spec.2.choose_spec
  change (∀ D ∈ P.retained,
      hiwCoeff P.g D / hiwCoeff P.g D₀ = P.z D * (H.choose D : ℂ) ∧
      H.choose D ^ 2 = C.Lstar (-1 * (D : ℤ)) / C.Lstar (-1 * (D₀ : ℤ))) ∧
    LeastCoefficientDepth (fun D => (H.choose D : ℚ_[2]))
      (S0Filter S₀ D₀) H.choose_spec.2.choose
  refine ⟨hr, ?_⟩
  obtain ⟨D, hD, _, hrD, hdepth⟩ := hmin.1
  refine ⟨⟨D, hD, ?_, ?_⟩, fun D hD ha => ?_⟩
  · change (H.choose D : ℚ_[2]) ≠ 0
    exact_mod_cast hrD
  · change Padic.valuation (H.choose D : ℚ_[2]) - (D.primeFactors.card : ℤ) =
      H.choose_spec.2.choose
    rw [Padic.valuation_ratCast]
    simpa only [omegaN] using hdepth
  · change (H.choose D : ℚ_[2]) ≠ 0 at ha
    have hrD : H.choose D ≠ 0 := by exact_mod_cast ha
    have hb := hmin.2 D hD (by simp) hrD
    change H.choose_spec.2.choose ≤
      Padic.valuation (H.choose D : ℚ_[2]) - (D.primeFactors.card : ℤ)
    rw [Padic.valuation_ratCast]
    simpa only [omegaN] using hb

/-- The original negative squareclass filter has the necessary index and type
conditions. Conductor-goodness follows from exclusion of the entire fixed
support, not from the converse of conductor-support containment. -/
theorem negativeCoefficientFilter_of_S0Filter (T : TypeData L ε) (τ : L)
    {S₀ : Finset ℕ} {D₀ : ℕ} (h2 : 2 ∈ S₀)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ S₀) (h7 : D₀ % 8 = 7)
    (htotal : ∀ D : ℕ, S0Filter S₀ D₀ D → (primeConfig D.primeFactors T.typ).total = τ) :
    NegativeCoefficientFilter T τ (S0Filter S₀ D₀) := by
  intro D hD
  have hprod := (hD.2.2.2 2 h2).1 rfl
  rw [Nat.mul_mod, h7] at hprod
  have hDmod : D % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hseven : D % 8 = 7 := by omega
  refine ⟨hD.1, hD.2.1, hseven, ?_, htotal D hD⟩
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  refine ⟨hprime, (Nat.Prime.coprime_iff_not_dvd hprime).mpr ?_⟩
  intro hpm
  exact hD.2.2.1 p (hmS p hprime hpm) (Nat.dvd_of_mem_primeFactors hp)

/-- Genuine prepared-source data for the fixed curve. The central values agree
with `W.Lstar`; each source is actual `EvenPhaseData` at sign minus one; the
coefficient function, minimum and symbol are the specified ones, and the index
predicate is exactly the original `S0Filter`. The type-filter dictionary and
fixed-`U` factorization are explicit inputs not supplied by `EvenPhaseData`.
There is no freely chosen coefficient function, subfilter, or unit premise. -/
def PreparedGenuineEvenSource {ℓ : ℕ} (W : WData ℓ) (T : TypeData L ε)
    (C : CentralNormalization (Ecurve ℓ)) (hW : WaldspurgerCor2)
    (hE : (Ecurve ℓ).IsElliptic)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : EvenLowerBound (Ecurve ℓ) C) (A : L → Config L → ZMod 2) : Prop :=
  C.Lstar = W.Lstar ∧
  ∀ τ : L, PreparedType W T τ →
    ∃ (D₀ : ℕ) (P : EvenPhaseData (Ecurve ℓ) C (-1) W.S D₀)
      (h₀ : C.Lstar (-1 * (D₀ : ℤ)) ≠ 0),
      D₀ % 8 = 7 ∧
      (∀ D : ℕ, S0Filter W.S D₀ D → (primeConfig D.primeFactors T.typ).total = τ) ∧
      (∀ B : ℕ, FixedUFactorization T
        (coeffReading (genuineEvenCoefficient hW hE P h₀ hcont h9)
          (genuineEvenNormalization hW hE P h₀ hcont h9).2 (S0Filter W.S D₀)) B) ∧
      A τ = genuineEvenSymbol T hW hE P h₀ hcont h9

/-- A genuine fixed source supplies the abstract certificate. The arbitrary
minimum in the certificate's universal reading field is equal to the already
attained even depth by uniqueness of least elements of the same set. -/
theorem preparedUnitCertificate_of_genuineEvenSource {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (C : CentralNormalization (Ecurve ℓ))
    (hW : WaldspurgerCor2) (hE : (Ecurve ℓ).IsElliptic)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : EvenLowerBound (Ecurve ℓ) C)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2)
    (hG : PreparedGenuineEvenSource W T C hW hE hcont h9 A) :
    PreparedUnitCertificate W T A := by
  intro τ hτ
  obtain ⟨D₀, P, h₀, h7, htotal, hfactor, hA⟩ := hG.2 τ hτ
  let M := genuineEvenNormalization hW hE P h₀ hcont h9
  let a := genuineEvenCoefficient hW hE P h₀ hcont h9
  let F := S0Filter W.S D₀
  have hM : LeastCoefficientDepth a F M.2 :=
    (genuineEvenNormalization_spec hW hE P h₀ hcont h9).2
  have hF : NegativeCoefficientFilter T τ F :=
    negativeCoefficientFilter_of_S0Filter T τ P.two_mem hmS h7 htotal
  refine ⟨a, F, M.2, hF, ?_, hM.2, ?_⟩
  · obtain ⟨D, hD, ha, _⟩ := hM.1
    exact ⟨D, hD, ha⟩
  · intro δ hδ
    have hδeq : δ = M.2 := by
      apply le_antisymm
      · obtain ⟨D, hD, ha, hdepth⟩ := hM.1
        simpa only [hdepth] using hδ.2 D hD ha
      · obtain ⟨D, hD, ha, hdepth⟩ := hδ.1
        simpa only [hdepth] using hM.2 D hD ha
    subst δ
    rw [hA]
    change NormalizedPrimeReading T (symb T (coeffReading a M.2 F)) a F M.2
    exact normalizedPrimeReading_of_dictionary T τ a F M.2 hF hfactor

/-- Bridge to the compatibility name of the abstract certificate. -/
theorem preparedEvenSourceInput_of_genuineEvenSource {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (C : CentralNormalization (Ecurve ℓ))
    (hW : WaldspurgerCor2) (hE : (Ecurve ℓ).IsElliptic)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : EvenLowerBound (Ecurve ℓ) C)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2)
    (hG : PreparedGenuineEvenSource W T C hW hE hcont h9 A) :
    PreparedEvenSourceInput W T A :=
  preparedUnitCertificate_of_genuineEvenSource W T C hW hE hcont h9 hmS A hG

/-- Direct seed bridge at the already attained index of the genuine even
minimum. The abstract certificate's generic minimum helper is not used. -/
theorem preparedSeedInput_of_genuineEvenSource {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (C : CentralNormalization (Ecurve ℓ))
    (hW : WaldspurgerCor2) (hE : (Ecurve ℓ).IsElliptic)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : EvenLowerBound (Ecurve ℓ) C)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2)
    (hG : PreparedGenuineEvenSource W T C hW hE hcont h9 A) :
    ∀ τ : L, PreparedType W T τ → ∃ Γ : Config L, IsUnitSeed ε (A τ) Γ := by
  intro τ hτ
  obtain ⟨D₀, P, h₀, h7, htotal, hfactor, hA⟩ := hG.2 τ hτ
  let M := genuineEvenNormalization hW hE P h₀ hcont h9
  let a := genuineEvenCoefficient hW hE P h₀ hcont h9
  let F := S0Filter W.S D₀
  have hF : NegativeCoefficientFilter T τ F :=
    negativeCoefficientFilter_of_S0Filter T τ P.two_mem hmS h7 htotal
  obtain ⟨D, hD, ha, hdepth⟩ := (genuineEvenNormalization_spec hW hE P h₀ hcont h9).2.1
  have hgood := (hF D hD).2.2.2.1
  have hread : NormalizedPrimeReading T (A τ) a F M.2 := by
    rw [hA]
    change NormalizedPrimeReading T (symb T (coeffReading a M.2 F)) a F M.2
    exact normalizedPrimeReading_of_dictionary T τ a F M.2 hF hfactor
  have hf : IsReal T (primeConfig D.primeFactors T.typ) id :=
    ⟨Set.injOn_id _, fun p hp => ⟨hgood p hp, rfl⟩, fun _ _ _ _ _ => rfl⟩
  refine ⟨primeConfig D.primeFactors T.typ, compatible_of_real T hf, ?_⟩
  rw [hread D hD]
  unfold coeffSymbol
  apply ite_eq_left
  exact ⟨hD, ha, by linarith⟩

/-- The prepared combinatorial clause follows from genuine fixed-source data
and the unchanged coefficient-rule and off-filter inputs. -/
theorem preparedClauseFour_of_genuineEvenSource {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (C : CentralNormalization (Ecurve ℓ))
    (hW : WaldspurgerCor2) (hE : (Ecurve ℓ).IsElliptic)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist (Ecurve ℓ) h) F)
    (h9 : EvenLowerBound (Ecurve ℓ) C)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2) (hA : ∀ τ : L, CoefficientRules ε (A τ))
    (hoff : ∀ τ : L, VanishesOffFilter (A τ) τ)
    (hG : PreparedGenuineEvenSource W T C hW hE hcont h9 A) :
    PreparedClauseFour W T A :=
  preparedClauseFour_of_preparedSeeds W T hmS A hA hoff
    (preparedSeedInput_of_genuineEvenSource W T C hW hE hcont h9 hmS A hG)

end ZInQ.Contrib.RC53Assist.AuxFactor

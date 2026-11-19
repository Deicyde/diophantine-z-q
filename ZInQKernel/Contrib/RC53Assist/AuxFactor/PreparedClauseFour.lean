import ZInQKernel.Contrib.OneProof.RC.Wiring.AuxFactor3

/-!
# Prepared negative types and the fourth auxiliary-factor clause

The negative types used in Appendix G have unsigned index seven modulo eight.
For each prepared type, a unit seed is nonempty. A minimum nonempty seed depends
only on its vertex labels, and matching all but one of its anchors, with a
nonempty remainder, gives a contraction certificate. This is the content of
Appendix G, lines 10096--10105, used at line 10139.

The phrase "every total type" at lines 10131--10132 is read in the context of
these prepared negative sources (lines 10057 and 10096), not as nonvanishing in
every possible local filter. No seed is requested at an unprepared type.

`PreparedUnitCertificate` is an abstract prime-unit certificate. Its coefficients
and index predicate are arbitrary, and a singleton predicate suffices. The
proved equivalence `preparedUnitCertificate_iff_primeUnits` records that exact
content. This certificate does not specify a modular form, its phase-removed
coefficients, or the original local-squareclass filter of Appendix E.

The combinatorial clause and its exact auxiliary-factor bridge are proved from
prepared units. The generic minimum and valuation lemmas below are conditional
algebraic helpers, not a construction of the genuine even source. A separate
binding to the actual fixed even form, original filter, same-source valuation
facts, and dictionary is required for a genuine-source-to-seed discharge.
The earlier coefficient-input name is retained only for compatibility with its
published abstract interface. No new printed theorem is introduced.
-/

set_option maxHeartbeats 600000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AuxFactor

open ZInQ.Manuscript ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Wiring
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
  ZInQ.Contrib.CloudB3RC53.AuxFactor Finset

variable {L : Type} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- A least normalized coefficient depth: attainment and a lower bound on all
retained nonzero values of an arbitrary coefficient function. -/
def LeastCoefficientDepth (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (δ : ℤ) : Prop :=
  (∃ D : ℕ, F D ∧ a D ≠ 0 ∧
    Padic.valuation (a D) - (D.primeFactors.card : ℤ) = δ) ∧
  ∀ D : ℕ, F D → a D ≠ 0 →
    δ ≤ Padic.valuation (a D) - (D.primeFactors.card : ℤ)

/-- A nonzero value and an integer lower bound imply an attained minimum.
This is a generic algebraic helper, not the genuine even-source minimizer. -/
theorem leastCoefficientDepth_exists (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (c : ℤ)
    (href : ∃ D : ℕ, F D ∧ a D ≠ 0)
    (hlow : ∀ D : ℕ, F D → a D ≠ 0 →
      c ≤ Padic.valuation (a D) - (D.primeFactors.card : ℤ)) :
    ∃ δ : ℤ, LeastCoefficientDepth a F δ := by
  obtain ⟨δ, hatt, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z => ∃ D : ℕ, F D ∧ a D ≠ 0 ∧
      Padic.valuation (a D) - (D.primeFactors.card : ℤ) = z)
    ⟨c, fun z ⟨D, hF, ha, hz⟩ => hz ▸ hlow D hF ha⟩
    (by obtain ⟨D, hF, ha⟩ := href; exact ⟨_, D, hF, ha, rfl⟩)
  exact ⟨δ, hatt, fun D hF ha => hmin _ ⟨D, hF, ha, rfl⟩⟩

/-- Arithmetic consequence of the displayed valuation comparisons (E.9) and
(E.11). With arbitrary functions `a` and `vL`, these comparisons do not by
themselves bind either function to the actual even form or central values. -/
theorem coefficientDepth_lowerBound_of_E9_E11 (a : ℕ → ℚ_[2]) (F : ℕ → Prop)
    (vL : ℕ → ℤ) (κ C : ℤ)
    (hE11 : ∀ D : ℕ, F D → a D ≠ 0 → vL D = 2 * Padic.valuation (a D) + κ)
    (hE9 : ∀ D : ℕ, F D → a D ≠ 0 → 2 * (D.primeFactors.card : ℤ) + C ≤ vL D) :
    ∀ D : ℕ, F D → a D ≠ 0 →
      (C - κ) / 2 ≤ Padic.valuation (a D) - (D.primeFactors.card : ℤ) := by
  intro D hF ha
  have heq := hE11 D hF ha
  have hle := hE9 D hF ha
  omega

/-- Necessary conditions on an arbitrary retained-index predicate. This
one-way condition permits a singleton predicate and does not assert equality
with the original support or local-squareclass filter of an even form. -/
def NegativeCoefficientFilter (T : TypeData L ε) (τ : L) (F : ℕ → Prop) : Prop :=
  ∀ D : ℕ, F D → 0 < D ∧ Squarefree D ∧ D % 8 = 7 ∧
    (∀ p ∈ D.primeFactors, T.Good p) ∧
    (primeConfig D.primeFactors T.typ).total = τ

/-- An abstract reading identity on an arbitrary index predicate. This
identity alone does not identify `a` with coefficients of a genuine form. -/
def NormalizedPrimeReading (T : TypeData L ε) (A : Config L → ZMod 2)
    (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (δ : ℤ) : Prop :=
  ∀ D : ℕ, F D → A (primeConfig D.primeFactors T.typ) = coeffSymbol a δ F D

/-- The dictionary proves the reading identity for its specified symbol,
conditionally on fixed-`U` factorization. It does not construct the form. -/
theorem normalizedPrimeReading_of_dictionary (T : TypeData L ε) (τ : L)
    (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (δ : ℤ)
    (hF : NegativeCoefficientFilter T τ F)
    (hswap : ∀ B : ℕ, FixedUFactorization T (coeffReading a δ F) B) :
    NormalizedPrimeReading T (symb T (coeffReading a δ F)) a F δ := by
  intro D hD
  obtain ⟨_, hsf, _, hgood, _⟩ := hF D hD
  rw [symb_primeConfig T a δ F (hswap _) D.primeFactors hgood le_rfl]
  change coeffSymbol a δ F (∏ p ∈ D.primeFactors, p) = coeffSymbol a δ F D
  rw [Nat.prod_primeFactors_of_squarefree hsf]

/-- An abstract prime-unit certificate for the prepared types. The arbitrary
coefficient function, index predicate, lower bound and reading can all be
manufactured from one allowed prime unit at each prepared type. The exact
equivalence is `preparedUnitCertificate_iff_primeUnits`. This is not a genuine
Appendix E source specification or a source-level discharge. -/
def PreparedUnitCertificate {ℓ : ℕ} (W : WData ℓ) (T : TypeData L ε)
    (A : L → Config L → ZMod 2) : Prop :=
  ∀ τ : L, PreparedType W T τ →
    ∃ (a : ℕ → ℚ_[2]) (F : ℕ → Prop) (c : ℤ),
      NegativeCoefficientFilter T τ F ∧
      (∃ D : ℕ, F D ∧ a D ≠ 0) ∧
      (∀ D : ℕ, F D → a D ≠ 0 →
        c ≤ Padic.valuation (a D) - (D.primeFactors.card : ℤ)) ∧
      ∀ δ : ℤ, LeastCoefficientDepth a F δ →
        NormalizedPrimeReading T (A τ) a F δ

/-- Compatibility name for the published abstract certificate. Despite its
older name, this proposition does not specify a genuine even source. -/
abbrev PreparedEvenSourceInput {ℓ : ℕ} (W : WData ℓ) (T : TypeData L ε)
    (A : L → Config L → ZMod 2) : Prop := PreparedUnitCertificate W T A

/-- Exact certificate content: allowed prime-configuration units, with no
coefficient rules, modular form, valuation comparison or analytic input needed.
The reverse implication uses a singleton index predicate. -/
theorem preparedUnitCertificate_iff_primeUnits {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (A : L → Config L → ZMod 2) :
    PreparedUnitCertificate W T A ↔
      ∀ τ : L, PreparedType W T τ →
        ∃ D : ℕ, 0 < D ∧ Squarefree D ∧ D % 8 = 7 ∧
          (∀ p ∈ D.primeFactors, T.Good p) ∧
          (primeConfig D.primeFactors T.typ).total = τ ∧
          A τ (primeConfig D.primeFactors T.typ) = 1 := by
  classical
  constructor
  · intro h τ hτ
    obtain ⟨a, F, c, hF, href, hlow, hread⟩ := h τ hτ
    obtain ⟨δ, hδ⟩ := leastCoefficientDepth_exists a F c href hlow
    obtain ⟨D, hD, ha, hdepth⟩ := hδ.1
    obtain ⟨hpos, hsf, hseven, hgood, htotal⟩ := hF D hD
    refine ⟨D, hpos, hsf, hseven, hgood, htotal, ?_⟩
    rw [hread δ hδ D hD]
    unfold coeffSymbol
    apply ite_eq_left
    exact ⟨hD, ha, by linarith⟩
  · intro h τ hτ
    obtain ⟨D₀, hpos, hsf, hseven, hgood, htotal, hunit⟩ := h τ hτ
    let a : ℕ → ℚ_[2] := fun D => if D = D₀ then 1 else 0
    let F : ℕ → Prop := fun D => D = D₀
    let c : ℤ := Padic.valuation (a D₀) - (D₀.primeFactors.card : ℤ)
    have ha₀ : a D₀ ≠ 0 := by simp [a]
    refine ⟨a, F, c, ?_, ⟨D₀, rfl, ha₀⟩, ?_, ?_⟩
    · intro D hD
      change D = D₀ at hD
      subst D
      exact ⟨hpos, hsf, hseven, hgood, htotal⟩
    · intro D hD _
      change D = D₀ at hD
      subst D
      exact le_rfl
    · intro δ hδ D hD
      change D = D₀ at hD
      subst D
      have hδc : δ = c := by
        obtain ⟨D, hD, _, hdepth⟩ := hδ.1
        change D = D₀ at hD
        subst D
        exact hdepth.symm
      rw [hunit]
      symm
      unfold coeffSymbol
      apply ite_eq_left
      refine ⟨rfl, ha₀, ?_⟩
      dsimp [c] at hδc
      linarith

/-- The abstract certificate supplies the exact prepared-seed input. This
projection is not a construction of coefficients of an actual even form. -/
theorem preparedSeedInput_of_unitCertificate {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (A : L → Config L → ZMod 2)
    (hcert : PreparedUnitCertificate W T A) :
    ∀ τ : L, PreparedType W T τ → ∃ Γ : Config L, IsUnitSeed ε (A τ) Γ := by
  intro τ hτ
  obtain ⟨a, F, c, hF, href, hlow, hread⟩ := hcert τ hτ
  obtain ⟨δ, hδ⟩ := leastCoefficientDepth_exists a F c href hlow
  obtain ⟨D, hD, ha, hdepth⟩ := hδ.1
  obtain ⟨_, _, _, hgood, _⟩ := hF D hD
  have hf : IsReal T (primeConfig D.primeFactors T.typ) id :=
    ⟨Set.injOn_id _, fun p hp => ⟨hgood p hp, rfl⟩, fun _ _ _ _ _ => rfl⟩
  refine ⟨primeConfig D.primeFactors T.typ, compatible_of_real T hf, ?_⟩
  rw [hread δ hδ D hD]
  unfold coeffSymbol
  apply ite_eq_left
  refine ⟨hD, ha, ?_⟩
  linarith

/-- A prepared total type has sign coordinate one, because its unsigned
squarefree index is seven modulo eight. This is a sign-coordinate statement,
not an assertion about the elliptic curve's root number. -/
theorem preparedType_sign_one {ℓ : ℕ} (W : WData ℓ) (T : TypeData L ε)
    (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S) {τ : L}
    (hτ : PreparedType W T τ) : ε τ = 1 := by
  obtain ⟨d, hd, h8, hsf, hdS, _, rfl⟩ := hτ
  set V := d.natAbs.primeFactors with hV
  have hgood : ∀ p ∈ V, T.Good p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    refine ⟨hprime, (Nat.Prime.coprime_iff_not_dvd hprime).mpr ?_⟩
    intro hpm
    exact hdS p (hmS p hprime hpm) (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  have hodd : ∀ p ∈ V, Odd p := by
    intro p hp
    rcases (hgood p hp).1.eq_two_or_odd' with htwo | ho
    · exact False.elim ((hgood p hp).ne_two htwo)
    · exact ho
  have hprod : ∏ p ∈ V, p = d.natAbs :=
    Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hsf)
  have habs : (d.natAbs : ℤ) = -d := by
    rw [← Int.natAbs_neg]
    exact Int.natAbs_of_nonneg (by omega)
  have hseven : d.natAbs % 8 = 7 := by omega
  have hhalf : ((d.natAbs / 2 : ℕ) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, show d.natAbs / 2 % 2 = 1 by omega]
    rfl
  have hsign : ε (primeConfig V T.typ).total = ∑ p ∈ V, ((p / 2 : ℕ) : ZMod 2) := by
    change ε (∑ p ∈ V, T.typ p) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun p hp => T.sign p (hgood p hp).1 (hgood p hp).2
  change ε (primeConfig V T.typ).total = 1
  rw [hsign, ← half_prod_odd V hodd, hprod]
  exact hhalf

/-- The text-faithful fourth clause, including the argument of Appendix G,
lines 10096--10105. At each prepared type, every unit seed is nonempty, a
minimum nonempty seed exists and its total is the prepared type, its bits are
irrelevant, and its first `r - 1` labels suffice for an anchor certificate with
a nonempty remainder. There is no quantification over unprepared types. -/
def PreparedClauseFour {ℓ : ℕ} (W : WData ℓ) (T : TypeData L ε)
    (A : L → Config L → ZMod 2) : Prop :=
  ∀ τ : L, PreparedType W T τ →
    (∀ Δ : Config L, IsUnitSeed ε (A τ) Δ → Δ.V.Nonempty) ∧
    ∃ Γ₀ : Config L, IsMinSeed ε (A τ) Γ₀ ∧ Γ₀.total = τ ∧
      (∀ Δ : Config L, Δ.Compatible ε → Δ.V = Γ₀.V →
        (∀ v ∈ Γ₀.V, Δ.t v = Γ₀.t v) → A τ Δ = 1) ∧
      ∀ Γ : Config L, Γ.Compatible ε → Γ.total = τ →
        ∀ s : ℕ, s ∈ Γ₀.V → ∀ anc : ℕ → ℕ,
          Set.InjOn anc (Γ₀.V.erase s) →
          (∀ v ∈ Γ₀.V.erase s, anc v ∈ Γ.V) →
          (∀ v ∈ Γ₀.V.erase s, Γ.t (anc v) = Γ₀.t v) →
          (Γ.V \ (Γ₀.V.erase s).image anc).Nonempty → IsPartitionable ε (A τ) Γ

/-- The entire prepared-type clause follows from the coefficient rules,
vanishing off the filter, and units at prepared types only. No edge-invariance
or partitionability assumption is added. -/
theorem preparedClauseFour_of_preparedSeeds {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2) (hA : ∀ τ : L, CoefficientRules ε (A τ))
    (hoff : ∀ τ : L, VanishesOffFilter (A τ) τ)
    (hseed : ∀ τ : L, PreparedType W T τ → ∃ Γ : Config L, IsUnitSeed ε (A τ) Γ) :
    PreparedClauseFour W T A := by
  intro τ hτ
  have hne : τ ≠ 0 := by
    intro hzero
    have hsign := preparedType_sign_one W T hmS hτ
    rw [hzero, map_zero] at hsign
    exact zero_ne_one hsign
  obtain ⟨Γ₀, hmin, htot, _, hpart⟩ :=
    negative_partitionable (hA τ) (hoff τ) hne (hseed τ hτ)
  exact ⟨fun Δ hΔ => negative_unitSeed_nonempty (hoff τ) hne hΔ,
    Γ₀, hmin, htot, fun Δ hΔ hV ht => minSeed_bits_irrelevant (hA τ) hmin hΔ hV ht, hpart⟩

/-- The faithful fourth clause supplies exactly the seed argument of
`auxFactor_of_prepared`, with no extra hypothesis and no change of type data. -/
theorem preparedSeedInput_of_clauseFour {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (A : L → Config L → ZMod 2)
    (h4 : PreparedClauseFour W T A) :
    ∀ τ : L, PreparedType W T τ → ∃ Γ : Config L, IsUnitSeed ε (A τ) Γ := by
  intro τ hτ
  obtain ⟨_, Γ₀, hmin, _, _, _⟩ := h4 τ hτ
  exact ⟨Γ₀, hmin.1⟩

/-- The abstract prime-unit certificate supplies the prepared combinatorial
clause. This is conditional on units, not a genuine-source-to-seed discharge. -/
theorem preparedClauseFour_of_unitCertificate {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2) (hA : ∀ τ : L, CoefficientRules ε (A τ))
    (hoff : ∀ τ : L, VanishesOffFilter (A τ) τ)
    (hcert : PreparedUnitCertificate W T A) : PreparedClauseFour W T A :=
  preparedClauseFour_of_preparedSeeds W T hmS A hA hoff
    (preparedSeedInput_of_unitCertificate W T A hcert)

/-- Direct integration: replacing the fourth input by the faithful prepared
clause produces the existing auxiliary factor. The other inputs are unchanged. -/
theorem auxFactor_of_clauseFour {ℓ : ℕ} (W : WData ℓ)
    (hS : ∀ p ∈ W.S, p.Prime) (hS2 : 2 ∈ W.S) [Fintype L]
    (T : TypeData L ε) (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2) (hA : ∀ τ : L, CoefficientRules ε (A τ))
    (hoff : ∀ τ : L, VanishesOffFilter (A τ) τ)
    (h4 : PreparedClauseFour W T A)
    (hspec : ∀ d : ℤ, d < 0 → Squarefree d → (∀ p ∈ W.S, ¬ (p : ℤ) ∣ d) →
      IsPartitionable ε (A (primeConfig d.natAbs.primeFactors T.typ).total)
        (primeConfig d.natAbs.primeFactors T.typ) → W.Partitionable d) :
    ∃ A₀ : ℕ, AuxFactor W A₀ :=
  auxFactor_of_prepared W hS hS2 T hmS A hA hoff
    (preparedSeedInput_of_clauseFour W T A h4) hspec

/-- Compatibility theorem for the earlier abstract certificate interface.
The older name does not turn its premise into a genuine even source. -/
theorem preparedSeedInput_of_evenSourceInput {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (A : L → Config L → ZMod 2)
    (hcert : PreparedEvenSourceInput W T A) :
    ∀ τ : L, PreparedType W T τ → ∃ Γ : Config L, IsUnitSeed ε (A τ) Γ :=
  preparedSeedInput_of_unitCertificate W T A hcert

/-- Compatibility theorem for the earlier abstract certificate interface.
The genuine source binding is a separate mathematical obligation. -/
theorem preparedClauseFour_of_evenSourceInput {ℓ : ℕ} (W : WData ℓ)
    (T : TypeData L ε) (hmS : ∀ p : ℕ, p.Prime → p ∣ T.m → p ∈ W.S)
    (A : L → Config L → ZMod 2) (hA : ∀ τ : L, CoefficientRules ε (A τ))
    (hoff : ∀ τ : L, VanishesOffFilter (A τ) τ)
    (hcert : PreparedEvenSourceInput W T A) : PreparedClauseFour W T A :=
  preparedClauseFour_of_unitCertificate W T hmS A hA hoff hcert

end ZInQ.Contrib.RC53Assist.AuxFactor

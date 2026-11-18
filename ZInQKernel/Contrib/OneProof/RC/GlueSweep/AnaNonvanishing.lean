import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaLevel
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Uses
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.RootNumberCheck
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Curve

/-!
# Lane RC22 (glue sweep): lane RC13's nonvanishing results without GLUE

Lane RC13 states its printed leaves in curve form (`HoffsteinLuo`, `BFHSimpleZero`,
`BFHNonvanishing`, `BFHTwistSign`, the interface `LocalRootNumbers`) and derives them from lane
RC8's statements with the GLUE facts `FromRC8.LevelSupport` and `FromRC8.RootNumberExists`
(`Nonvanishing/FromPrintsAnalytic.lean`); lane RC8 derives its curve forms from the literal prints
for newforms with the GLUE facts `TwistDictionary` and `HasseConvergence`.

Now `LevelSupport` is PROVED from RC8's print `ModularNewform`
(`GlueSweep.Ana.levelSupport_of_modularNewform`) and `TwistDictionary` is PROVED by lane RC18
(`TwistDictionary.twistDictionary`). This file
records the consequences, every theorem `PROVED`:

* **RC13's leaves from RC8's curve forms and `ModularNewform`** (`LevelSupport` removed):
  `bfhSimpleZero_of_curve_modular`, `bfhNonvanishing_of_curve_modular`,
  `bfhTwistSign_of_curve_modular`; the root-number check `rootNumber_of_mem_integral_modular`
  (`RootNumberExists` replaced by `ModularNewform` and `HasseConvergence`).
* **RC13's leaves from the literal prints** (`HoffsteinLuoTheorem`, `BFHTheorem`,
  `TwistedFunctionalEquation`), `ModularNewform` and the one remaining GLUE `HasseConvergence`:
  `hoffsteinLuo_of_prints`, `bfhSimpleZero_of_prints`, `bfhNonvanishing_of_prints`,
  `bfhTwistSign_of_prints`; BCDT is `PrintsAnalytic.bcdtThmA_of_modularNewform`.
* **RC13's results from the literal prints**: Propositions `ex:sec7-nonvanishing` (tex 1968–1992)
  and `ex:app-five-prime` (tex 10001–10029), the genus partner (tex 8251–8254), the fixed witness
  (tex 2461–2463) and the rough companion (tex 2373–2387): `nonvanishing_even_of_prints`,
  `nonvanishing_odd_of_prints`, `fivePrime_four_of_prints`, `genusPartner_of_prints`,
  `genusPartner_of_BFH_prints`, `witness_of_prints`, `roughCompanion_of_prints`.
* **The root-number check without the interface `LocalRootNumbers`** (tex 1994–2001), for a model
  over `ℤ` (the curves `E_ℓ` have one): `fivePrime_of_mem_integral`,
  `nonvanishing_odd_of_mem_integral` replace RC13's `fivePrime_of_mem` and
  `nonvanishing_odd_of_mem`, whose interface `LocalRootNumbers` carries four GLUE fields, by lane
  RC8's print `DesjardinsRootNumberFilter`.

The remaining hypotheses are the literal prints (PRINT), `ModularNewform` (PRINT) and
`HasseConvergence` (GLUE: Hasse's bound, not in Mathlib or the tree).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Ana

open ZInQ.Manuscript ZInQ.Manuscript.PoleS12 ZInQ.Contrib.CloudB3RC53
  ZInQ.Manuscript.RC.Nonvanishing ZInQ.Manuscript.RC.PrintsAnalytic

/-! ### RC13's leaves without `LevelSupport` -/

/-- **Bump–Friedberg–Hoffstein (i), RC13's leaf** (PROVED from RC8's `BFHCurve` and
`ModularNewform`): RC13's `FromRC8.bfhSimpleZero_of_curve` with its GLUE `LevelSupport`
discharged by `levelSupport_of_modularNewform` (tex 1985–1992). -/
theorem bfhSimpleZero_of_curve_modular (h : BFHCurve) (hM : ModularNewform) : BFHSimpleZero :=
  FromRC8.bfhSimpleZero_of_curve h (levelSupport_of_modularNewform hM)

/-- **Bump–Friedberg–Hoffstein (ii), RC13's leaf** (PROVED from RC8's `BFHCurve` and
`ModularNewform`): RC13's `FromRC8.bfhNonvanishing_of_curve` with `LevelSupport` discharged
(App F tex 8251–8254). -/
theorem bfhNonvanishing_of_curve_modular (h : BFHCurve) (hM : ModularNewform) :
    BFHNonvanishing :=
  FromRC8.bfhNonvanishing_of_curve h (levelSupport_of_modularNewform hM)

/-- **The twisted sign, RC13's leaf** (PROVED from RC8's `TwistedRootNumberCurve` and
`ModularNewform`): RC13's `FromRC8.bfhTwistSign_of_curve` with `LevelSupport` discharged
(tex 10025–10026, 10046). -/
theorem bfhTwistSign_of_curve_modular (h : TwistedRootNumberCurve) (hM : ModularNewform) :
    BFHTwistSign :=
  FromRC8.bfhTwistSign_of_curve h (levelSupport_of_modularNewform hM)

/-- **The root-number check for an integral model** (PROVED from RC8's
`DesjardinsRootNumberFilter`, `ModularNewform` and `HasseConvergence`; tex 1994–2001): RC13's
`FromRC8.rootNumber_of_mem_integral` with its GLUE `RootNumberExists` discharged by
`rootNumberExists_of_modularNewform` (RC8's `milneHasseWeil_of`). -/
theorem rootNumber_of_mem_integral_modular (hDes : DesjardinsRootNumberFilter)
    (hM : ModularNewform) (hH : HasseConvergence) {W : WeierstrassCurve ℤ}
    (hE : (W.map (Int.castRingHom ℚ)).IsElliptic) (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S)
    (h3 : 3 ∈ Φ.S) (hbad : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → p ∈ Φ.S) {u₀ : ℤ}
    (hu₀ : Φ.Mem u₀) (hsf₀ : Squarefree u₀) {w : ℤ}
    (hw : RootNumber (qtwist (W.map (Int.castRingHom ℚ)) u₀) w) :
    Φ.RootNumber (W.map (Int.castRingHom ℚ)) w :=
  FromRC8.rootNumber_of_mem_integral hDes (rootNumberExists_of_modularNewform hM hH) hE Φ h2 h3
    hbad hu₀ hsf₀ hw

/-! ### RC13's leaves from the literal prints -/

/-- **Hoffstein–Luo, RC13's leaf, from the print** (PROVED from `HoffsteinLuoTheorem`,
`ModularNewform` and `HasseConvergence`; tex 1990–1991, 9996): RC8's curve form
(`hoffsteinLuoCurve_of`, with lane RC18's proved `twistDictionary`) read by RC13's
`FromRC8.hoffsteinLuo_of_curve`. -/
theorem hoffsteinLuo_of_prints (hHL : HoffsteinLuoTheorem) (hM : ModularNewform)
    (hH : HasseConvergence) : HoffsteinLuo :=
  FromRC8.hoffsteinLuo_of_curve (TwistDictionary.hoffsteinLuoCurve_of_print hHL hM hH)

/-- **Bump–Friedberg–Hoffstein (i), RC13's leaf, from the print** (PROVED from `BFHTheorem`,
`ModularNewform` and `HasseConvergence`; tex 1992). -/
theorem bfhSimpleZero_of_prints (hB : BFHTheorem) (hM : ModularNewform) (hH : HasseConvergence) :
    BFHSimpleZero :=
  bfhSimpleZero_of_curve_modular (TwistDictionary.bfhCurve_of_print hB hM hH) hM

/-- **Bump–Friedberg–Hoffstein (ii), RC13's leaf, from the print** (PROVED from `BFHTheorem`,
`ModularNewform` and `HasseConvergence`; App F tex 8251–8254). -/
theorem bfhNonvanishing_of_prints (hB : BFHTheorem) (hM : ModularNewform)
    (hH : HasseConvergence) : BFHNonvanishing :=
  bfhNonvanishing_of_curve_modular (TwistDictionary.bfhCurve_of_print hB hM hH) hM

/-- **The twisted sign, RC13's leaf, from the print** (PROVED from `TwistedFunctionalEquation`,
`ModularNewform` and `HasseConvergence`; tex 10025–10026, 10046). -/
theorem bfhTwistSign_of_prints (hTFE : TwistedFunctionalEquation) (hM : ModularNewform)
    (hH : HasseConvergence) : BFHTwistSign :=
  bfhTwistSign_of_curve_modular (TwistDictionary.twistedRootNumberCurve_of_print hTFE hM hH) hM

/-! ### RC13's results from the literal prints -/

/-- **Proposition `ex:sec7-nonvanishing`, even case** (tex 1968–1991; PROVED from the literal
prints `HoffsteinLuoTheorem`, `TwistedFunctionalEquation`, `ModularNewform` and the GLUE
`HasseConvergence`): RC13's `nonvanishing_even`. -/
theorem nonvanishing_even_of_prints (hHL : HoffsteinLuoTheorem) (hTFE : TwistedFunctionalEquation)
    (hM : ModularNewform) (hH : HasseConvergence) {E : WeierstrassCurve ℚ} (hE : E.IsElliptic)
    (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S) (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt E p → p ∈ Φ.S)
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (heven : Φ.RootNumber E 1) :
    ∃ u : ℤ, Φ.Mem u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧
      Nonvanishing.omega u ≤ 5 ∧
      CentralNonzero (qtwist E u) :=
  nonvanishing_even (hoffsteinLuo_of_prints hHL hM hH) (bfhTwistSign_of_prints hTFE hM hH)
    (bcdtThmA_of_modularNewform hM) hE Φ h2 hbad B hB heven

/-- **Proposition `ex:sec7-nonvanishing`, odd case** (tex 1979, 1984–1992; PROVED from the
literal print `BFHTheorem`, `ModularNewform` and the GLUE `HasseConvergence`): RC13's
`nonvanishing_odd`. -/
theorem nonvanishing_odd_of_prints (hB : BFHTheorem) (hM : ModularNewform)
    (hH : HasseConvergence) {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) (Φ : SignedUnitFilter)
    (h2 : 2 ∈ Φ.S) (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt E p → p ∈ Φ.S)
    (B : Finset ℕ) (hB' : ∀ p ∈ B, p.Prime) (hodd : Φ.RootNumber E (-1)) :
    ∃ u : ℤ, Φ.Mem u ∧ Odd u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧
      AnalyticRank (qtwist E u) 1 :=
  nonvanishing_odd (bfhSimpleZero_of_prints hB hM hH) (bcdtThmA_of_modularNewform hM) hE Φ h2
    hbad B hB' hodd

/-- **Proposition `ex:app-five-prime`** (tex 10001–10029; PROVED from the literal prints
`HoffsteinLuoTheorem`, `TwistedFunctionalEquation`, `ModularNewform` and the GLUE
`HasseConvergence`): RC13's `fivePrime_four`. -/
theorem fivePrime_four_of_prints (hHL : HoffsteinLuoTheorem) (hTFE : TwistedFunctionalEquation)
    (hM : ModularNewform) (hH : HasseConvergence) {A : WeierstrassCurve ℚ} (hA : A.IsElliptic)
    (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S) (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt A p → p ∈ Φ.S)
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (heven : Φ.RootNumber A 1) :
    ∃ u : ℤ, Φ.Mem u ∧ Odd u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧
      Nonvanishing.omega u ≤ 5 ∧
      CentralNonzero (qtwist A u) :=
  fivePrime_four (hoffsteinLuo_of_prints hHL hM hH) (bfhTwistSign_of_prints hTFE hM hH)
    (bcdtThmA_of_modularNewform hM) hA Φ h2 hbad B hB heven

/-- **The genus partner `h_*`** (tex 8251–8254, 1985–1991; PROVED from the literal prints
`HoffsteinLuoTheorem`, `TwistedFunctionalEquation`, `ModularNewform` and the GLUE
`HasseConvergence`): RC13's `genusPartner`. -/
theorem genusPartner_of_prints (hHL : HoffsteinLuoTheorem) (hTFE : TwistedFunctionalEquation)
    (hM : ModularNewform) (hH : HasseConvergence) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hw : RootNumber (Ecurve ℓ) (-1)) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (h2 : 2 ∈ S)
    (h3 : 3 ∈ S) (hℓS : ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ S) (B : Finset ℕ)
    (hB : ∀ p ∈ B, p.Prime) :
    ∃ hstar : ℤ, hstar < 0 ∧ hstar % 8 = 1 ∧ Nonvanishing.IsFundamentalDiscriminant hstar ∧
      (∀ p ∈ S, IsSquareAt p (hstar : ℚ) ∧ ¬ (p : ℤ) ∣ hstar) ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ hstar) ∧
      Nonvanishing.omega hstar ≤ 5 ∧ CentralNonzero (curve ((hstar * ℓ : ℤ) : ℚ)) :=
  genusPartner (hoffsteinLuo_of_prints hHL hM hH) (bfhTwistSign_of_prints hTFE hM hH)
    (bcdtThmA_of_modularNewform hM) hℓ hw hS h2 h3 hℓS B hB

/-- **The genus partner from Bump–Friedberg–Hoffstein (ii)** (App F tex 8251–8254; PROVED from the
literal print `BFHTheorem`, `ModularNewform` and the GLUE `HasseConvergence`): RC13's
`genusPartner_of_BFH`. -/
theorem genusPartner_of_BFH_prints (hB : BFHTheorem) (hM : ModularNewform)
    (hH : HasseConvergence) {ℓ : ℕ} (hℓ : 0 < ℓ) (hw : RootNumber (Ecurve ℓ) (-1))
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (h2 : 2 ∈ S) (h3 : 3 ∈ S)
    (hℓS : ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ S) :
    ∃ hstar : ℤ, hstar < 0 ∧ hstar % 8 = 1 ∧ Nonvanishing.IsFundamentalDiscriminant hstar ∧
      (∀ p ∈ S, SplitsIn hstar p) ∧ CentralNonzero (curve ((hstar * ℓ : ℤ) : ℚ)) :=
  genusPartner_of_BFH (bfhNonvanishing_of_prints hB hM hH) (bcdtThmA_of_modularNewform hM) hℓ hw
    hS h2 h3 hℓS

/-- **The fixed witness `D_w`** (tex 2461–2463; PROVED from the literal prints `BFHTheorem`,
`TwistedFunctionalEquation`, `ModularNewform` and the GLUE `HasseConvergence`): RC13's
`witness`. -/
theorem witness_of_prints (hB : BFHTheorem) (hTFE : TwistedFunctionalEquation)
    (hM : ModularNewform) (hH : HasseConvergence) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hw : RootNumber (Ecurve ℓ) (-1)) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (h2 : 2 ∈ S)
    (h3 : 3 ∈ S) (hℓS : ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ S) (B : Finset ℕ)
    (hB' : ∀ p ∈ B, p.Prime) :
    ∃ Dw : ℤ, 0 < Dw ∧ Dw % 8 = 1 ∧ Squarefree Dw ∧
      (∀ p ∈ S, IsSquareAt p (Dw : ℚ) ∧ ¬ (p : ℤ) ∣ Dw) ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ Dw) ∧
      AnalyticRankOne (curve ((Dw * ℓ : ℤ) : ℚ)) :=
  witness (bfhSimpleZero_of_prints hB hM hH) (bfhTwistSign_of_prints hTFE hM hH)
    (bcdtThmA_of_modularNewform hM) hℓ hw hS h2 h3 hℓS B hB'

/-- **The rough companion** (tex 2373–2387; PROVED from the literal prints `HoffsteinLuoTheorem`,
`TwistedFunctionalEquation`, `ModularNewform`, the GLUE `HasseConvergence`, and RC13's own
remaining inputs `hdummy` (ELLIOT), `hforward` (PRINT) and `h33b` (ELLIOT)): RC13's
`roughCompanion`. -/
theorem roughCompanion_of_prints (hHL : HoffsteinLuoTheorem) (hTFE : TwistedFunctionalEquation)
    (hM : ModularNewform) (hH : HasseConvergence)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (h2 : 2 ∈ S) (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt E p → p ∈ S)
    (Partitionable CorankZero : ℤ → Prop) (vL s : ℤ → ℤ) (C₁ : ℤ) (A₀ : ℕ)
    (hdummy : ∀ h : ℤ, 0 < h → Squarefree h → h % 8 = 1 → (∀ p ∈ S, ¬ (p : ℤ) ∣ h) →
      ∀ X : Finset ℕ, (∀ p ∈ X, p.Prime) →
      ∃ a : ℤ, 0 < a ∧ Squarefree a ∧ Nonvanishing.omega a = A₀ ∧
        (∀ p ∈ S ∪ X, ¬ (p : ℤ) ∣ a) ∧
        IsCoprime a h ∧ ∀ u : ℤ, a * u < 0 → (a * u) % 8 = 1 → Squarefree (a * u) →
          (∀ p ∈ S ∪ h.natAbs.primeFactors, IsSquareAt p ((a * u : ℤ) : ℚ)) →
          CentralNonzero (qtwist E ((h * (a * u) : ℤ) : ℚ)) →
            Partitionable (h * (a * u)))
    (hforward : ∀ d : ℤ, CentralNonzero (qtwist E d) → CorankZero d)
    (h33b : ∀ d : ℤ, Partitionable d → CorankZero d →
      vL d ≤ 2 * Nonvanishing.omega d + s d + C₁) :
    ∃ (A : ℕ) (CE : ℤ), ∀ h : ℤ, 0 < h → Squarefree h → h % 8 = 1 → (∀ p ∈ S, ¬ (p : ℤ) ∣ h) →
      RootNumber (qtwist E h) (-1) → ∀ X : Finset ℕ, (∀ p ∈ X, p.Prime) →
        ∃ k' : ℤ, k' < 0 ∧ k' % 8 = 1 ∧ Nonvanishing.IsFundamentalDiscriminant k' ∧
          (∀ p ∈ S ∪ h.natAbs.primeFactors, IsSquareAt p (k' : ℚ) ∧ ¬ (p : ℤ) ∣ k') ∧
          (∀ p ∈ X, ¬ (p : ℤ) ∣ k') ∧ Partitionable (h * k') ∧
          CentralNonzero (qtwist E ((h * k' : ℤ) : ℚ)) ∧ Nonvanishing.omega k' ≤ A ∧
          vL (h * k') ≤ 2 * Nonvanishing.omega h + 2 * Nonvanishing.omega k' + s (h * k') + CE :=
  roughCompanion (hoffsteinLuo_of_prints hHL hM hH) (bfhTwistSign_of_prints hTFE hM hH)
    (bcdtThmA_of_modularNewform hM) hE hS h2 hbad Partitionable CorankZero vL s C₁ A₀ hdummy
    hforward h33b

/-! ### The root-number check without `LocalRootNumbers` (integral models) -/

/-- **A model over `ℤ` is good at every prime not dividing its discriminant** (PROVED): the
coefficients are integers (denominator `1`) and `v_p(Δ) = 0`. -/
theorem goodAt_map_of_not_dvd {W : WeierstrassCurve ℤ} {p : ℕ} (hp : p.Prime)
    (hΔ : ¬ (p : ℤ) ∣ W.Δ) : GoodAt (W.map (Int.castRingHom ℚ)) p := by
  have hp1 : ¬ p ∣ 1 := hp.not_dvd_one
  have hΔ0 : W.Δ ≠ 0 := fun h => hΔ (h ▸ dvd_zero _)
  have hmapΔ : (W.map (Int.castRingHom ℚ)).Δ = (W.Δ : ℚ) := by
    rw [WeierstrassCurve.map_Δ]; rfl
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [WeierstrassCurve.map] using hp1
  · simpa [WeierstrassCurve.map] using hp1
  · simpa [WeierstrassCurve.map] using hp1
  · simpa [WeierstrassCurve.map] using hp1
  · simpa [WeierstrassCurve.map] using hp1
  · rw [hmapΔ]; exact_mod_cast hΔ0
  · rw [hmapΔ, padicValRat.of_int]
    exact_mod_cast padicValInt.eq_zero_of_not_dvd hΔ

/-- The bad primes of a model over `ℤ` divide its discriminant (PROVED). -/
theorem bad_of_dvd {W : WeierstrassCurve ℤ} {S : Finset ℕ}
    (hbad : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → p ∈ S) :
    ∀ p : ℕ, p.Prime → ¬ GoodAt (W.map (Int.castRingHom ℚ)) p → p ∈ S := fun p hp hng =>
  hbad p hp (by_contra fun h => hng (goodAt_map_of_not_dvd hp h))

/-- **Proposition `ex:app-five-prime` with the filter's root number read off one parameter**
(tex 10001–10006 with the root-number check 1994–2001; PROVED from the literal prints
`HoffsteinLuoTheorem`, `TwistedFunctionalEquation`, `DesjardinsRootNumberFilter`,
`ModularNewform` and the GLUE `HasseConvergence`), for a model over `ℤ`: RC13's
`fivePrime_of_mem` without the interface `LocalRootNumbers`. -/
theorem fivePrime_of_mem_integral (hHL : HoffsteinLuoTheorem) (hTFE : TwistedFunctionalEquation)
    (hDes : DesjardinsRootNumberFilter) (hM : ModularNewform) (hH : HasseConvergence)
    {W : WeierstrassCurve ℤ} (hE : (W.map (Int.castRingHom ℚ)).IsElliptic)
    (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S) (h3 : 3 ∈ Φ.S)
    (hbad : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → p ∈ Φ.S) {u₀ : ℤ} (hu₀ : Φ.Mem u₀)
    (hsf₀ : Squarefree u₀) (heven : RootNumber (qtwist (W.map (Int.castRingHom ℚ)) u₀) 1)
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) :
    ∃ u : ℤ, Φ.Mem u ∧ Odd u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧
      Nonvanishing.omega u ≤ 5 ∧
      CentralNonzero (qtwist (W.map (Int.castRingHom ℚ)) u) :=
  fivePrime_four_of_prints hHL hTFE hM hH hE Φ h2 (bad_of_dvd hbad) B hB
    (rootNumber_of_mem_integral_modular hDes hM hH hE Φ h2 h3 hbad hu₀ hsf₀ heven)

/-- **Proposition `ex:sec7-nonvanishing`, odd case, with the filter's root number read off one
parameter** (tex 1979, 1984–2001; PROVED from the literal prints `BFHTheorem`,
`DesjardinsRootNumberFilter`, `ModularNewform` and the GLUE `HasseConvergence`), for a model over
`ℤ`: RC13's `nonvanishing_odd_of_mem` without the interface `LocalRootNumbers`. -/
theorem nonvanishing_odd_of_mem_integral (hB : BFHTheorem) (hDes : DesjardinsRootNumberFilter)
    (hM : ModularNewform) (hH : HasseConvergence) {W : WeierstrassCurve ℤ}
    (hE : (W.map (Int.castRingHom ℚ)).IsElliptic) (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S)
    (h3 : 3 ∈ Φ.S) (hbad : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → p ∈ Φ.S) {u₀ : ℤ}
    (hu₀ : Φ.Mem u₀) (hsf₀ : Squarefree u₀)
    (hodd : RootNumber (qtwist (W.map (Int.castRingHom ℚ)) u₀) (-1))
    (B : Finset ℕ) (hB' : ∀ p ∈ B, p.Prime) :
    ∃ u : ℤ, Φ.Mem u ∧ Odd u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧
      AnalyticRank (qtwist (W.map (Int.castRingHom ℚ)) u) 1 :=
  nonvanishing_odd_of_prints hB hM hH hE Φ h2 (bad_of_dvd hbad) B hB'
    (rootNumber_of_mem_integral_modular hDes hM hH hE Φ h2 h3 hbad hu₀ hsf₀ hodd)

end ZInQ.Manuscript.RC.GlueSweep.Ana

import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Symbols

/-!
# The coefficient dictionary input (O.9) in the manuscript's form: `a_p ≡ p + 1 (mod 4)`

Manuscript `diophantine_zq.tex`, tex L9585 ("For a split prime `a_p ≡ p + 1 (mod 4)`") and
L9593–9594 ("Here every prime is split in the rational two-torsion field, so
`a_p ≡ p + 1 (mod 4)`").

DEPARTURE (§(4b), O.9): the coefficient dictionary (`CoefficientDictionary/Rules.lean`) assumes
only `ApEven` (`a_p` even at good primes), which is weaker than the manuscript's statement. This
file states the manuscript's input and closes the departure for the actual curves:

* `ApModFour T ap`: `a_p ≡ p + 1 (mod 4)` at every good prime (the manuscript's (O.9) input).
* `apEven_of_apModFour` (PROVED): `ApModFour → ApEven` (good primes are odd), so every consumer
  of `ApEven` accepts the manuscript's input.
* **`apModFour_curve_typeData` (PROVED)**: for the actual curve `E_m : y² = x(x − m)(x + 3m)`
  (`ZInQ.Manuscript.curve m`, full rational two-torsion) and any type data whose conductor
  contains every prime factor of `6m`, the coefficients of Mathlib's `L(E_m, s)` satisfy
  `ApModFour`. This is lane RC's `apModFour_curve`: `a_p = p + 1 − |Ẽ_m(𝔽_p)|` and
  `Ẽ_m(𝔽_p)[2] = {O, (0, 0), (m, 0), (−3m, 0)}` has order four.
* `apEven_curve_typeData`: hence `ApEven` for the actual curve, through the manuscript's form.
* Non-vacuity: `apModFour_curve_one_five` — `a_5(E_1) ≡ 6 (mod 4)`.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.FrobCount

open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- **The manuscript's (O.9) input**: `a_p ≡ p + 1 (mod 4)` at every good prime. -/
def ApModFour (T : TypeData L ε) (ap : ℕ → ℤ) : Prop :=
  ∀ p, T.Good p → ap p ≡ (p : ℤ) + 1 [ZMOD 4]

/-- **The manuscript's input implies the dictionary's** (good primes are odd). PROVED. -/
theorem apEven_of_apModFour (T : TypeData L ε) (ap : ℕ → ℤ) (h : ApModFour T ap) :
    ApEven T ap := by
  intro p hp
  obtain ⟨k, hk⟩ := hp.1.odd_of_ne_two hp.ne_two
  have h4 := Int.emod_emod_of_dvd (ap p) (show (2 : ℤ) ∣ 4 by norm_num)
  have h4' := Int.emod_emod_of_dvd ((p : ℤ) + 1) (show (2 : ℤ) ∣ 4 by norm_num)
  have hmod : ap p % 4 = ((p : ℤ) + 1) % 4 := h p hp
  rw [even_iff_two_dvd, Int.dvd_iff_emod_eq_zero, ← h4, hmod, h4']
  subst hk
  push_cast
  omega

/-- **(O.9) for the actual curve** `E_m` (full rational two-torsion), for type data whose
conductor contains every prime factor of `6m`. PROVED (lane RC's `apModFour_curve`). -/
theorem apModFour_curve_typeData (T : TypeData L ε) (m : ℤ)
    (hM : ∀ q : ℕ, q.Prime → q ∣ 6 * m.natAbs → q ∣ T.m) :
    ApModFour T (fun p => (ZInQ.Manuscript.curve (m : ℚ)).LFunction p) :=
  fun p hp => ZInQ.Manuscript.RC.AddressGenuine.apModFour_curve m T.m hM p hp.1 hp.2

/-- `ApEven` for the actual curve, through the manuscript's form. PROVED. -/
theorem apEven_curve_typeData (T : TypeData L ε) (m : ℤ)
    (hM : ∀ q : ℕ, q.Prime → q ∣ 6 * m.natAbs → q ∣ T.m) :
    ApEven T (fun p => (ZInQ.Manuscript.curve (m : ℚ)).LFunction p) :=
  apEven_of_apModFour T _ (apModFour_curve_typeData T m hM)

/-- **Non-vacuity**: `a_5(E_1) ≡ 6 (mod 4)`. -/
theorem apModFour_curve_one_five :
    (ZInQ.Manuscript.curve ((1 : ℤ) : ℚ)).LFunction 5 ≡ (5 : ℤ) + 1 [ZMOD 4] := by
  have := ZInQ.Manuscript.RC.AddressGenuine.apModFour_curve 1 6
    (fun q _ hq => by simpa using hq) 5 (by norm_num) (by norm_num)
  exact_mod_cast this

end ZInQ.Contrib.CloudB3RC53.FrobCount

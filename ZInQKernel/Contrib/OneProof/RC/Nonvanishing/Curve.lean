import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.RootNumberCheck

/-!
# Lane RC13 (nonvanishing), part 6: the curve `E_ℓ` of Section 7

The fixed curve of Section 7 is `E = E_ℓ : y² = x(x - ℓ)(x + 3ℓ)` (tex 1761–1763,
`CloudB3RC53.Ecurve ℓ`), and its twists are again curves of the family
(`qtwist (curve ℓ) u = curve (u * ℓ)`). This file specializes part 4 to `E_ℓ` and derives the two
other applications of Section `sec:nonvan` in the proof:

* `nonvanishing_even_curve`, `nonvanishing_odd_curve`: Proposition `ex:sec7-nonvanishing` for
  `E_ℓ` (tex 1968–2004), with the twists written as `curve (u * ℓ)`.
* `rootNumber_curve_twist`: in the filter containing one at `S ⊇ {2, 3} ∪ primes(ℓ)`, the root
  number of `E^{(h)}` is `sgn(h) w(E)` (BFH p. 543); so with `w(E) = −1` (Dokchitser–Dokchitser,
  tex 1793–1797) the positive filter is odd (tex 2346: "`w(E^{(h)}) = −1`") and the negative one
  even.
* `genusPartner`: a negative genus partner `h_*` with `L(E^{(h_*)}, 1) ≠ 0`, odd fundamental,
  `|h_*| > 4`, in the squareclasses of the prepared filter containing one at every `p ∈ S`
  (tex 2404–2410), from the even case; `genusPartner_of_BFH` the same from clause (ii) of
  Bump–Friedberg–Hoffstein, as App F (8251–8254) does it.
* `witness`: a positive squarefree `D_w` in the filter containing one with
  `ord_{s=1} L(E^{(D_w)}, s) = 1` ("Section `sec:nonvan` supplies `L'(E^{(D_w)}, 1) ≠ 0`",
  tex 2461–2463), from the odd case.
-/

namespace ZInQ.Manuscript.RC.Nonvanishing

open ZInQ.Manuscript ZInQ.Manuscript.PoleS12 ZInQ.Contrib.CloudB3RC53 SignedUnitFilter

/-- **The bad primes of `E_m` lie in `S`** when `2, 3 ∈ S` and every prime factor of `m` lies in
`S` (`E_m` is good at every `p ∤ 6m`). PROVED. -/
theorem bad_curve_mem {m : ℤ} {S : Finset ℕ} (h2 : 2 ∈ S) (h3 : 3 ∈ S)
    (hm : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → p ∈ S) :
    ∀ p : ℕ, p.Prime → ¬ GoodAt (curve (m : ℚ)) p → p ∈ S := by
  intro p hp hng
  by_contra hpS
  apply hng (goodAt_curve hp ?_)
  intro hdvd
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpZ.dvd_or_dvd hdvd with h6 | hpm
  · have h6' : p ∣ 6 := by exact_mod_cast h6
    have : p = 2 ∨ p = 3 := by
      have h6'' : p ∣ 2 * 3 := h6'
      rcases (Nat.Prime.dvd_mul hp).mp h6'' with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
    rcases this with rfl | rfl
    · exact hpS h2
    · exact hpS h3
  · exact hpS (hm p hp hpm)

theorem curve_nat_isElliptic {ℓ : ℕ} (hℓ : 0 < ℓ) : (Ecurve ℓ).IsElliptic :=
  curve_isElliptic' (by exact_mod_cast hℓ.ne')

theorem qtwist_Ecurve (ℓ : ℕ) (u : ℤ) : qtwist (Ecurve ℓ) (u : ℚ) = curve ((u * ℓ : ℤ) : ℚ) := by
  rw [Ecurve, qtwist_curve]; push_cast; ring_nf

/-- **Proposition `ex:sec7-nonvanishing`, even case, for `E_ℓ`** (tex 1968–1991). PROVED. -/
theorem nonvanishing_even_curve (hHL : HoffsteinLuo) (hTS : BFHTwistSign) (hBCDT : BCDTThmA)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S) (h3 : 3 ∈ Φ.S)
    (hℓS : ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ Φ.S) (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime)
    (heven : Φ.RootNumber (Ecurve ℓ) 1) :
    ∃ u : ℤ, Φ.Mem u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧ omega u ≤ 5 ∧
      CentralNonzero (curve ((u * ℓ : ℤ) : ℚ)) := by
  have hbad := bad_curve_mem (m := (ℓ : ℤ)) h2 h3 fun p hp h => hℓS p hp (by exact_mod_cast h)
  obtain ⟨u, hu, hsf, hB', hω, hL⟩ :=
    nonvanishing_even hHL hTS hBCDT (curve_nat_isElliptic hℓ) Φ h2 (by exact_mod_cast hbad) B hB
      heven
  exact ⟨u, hu, hsf, hB', hω, by rw [← qtwist_Ecurve]; exact hL⟩

/-- **Proposition `ex:sec7-nonvanishing`, odd case, for `E_ℓ`** (tex 1979, 1984–1992). PROVED. -/
theorem nonvanishing_odd_curve (hBFH : BFHSimpleZero) (hBCDT : BCDTThmA)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S) (h3 : 3 ∈ Φ.S)
    (hℓS : ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ Φ.S) (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime)
    (hodd : Φ.RootNumber (Ecurve ℓ) (-1)) :
    ∃ u : ℤ, Φ.Mem u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧
      AnalyticRankOne (curve ((u * ℓ : ℤ) : ℚ)) := by
  have hbad := bad_curve_mem (m := (ℓ : ℤ)) h2 h3 fun p hp h => hℓS p hp (by exact_mod_cast h)
  obtain ⟨u, hu, -, hsf, hB', hL⟩ :=
    nonvanishing_odd hBFH hBCDT (curve_nat_isElliptic hℓ) Φ h2 (by exact_mod_cast hbad) B hB hodd
  exact ⟨u, hu, hsf, hB', by rw [← analyticRank_one_iff, ← qtwist_Ecurve]; exact hL⟩

/-! ### The filters containing `±1` -/

/-- **The signed unit filter of sign `σ` and trivial classes** at `S`: `u` is a square of `ℚ_p` at
every `p ∈ S`. For `σ = 1` this is "the prepared positive unit filter containing one" (tex 2345,
8247), for `σ = -1` its negative counterpart (the genus partner, tex 2405–2406). -/
def trivialFilter (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (σ : ℤˣ) : SignedUnitFilter where
  S := S
  prime_of_mem := hS
  sign := σ
  cls := fun _ => 1
  cls_unit := fun p hp h => (hS p hp).ne_one (Nat.dvd_one.mp (Int.natCast_dvd.mp h))

theorem trivialFilter_mem {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime} {σ : ℤˣ} {u : ℤ}
    (h : (trivialFilter S hS σ).Mem u) : ∀ p ∈ S, IsSquareAt p (u : ℚ) := by
  intro p hp
  have := h.isSquareAt hp
  simpa [trivialFilter] using this

/-- A member of the trivial filter at `S ∋ 2`, other than `1`, is a fundamental discriminant
`≡ 1 (mod 8)` split at every prime of `S`. PROVED. -/
theorem trivialFilter_fund {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime} {σ : ℤˣ} (h2 : 2 ∈ S) {u : ℤ}
    (h : (trivialFilter S hS σ).Mem u) :
    u % 8 = 1 ∧ (∀ p ∈ S, SplitsIn u p) := by
  have hsplit : ∀ p ∈ S, SplitsIn u p := fun p hp =>
    splitsIn_of_isSquareAt (hS p hp) (h.not_dvd hp) (trivialFilter_mem h p hp)
  exact ⟨(hsplit 2 h2).two, hsplit⟩

theorem isFund_of_mod_eight {u : ℤ} (h8 : u % 8 = 1) (hsf : Squarefree u) (h1 : u ≠ 1) :
    IsFundamentalDiscriminant u := ⟨h1, Or.inl ⟨by omega, hsf⟩⟩

/-- **The root number on the trivial filter** (BFH p. 543; tex 2346 "`w(E^{(h)}) = −1`"): for
`h` squarefree in the trivial filter of sign `σ` at `S ⊇ {2, 3} ∪ primes(ℓ)`, `E_ℓ^{(h)}` has root
number `σ w(E_ℓ)`. PROVED from `BFHTwistSign`. -/
theorem rootNumber_curve_twist (hTS : BFHTwistSign) (hBCDT : BCDTThmA) {ℓ : ℕ} (hℓ : 0 < ℓ)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (h2 : 2 ∈ S) (h3 : 3 ∈ S)
    (hℓS : ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ S) {w : ℤ} (hw : RootNumber (Ecurve ℓ) w) (σ : ℤˣ) :
    (trivialFilter S hS σ).RootNumber (Ecurve ℓ) ((σ : ℤ) * w) := by
  intro u hu hsf
  have hE := curve_nat_isElliptic hℓ
  obtain ⟨h8, hsplit⟩ := trivialFilter_fund h2 hu
  have hbad := bad_curve_mem (m := (ℓ : ℤ)) h2 h3 fun p hp h => hℓS p hp (by exact_mod_cast h)
  have hsign : Int.sign u = (σ : ℤ) := hu.2.1
  by_cases hu1 : u = 1
  · -- `u = 1`: `E^{(1)} = E` and `σ = 1`
    subst hu1
    have hσ : (σ : ℤ) = 1 := by rw [← hsign]; rfl
    rw [hσ, one_mul]
    have : qtwist (Ecurve ℓ) ((1 : ℤ) : ℚ) = Ecurve ℓ := by
      rw [Int.cast_one, Ecurve, qtwist_curve, one_mul]
    rw [this]; exact hw
  · have := hTS _ hE (hBCDT _ hE) w hw u (isFund_of_mod_eight h8 hsf hu1)
      fun p hp hng => hsplit p (by exact_mod_cast hbad p hp hng)
    rwa [hsign] at this

/-! ### The genus partner and the fixed witness -/

/-- **The genus partner `h_*`** (tex 2404–2410; via Proposition `ex:sec7-nonvanishing`). With
`w(E_ℓ) = −1` (Dokchitser–Dokchitser, tex 1793–1797), for any finite `S ⊇ {2, 3} ∪ primes(ℓ)` and
any finite avoidance set `B` there is a negative odd fundamental discriminant `h_*`,
`h_* ≡ 1 (mod 8)` (so `|h_*| > 4` and `ℚ(√h_*) ≠ ℚ(i), ℚ(√−3)`), a square of `ℚ_p` at every
`p ∈ S` (the squareclasses of the prepared filter containing one), prime to `S ∪ B`, with
`L(E^{(h_*)}, 1) ≠ 0` and `ω(h_*) ≤ 5`. PROVED. -/
theorem genusPartner (hHL : HoffsteinLuo) (hTS : BFHTwistSign) (hBCDT : BCDTThmA) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hw : RootNumber (Ecurve ℓ) (-1)) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (h2 : 2 ∈ S) (h3 : 3 ∈ S) (hℓS : ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ S)
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) :
    ∃ hstar : ℤ, hstar < 0 ∧ hstar % 8 = 1 ∧ IsFundamentalDiscriminant hstar ∧
      (∀ p ∈ S, IsSquareAt p (hstar : ℚ) ∧ ¬ (p : ℤ) ∣ hstar) ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ hstar) ∧
      omega hstar ≤ 5 ∧ CentralNonzero (curve ((hstar * ℓ : ℤ) : ℚ)) := by
  have heven : (trivialFilter S hS (-1)).RootNumber (Ecurve ℓ) 1 := by
    have := rootNumber_curve_twist hTS hBCDT hℓ hS h2 h3 hℓS hw (-1)
    simpa using this
  obtain ⟨u, hu, hsf, hB', hω, hL⟩ :=
    nonvanishing_even_curve hHL hTS hBCDT hℓ (trivialFilter S hS (-1)) h2 h3 hℓS B hB heven
  obtain ⟨h8, -⟩ := trivialFilter_fund h2 hu
  have hneg : u < 0 := by
    have hs : Int.sign u = -1 := hu.2.1
    rcases lt_trichotomy u 0 with h | h | h
    · exact h
    · exact absurd h hu.ne_zero
    · rw [Int.sign_eq_one_of_pos h] at hs; exact absurd hs (by decide)
  exact ⟨u, hneg, h8, isFund_of_mod_eight h8 hsf (by omega),
    fun p hp => ⟨trivialFilter_mem hu p hp, hu.not_dvd hp⟩, hB', hω, hL⟩

/-- **The genus partner from Bump–Friedberg–Hoffstein, clause (ii)** (App F, tex 8251–8254: "Apply
clause (ii) of [bfh, pp. 543–544] to its weight-two newform, with every old prime in the splitting
set, to obtain a negative fundamental discriminant `h_*` with `L(E^{(h_*)}, 1) ≠ 0`. Including two
makes `h_*` odd and excludes the extra-unit fields."). PROVED. -/
theorem genusPartner_of_BFH (hBFH : BFHNonvanishing) (hBCDT : BCDTThmA) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hw : RootNumber (Ecurve ℓ) (-1)) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (h2 : 2 ∈ S) (h3 : 3 ∈ S) (hℓS : ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ S) :
    ∃ hstar : ℤ, hstar < 0 ∧ hstar % 8 = 1 ∧ IsFundamentalDiscriminant hstar ∧
      (∀ p ∈ S, SplitsIn hstar p) ∧ CentralNonzero (curve ((hstar * ℓ : ℤ) : ℚ)) := by
  have hE := curve_nat_isElliptic hℓ
  have hbad := bad_curve_mem (m := (ℓ : ℤ)) h2 h3 fun p hp h => hℓS p hp (by exact_mod_cast h)
  obtain ⟨D, hDF, hDs, hDsplit, hDL⟩ :=
    hBFH _ hE (hBCDT _ hE) (-1) hw S hS (by exact_mod_cast hbad)
  have hneg : D < 0 := by linarith
  exact ⟨D, hneg, (hDsplit 2 h2).two, hDF, hDsplit, by rw [← qtwist_Ecurve]; exact hDL⟩

/-- **The fixed witness `D_w`** (tex 2461–2463: "Choose one positive squarefree `D_w` in the odd
filter containing one, after adjoining the primes of `h_*` and their compatible unit tests.
Section `sec:nonvan` supplies `L'(E^{(D_w)}, 1) ≠ 0`."). With `w(E_ℓ) = −1`, for any finite
`S ⊇ {2, 3} ∪ primes(ℓ)` (to contain the primes of `h_*`) and avoidance set `B`, there is a positive
squarefree `D_w ≡ 1 (mod 8)`, a square of `ℚ_p` at every `p ∈ S`, prime to `S ∪ B`, with
`ord_{s=1} L(E^{(D_w)}, s) = 1`. PROVED (odd case of `ex:sec7-nonvanishing`). -/
theorem witness (hBFH : BFHSimpleZero) (hTS : BFHTwistSign) (hBCDT : BCDTThmA) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hw : RootNumber (Ecurve ℓ) (-1)) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (h2 : 2 ∈ S) (h3 : 3 ∈ S) (hℓS : ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ S)
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) :
    ∃ Dw : ℤ, 0 < Dw ∧ Dw % 8 = 1 ∧ Squarefree Dw ∧
      (∀ p ∈ S, IsSquareAt p (Dw : ℚ) ∧ ¬ (p : ℤ) ∣ Dw) ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ Dw) ∧
      AnalyticRankOne (curve ((Dw * ℓ : ℤ) : ℚ)) := by
  have hodd : (trivialFilter S hS 1).RootNumber (Ecurve ℓ) (-1) := by
    have := rootNumber_curve_twist hTS hBCDT hℓ hS h2 h3 hℓS hw 1
    simpa using this
  obtain ⟨u, hu, hsf, hB', hL⟩ :=
    nonvanishing_odd_curve hBFH hBCDT hℓ (trivialFilter S hS 1) h2 h3 hℓS B hB hodd
  obtain ⟨h8, -⟩ := trivialFilter_fund h2 hu
  have hpos : 0 < u := by
    have hs : Int.sign u = 1 := hu.2.1
    exact Int.sign_eq_one_iff_pos.mp hs
  exact ⟨u, hpos, h8, hsf, fun p hp => ⟨trivialFilter_mem hu p hp, hu.not_dvd hp⟩, hB', hL⟩

end ZInQ.Manuscript.RC.Nonvanishing

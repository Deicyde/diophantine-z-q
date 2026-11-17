import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Realization
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Prints

/-!
# Lane RC13 (nonvanishing), part 4: the five-prime proposition and nonvanishing in a filter

* `fivePrime` — **Proposition `ex:app-five-prime`** (App G, tex 10001–10033), PROVED from
  Hoffstein–Luo (`HoffsteinLuoBound r`; the printed `r = 4` gives the bound five), the twisted sign
  (`BFHTwistSign`) and modularity (`BCDTThmA`), with the CRT and Dirichlet step of part 2. The
  proof follows App G line by line: the signed prime `q₀` (10016–10017), Hoffstein–Luo applied to
  `A^{q₀}` with splitting set `S' = S ∪ B ∪ {|q₀|}` (10017–10024; `S'` contains every prime at which
  the model of `A^{q₀}` is not good), `d > 0` from the functional equation (10025–10026),
  `d ≡ 1 (mod 8)` from splitting at two (10026–10027), and the properties of `q₀d` (10027–10029).
* `nonvanishing_even`, `nonvanishing_odd` — **Proposition `ex:sec7-nonvanishing`** (tex
  1968–2004), even case from `fivePrime`, odd case from the simple-zero clause (i) of
  Bump–Friedberg–Hoffstein (`BFHSimpleZero`), PROVED.
* `rootNumber_of_mem` — **the root-number check** (tex 1994–2001), PROVED from the local
  root-number interface `LocalRootNumbers` (Desjardins, Prop. 3.3): the root number of `A^{(u)}`
  is the same for all squarefree `u` in a signed unit filter at `S ∋ 2, 3`, so a filter "has a
  root number"; the dyadic classes `3, 7 (mod 8)` are allowed and no odd-discriminant root formula
  is used on them.
* `fivePrime_of_mem`, `nonvanishing_odd_of_mem`: the two propositions with the filter's root
  number read off one parameter, as the manuscript states them.
* `nonvanishing_even_curve`, `nonvanishing_odd_curve`: the case `E = E_ℓ` of Section 7, with the
  twists written as curves of the family.
-/

namespace ZInQ.Manuscript.RC.Nonvanishing

open ZInQ.Manuscript ZInQ.Manuscript.PoleS12 ZInQ.Contrib.CloudB3RC53 SignedUnitFilter

/-! ### Small facts about the signed prime -/

theorem natAbs_unit_mul (σ : ℤˣ) (q : ℕ) : ((σ : ℤ) * q).natAbs = q := by
  rcases Int.units_eq_one_or σ with h | h <;> rw [h] <;> simp

theorem squarefree_unit_mul_prime (σ : ℤˣ) {q : ℕ} (hq : q.Prime) : Squarefree ((σ : ℤ) * q) := by
  rw [← Int.squarefree_natAbs, natAbs_unit_mul]; exact hq.squarefree

theorem not_dvd_unit_mul_prime {σ : ℤˣ} {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q) :
    ¬ (p : ℤ) ∣ (σ : ℤ) * q := by
  intro h
  have h' : p ∣ ((σ : ℤ) * q).natAbs := Int.natCast_dvd.mp h
  rw [natAbs_unit_mul] at h'
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h')

/-- The primes at which `A^{(q₀)}` is not good lie in `S ∪ {q}` (`q₀ = ±q`, `2 ∈ S`). PROVED. -/
theorem bad_twist_subset {A : WeierstrassCurve ℚ} {S : Finset ℕ} (h2 : 2 ∈ S)
    (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt A p → p ∈ S) {σ : ℤˣ} {q : ℕ} (hq : q.Prime) :
    ∀ p : ℕ, p.Prime → ¬ GoodAt (qtwist A (((σ : ℤ) * q : ℤ) : ℚ)) p → p ∈ S ∨ p = q := by
  intro p hp hng
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hpS, hpq⟩ := hcon
  have hp2 : p ≠ 2 := fun h => hpS (h ▸ h2)
  have hgood : GoodAt A p := by by_contra h; exact hpS (hbad p hp h)
  exact hng (goodAt_twist hp hp2 hgood (not_dvd_unit_mul_prime hq hp hpq))

/-- `ω(q₀ d) = 1 + ω(d)` when `q ∤ d`. PROVED. -/
theorem omega_unit_mul_prime_mul {σ : ℤˣ} {q : ℕ} (hq : q.Prime) {d : ℤ}
    (hqd : ¬ (q : ℤ) ∣ d) : omega ((σ : ℤ) * q * d) = 1 + omega d := by
  have hcop : Nat.Coprime q d.natAbs :=
    (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => hqd (Int.natCast_dvd.mpr h)
  have h : ((σ : ℤ) * q * d).natAbs = q * d.natAbs := by rw [Int.natAbs_mul, natAbs_unit_mul]
  simp only [omega]
  rw [h, ArithmeticFunction.cardDistinctFactors_mul hcop,
    ArithmeticFunction.cardDistinctFactors_apply_prime hq]

theorem squarefree_unit_mul_prime_mul {σ : ℤˣ} {q : ℕ} (hq : q.Prime) {d : ℤ}
    (hd : Squarefree d) (hqd : ¬ (q : ℤ) ∣ d) : Squarefree ((σ : ℤ) * q * d) := by
  have hcop : Nat.Coprime q d.natAbs :=
    (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => hqd (Int.natCast_dvd.mpr h)
  rw [← Int.squarefree_natAbs, Int.natAbs_mul, natAbs_unit_mul]
  exact Nat.squarefree_mul_iff.mpr ⟨hcop, hq.squarefree, Int.squarefree_natAbs.mpr hd⟩

theorem twist_mul_cast (A : WeierstrassCurve ℚ) (q₀ d : ℤ) :
    qtwist (qtwist A (q₀ : ℚ)) (d : ℚ) = qtwist A ((q₀ * d : ℤ) : ℚ) := by
  rw [qtwist_qtwist]; push_cast; ring_nf

/-- **Non-vacuity of `SignedUnitFilter.RootNumber`**: every signed unit filter has a squarefree
member (a signed prime), so "the filter has root number `w`" is a genuine condition on the root
number of an actual twist. PROVED. -/
theorem SignedUnitFilter.exists_squarefree_mem (Φ : SignedUnitFilter) :
    ∃ u : ℤ, Φ.Mem u ∧ Squarefree u := by
  obtain ⟨q, hq, -, -, hmem⟩ := Φ.exists_signed_prime ∅
  exact ⟨_, hmem, squarefree_unit_mul_prime _ hq⟩

/-! ### Proposition `ex:app-five-prime` -/

/-- **Proposition `ex:app-five-prime`** (App G, tex 10001–10033; PROVED from the prints). Let `A/ℚ`
be an elliptic curve (modular by BCDT), `S` a finite set of primes containing `2` and every prime
at which the model of `A` is not good, and `B` a finite exclusion set of primes. In every signed
unit filter at `S` of even root number there is a signed odd squarefree parameter `u`, prime to
`S ∪ B`, with `L(A^{(u)}, 1) ≠ 0` and `ω(u) ≤ r + 1`, where `r` is the Hoffstein–Luo bound
(`r = 4` in the print: `fivePrime_four`). Only the intermediate parameter `d` is fundamental;
`u` itself need not be (its field discriminant may be `4u`). No bound on the size of `u` is
asserted. The hypothesis `3 ∈ S` of the manuscript is not needed here (it enters the root-number
check, `rootNumber_of_mem`). -/
theorem fivePrime {r : ℕ} (hHL : HoffsteinLuoBound r) (hTS : BFHTwistSign) (hBCDT : BCDTThmA)
    {A : WeierstrassCurve ℚ} (hA : A.IsElliptic) (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S)
    (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt A p → p ∈ Φ.S)
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (heven : Φ.RootNumber A 1) :
    ∃ u : ℤ, Φ.Mem u ∧ Odd u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧ omega u ≤ r + 1 ∧
      CentralNonzero (qtwist A u) := by
  classical
  -- tex 10016–10017: by CRT and Dirichlet, a signed prime `q₀ = σq` in the filter, outside `S ∪ B`
  obtain ⟨q, hq, hqB, hqS, hmem⟩ := Φ.exists_signed_prime B
  set q₀ : ℤ := (Φ.sign : ℤ) * q with hq₀
  have hq₀0 : (q₀ : ℚ) ≠ 0 := by exact_mod_cast hmem.ne_zero
  have hA' : (qtwist A q₀).IsElliptic := qtwist_isElliptic hA hq₀0
  -- `A^{q₀}` has even root number (the filter is even)
  have hw' : RootNumber (qtwist A q₀) 1 := heven q₀ hmem (squarefree_unit_mul_prime _ hq)
  -- tex 10019–10022: the splitting set `S' = S ∪ B ∪ {|q₀|} ∪ {p ∣ N_{A^{q₀}}}`
  let S' : Finset ℕ := Φ.S ∪ B ∪ {q}
  have hS'p : ∀ p ∈ S', p.Prime := by
    intro p hp
    simp only [S', Finset.mem_union, Finset.mem_singleton] at hp
    rcases hp with (hp | hp) | rfl
    · exact Φ.prime_of_mem p hp
    · exact hB p hp
    · exact hq
  have hS'bad : ∀ p : ℕ, p.Prime → ¬ GoodAt (qtwist A q₀) p → p ∈ S' := by
    intro p hp hng
    rcases bad_twist_subset h2 hbad hq p hp hng with h | h
    · simp [S', h]
    · simp [S', h]
  -- tex 10023–10024: Hoffstein–Luo gives a fundamental `d`, split at `S'`, `ω(d) ≤ r`
  obtain ⟨d, hdF, hdodd, hdω, hdsplit, hdL⟩ :=
    (hHL _ hA' (hBCDT _ hA') S' hS'p hS'bad).nonempty
  -- tex 10025–10026: the functional equation forces `d > 0`
  have hdpos : 0 < d := by
    have hwd := hTS _ hA' (hBCDT _ hA') 1 hw' d hdF fun p hp h => hdsplit p (hS'bad p hp h)
    have h1 := rootNumber_eq_one_of_centralNonzero hwd hdL
    rw [mul_one] at h1
    exact Int.sign_eq_one_iff_pos.mp h1
  -- tex 10026–10027: splitting at two gives `d ≡ 1 (mod 8)`; `d` is squarefree
  have hdsf : Squarefree d := (hdF.squarefree_of_odd hdodd).1
  have hqd : ¬ (q : ℤ) ∣ d := (hdsplit q (by simp [S'])).not_dvd hq
  -- tex 10027–10029: `q₀d` has the original classes, is prime to `B`, squarefree, `ω ≤ r + 1`
  refine ⟨q₀ * d, Φ.mem_mul hmem hdpos fun p hp => hdsplit p (by simp [S', hp]),
    Int.odd_mul.mpr ⟨hmem.odd h2, hdodd⟩, squarefree_unit_mul_prime_mul hq hdsf hqd, ?_, ?_, ?_⟩
  · intro p hp hdvd
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (hB p hp)
    rcases hpZ.dvd_or_dvd hdvd with h | h
    · exact not_dvd_unit_mul_prime hq (hB p hp) (fun hpq => hqB (hpq ▸ hp)) h
    · exact (hdsplit p (by simp [S', hp])).not_dvd (hB p hp) h
  · rw [omega_unit_mul_prime_mul hq hqd]; omega
  · rw [← twist_mul_cast]; exact hdL

/-- **Proposition `ex:app-five-prime` with the printed bound** (`r = 4`): at most five primes. -/
theorem fivePrime_four (hHL : HoffsteinLuo) (hTS : BFHTwistSign) (hBCDT : BCDTThmA)
    {A : WeierstrassCurve ℚ} (hA : A.IsElliptic) (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S)
    (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt A p → p ∈ Φ.S)
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (heven : Φ.RootNumber A 1) :
    ∃ u : ℤ, Φ.Mem u ∧ Odd u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧ omega u ≤ 5 ∧
      CentralNonzero (qtwist A u) :=
  fivePrime hHL hTS hBCDT hA Φ h2 hbad B hB heven

/-! ### Proposition `ex:sec7-nonvanishing` -/

/-- **Proposition `ex:sec7-nonvanishing`, even case** (tex 1968–1991; PROVED). In a signed unit
filter at `S` (containing `2` and the primes where the model is not good) of even root number,
outside any finite avoidance set `B`, there is a squarefree parameter with at most five prime
factors and nonzero central value. The bound does not depend on `S`, `B` or the filter. -/
theorem nonvanishing_even (hHL : HoffsteinLuo) (hTS : BFHTwistSign) (hBCDT : BCDTThmA)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S)
    (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt E p → p ∈ Φ.S)
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (heven : Φ.RootNumber E 1) :
    ∃ u : ℤ, Φ.Mem u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧ omega u ≤ 5 ∧
      CentralNonzero (qtwist E u) := by
  obtain ⟨u, hu, -, hsf, hB', hω, hL⟩ := fivePrime_four hHL hTS hBCDT hE Φ h2 hbad B hB heven
  exact ⟨u, hu, hsf, hB', hω, hL⟩

/-- **Proposition `ex:sec7-nonvanishing`, odd case** (tex 1979, 1984–1992; PROVED from the
simple-zero clause (i) of Bump–Friedberg–Hoffstein). In a signed unit filter of odd root number,
outside any finite avoidance set `B`, there is a squarefree parameter `u` with a simple zero:
`ord_{s=1} L(E^{(u)}, s) = 1`. No prime-count bound is asserted. -/
theorem nonvanishing_odd (hBFH : BFHSimpleZero) (hBCDT : BCDTThmA)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S)
    (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt E p → p ∈ Φ.S)
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (hodd : Φ.RootNumber E (-1)) :
    ∃ u : ℤ, Φ.Mem u ∧ Odd u ∧ Squarefree u ∧ (∀ p ∈ B, ¬ (p : ℤ) ∣ u) ∧
      AnalyticRank (qtwist E u) 1 := by
  classical
  -- tex 1984–1985: the signed prime `q₀`
  obtain ⟨q, hq, hqB, hqS, hmem⟩ := Φ.exists_signed_prime B
  set q₀ : ℤ := (Φ.sign : ℤ) * q with hq₀
  have hq₀0 : (q₀ : ℚ) ≠ 0 := by exact_mod_cast hmem.ne_zero
  have hE' : (qtwist E q₀).IsElliptic := qtwist_isElliptic hE hq₀0
  have hw' : RootNumber (qtwist E q₀) (-1) := hodd q₀ hmem (squarefree_unit_mul_prime _ hq)
  -- tex 1987–1989: BFH on `E^{(q₀)}`, positive `d` split at `S ∪ B ∪ {|q₀|}` and the conductor
  let S' : Finset ℕ := Φ.S ∪ B ∪ {q}
  have hS'p : ∀ p ∈ S', p.Prime := by
    intro p hp
    simp only [S', Finset.mem_union, Finset.mem_singleton] at hp
    rcases hp with (hp | hp) | rfl
    · exact Φ.prime_of_mem p hp
    · exact hB p hp
    · exact hq
  have hS'bad : ∀ p : ℕ, p.Prime → ¬ GoodAt (qtwist E q₀) p → p ∈ S' := by
    intro p hp hng
    rcases bad_twist_subset h2 hbad hq p hp hng with h | h
    · simp [S', h]
    · simp [S', h]
  -- tex 1992: the simple-zero clause
  obtain ⟨d, hdF, hdsign, hdsplit, hdL⟩ := hBFH _ hE' (hBCDT _ hE') (-1) hw' S' hS'p hS'bad
  have hdpos : 0 < d := by linarith
  have hd8 : d % 8 = 1 := (hdsplit 2 (by simp [S', h2])).two
  have hdodd : Odd d := Int.odd_iff.mpr (by omega)
  have hdsf : Squarefree d := (hdF.squarefree_of_odd hdodd).1
  have hqd : ¬ (q : ℤ) ∣ d := (hdsplit q (by simp [S'])).not_dvd hq
  refine ⟨q₀ * d, Φ.mem_mul hmem hdpos fun p hp => hdsplit p (by simp [S', hp]),
    Int.odd_mul.mpr ⟨hmem.odd h2, hdodd⟩, squarefree_unit_mul_prime_mul hq hdsf hqd, ?_, ?_⟩
  · intro p hp hdvd
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (hB p hp)
    rcases hpZ.dvd_or_dvd hdvd with h | h
    · exact not_dvd_unit_mul_prime hq (hB p hp) (fun hpq => hqB (hpq ▸ hp)) h
    · exact (hdsplit p (by simp [S', hp])).not_dvd (hB p hp) h
  · rw [← twist_mul_cast]; exact hdL

end ZInQ.Manuscript.RC.Nonvanishing

import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Curve

/-!
# Lane RC13 (nonvanishing), part 7: the rough companion (tex 2343–2401, App G 10035–10150)

**The construction** (`roughCompanion_nonvanishing`, PROVED from the prints). For the rough
companion "the curve itself varies: write `a` for the bounded dummy product and take
`A = E^{ha}`. Choose `q₀` so `k₀ = aq₀` is negative, `1` modulo eight and a square at every prime of
`2Nh`, with the required exclusions. Then `k₀` is odd fundamental, prime to `N_{E^h}`, and
`w(E^{hk₀}) = w(E^h)χ_{k₀}(−N_{E^h}) = +1`. … Apply Hoffstein–Luo to `E^{hk₀}` with every conductor,
old, `h`, dummy and forbidden prime in its splitting set. The resulting `k' = k₀d` adds at most
five new primes" (App G 10040–10051); in the main text: "Absorb `h` and the dummy product into the
curve and use the preceding nonvanishing theorem in its even filter. It adds at most five new
primes" (2382–2384). The Lean proof is exactly this: Proposition `ex:app-five-prime`
(`fivePrime_four`) applied to `A = E^{(ha)}` in the *companion filter* (`companionFilter`: sign
`−1`, class of `a` at `S ∪ primes(h)`, so that `aq₀` is a square there), whose even root number
is the text's direct sign computation (`companionFilter_rootNumber`, from `BFHTwistSign`). Then
`k' = a u` with `u = q₀ d` the output of the proposition.

**The assembly of (3.3)** (`roughCompanion`, PROVED from the construction and three inputs stated
as hypotheses in the manuscript's order of choices): constants `A = (dummy count) + 5` and
`C_E = C₁` are fixed before `h` and the exclusion set; then for each `h` and exclusion set the
dummy realization (RC2), the construction above, the forward rank-zero theorem (PRINT) and (3.3b)
(RC2, the even upper bound) give `k'` with (3.3):
`ω(k') ≤ A`, `v₂L_*(hk') ≤ 2ω(h) + 2ω(k') + s(hk') + C_E`.
-/

namespace ZInQ.Manuscript.RC.Nonvanishing

open ZInQ.Manuscript ZInQ.Manuscript.PoleS12 ZInQ.Contrib.CloudB3RC53 SignedUnitFilter

/-- **The companion filter** at `S ∪ primes(h) ∪ primes(a)`: sign `−1`, the class of `a` at the
primes of `S ∪ primes(h)` (so that `a u` is a square there, i.e. `k₀ = aq₀` is "a square at every
prime of `2Nh`", tex 10042–10043), and the trivial class at the dummy primes. -/
def companionFilter (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (h a : ℤ) (ha : a ≠ 0) :
    SignedUnitFilter where
  S := S ∪ h.natAbs.primeFactors ∪ a.natAbs.primeFactors
  prime_of_mem := by
    intro p hp
    simp only [Finset.mem_union] at hp
    rcases hp with (hp | hp) | hp
    · exact hS p hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
  sign := -1
  cls := fun p => if p ∈ a.natAbs.primeFactors then 1 else a
  cls_unit := by
    intro p hp hdvd
    have hpp : p.Prime := by
      simp only [Finset.mem_union] at hp
      rcases hp with (hp | hp) | hp
      · exact hS p hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp
    split_ifs at hdvd with hpa
    · exact hpp.ne_one (Nat.dvd_one.mp (Int.natCast_dvd.mp hdvd))
    · exact hpa (Nat.mem_primeFactors.mpr ⟨hpp, Int.natCast_dvd.mp hdvd,
        Int.natAbs_ne_zero.mpr ha⟩)

theorem not_dvd_of_coprime_prime {p : ℕ} (hp : p.Prime) {a h : ℤ} (hah : IsCoprime a h)
    (hph : (p : ℤ) ∣ h) : ¬ (p : ℤ) ∣ a := fun hpa =>
  (Nat.prime_iff_prime_int.mp hp).not_isUnit (hah.isUnit_of_dvd' hpa hph)

/-- Members `u` of the companion filter: `a u` is a square of `ℚ_p` and prime to `p` at every
`p ∈ S ∪ primes(h)`, `a u ≡ 1 (mod 8)`, `a u < 0`, and `a u` is squarefree with `a, u` coprime.
PROVED. -/
theorem companionFilter_mem {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime} (h2 : 2 ∈ S) {h a : ℤ}
    {ha : a ≠ 0} (ha0 : 0 < a) (hasf : Squarefree a) (haS : ∀ p ∈ S, ¬ (p : ℤ) ∣ a)
    (hah : IsCoprime a h) {u : ℤ} (hu : (companionFilter S hS h a ha).Mem u)
    (hsf : Squarefree u) :
    (∀ p ∈ S ∪ h.natAbs.primeFactors, IsSquareAt p ((a * u : ℤ) : ℚ) ∧ ¬ (p : ℤ) ∣ a * u) ∧
      (a * u) % 8 = 1 ∧ a * u < 0 ∧ Squarefree (a * u) ∧ IsCoprime a u := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  -- `p ∈ S ∪ primes(h)` is not a dummy prime
  have hnotdummy : ∀ p ∈ S ∪ h.natAbs.primeFactors, p ∉ a.natAbs.primeFactors := by
    intro p hp hpa
    have hpa' : (p : ℤ) ∣ a := Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hpa)
    rcases Finset.mem_union.mp hp with hpS | hph
    · exact haS p hpS hpa'
    · exact not_dvd_of_coprime_prime (Nat.prime_of_mem_primeFactors hpa) hah
        (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hph)) hpa'
  have hsq : ∀ p ∈ S ∪ h.natAbs.primeFactors,
      IsSquareAt p ((a * u : ℤ) : ℚ) ∧ ¬ (p : ℤ) ∣ a * u := by
    intro p hp
    have hpc : p ∈ (companionFilter S hS h a ha).S := by
      simp only [companionFilter, Finset.mem_union] at hp ⊢
      tauto
    have h1 := hu.isSquareAt hpc
    have hcls : (companionFilter S hS h a ha).cls p = a := by
      show (if p ∈ a.natAbs.primeFactors then (1 : ℤ) else a) = a
      simp only [hnotdummy p hp, ↓reduceIte]
    rw [hcls] at h1
    have hpp : p.Prime := (companionFilter S hS h a ha).prime_of_mem p hpc
    refine ⟨?_, ?_⟩
    · have : ((a * u : ℤ) : ℚ) = ((u : ℚ) / a) * (a : ℚ) ^ 2 := by push_cast; field_simp
      rw [this]; exact isSquareAt_mul h1 (isSquareAt_sq _)
    · intro hdvd
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
      rcases hpZ.dvd_or_dvd hdvd with hpa | hpu
      · exact hnotdummy p hp (Nat.mem_primeFactors.mpr ⟨hpp, Int.natCast_dvd.mp hpa,
          Int.natAbs_ne_zero.mpr ha⟩)
      · exact hu.not_dvd hpc hpu
  -- the class at `2`: `u ≡ a (mod 8)`, so `a u ≡ 1 (mod 8)`
  have h2c : 2 ∈ (companionFilter S hS h a ha).S := by simp [companionFilter, h2]
  have hodd_a : Odd a := odd_iff_not_two_dvd.mpr (haS 2 h2)
  have hodd_u : Odd u := hu.odd h2c
  have h8 : (a * u) % 8 = 1 := by
    have hcls2 : (companionFilter S hS h a ha).cls 2 = a := by
      show (if 2 ∈ a.natAbs.primeFactors then (1 : ℤ) else a) = a
      simp only [hnotdummy 2 (Finset.mem_union_left _ h2), ↓reduceIte]
    have h1 := hu.isSquareAt h2c
    rw [hcls2] at h1
    have hm := modEq_eight_of_isSquareAt_two hodd_u hodd_a h1
    obtain ⟨k, rfl⟩ := hodd_a
    unfold Int.ModEq at hm
    have : (2 * k + 1) * u % 8 = (2 * k + 1) * (2 * k + 1) % 8 := by
      rw [Int.mul_emod, hm, ← Int.mul_emod]
    rw [this]
    have hk : (2 * k + 1) * (2 * k + 1) = 4 * (k * (k + 1)) + 1 := by ring
    rw [hk]
    obtain ⟨j, hj⟩ := Int.even_mul_succ_self k
    rw [hj]; omega
  -- the sign
  have hneg : a * u < 0 := by
    have hs : Int.sign u = -1 := hu.2.1
    have hun : u < 0 := by
      rcases lt_trichotomy u 0 with h' | h' | h'
      · exact h'
      · exact absurd h' hu.ne_zero
      · rw [Int.sign_eq_one_of_pos h'] at hs; exact absurd hs (by decide)
    exact mul_neg_of_pos_of_neg ha0 hun
  -- coprimality and squarefreeness
  have hcop : IsCoprime a u := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    have hpa : (p : ℤ) ∣ a := (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_left _ _)
    have hpu : (p : ℤ) ∣ u := (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_right _ _)
    have hpc : p ∈ (companionFilter S hS h a ha).S := by
      simp only [companionFilter, Finset.mem_union]
      exact Or.inr (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp hpa,
        Int.natAbs_ne_zero.mpr ha⟩)
    exact hu.not_dvd hpc hpu
  have hsfau : Squarefree (a * u) := by
    rw [← Int.squarefree_natAbs, Int.natAbs_mul]
    refine Nat.squarefree_mul_iff.mpr ⟨?_, Int.squarefree_natAbs.mpr hasf,
      Int.squarefree_natAbs.mpr hsf⟩
    exact Int.isCoprime_iff_gcd_eq_one.mp hcop
  exact ⟨hsq, h8, hneg, hsfau, hcop⟩

/-- **The sign of the rough companion** (App G 10042–10048: "Then `k₀` is odd fundamental, prime
to `N_{E^h}`, and `w(E^{hk₀}) = w(E^h)χ_{k₀}(−N_{E^h}) = +1`. This proves the sign directly for the
actual application."): with `w(E^{(h)}) = −1`, the companion filter has even root number for
`A = E^{(ha)}` — for every squarefree member `u`, `k₀ = au` is a negative fundamental discriminant
split at every prime where the model of `E^{(h)}` is not good, so `w(E^{(hau)}) = sgn(au) w(E^{(h)})
= +1`. PROVED from `BFHTwistSign`. -/
theorem companionFilter_rootNumber (hTS : BFHTwistSign) (hBCDT : BCDTThmA)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) {S : Finset ℕ} {hS : ∀ p ∈ S, p.Prime}
    (h2 : 2 ∈ S) (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt E p → p ∈ S)
    {h : ℤ} (hh0 : h ≠ 0) (hhw : RootNumber (qtwist E h) (-1))
    {a : ℤ} {ha : a ≠ 0} (ha0 : 0 < a) (hasf : Squarefree a) (haS : ∀ p ∈ S, ¬ (p : ℤ) ∣ a)
    (hah : IsCoprime a h) :
    (companionFilter S hS h a ha).RootNumber (qtwist E ((h * a : ℤ) : ℚ)) 1 := by
  intro u hu hsf
  obtain ⟨hsq, h8, hneg, hsfau, -⟩ := companionFilter_mem h2 ha0 hasf haS hah hu hsf
  have hEh : (qtwist E h).IsElliptic := qtwist_isElliptic hE (by exact_mod_cast hh0)
  have hfund : IsFundamentalDiscriminant (a * u) := isFund_of_mod_eight h8 hsfau (by omega)
  have hsplit : ∀ p : ℕ, p.Prime → ¬ GoodAt (qtwist E h) p → SplitsIn (a * u) p := by
    intro p hp hng
    have hmem := bad_qtwist_mem h2 hbad hh0 p hp hng
    exact splitsIn_of_isSquareAt hp (hsq p hmem).2 (hsq p hmem).1
  have hw := hTS _ hEh (hBCDT _ hEh) (-1) hhw (a * u) hfund hsplit
  rw [Int.sign_eq_neg_one_of_neg hneg, show (-1 : ℤ) * -1 = 1 by norm_num] at hw
  have heq : qtwist (qtwist E ((h * a : ℤ) : ℚ)) (u : ℚ) =
      qtwist (qtwist E (h : ℚ)) ((a * u : ℤ) : ℚ) := by
    rw [qtwist_qtwist, qtwist_qtwist]; push_cast; ring_nf
  rw [heq]; exact hw

/-- **The rough companion, its nonvanishing part** (tex 2373–2395; App G 10035–10053). PROVED.
`E/ℚ` elliptic, `S ∋ 2` a finite set of primes containing every prime at which the model of `E` is
not good (the fixed support), `h > 0` prime to `S` with `w(E^{(h)}) = −1` (the prepared odd-sign
filter, tex 2345–2346), `a > 0` the squarefree dummy product (prime to `S`, to `h` and to the
exclusions; its realization by primes is lane RC2's), `B` a finite exclusion set of primes. Then
there is `k' = a u` with: `k' < 0`, `k' ≡ 1 (mod 8)`, `k'` an odd fundamental discriminant (so
`ℚ(√k')` avoids the extra-unit fields `ℚ(i), ℚ(√−3)`), a square of `ℚ_p` and prime to `p` at every
`p ∈ S ∪ primes(h)` ("square at every place dividing `2Nh`"), prime to `B`, the new part `u`
with at most five primes, all outside `S ∪ primes(h) ∪ primes(a) ∪ B` ("adds at most five new
primes"), `ω(k') ≤ ω(a) + 5`, and `L(E^{(hk')}, 1) ≠ 0` (`L_*(hk') ≠ 0`). The bound does not depend
on `h`, `a`, `S` or `B`; no size bound is asserted. -/
theorem roughCompanion_nonvanishing (hHL : HoffsteinLuo) (hTS : BFHTwistSign) (hBCDT : BCDTThmA)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (h2 : 2 ∈ S) (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt E p → p ∈ S)
    {h : ℤ} (hh0 : 0 < h) (hhw : RootNumber (qtwist E h) (-1))
    {a : ℤ} (ha0 : 0 < a) (hasf : Squarefree a) (haS : ∀ p ∈ S, ¬ (p : ℤ) ∣ a)
    (hah : IsCoprime a h) (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (haB : ∀ p ∈ B, ¬ (p : ℤ) ∣ a) :
    ∃ k' u : ℤ, k' = a * u ∧ k' < 0 ∧ k' % 8 = 1 ∧ IsFundamentalDiscriminant k' ∧
      (∀ p ∈ S ∪ h.natAbs.primeFactors, IsSquareAt p (k' : ℚ) ∧ ¬ (p : ℤ) ∣ k') ∧
      (∀ p ∈ B, ¬ (p : ℤ) ∣ k') ∧ omega u ≤ 5 ∧
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ u →
        p ∉ S ∪ h.natAbs.primeFactors ∪ a.natAbs.primeFactors ∪ B) ∧
      omega k' ≤ omega a + 5 ∧ CentralNonzero (qtwist E ((h * k' : ℤ) : ℚ)) := by
  have ha : a ≠ 0 := ha0.ne'
  set Φ := companionFilter S hS h a ha with hΦ
  have hA : (qtwist E ((h * a : ℤ) : ℚ)).IsElliptic :=
    qtwist_isElliptic hE (by exact_mod_cast (mul_pos hh0 ha0).ne')
  have h2Φ : 2 ∈ Φ.S := by simp [Φ, companionFilter, h2]
  have hbadA : ∀ p : ℕ, p.Prime → ¬ GoodAt (qtwist E ((h * a : ℤ) : ℚ)) p → p ∈ Φ.S := by
    intro p hp hng
    have := bad_qtwist_mem h2 hbad (mul_pos hh0 ha0).ne' p hp hng
    simp only [Φ, companionFilter, Finset.mem_union] at this ⊢
    rcases this with h1 | h1
    · exact Or.inl (Or.inl h1)
    · rw [Int.natAbs_mul, Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr hh0.ne')
        (Int.natAbs_ne_zero.mpr ha), Finset.mem_union] at h1
      rcases h1 with h1 | h1
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h1
  have heven := companionFilter_rootNumber (hS := hS) (ha := ha) hTS hBCDT hE h2 hbad hh0.ne'
    hhw ha0 hasf haS hah
  -- "use the preceding nonvanishing theorem in its even filter" (2382–2384)
  obtain ⟨u, hu, -, hsf, huB, huω, hL⟩ :=
    fivePrime_four hHL hTS hBCDT hA Φ h2Φ hbadA B hB heven
  obtain ⟨hsq, h8, hneg, hsfau, hcop⟩ := companionFilter_mem h2 ha0 hasf haS hah hu hsf
  have hu0 : u ≠ 0 := hu.ne_zero
  refine ⟨a * u, u, rfl, hneg, h8, isFund_of_mod_eight h8 hsfau (by omega), hsq, ?_, huω, ?_, ?_,
    ?_⟩
  · intro p hp hdvd
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (hB p hp)
    rcases hpZ.dvd_or_dvd hdvd with h1 | h1
    · exact haB p hp h1
    · exact huB p hp h1
  · intro p hp hpu hmem
    simp only [Finset.mem_union] at hmem
    rcases hmem with ((h1 | h1) | h1) | h1
    · exact hu.not_dvd (by simp [Φ, companionFilter, h1]) hpu
    · exact hu.not_dvd (by simp [Φ, companionFilter, h1]) hpu
    · exact hu.not_dvd (by simp [Φ, companionFilter, h1]) hpu
    · exact huB p h1 hpu
  · have hcop' : Nat.Coprime a.natAbs u.natAbs := Int.isCoprime_iff_gcd_eq_one.mp hcop
    simp only [omega, Int.natAbs_mul]
    rw [ArithmeticFunction.cardDistinctFactors_mul hcop']
    simp only [omega] at huω
    omega
  · have heq : qtwist E ((h * (a * u) : ℤ) : ℚ) = qtwist (qtwist E ((h * a : ℤ) : ℚ)) (u : ℚ) := by
      rw [qtwist_qtwist]; push_cast; ring_nf
    rw [heq]; exact hL

/-- **The rough companion for `E_ℓ`** (tex 2343–2395), with the twists as curves of the family and
`w(E^{(h)}) = −1` derived from `w(E_ℓ) = −1` for `h` in the prepared positive filter containing one
(tex 2345–2346). PROVED. -/
theorem roughCompanion_curve (hHL : HoffsteinLuo) (hTS : BFHTwistSign) (hBCDT : BCDTThmA)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (hw : RootNumber (Ecurve ℓ) (-1)) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (h2 : 2 ∈ S) (h3 : 3 ∈ S) (hℓS : ∀ p : ℕ, p.Prime → p ∣ ℓ → p ∈ S)
    {h : ℤ} (hh : (trivialFilter S hS 1).Mem h) (hhsf : Squarefree h)
    {a : ℤ} (ha0 : 0 < a) (hasf : Squarefree a) (haS : ∀ p ∈ S, ¬ (p : ℤ) ∣ a)
    (hah : IsCoprime a h) (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (haB : ∀ p ∈ B, ¬ (p : ℤ) ∣ a) :
    ∃ k' u : ℤ, k' = a * u ∧ k' < 0 ∧ k' % 8 = 1 ∧ IsFundamentalDiscriminant k' ∧
      (∀ p ∈ S ∪ h.natAbs.primeFactors, IsSquareAt p (k' : ℚ) ∧ ¬ (p : ℤ) ∣ k') ∧
      (∀ p ∈ B, ¬ (p : ℤ) ∣ k') ∧ omega u ≤ 5 ∧ omega k' ≤ omega a + 5 ∧
      CentralNonzero (curve ((h * k' * ℓ : ℤ) : ℚ)) := by
  have hE := curve_nat_isElliptic hℓ
  have hbad := bad_curve_mem (m := (ℓ : ℤ)) h2 h3 fun p hp h => hℓS p hp (by exact_mod_cast h)
  have hh0 : 0 < h := Int.sign_eq_one_iff_pos.mp hh.2.1
  have hhw : RootNumber (qtwist (Ecurve ℓ) h) (-1) := by
    have := rootNumber_curve_twist hTS hBCDT hℓ hS h2 h3 hℓS hw 1 h hh hhsf
    simpa using this
  obtain ⟨k', u, hk', hneg, h8, hF, hsq, hB', hω, -, hωk, hL⟩ :=
    roughCompanion_nonvanishing hHL hTS hBCDT hE hS h2 (by exact_mod_cast hbad) hh0 hhw ha0 hasf
      haS hah B hB haB
  exact ⟨k', u, hk', hneg, h8, hF, hsq, hB', hω, hωk, by rw [← qtwist_Ecurve]; exact hL⟩

/-! ### The assembly of (3.3) -/

/-- `ω(hk') = ω(h) + ω(k')` for coprime `h, k'`. PROVED. -/
theorem omega_mul_of_coprime {x y : ℤ} (h : IsCoprime x y) : omega (x * y) = omega x + omega y := by
  simp only [omega, Int.natAbs_mul]
  exact ArithmeticFunction.cardDistinctFactors_mul (Int.isCoprime_iff_gcd_eq_one.mp h)

/-- **Proposition `ex:sec7-rough-companion` / `ex:app-rough-companion` (3.3)** (tex 2343–2401,
App G 10056–10149), assembled in Lean from the construction (`roughCompanion_nonvanishing`) and
three inputs, in Elliot's order of choices: the constants `A = A₀ + 5` and `C_E = C₁` are fixed
before `h` and before the exclusion set. The inputs:

* `hdummy` (ELLIOT; lane RC2-symbols; tex 2359–2379, 2384–2385, App G 10096–10105, 10131–10139):
  a bounded supply of `A₀` dummy labels, fixed before `h`, is realized for each prepared `h`
  (positive, squarefree, `≡ 1 (mod 8)`, prime to `S`; tex 2344–2346) and exclusion set `X` by a
  squarefree positive product `a` of distinct primes outside `S`, `h` and `X`, and "for the actual
  resulting total type, the already chosen dummy supply makes `hk'` partitionable": every
  `k' = a u` of the companion's shape (negative, `≡ 1 (mod 8)`, a square at every
  `p ∈ S ∪ primes(h)`, squarefree) with `L(E^{(hk')},1) ≠ 0` makes `hk'` partitionable.
* `hforward` (PRINT Kato Cor 14.3, or GLUE Kolyvagin Thm 1, cited statement; `lem:forward-rank`;
  tex 2386): nonvanishing gives Selmer corank zero.
* `h33b` (ELLIOT; (3.3b), tex 2295–2341, App G (F.2) 10107–10129; lane RC2-symbols/RC11-even): a
  partitionable parameter of Selmer corank zero has `v₂L_*(d) − 2ω(d) − s(d) ≤ C₁`.

`vL d` stands for `v₂L_*(d)` and `s d` for `s(d)`; `Partitionable` and `CorankZero` are the
predicates of Definition `ex:sec7-seed-partition` and of the Selmer corank. PROVED. -/
theorem roughCompanion (hHL : HoffsteinLuo) (hTS : BFHTwistSign) (hBCDT : BCDTThmA)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (h2 : 2 ∈ S) (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt E p → p ∈ S)
    (Partitionable CorankZero : ℤ → Prop) (vL s : ℤ → ℤ) (C₁ : ℤ) (A₀ : ℕ)
    (hdummy : ∀ h : ℤ, 0 < h → Squarefree h → h % 8 = 1 → (∀ p ∈ S, ¬ (p : ℤ) ∣ h) →
      ∀ X : Finset ℕ, (∀ p ∈ X, p.Prime) →
      ∃ a : ℤ, 0 < a ∧ Squarefree a ∧ omega a = A₀ ∧ (∀ p ∈ S ∪ X, ¬ (p : ℤ) ∣ a) ∧
        IsCoprime a h ∧ ∀ u : ℤ, a * u < 0 → (a * u) % 8 = 1 → Squarefree (a * u) →
          (∀ p ∈ S ∪ h.natAbs.primeFactors, IsSquareAt p ((a * u : ℤ) : ℚ)) →
          CentralNonzero (qtwist E ((h * (a * u) : ℤ) : ℚ)) →
            Partitionable (h * (a * u)))
    (hforward : ∀ d : ℤ, CentralNonzero (qtwist E d) → CorankZero d)
    (h33b : ∀ d : ℤ, Partitionable d → CorankZero d → vL d ≤ 2 * omega d + s d + C₁) :
    ∃ (A : ℕ) (CE : ℤ), ∀ h : ℤ, 0 < h → Squarefree h → h % 8 = 1 → (∀ p ∈ S, ¬ (p : ℤ) ∣ h) →
      RootNumber (qtwist E h) (-1) → ∀ X : Finset ℕ, (∀ p ∈ X, p.Prime) →
        ∃ k' : ℤ, k' < 0 ∧ k' % 8 = 1 ∧ IsFundamentalDiscriminant k' ∧
          (∀ p ∈ S ∪ h.natAbs.primeFactors, IsSquareAt p (k' : ℚ) ∧ ¬ (p : ℤ) ∣ k') ∧
          (∀ p ∈ X, ¬ (p : ℤ) ∣ k') ∧ Partitionable (h * k') ∧
          CentralNonzero (qtwist E ((h * k' : ℤ) : ℚ)) ∧ omega k' ≤ A ∧
          vL (h * k') ≤ 2 * omega h + 2 * omega k' + s (h * k') + CE := by
  refine ⟨A₀ + 5, C₁, fun h hh0 hhsf hh8 hhS hhw X hX => ?_⟩
  -- the dummy realization after `h` and the exclusions (2373–2379)
  obtain ⟨a, ha0, hasf, haω, haSX, hah, hpart⟩ := hdummy h hh0 hhsf hh8 hhS X hX
  have haS : ∀ p ∈ S, ¬ (p : ℤ) ∣ a := fun p hp => haSX p (Finset.mem_union_left _ hp)
  have haX : ∀ p ∈ X, ¬ (p : ℤ) ∣ a := fun p hp => haSX p (Finset.mem_union_right _ hp)
  -- the nonvanishing construction (2380–2384)
  obtain ⟨k', u, rfl, hneg, h8, hF, hsq, hX', -, -, hωk, hL⟩ :=
    roughCompanion_nonvanishing hHL hTS hBCDT hE hS h2 hbad hh0 hhw ha0 hasf haS hah X hX haX
  have hsfk : Squarefree (a * u) := (hF.squarefree_of_odd (Int.odd_iff.mpr (by omega))).1
  -- partitionability (2384–2385), corank zero (2386), (3.3b) (2387)
  have hP := hpart u hneg h8 hsfk (fun p hp => (hsq p hp).1) hL
  have hC := hforward _ (by exact_mod_cast hL)
  have hV := h33b _ hP hC
  -- `ω(hk') = ω(h) + ω(k')`: `k'` is prime to the primes of `h`
  have hcop : IsCoprime h (a * u) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    have hph : (p : ℤ) ∣ h := (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_left _ _)
    have hpk : (p : ℤ) ∣ a * u := (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_right _ _)
    have hmem : p ∈ S ∪ h.natAbs.primeFactors := Finset.mem_union_right _
      (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp hph, Int.natAbs_ne_zero.mpr hh0.ne'⟩)
    exact (hsq p hmem).2 hpk
  refine ⟨a * u, hneg, h8, hF, hsq, hX', hP, hL, by omega, ?_⟩
  rw [omega_mul_of_coprime hcop] at hV
  push_cast at hV ⊢
  linarith

end ZInQ.Manuscript.RC.Nonvanishing

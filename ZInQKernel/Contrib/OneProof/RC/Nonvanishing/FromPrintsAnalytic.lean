import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Companion
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.BFH
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Desjardins

/-!
# Lane RC13 (nonvanishing), part 8 (optional): the leaves from lane RC8's statements

Lane RC8-prints-analytic states the analytic prints over the shared vocabulary in the namespace
`ZInQ.Manuscript.RC.PrintsAnalytic` (curve forms `HoffsteinLuoCurve`, `BFHCurve`,
`TwistedRootNumberCurve`, and Desjardins in the global form `DesjardinsRootNumberFilter`). This
file derives this lane's leaves (part 3) from them, so that one set of printed leaves serves both
lanes:

* `hoffsteinLuo_of_curve : HoffsteinLuoCurve → HoffsteinLuo` (PROVED);
* `bfhSimpleZero_of_curve`, `bfhNonvanishing_of_curve : BFHCurve → LevelSupport → …` (PROVED);
* `bfhTwistSign_of_curve : TwistedRootNumberCurve → LevelSupport → BFHTwistSign` (PROVED);
* `rootNumber_of_mem_integral`: the root-number check from `DesjardinsRootNumberFilter` and
  `RootNumberExists`, for an integral model (PROVED).

Two GLUE facts are needed, both consequences of modularity and of the uniqueness of the
functional equation of the nonzero `L(A, s)`:

* `LevelSupport` (GLUE): a level `N` at which `L(A, s)` has a functional equation is supported on
  the primes at which the model of `A` is not good (the level is the conductor, whose primes are
  bad, and a good model has good reduction).
* `RootNumberExists` (GLUE): every elliptic curve over `ℚ` has a root number (BCDT and Hecke).
-/

namespace ZInQ.Manuscript.RC.Nonvanishing

open ZInQ.Manuscript ZInQ.Manuscript.PoleS12 ZInQ.Contrib.CloudB3RC53 SignedUnitFilter

namespace FromRC8

open ZInQ.Manuscript.RC

/-- **The level of a functional equation is the conductor** (GLUE): if `L(A, s)` satisfies the
functional equation of level `N` (lane RC8's `RootNumberAt`), every prime of `N` is a prime at
which the model of `A` is not good. -/
def LevelSupport : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → ∀ (N : ℕ) (w : ℤ), PrintsAnalytic.RootNumberAt A N w →
    ∀ p : ℕ, p.Prime → p ∣ N → ¬ GoodAt A p

/-- **Every elliptic curve over `ℚ` has a root number** (GLUE: BCDT Theorem A and Hecke's
functional equation for the newform). -/
def RootNumberExists : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → ∃ w : ℤ, RootNumber A w

theorem isFund_iff {D : ℤ} :
    PrintsAnalytic.IsFundamentalDiscriminant D ↔ IsFundamentalDiscriminant D := Iff.rfl

theorem omega_eq (D : ℤ) : PrintsAnalytic.omega D = omega D := by
  simp only [PrintsAnalytic.omega, omega, ArithmeticFunction.cardDistinctFactors_apply,
    Nat.primeFactors, List.card_toFinset]

theorem kronecker_two (D : ℤ) : PrintsAnalytic.kronecker D 2 = PrintsAnalytic.kroneckerTwo D := by
  simp [PrintsAnalytic.kronecker, Nat.Prime.factorization_self Nat.prime_two]

theorem kronecker_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (D : ℤ) :
    PrintsAnalytic.kronecker D p = jacobiSym D p := by
  have h0 : p.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  simp [PrintsAnalytic.kronecker, h0]

/-- `χ_D(p) = 1` gives `SplitsIn D p` for a fundamental discriminant `D`. PROVED. -/
theorem splitsIn_of_kronecker {D : ℤ} (hD : IsFundamentalDiscriminant D) {p : ℕ} (hp : p.Prime)
    (h : PrintsAnalytic.kronecker D p = 1) : SplitsIn D p := by
  refine ⟨fun hp2 => ?_, fun hp2 => ?_⟩
  · subst hp2
    rw [kronecker_two] at h
    unfold PrintsAnalytic.kroneckerTwo at h
    split_ifs at h with h1 h2
    all_goals first
      | exact absurd h (by decide)
      | (rcases hD.2 with ⟨h4, -⟩ | ⟨m, rfl, -, -⟩ <;> omega)
  · have : Fact p.Prime := ⟨hp⟩
    rw [kronecker_odd hp hp2, ← jacobiSym.legendreSym.to_jacobiSym] at h
    have hne : ((D : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      rw [(legendreSym.eq_zero_iff p D).mpr h0] at h
      exact absurd h (by decide)
    refine ⟨fun hdvd => hne ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hdvd), ?_⟩
    exact (legendreSym.eq_one_iff p hne).mp h

/-- `SplitsIn D p` gives `χ_D(p) = 1`. PROVED. -/
theorem kronecker_of_splitsIn {D : ℤ} {p : ℕ} (hp : p.Prime) (h : SplitsIn D p) :
    PrintsAnalytic.kronecker D p = 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h8 := h.two
    rw [kronecker_two]
    unfold PrintsAnalytic.kroneckerTwo
    have h1 : ¬ (D % 2 = 0) := by omega
    have h2 : D % 8 = 1 ∨ D % 8 = 7 := Or.inl h8
    simp only [h1, h2, ↓reduceIte]
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨hnd, hsq⟩ := h.2 hp2
    rw [kronecker_odd hp hp2, ← jacobiSym.legendreSym.to_jacobiSym]
    have hne : ((D : ℤ) : ZMod p) ≠ 0 := fun h0 =>
      hnd ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp h0)
    exact (legendreSym.eq_one_iff p hne).mpr hsq

/-- **Hoffstein–Luo**: this lane's leaf from lane RC8's curve form. PROVED. -/
theorem hoffsteinLuo_of_curve (h : PrintsAnalytic.HoffsteinLuoCurve) : HoffsteinLuo := by
  intro A hA _ S hS _
  refine (h A hA S hS).mono fun d hd => ?_
  obtain ⟨hF, hodd, hω, hk, hL⟩ := hd
  exact ⟨hF, hodd, by rw [← omega_eq]; exact hω, fun p hp => splitsIn_of_kronecker hF (hS p hp)
    (hk p hp), hL⟩

theorem level_mem {A : WeierstrassCurve ℚ} (hA : A.IsElliptic) (hLS : LevelSupport)
    {S : Finset ℕ} (hbad : ∀ p : ℕ, p.Prime → ¬ GoodAt A p → p ∈ S) {N : ℕ} {w : ℤ}
    (hN : PrintsAnalytic.RootNumberAt A N w) : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S :=
  fun p hp hpN => hbad p hp (hLS A hA N w hN p hp hpN)

/-- **Bump–Friedberg–Hoffstein (i)**: this lane's leaf from lane RC8's curve form. PROVED. -/
theorem bfhSimpleZero_of_curve (h : PrintsAnalytic.BFHCurve) (hLS : LevelSupport) :
    BFHSimpleZero := by
  intro A hA _ w hw S hS hbad
  obtain ⟨N, hN⟩ := hw
  obtain ⟨⟨D, hF, hs, hk, hL⟩, -⟩ := h A hA N w hN S hS (level_mem hA hLS hbad hN)
  exact ⟨D, hF, hs, fun p hp => splitsIn_of_kronecker hF (hS p hp) (hk p hp), hL⟩

/-- **Bump–Friedberg–Hoffstein (ii)**: this lane's leaf from lane RC8's curve form. PROVED. -/
theorem bfhNonvanishing_of_curve (h : PrintsAnalytic.BFHCurve) (hLS : LevelSupport) :
    BFHNonvanishing := by
  intro A hA _ w hw S hS hbad
  obtain ⟨N, hN⟩ := hw
  obtain ⟨-, ⟨D, hF, hs, hk, hL⟩⟩ := h A hA N w hN S hS (level_mem hA hLS hbad hN)
  exact ⟨D, hF, hs, fun p hp => splitsIn_of_kronecker hF (hS p hp) (hk p hp), hL⟩

/-- **The twisted sign** (BFH p. 543): this lane's leaf from lane RC8's
`TwistedRootNumberCurve`. PROVED. -/
theorem bfhTwistSign_of_curve (h : PrintsAnalytic.TwistedRootNumberCurve) (hLS : LevelSupport) :
    BFHTwistSign := by
  intro A hA _ w hw D hD hsplit
  obtain ⟨N, hN⟩ := hw
  have hNpos : 0 < N := hN.1
  have hsN : ∀ p : ℕ, p.Prime → p ∣ N → SplitsIn D p :=
    fun p hp hpN => hsplit p hp (hLS A hA N w hN p hp hpN)
  have hcop : IsCoprime D (N : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    have hpD : (p : ℤ) ∣ D := (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_left _ _)
    have hpN : (p : ℤ) ∣ (N : ℤ) := (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_right _ _)
    exact (hsN p hp (Int.natCast_dvd_natCast.mp hpN)).not_dvd hp hpD
  have hkN : PrintsAnalytic.kronecker D N = 1 :=
    PrintsAnalytic.kronecker_eq_one_of_forall_prime_dvd hNpos.ne'
      fun p hp hpN => kronecker_of_splitsIn hp (hsN p hp hpN)
  have := h A hA N w hN D hD hcop
  rw [hkN, mul_one, PrintsAnalytic.kroneckerNegOne, mul_comm w (Int.sign D)] at this
  exact ⟨_, this⟩

/-- Two members of a filter at `S ∋ 2` are in one class in lane RC8's sense. PROVED. -/
theorem sameSignedUnitClasses_of_mem {Φ : SignedUnitFilter} (h2 : 2 ∈ Φ.S) {u u' : ℤ}
    (hu : Φ.Mem u) (hu' : Φ.Mem u') : PrintsAnalytic.SameSignedUnitClasses Φ.S u u' := by
  refine ⟨hu.2.1.trans hu'.2.1.symm, fun q hq => ⟨hu.not_dvd hq, hu'.not_dvd hq, ?_, ?_⟩⟩
  · rintro rfl
    have h8 := modEq_eight_of_isSquareAt_two (hu'.odd h2) (hu.odd h2) (hu.isSquareAt_ratio hu' h2)
    obtain ⟨k, hk⟩ := hu.odd h2
    unfold Int.ModEq at h8
    have : u * u' % 8 = u * u % 8 := by rw [Int.mul_emod, h8, ← Int.mul_emod]
    rw [this, hk]
    have hk2 : (2 * k + 1) * (2 * k + 1) = 4 * (k * (k + 1)) + 1 := by ring
    rw [hk2]
    obtain ⟨j, hj⟩ := Int.even_mul_succ_self k
    rw [hj]; omega
  · intro hq2
    have hqp := Φ.prime_of_mem q hq
    have hsq : IsSquareAt q ((u * u' : ℤ) : ℚ) := by
      have hu0 : (u : ℚ) ≠ 0 := by exact_mod_cast hu.ne_zero
      have : ((u * u' : ℤ) : ℚ) = ((u' : ℚ) / u) * (u : ℚ) ^ 2 := by push_cast; field_simp
      rw [this]; exact isSquareAt_mul (hu.isSquareAt_ratio hu' hq) (isSquareAt_sq _)
    have hnd : ¬ (q : ℤ) ∣ u * u' := by
      intro hdvd
      rcases (Nat.prime_iff_prime_int.mp hqp).dvd_or_dvd hdvd with h | h
      · exact hu.not_dvd hq h
      · exact hu'.not_dvd hq h
    exact ((splitsIn_of_isSquareAt hqp hnd hsq).2 hq2).2

/-- **The root-number check from lane RC8's Desjardins** (global form) for an integral model `W`
with `2, 3` and the primes of `Δ(W)` in `S`: if one squarefree member `u₀` gives root number `w`,
the filter has root number `w`. PROVED from `DesjardinsRootNumberFilter` and `RootNumberExists`. -/
theorem rootNumber_of_mem_integral (hDes : PrintsAnalytic.DesjardinsRootNumberFilter)
    (hEx : RootNumberExists) {W : WeierstrassCurve ℤ} (hE : (W.map (Int.castRingHom ℚ)).IsElliptic)
    (Φ : SignedUnitFilter) (h2 : 2 ∈ Φ.S) (h3 : 3 ∈ Φ.S)
    (hbad : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → p ∈ Φ.S) {u₀ : ℤ} (hu₀ : Φ.Mem u₀)
    (hsf₀ : Squarefree u₀) {w : ℤ} (hw : RootNumber (qtwist (W.map (Int.castRingHom ℚ)) u₀) w) :
    Φ.RootNumber (W.map (Int.castRingHom ℚ)) w := by
  intro u hu hsf
  obtain ⟨w', hw'⟩ := hEx (qtwist (W.map (Int.castRingHom ℚ)) (u : ℚ))
    (qtwist_isElliptic hE (d := (u : ℚ)) (by exact_mod_cast hu.ne_zero))
  have := PrintsAnalytic.rootNumber_eq_of_sameSignedUnitClasses hDes hE Φ.prime_of_mem h2 h3 hbad
    hsf₀ hsf (sameSignedUnitClasses_of_mem h2 hu₀ hu) hw hw'
  rw [this]; exact hw'

end FromRC8

end ZInQ.Manuscript.RC.Nonvanishing

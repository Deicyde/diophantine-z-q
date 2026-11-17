import Mathlib

/-!
# `Λ[1/2]` as an intersection, the central specialization, and (5.5) + (4.6) ⇒ (3.5)

Lane RC16-uniform (Section 9 of the manuscript, proof of Theorem 5.3), part `lambda`.

This file formalizes three algebraic steps in Elliot Glazer's proof of the proposition
`ex:limits-uniform-lower-bound` ("Uniform ring lower bound and height-one regularity",
tex lines 4909-4926). The statement reads

  `v₂ u_prim ≥ -C(E,A),   u_prim ∈ Λ[1/2]`,
  "where the first valuation is that of `𝒪` ... Consequently its central specialization and
  (4.6) imply (3.5)."

1. tex 5191-5194: "This proves regularity at every `𝔭 ≠ (2)` ... Finally the normal-domain
   intersection formula for `Λ[1/2]` gives `u_prim ∈ Λ[1/2]`."
   General UFD form: `mem_away_iff_forall_prime` (over prime elements) and
   `mem_away_iff_forall_height_one` (over height-one primes, using
   `height_eq_one_iff_exists_prime`); with genuine localizations:
   `mem_range_away_iff_forall_height_one`. For `Λ = ℤ₂[[t]]`, `π = 2`:
   `prime_two_lambda`, `lambda_ufd`, `mem_lambdaHalf_iff_forall_prime`,
   `mem_range_lambdaHalf_iff_forall_prime`, `mem_range_lambdaHalf_iff_forall_height_one`.
2. tex 4914-4920: the central specialization `t ↦ 0` of `Λ[1/2]`, and "`v₂ u(0)` is at least the
   Gauss valuation": `centralSpecialization`, `valuation_central_ge`,
   `two_pow_mul_mem_range_iff`, `valuation_central_ge_sharp`.
3. tex 5200-5202, with (3.5) (tex 2446) and (4.6) (tex 4045): "Combining (5.5), for the known
   simple-zero instances, with (4.6) and `∑_{p ∣ k} t_p ≤ 2A` proves (3.5)."
   `sum_t_le`, `eq46_absorbed`, `eq35_of_eq55_eq46`, `eq35_of_eq55_eq46_absorbed`,
   `eq35_of_lambdaHalf`.

Everything in this file is `PROVED`; there is no `GLUE` and no `ELLIOT` statement. The textbook
fact that `ℤ₂[[t]]` is a UFD is a theorem of Mathlib (`lambda_ufd`).
-/

namespace ZInQ.Manuscript.RC.Uniform

open IsLocalization

/-! ## 1. The intersection formula over a UFD -/

section Intersection

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

omit [IsDomain R] in
/-- Helper for `mem_away_iff_forall_prime` (`PROVED`). In a UFD, a nonzero `b` all of whose prime
divisors are associated to `π` divides a power of `π`. -/
theorem dvd_pow_of_forall_prime_dvd {π : R} (b : R) (hb : b ≠ 0)
    (h : ∀ q : R, Prime q → q ∣ b → Associated q π) : ∃ m : ℕ, b ∣ π ^ m := by
  revert hb h
  refine UniqueFactorizationMonoid.induction_on_prime b ?_ ?_ ?_
  · intro h0
    exact absurd rfl h0
  · intro x hx _ _
    exact ⟨0, by rw [pow_zero]; exact hx.dvd⟩
  · intro a q ha hq ih _ h
    obtain ⟨m, hm⟩ := ih ha (fun q' hq' hdvd => h q' hq' (dvd_mul_of_dvd_right hdvd q))
    have hqπ : q ∣ π := (h q hq (dvd_mul_right q a)).dvd
    exact ⟨m + 1, by rw [pow_succ']; exact mul_dvd_mul hqπ hm⟩

/-- In a UFD, `(p)` has height one for every prime element `p` (`PROVED`). A nonzero prime
`𝔮 ⊊ (p)` would contain a prime element `r`; then `p ∣ r`, so `(p) = (r) ⊆ 𝔮`. -/
theorem height_span_prime {p : R} (hp : Prime p) : (Ideal.span {p}).height = 1 := by
  have hP : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  apply le_antisymm
  · have key := Ideal.height_le_iff (p := Ideal.span {p}) (n := 1)
    rw [Nat.cast_one] at key
    rw [key]
    intro q hq hlt
    have hq0 : q = ⊥ := by
      by_contra hne
      obtain ⟨r, hrq, hr⟩ := hq.exists_mem_prime_of_ne_bot hne
      have hpr : p ∣ r := Ideal.mem_span_singleton.mp (hlt.le hrq)
      obtain ⟨c, hc⟩ := (hp.irreducible.associated_of_dvd hr.irreducible hpr).symm.dvd
      have hle : Ideal.span {p} ≤ q := by
        rw [Ideal.span_singleton_le_iff_mem, hc]
        exact q.mul_mem_right c hrq
      exact lt_irrefl _ (lt_of_le_of_lt hle hlt)
    rw [hq0, Ideal.height_bot]
    exact zero_lt_one
  · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp.ne_zero

/-- **Height-one primes of a UFD** (`PROVED`): a prime ideal `𝔭` of a UFD has height one iff
`𝔭 = (p)` for a prime element `p`. -/
theorem height_eq_one_iff_exists_prime (P : Ideal R) [P.IsPrime] :
    P.height = 1 ↔ ∃ p : R, Prime p ∧ P = Ideal.span {p} := by
  constructor
  · intro h1
    obtain ⟨p, hpP, hp⟩ :=
      Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹P.IsPrime› (Ideal.ne_bot_of_height_eq_one h1)
    exact ⟨p, hp, Ideal.eq_span_singleton_of_height_eq_one h1 hpP hp⟩
  · rintro ⟨p, hp, rfl⟩
    exact height_span_prime hp

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The intersection formula for `R[1/π]`, over prime elements** (tex 5192-5194, `PROVED`).

Manuscript: "Finally the normal-domain intersection formula for `Λ[1/2]` gives
`u_prim ∈ Λ[1/2]`", i.e. `Λ[1/2] = ⋂_{𝔭 ≠ (2), ht 𝔭 = 1} Λ_𝔭` inside `Frac Λ`, used in the
direction `⊇`.

Here `R` is any domain with `UniqueFactorizationMonoid R`, `π` is a prime element and `K` is a
fraction field of `R` (for instance `K = FractionRing R`). For `x : K`:

* left side: `x` lies in the image of `R[1/π] = Localization.Away π`, written elementwise as
  `∃ a m, x · π^m = a` (the two forms agree by `mem_range_away_iff`);
* right side: for every prime element `p` not associated to `π`, `x` lies in the localization
  `R_(p)` at the height-one prime `(p)`, written elementwise as `∃ a s, s ∉ (p) ∧ x · s = a`
  (the two forms agree by `mem_range_atPrime_iff`).

Both directions are proved. Proof of `⊇`: write `x = a/b` as a reduced fraction; a prime factor
`q` of `b` not associated to `π` would give `x · s = a'` with `q ∤ s`, hence `q ∣ a·s`, hence
`q ∣ a`, contradicting reducedness; so every prime factor of `b` is associated to `π` and
`b ∣ π^m`.

DEPARTURE (form): the intersection runs over the principal primes `(p)`, `p` a prime element not
associated to `π`, rather than over the height-one primes `𝔭 ≠ (π)`. In a UFD these are the same
ideals (`height_eq_one_iff_exists_prime`); the height-one form itself is
`mem_away_iff_forall_height_one`. Only "UFD" is used, not "normal noetherian domain"; for
`Λ = ℤ₂[[t]]` it is available (`lambda_ufd`). -/
theorem mem_away_iff_forall_prime {π : R} (hπ : Prime π) (x : K) :
    (∃ a : R, ∃ m : ℕ, x * algebraMap R K (π ^ m) = algebraMap R K a) ↔
      ∀ p : R, Prime p → ¬ Associated p π →
        ∃ a s : R, s ∉ Ideal.span {p} ∧ x * algebraMap R K s = algebraMap R K a := by
  constructor
  · rintro ⟨a, m, hx⟩ p hp hpπ
    refine ⟨a, π ^ m, ?_, hx⟩
    rw [Ideal.mem_span_singleton]
    intro hdvd
    exact hpπ (hp.irreducible.associated_of_dvd hπ.irreducible (hp.dvd_of_dvd_pow hdvd))
  · intro h
    obtain ⟨a, b, hab, rfl⟩ := IsFractionRing.exists_reduced_fraction R x
    have hxb : IsLocalization.mk' K a b * algebraMap R K (b : R) = algebraMap R K a :=
      IsLocalization.mk'_spec K a b
    have hb0 : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    have hfac : ∀ q : R, Prime q → q ∣ (b : R) → Associated q π := by
      intro q hq hqb
      by_contra hqπ
      obtain ⟨a', s, hs, hxs⟩ := h q hq hqπ
      have key : a * s = a' * b := by
        apply IsFractionRing.injective R K
        rw [map_mul, map_mul, ← hxb, ← hxs]
        ring
      have hqas : q ∣ a * s := key ▸ dvd_mul_of_dvd_right hqb a'
      rcases hq.dvd_or_dvd hqas with hqa | hqs
      · exact hq.not_isUnit (hab hqa hqb)
      · exact hs (Ideal.mem_span_singleton.mpr hqs)
    obtain ⟨m, c, hc⟩ := dvd_pow_of_forall_prime_dvd (b : R) hb0 hfac
    refine ⟨a * c, m, ?_⟩
    rw [hc, map_mul, ← mul_assoc, hxb, map_mul]

/-- **The intersection formula for `R[1/π]`, over height-one primes** (tex 5192-5194, `PROVED`):
`R[1/π] = ⋂_{𝔭 ≠ (π), ht 𝔭 = 1} R_𝔭` inside `K`, elementwise (membership of `x` in `R_𝔭` is
`∃ a s, s ∉ 𝔭 ∧ x · s = a`). This is the manuscript's formula verbatim (with `R = Λ`, `π = 2`);
it follows from `mem_away_iff_forall_prime` and `height_eq_one_iff_exists_prime`. -/
theorem mem_away_iff_forall_height_one {π : R} (hπ : Prime π) (x : K) :
    (∃ a : R, ∃ m : ℕ, x * algebraMap R K (π ^ m) = algebraMap R K a) ↔
      ∀ P : Ideal R, P.IsPrime → P.height = 1 → P ≠ Ideal.span {π} →
        ∃ a s : R, s ∉ P ∧ x * algebraMap R K s = algebraMap R K a := by
  rw [mem_away_iff_forall_prime hπ]
  constructor
  · intro h P hP h1 hPπ
    obtain ⟨p, hp, rfl⟩ := (height_eq_one_iff_exists_prime P).mp h1
    exact h p hp fun hpπ => hPπ (Ideal.span_singleton_eq_span_singleton.mpr hpπ)
  · intro h p hp hpπ
    have hP : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    exact h _ hP (height_span_prime hp)
      fun hPπ => hpπ (Ideal.span_singleton_eq_span_singleton.mp hPπ)

omit [UniqueFactorizationMonoid R] in
/-- The image of `Localization.Away π` in `K` (`PROVED`): `x` is in the range of the canonical map
`R[1/π] → K` iff `x · π^m ∈ R` for some `m`. -/
theorem mem_range_away_iff {π : R} (hπ : π ≠ 0) (x : K) :
    x ∈ (Localization.mapToFractionRing K (Submonoid.powers π) (Localization.Away π)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hπ)).range ↔
      ∃ a : R, ∃ m : ℕ, x * algebraMap R K (π ^ m) = algebraMap R K a := by
  rw [Localization.mem_range_mapToFractionRing_iff]
  constructor
  · rintro ⟨a, s, hs, rfl⟩
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hs
    exact ⟨a, m, IsLocalization.mk'_spec K a _⟩
  · rintro ⟨a, m, hx⟩
    exact ⟨a, π ^ m, ⟨m, rfl⟩, IsLocalization.eq_mk'_iff_mul_eq.mpr hx⟩

omit [UniqueFactorizationMonoid R] in
/-- The image of the localization `R_𝔭` at a prime `𝔭` in `K` (`PROVED`): `x` is in the range of
the canonical map `R_𝔭 → K` iff `x · s ∈ R` for some `s ∉ 𝔭`. -/
theorem mem_range_atPrime_iff (P : Ideal R) [P.IsPrime] (x : K) :
    x ∈ (Localization.mapToFractionRing K P.primeCompl (Localization.AtPrime P)
        (Ideal.primeCompl_le_nonZeroDivisors P)).range ↔
      ∃ a s : R, s ∉ P ∧ x * algebraMap R K s = algebraMap R K a := by
  rw [Localization.mem_range_mapToFractionRing_iff]
  constructor
  · rintro ⟨a, s, hs, rfl⟩
    exact ⟨a, s, hs, IsLocalization.mk'_spec K a _⟩
  · rintro ⟨a, s, hs, hx⟩
    exact ⟨a, s, hs, IsLocalization.eq_mk'_iff_mul_eq.mpr hx⟩

/-- **The intersection formula with genuine localizations** (tex 5192-5194, `PROVED`):
`R[1/π] = ⋂_{𝔭 ≠ (π), ht 𝔭 = 1} R_𝔭` inside `K`, stated with the canonical maps
`Localization.Away π → K` and `Localization.AtPrime 𝔭 → K`. -/
theorem mem_range_away_iff_forall_height_one {π : R} (hπ : Prime π) (x : K) :
    x ∈ (Localization.mapToFractionRing K (Submonoid.powers π) (Localization.Away π)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero)).range ↔
      ∀ (P : Ideal R) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {π} →
        x ∈ (Localization.mapToFractionRing K P.primeCompl (Localization.AtPrime P)
          (Ideal.primeCompl_le_nonZeroDivisors P)).range := by
  rw [mem_range_away_iff hπ.ne_zero, mem_away_iff_forall_height_one hπ]
  constructor
  · intro h P _ h1 hPπ
    exact (mem_range_atPrime_iff P x).mpr (h P ‹_› h1 hPπ)
  · intro h P hP h1 hPπ
    exact (mem_range_atPrime_iff P x).mp (h P h1 hPπ)

end Intersection

/-! ## 2. `Λ = ℤ₂[[t]]`, `Λ[1/2]` and the central specialization -/

/-- `Λ = ℤ₂[[t]]`, the coefficient ring of Section 9. -/
abbrev Lambda : Type := PowerSeries ℤ_[2]

/-- `Λ[1/2]`, the genuine localization of `Λ` away from `2`. -/
abbrev LambdaHalf : Type := Localization.Away (2 : Lambda)

/-- In `Λ`, `2 ∣ f` iff every coefficient of `f` is divisible by `2` in `ℤ₂` (`PROVED`). -/
theorem two_dvd_iff_forall_coeff (f : Lambda) :
    (2 : Lambda) ∣ f ↔ ∀ n : ℕ, (2 : ℤ_[2]) ∣ PowerSeries.coeff n f := by
  have h2 : (2 : Lambda) = PowerSeries.C (2 : ℤ_[2]) := (map_ofNat _ 2).symm
  constructor
  · rintro ⟨g, rfl⟩ n
    exact ⟨PowerSeries.coeff n g, by rw [h2, PowerSeries.coeff_C_mul]⟩
  · intro h
    choose g hg using h
    refine ⟨PowerSeries.mk g, PowerSeries.ext fun n => ?_⟩
    rw [h2, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hg n]

/-- **`2` is prime in `Λ`** (`PROVED`). Proof: `2 ∣ f` iff `f` reduces to `0` in `𝔽₂[[t]]`
(coefficientwise, via `ℤ₂ → ℤ₂/2 = 𝔽₂`), and `𝔽₂[[t]]` is a domain; i.e. `Λ/2 ≅ 𝔽₂[[t]]` is a
domain. -/
theorem prime_two_lambda : Prime (2 : Lambda) := by
  let φ : Lambda →+* PowerSeries (ZMod 2) := PowerSeries.map PadicInt.toZMod
  have hker : ∀ f : Lambda, φ f = 0 ↔ (2 : Lambda) ∣ f := by
    intro f
    rw [two_dvd_iff_forall_coeff]
    have hcoeff : ∀ n : ℕ,
        PowerSeries.coeff n (φ f) = 0 ↔ (2 : ℤ_[2]) ∣ PowerSeries.coeff n f := by
      intro n
      rw [PowerSeries.coeff_map, ← RingHom.mem_ker, PadicInt.ker_toZMod,
        PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
      norm_num
    constructor
    · intro h n
      rw [← hcoeff n, h, map_zero]
    · intro h
      ext n
      rw [map_zero]
      exact (hcoeff n).mpr (h n)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg PowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at this
    exact two_ne_zero this
  · intro hu
    have h0 : φ 2 = 0 := (hker 2).mpr dvd_rfl
    have := hu.map φ
    rw [h0] at this
    exact not_isUnit_zero this
  · intro f g hfg
    rw [← hker, map_mul] at hfg
    rw [← hker, ← hker]
    exact mul_eq_zero.mp hfg

/-- **`Λ = ℤ₂[[t]]` is a UFD** (`PROVED`, by a Mathlib instance).

Mathlib proves that `R⟦X⟧` is a `UniqueFactorizationMonoid` for every principal ideal domain `R`
(Kaplansky's criterion: every nonzero prime ideal contains a prime element); `ℤ₂` is a DVR.
Textbook route: `ℤ₂[[t]]` is a two-dimensional regular local ring, and a regular local ring is a
UFD (Auslander–Buchsbaum; Stacks Project, Lemma 15.122.2, Tag 0AG0; also Matsumura, Commutative
Ring Theory, Thm 20.3, UNVERIFIED locator). No `GLUE` hypothesis is needed for this fact. -/
theorem lambda_ufd : UniqueFactorizationMonoid Lambda := inferInstance

/-- The canonical map `Λ[1/2] → Frac Λ`. -/
noncomputable def lambdaHalfToFrac : LambdaHalf →ₐ[Lambda] FractionRing Lambda :=
  Localization.mapToFractionRing (FractionRing Lambda) (Submonoid.powers (2 : Lambda)) LambdaHalf
    (powers_le_nonZeroDivisors_of_noZeroDivisors prime_two_lambda.ne_zero)

/-- `Λ[1/2] → Frac Λ` is injective (`PROVED`), so "lies in the image of `Λ[1/2]`" is membership
in the subring `Λ[1/2] ⊂ Frac Λ`. -/
theorem lambdaHalfToFrac_injective : Function.Injective lambdaHalfToFrac := by
  intro a b hab
  have hinj := (IsLocalization.lift_injective_iff
    (M := Submonoid.powers (2 : Lambda)) (S := LambdaHalf)
    (Localization.map_isUnit_of_le (FractionRing Lambda) _
      (powers_le_nonZeroDivisors_of_noZeroDivisors prime_two_lambda.ne_zero))).mpr
    (fun x y => ⟨fun h => congrArg _ (IsLocalization.injective LambdaHalf
        (powers_le_nonZeroDivisors_of_noZeroDivisors prime_two_lambda.ne_zero) h),
      fun h => congrArg _ (IsFractionRing.injective Lambda (FractionRing Lambda) h)⟩)
  exact hinj hab

/-- **The intersection formula for `Λ[1/2]`**, elementwise, over prime elements (tex 5192-5194,
`PROVED`): `mem_away_iff_forall_prime` for `R = Λ = ℤ₂[[t]]`, `π = 2`, using
`prime_two_lambda` and `lambda_ufd`. Same DEPARTURE of form (prime elements; the height-one form
is `mem_range_lambdaHalf_iff_forall_height_one`). -/
theorem mem_lambdaHalf_iff_forall_prime (x : FractionRing Lambda) :
    (∃ a : Lambda, ∃ m : ℕ,
        x * algebraMap Lambda (FractionRing Lambda) (2 ^ m) =
          algebraMap Lambda (FractionRing Lambda) a) ↔
      ∀ p : Lambda, Prime p → ¬ Associated p 2 →
        ∃ a s : Lambda, s ∉ Ideal.span {p} ∧
          x * algebraMap Lambda (FractionRing Lambda) s =
            algebraMap Lambda (FractionRing Lambda) a :=
  mem_away_iff_forall_prime prime_two_lambda x

/-- **`u_prim ∈ Λ[1/2]` from regularity at the primes `(p) ≠ (2)`** (tex 5191-5194, `PROVED`):
`x ∈ Frac Λ` lies in (the image of) the genuine `Λ[1/2]` iff it is regular at every prime `(p)`,
`p` a prime element not associated to `2`. The direction used in the manuscript is `←`. Same
DEPARTURE of form (prime elements; see `mem_range_lambdaHalf_iff_forall_height_one`). -/
theorem mem_range_lambdaHalf_iff_forall_prime (x : FractionRing Lambda) :
    x ∈ lambdaHalfToFrac.range ↔
      ∀ p : Lambda, Prime p → ¬ Associated p 2 →
        ∃ a s : Lambda, s ∉ Ideal.span {p} ∧
          x * algebraMap Lambda (FractionRing Lambda) s =
            algebraMap Lambda (FractionRing Lambda) a := by
  rw [← mem_lambdaHalf_iff_forall_prime]
  exact mem_range_away_iff prime_two_lambda.ne_zero x

/-- **`Λ[1/2] = ⋂_{𝔭 ≠ (2), ht 𝔭 = 1} Λ_𝔭`** (tex 5191-5194, `PROVED`), with genuine Mathlib
localizations, no departure of form: "This proves regularity at every `𝔭 ≠ (2)`, including both
quadratic specializations. Finally the normal-domain intersection formula for `Λ[1/2]` gives
`u_prim ∈ Λ[1/2]`." The manuscript uses the direction `←`: an element of `Frac Λ` lying in `Λ_𝔭`
for every height-one prime `𝔭 ≠ (2)` lies in `Λ[1/2]`. -/
theorem mem_range_lambdaHalf_iff_forall_height_one (x : FractionRing Lambda) :
    x ∈ lambdaHalfToFrac.range ↔
      ∀ (P : Ideal Lambda) [P.IsPrime], P.height = 1 → P ≠ Ideal.span {2} →
        x ∈ (Localization.mapToFractionRing (FractionRing Lambda) P.primeCompl
          (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)).range :=
  mem_range_away_iff_forall_height_one prime_two_lambda x

/-- The evaluation `Λ → ℚ₂`, `f ↦ f(0)`: constant coefficient followed by `ℤ₂ ⊂ ℚ₂`. -/
noncomputable def lambdaEvalZero : Lambda →+* ℚ_[2] :=
  PadicInt.Coe.ringHom.comp PowerSeries.constantCoeff

/-- `2` maps to a unit of `ℚ₂` under `lambdaEvalZero` (`PROVED`). -/
theorem isUnit_lambdaEvalZero_two : IsUnit (lambdaEvalZero (2 : Lambda)) := by
  rw [map_ofNat]
  exact isUnit_iff_ne_zero.mpr two_ne_zero

/-- **The central specialization** `Λ[1/2] → ℚ₂`, `u ↦ u(0)`, i.e. `t ↦ 0` (tex 4920, 4045,
5200-5202). It is `IsLocalization.Away.lift` of `lambdaEvalZero` (constant coefficient, then
`ℤ₂ ⊂ ℚ₂`); `2` is a unit in `ℚ₂`. -/
noncomputable def centralSpecialization : LambdaHalf →+* ℚ_[2] :=
  IsLocalization.Away.lift (2 : Lambda) isUnit_lambdaEvalZero_two

/-- On `Λ ⊂ Λ[1/2]` the central specialization is `f ↦ f(0)` (`PROVED`). -/
@[simp]
theorem centralSpecialization_algebraMap (f : Lambda) :
    centralSpecialization (algebraMap Lambda LambdaHalf f) =
      ((PowerSeries.constantCoeff f : ℤ_[2]) : ℚ_[2]) :=
  IsLocalization.Away.lift_eq _ _ f

/-- `v₂(2) = 1` in `ℚ₂` (`PROVED`). -/
theorem padic_valuation_two : Padic.valuation (2 : ℚ_[2]) = 1 := by
  have := Padic.valuation_p (p := 2)
  exact_mod_cast this

/-- **`v₂ u(0)` is at least the Gauss valuation** (tex 4914-4920 and 5200-5202, `PROVED`).

(5.5) reads `v₂ u_prim ≥ -C(E,A)`, "where the first valuation is that of `𝒪`"; here
`𝒪 = (Λ_(2))^` is the completed DVR with uniformizer `2`. Integral form used here: for
`u ∈ Λ[1/2]`, `v_𝒪(u) ≥ -C ⟺ 2^C u ∈ Λ`. Indeed write `u = f/2^m` with `f ∈ Λ`. Because `2` is
prime in `Λ` (`prime_two_lambda`), the `(2)`-adic valuation of `Λ` is `f ↦` (multiplicity of `2`
in `f`) `= min_i v₂(coeff_i f)`, the Gauss valuation, and `v_𝒪(f/2^m) = v_(2)(f) - m`. So
`v_𝒪(u) ≥ -C` iff `2^(m-C) ∣ f` (automatic if `m ≤ C`) iff `2^C u ∈ Λ`; the last equivalence
is `two_pow_mul_mem_range_iff`.

Conclusion: if `2^C u ∈ Λ` then `u(0) = 0` or `v₂(u(0)) ≥ -C`: the constant coefficient of
`2^C u ∈ Λ` lies in `ℤ₂`, so `C + v₂(u(0)) ≥ 0`. The bound is attained
(`valuation_central_ge_sharp`).

DEPARTURE (form): `C` is taken in `ℕ`; a larger constant is always allowed in (5.5). -/
theorem valuation_central_ge (C : ℕ) (u : LambdaHalf)
    (h55 : (2 : LambdaHalf) ^ C * u ∈ (algebraMap Lambda LambdaHalf).range) :
    centralSpecialization u = 0 ∨ -(C : ℤ) ≤ Padic.valuation (centralSpecialization u) := by
  by_cases hu : centralSpecialization u = 0
  · exact Or.inl hu
  right
  obtain ⟨f, hf⟩ := h55
  have h1 : (2 : ℚ_[2]) ^ C * centralSpecialization u =
      ((PowerSeries.constantCoeff f : ℤ_[2]) : ℚ_[2]) := by
    have := congrArg centralSpecialization hf
    rw [centralSpecialization_algebraMap, map_mul, map_pow, map_ofNat] at this
    exact this.symm
  have h2 : Padic.valuation ((2 : ℚ_[2]) ^ C * centralSpecialization u) =
      C + Padic.valuation (centralSpecialization u) := by
    rw [Padic.valuation_mul (pow_ne_zero _ two_ne_zero) hu, Padic.valuation_pow,
      padic_valuation_two, mul_one]
  have h3 : 0 ≤ Padic.valuation ((PowerSeries.constantCoeff f : ℤ_[2]) : ℚ_[2]) :=
    PadicInt.valuation_coe_nonneg
  rw [← h1, h2] at h3
  omega

/-- Every `u ∈ Λ[1/2]` has the form `f/2^m` with `f ∈ Λ` (`PROVED`); so the hypothesis of
`two_pow_mul_mem_range_iff` is satisfiable for every `u`. -/
theorem exists_mul_two_pow_eq (u : LambdaHalf) :
    ∃ (f : Lambda) (m : ℕ),
      u * algebraMap Lambda LambdaHalf (2 ^ m) = algebraMap Lambda LambdaHalf f := by
  obtain ⟨⟨f, s⟩, hf⟩ := IsLocalization.surj (Submonoid.powers (2 : Lambda)) u
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  exact ⟨f, m, by rw [hm]; exact hf⟩

/-- The integral form of `v_𝒪(u) ≥ -C`, made precise (`PROVED`): for `u = f/2^m ∈ Λ[1/2]`
(i.e. `u · 2^m = f` with `f ∈ Λ`), `2^C u ∈ Λ` iff `2^(m-C) ∣ f` in `Λ` (truncated subtraction),
i.e. iff the multiplicity of the prime `2` in `f` (the `(2)`-adic, equivalently Gauss, valuation
of `f`) is at least `m - C`; that is, iff `v_𝒪(u) = v_(2)(f) - m ≥ -C`. -/
theorem two_pow_mul_mem_range_iff {u : LambdaHalf} {f : Lambda} {m C : ℕ}
    (hu : u * algebraMap Lambda LambdaHalf (2 ^ m) = algebraMap Lambda LambdaHalf f) :
    (2 : LambdaHalf) ^ C * u ∈ (algebraMap Lambda LambdaHalf).range ↔
      ((m - C : ℕ) : ℕ∞) ≤ emultiplicity (2 : Lambda) f := by
  rw [← pow_dvd_iff_le_emultiplicity]
  rcases le_or_gt C m with hCm | hmC
  · obtain ⟨d, rfl⟩ : ∃ d, m = d + C := ⟨m - C, (Nat.sub_add_cancel hCm).symm⟩
    rw [Nat.add_sub_cancel]
    have hinj : Function.Injective (algebraMap Lambda LambdaHalf) :=
      IsLocalization.injective LambdaHalf
        (powers_le_nonZeroDivisors_of_noZeroDivisors prime_two_lambda.ne_zero)
    have h2u : IsUnit (2 : LambdaHalf) := by
      have := IsLocalization.Away.algebraMap_isUnit (S := LambdaHalf) (2 : Lambda)
      rwa [map_ofNat] at this
    rw [map_pow, map_ofNat, pow_add] at hu
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, hinj ?_⟩
      rw [← hu, map_mul, map_pow, map_ofNat, hg]
      ring
    · rintro ⟨g, rfl⟩
      have key : (2 : LambdaHalf) ^ d * algebraMap Lambda LambdaHalf g =
          2 ^ d * (2 ^ C * u) := by
        calc (2 : LambdaHalf) ^ d * algebraMap Lambda LambdaHalf g
            = algebraMap Lambda LambdaHalf (2 ^ d * g) := by rw [map_mul, map_pow, map_ofNat]
          _ = u * (2 ^ d * 2 ^ C) := hu.symm
          _ = 2 ^ d * (2 ^ C * u) := by ring
      exact ⟨g, (h2u.pow d).mul_left_cancel key⟩
  · rw [Nat.sub_eq_zero_of_le hmC.le, pow_zero]
    refine iff_of_true ?_ (one_dvd f)
    obtain ⟨e, rfl⟩ : ∃ e, C = e + m := ⟨C - m, (Nat.sub_add_cancel hmC.le).symm⟩
    refine ⟨2 ^ e * f, ?_⟩
    rw [map_mul, ← hu]
    simp only [map_pow, map_ofNat, pow_add]
    ring

/-- Sharpness and non-vacuity of `valuation_central_ge` (`PROVED`): `u = 2^(-C)` satisfies the
integral form of (5.5) with constant `C`, and `v₂ u(0) = -C`. -/
theorem valuation_central_ge_sharp (C : ℕ) : ∃ u : LambdaHalf,
    (2 : LambdaHalf) ^ C * u ∈ (algebraMap Lambda LambdaHalf).range ∧
      centralSpecialization u ≠ 0 ∧ Padic.valuation (centralSpecialization u) = -(C : ℤ) := by
  set w : LambdaHalf := IsLocalization.Away.invSelf (2 : Lambda)
  have hw : (2 : LambdaHalf) * w = 1 := by
    have := IsLocalization.Away.mul_invSelf (S := LambdaHalf) (2 : Lambda)
    rwa [map_ofNat] at this
  have hcs : centralSpecialization w = (2 : ℚ_[2])⁻¹ := by
    have := congrArg centralSpecialization hw
    rw [map_mul, map_ofNat, map_one] at this
    exact (inv_eq_of_mul_eq_one_right this).symm
  refine ⟨w ^ C, ⟨1, ?_⟩, ?_, ?_⟩
  · rw [map_one, ← mul_pow, hw, one_pow]
  · rw [map_pow, hcs]
    exact pow_ne_zero _ (inv_ne_zero two_ne_zero)
  · rw [map_pow, hcs, Padic.valuation_pow, Padic.valuation_inv, padic_valuation_two]
    ring

/-! ## 3. (5.5) + (4.6) ⇒ (3.5) -/

/-- **`∑_{p ∣ k} t_p ≤ 2A`** (tex 5201, `PROVED`). `P` is the finset of companion primes `p ∣ k`,
so `#P = ω(k) ≤ A`, and `t_p ≤ 2` (tex 4000, 4039: `t_p = dim_{𝔽₂} E[2]^{Fr_p} ≤ 2`). -/
theorem sum_t_le {P : Finset ℕ} {t : ℕ → ℤ} {A : ℕ} (ht : ∀ p ∈ P, t p ≤ 2)
    (hP : P.card ≤ A) : ∑ p ∈ P, t p ≤ 2 * (A : ℤ) := by
  have h1 : ∑ p ∈ P, t p ≤ P.card • (2 : ℤ) := Finset.sum_le_card_nsmul P t 2 ht
  have h2 : (P.card : ℤ) ≤ A := by exact_mod_cast hP
  rw [nsmul_eq_mul] at h1
  linarith

/-- **(4.6) with the companion sum absorbed** (tex 4045-4047 and 5200-5202, `PROVED`).
(4.6): `v₂ u_prim(0) = 2 j_rc(h,k) - 4ω(h) - s(h) - s(hk) - ∑_{p ∣ k} t_p + O_{E,π}(1)`, written
as `|v - (2 j_rc - 4ω - sh - shk - ∑_{p ∈ P} t p)| ≤ C₀`. With `0 ≤ t_p ≤ 2` and `#P ≤ A`
("Only after a bound on `ω(k)` is imposed may the companion sum be absorbed", tex 4001-4002):
`|v - (2 j_rc - 4ω - sh - shk)| ≤ C₀ + 2A`. -/
theorem eq46_absorbed {j_rc ω sh shk v C₀ : ℤ} {P : Finset ℕ} {t : ℕ → ℤ} {A : ℕ}
    (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 2) (hP : P.card ≤ A)
    (h46 : |v - (2 * j_rc - 4 * ω - sh - shk - ∑ p ∈ P, t p)| ≤ C₀) :
    |v - (2 * j_rc - 4 * ω - sh - shk)| ≤ C₀ + 2 * A := by
  have hS := sum_t_le (fun p hp => (ht p hp).2) hP
  have hS0 : 0 ≤ ∑ p ∈ P, t p := Finset.sum_nonneg (fun p hp => (ht p hp).1)
  rw [abs_le] at h46 ⊢
  constructor <;> linarith [h46.1, h46.2]

/-- **(5.5) + (4.6) ⇒ (3.5)** (tex 5200-5202, `PROVED`).

(3.5) (tex 2446): `2 j_rc(h,k') ≥ 4ω(h) + s(h) + s(hk') - C_R(E,A)`, `ω(k') ≤ A`; here the
companion `k' = k` and `P` is its finset of prime divisors.
Inputs: (4.6) as `|v - (2 j_rc - 4ω - sh - shk - ∑_{p ∈ P} t p)| ≤ C₀` (`C₀` the `O_{E,π}(1)`),
and (5.5) at the centre as `-C ≤ v`, where `v = v₂ u_prim(0)` (see `valuation_central_ge`).
Conclusion with `C_R := C + C₀`.

Only `t_p ≥ 0` is needed for this direction (a presentation point noted in the manuscript
check: the bound `∑ t_p ≤ 2A` is not needed here). The companion sum enters (4.6) with a minus
sign, so dropping it only weakens the upper bound for `v`. Elliot's hypotheses
`0 ≤ t_p ≤ 2`, `ω(k) ≤ A` give `ht` by `fun p hp => (h p hp).1`. His literal route through
`∑ t_p ≤ 2A` (`sum_t_le`) and the absorbed two-sided form (`eq46_absorbed`) is
`eq35_of_eq55_eq46_absorbed`; it gives the constant `C + C₀ + 2A`, also of the form `C_R(E,A)`. -/
theorem eq35_of_eq55_eq46 {j_rc ω sh shk v C C₀ : ℤ} {P : Finset ℕ} {t : ℕ → ℤ}
    (ht : ∀ p ∈ P, 0 ≤ t p)
    (h46 : |v - (2 * j_rc - 4 * ω - sh - shk - ∑ p ∈ P, t p)| ≤ C₀)
    (h55 : -C ≤ v) :
    2 * j_rc ≥ 4 * ω + sh + shk - (C + C₀) := by
  have hS0 : 0 ≤ ∑ p ∈ P, t p := Finset.sum_nonneg ht
  have := (abs_le.mp h46).2
  linarith

/-- **(5.5) + (4.6) ⇒ (3.5), Elliot's literal route** (tex 5200-5202, `PROVED`): first
`∑_{p ∣ k} t_p ≤ 2A` (`sum_t_le`), then the absorbed form
`|v - (2 j_rc - 4ω - sh - shk)| ≤ C₀ + 2A` (`eq46_absorbed`), then (5.5) `-C ≤ v`. This gives
(3.5) with `C_R(E,A) := C + C₀ + 2A`. -/
theorem eq35_of_eq55_eq46_absorbed {j_rc ω sh shk v C C₀ : ℤ} {P : Finset ℕ} {t : ℕ → ℤ}
    {A : ℕ} (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 2) (hP : P.card ≤ A)
    (h46 : |v - (2 * j_rc - 4 * ω - sh - shk - ∑ p ∈ P, t p)| ≤ C₀)
    (h55 : -C ≤ v) :
    2 * j_rc ≥ 4 * ω + sh + shk - (C + (C₀ + 2 * A)) := by
  have habs := (abs_le.mp (eq46_absorbed ht hP h46)).2
  linarith

/-- **(3.5) from `u ∈ Λ[1/2]`** (tex 4914-4920 and 5200-5202, `PROVED`): the combined statement.
`u : Λ[1/2]` satisfies (5.5) in integral form, `2^C u ∈ Λ` (see `valuation_central_ge`), its
central specialization `u(0)` is nonzero, and (4.6) holds for `v₂ u(0)` (`Padic.valuation`):
`|v₂ u(0) - (2 j_rc - 4ω - sh - shk - ∑_{p ∈ P} t p)| ≤ C₀`. Then (3.5) holds with
`C_R := C + C₀`. Only `t_p ≥ 0` is used (see `eq35_of_eq55_eq46`). -/
theorem eq35_of_lambdaHalf {j_rc ω sh shk C₀ : ℤ} {P : Finset ℕ} {t : ℕ → ℤ}
    (C : ℕ) (u : LambdaHalf)
    (h55 : (2 : LambdaHalf) ^ C * u ∈ (algebraMap Lambda LambdaHalf).range)
    (hu0 : centralSpecialization u ≠ 0)
    (ht : ∀ p ∈ P, 0 ≤ t p)
    (h46 : |Padic.valuation (centralSpecialization u) -
        (2 * j_rc - 4 * ω - sh - shk - ∑ p ∈ P, t p)| ≤ C₀) :
    2 * j_rc ≥ 4 * ω + sh + shk - ((C : ℤ) + C₀) := by
  have hv := (valuation_central_ge C u h55).resolve_left hu0
  exact eq35_of_eq55_eq46 ht h46 hv

/-- Non-vacuity of the hypotheses of `eq46_absorbed`, `eq35_of_eq55_eq46` and
`eq35_of_eq55_eq46_absorbed`, with two companion primes and `t_p = 2`. -/
example : ∃ (j_rc ω sh shk v C C₀ : ℤ) (P : Finset ℕ) (t : ℕ → ℤ) (A : ℕ),
    P.Nonempty ∧ (∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 2) ∧ P.card ≤ A ∧
      |v - (2 * j_rc - 4 * ω - sh - shk - ∑ p ∈ P, t p)| ≤ C₀ ∧ -C ≤ v := by
  refine ⟨10, 1, 0, 0, 12, 0, 0, {3, 5}, fun _ => 2, 2, ⟨3, by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro p _
    norm_num
  · decide
  · simp
  · norm_num

/-- Non-vacuity of the hypotheses of `eq35_of_lambdaHalf`: `u = 2^(-2)`, one companion prime. -/
example : ∃ (u : LambdaHalf) (C : ℕ) (j_rc ω sh shk C₀ : ℤ) (P : Finset ℕ) (t : ℕ → ℤ),
    (2 : LambdaHalf) ^ C * u ∈ (algebraMap Lambda LambdaHalf).range ∧
      centralSpecialization u ≠ 0 ∧ (∀ p ∈ P, 0 ≤ t p) ∧
      |Padic.valuation (centralSpecialization u) -
          (2 * j_rc - 4 * ω - sh - shk - ∑ p ∈ P, t p)| ≤ C₀ := by
  obtain ⟨u, h55, hu0, hv⟩ := valuation_central_ge_sharp 2
  refine ⟨u, 2, 2, 1, 0, 0, 0, {3}, fun _ => 2, h55, hu0, fun _ _ => by norm_num, ?_⟩
  rw [hv]
  simp

end ZInQ.Manuscript.RC.Uniform

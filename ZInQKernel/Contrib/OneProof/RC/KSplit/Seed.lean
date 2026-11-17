import ZInQKernel.Contrib.OneProof.RC.KSplit.TwoPrimary
import ZInQKernel.Contrib.OneProof.RC.KSplit.Twist
import ZInQKernel.Contrib.OneProof.RC.KSplit.Ap
import ZInQKernel.Contrib.OneProof.RC.KSplit.Primes
import ZInQKernel.Contrib.OneProof.RC.KSplit.Coefficients

/-!
# Lane RC3: the nonempty `K`-split seed for `E_ℓ` (Lemma `ex:sec7-ksplit-seed`)

Manuscript `diophantine_zq.tex` (11/5): Lemma `ex:sec7-ksplit-seed` (tex 2628–2654) and the
nonempty-seed part of Proposition `ex:app-nonempty-seeds` (tex 10259–10507).

`E^{(k)}` is the quadratic twist `y² = x(x − kℓ)(x + 3kℓ)` of `E_ℓ`, i.e.
`ZInQ.Manuscript.curve (kℓ)`, and `a_p(E^{(k)})` is the Dirichlet coefficient at `p` of Mathlib's
`L(E^{(k)}, s)` (`Ap.lean` identifies it with `p + 1 − #Ẽ^{(k)}(𝔽_p)` at `p ∤ 6kℓ`).

* `exists_ksplit_prime_v2_eq_two` (`PROVED`, unconditional): for the manuscript's `ℓ` and `k`
  (odd squarefree, with a prime `q₀ ∣ k`, `q₀ ∤ 2ℓ`), there are arbitrarily large primes
  `p ≡ 1 (mod 4)` with `(ℓ/p) = −1`, `(k/p) = 1`, `p ∤ 6kℓ`, and
  `v₂(p + 1 − a_p(E^{(k)})) = 2`. This is the whole elementary content of the second paragraph of
  the proof of `ex:sec7-ksplit-seed` (tex 2643–2653) and of tex 10482–10500.
* `AppGCongruence` (`ELLIOT`, tex 2636–2641, 10319–10481): under the assumed absence of a nonempty
  `K`-split unit seed, `a_p(E^{(k)}) ≡ p + 1 (mod 8)` at every fresh good `K`-split prime outside
  the finite support. (For an odd prime `p ∤ k`, `p` splits in `K = ℚ(√k)` iff `(k/p) = 1`; this
  textbook criterion is used to read "`K`-split" as `(k/p) = 1`, `GLUE`.)
* `ksplit_seed` (`PROVED` from `AppGCongruence`): **Lemma `ex:sec7-ksplit-seed`** — the assumed
  absence of a nonempty `K`-split unit seed is refuted.
* `appGCongruence_of_traceData`, `app_nonempty_seed` (`PROVED` from the `ELLIOT` interface
  `NoSeedTraceData` of `Coefficients.lean`): the same, with Elliot's App G coefficient calculation
  carried out in Lean: the no-seed trace data at a prime give `a_p ≡ p + 1 (mod 8)`.
-/

namespace ZInQ.Manuscript.RC.KSplit

open ZInQ.Manuscript.PoleRC

/-- Facts about a prime `p` with `(ℓ/p) = −1`, `(k/p) = 1`, `p ≡ 1 (mod 4)`: `p ∤ 6kℓ`, `k` is a
nonzero square and `ℓ` a nonsquare modulo `p` (`PROVED`). -/
theorem seed_prime_facts {ℓ : ℕ} {k : ℤ} {p : ℕ} [hp : Fact p.Prime] (hp4 : p % 4 = 1)
    (hJℓ : jacobiSym (ℓ : ℤ) p = -1) (hJk : jacobiSym k p = 1) :
    ¬ (p : ℤ) ∣ 6 * (k * ℓ) ∧ IsSquare ((k : ℤ) : ZMod p) ∧ ((k : ℤ) : ZMod p) ≠ 0 ∧
      ¬ IsSquare (((ℓ : ℤ)) : ZMod p) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hJℓ hJk
  have hk0 : ((k : ℤ) : ZMod p) ≠ 0 := by
    intro h
    rw [(legendreSym.eq_zero_iff p k).mpr h] at hJk
    exact zero_ne_one hJk
  have hℓ0 : (((ℓ : ℤ)) : ZMod p) ≠ 0 := by
    intro h
    rw [(legendreSym.eq_zero_iff p ℓ).mpr h] at hJℓ
    norm_num at hJℓ
  have hksq : IsSquare ((k : ℤ) : ZMod p) := (legendreSym.eq_one_iff p hk0).mp hJk
  have hℓsq : ¬ IsSquare (((ℓ : ℤ)) : ZMod p) := (legendreSym.eq_neg_one_iff p).mp hJℓ
  refine ⟨?_, hksq, hk0, hℓsq⟩
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp4
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at hp4
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  intro hdvd
  rcases hpz.dvd_or_dvd hdvd with h6 | hkℓ
  · have : p ∣ 6 := by exact_mod_cast h6
    have h6' : p ∣ 2 * 3 := this
    rcases (Nat.Prime.dvd_mul hp.out).mp h6' with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h)
  · rcases hpz.dvd_or_dvd hkℓ with h | h
    · exact hk0 ((ZMod.intCast_zmod_eq_zero_iff_dvd k p).mpr h)
    · exact hℓ0 ((ZMod.intCast_zmod_eq_zero_iff_dvd ℓ p).mpr h)

/-- **`p + 1 − a_p(E^{(k)})` is the number of points of `E_ℓ` mod `p`** (`PROVED`; tex 2645–2647):
at a prime `p ∤ 6kℓ` with `k` a nonzero square mod `p`, Mathlib's coefficient gives
`p + 1 − a_p(E^{(k)}) = #Ẽ^{(k)}(𝔽_p) = #Ẽ_ℓ(𝔽_p)`. -/
theorem sub_LFunction_twist_eq_card {ℓ : ℕ} {k : ℤ} {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1)
    (hp6 : ¬ (p : ℤ) ∣ 6 * (k * ℓ)) (hksq : IsSquare ((k : ℤ) : ZMod p))
    (hk0 : ((k : ℤ) : ZMod p) ≠ 0) (hℓ0 : (((ℓ : ℤ)) : ZMod p) ≠ 0) :
    (p : ℤ) + 1 - (ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p =
      Nat.card (curveF (((ℓ : ℤ)) : ZMod p)).toAffine.Point := by
  obtain ⟨h2, h3⟩ := two_three_ne_zero_of_one_mod_four hp4
  rw [LFunction_curve_apply_prime (k * ℓ) p hp6, show (((k * ℓ : ℤ)) : ZMod p) =
    ((k : ℤ) : ZMod p) * (((ℓ : ℤ)) : ZMod p) by push_cast; ring,
    natCard_curveF_mul_of_isSquare h2 h3 hℓ0 hksq hk0]
  ring

/-- **The `K`-split prime of the seed argument** (`PROVED`; tex 2643–2653 and 10482–10500): for
positive squarefree `ℓ ≡ 11 (mod 12)` and odd squarefree `k` with a prime `q₀ ∣ k`, `q₀ ∤ 2ℓ` (a
prime ramified in `K = ℚ(√k)` outside the ramification of `ℚ(i, √ℓ)`), there are arbitrarily large
primes `p` with `p ≡ 1 (mod 4)`, `(ℓ/p) = −1`, `(k/p) = 1` (so `p` splits in `K`), `p ∤ 6kℓ`
(so `E^{(k)}` has good reduction at `p`), and `v₂(p + 1 − a_p(E^{(k)})) = 2`: the reductions of
`E^{(k)}` and `E_ℓ` are isomorphic, none of the three nonzero points of order two can be halved
(the required differences `−ℓ, ℓ, −4ℓ` are nonsquares), and the two-primary reduction group has
order exactly four. -/
theorem exists_ksplit_prime_v2_eq_two {ℓ : ℕ} (hℓ_pos : 0 < ℓ) (hℓ_sf : Squarefree ℓ)
    (hℓ12 : ℓ % 12 = 11) {k : ℤ} (hk_odd : Odd k) (hk_sf : Squarefree k) {q₀ : ℕ}
    (hq₀ : q₀.Prime) (hq₀k : (q₀ : ℤ) ∣ k) (hq₀ℓ : ¬ q₀ ∣ 2 * ℓ) (n : ℕ) :
    ∃ p : ℕ, n < p ∧ p.Prime ∧ p % 4 = 1 ∧ jacobiSym (ℓ : ℤ) p = -1 ∧ jacobiSym k p = 1 ∧
      ¬ (p : ℤ) ∣ 6 * (k * ℓ) ∧
      (4 : ℤ) ∣ (p : ℤ) + 1 - (ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p ∧
      ¬ (8 : ℤ) ∣ (p : ℤ) + 1 - (ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p := by
  obtain ⟨p, hpn, hp, hp4, hJℓ, hJk⟩ :=
    exists_prime_seed_conditions_of_mod_twelve hℓ_pos hℓ_sf hℓ12 hk_odd hk_sf hq₀ hq₀k hq₀ℓ n
  have := Fact.mk hp
  obtain ⟨hp6, hksq, hk0, hℓsq⟩ := seed_prime_facts hp4 hJℓ hJk
  have hℓ0 : (((ℓ : ℤ)) : ZMod p) ≠ 0 := by rintro h; exact hℓsq (h ▸ ⟨0, by ring⟩)
  obtain ⟨h4, h8⟩ := card_curveF_zmod_of_conditions hp4 hℓsq
  refine ⟨p, hpn, hp, hp4, hJℓ, hJk, hp6, ?_, ?_⟩
  · rw [sub_LFunction_twist_eq_card hp4 hp6 hksq hk0 hℓ0]; exact_mod_cast h4
  · rw [sub_LFunction_twist_eq_card hp4 hp6 hksq hk0 hℓ0]; exact_mod_cast h8

/-- **The App G congruence** (`ELLIOT`; tex 2636–2641, 10319–10481; Version 19 states its scope
explicitly, `quartic_v19.tex` 18569–18583: "at every fresh good `K`-split prime outside the support,
whether or not it lies in the coefficient filter"): `a_p(E^{(k)}) ≡ p + 1 (mod 8)` at every prime
`p` outside the finite support `S` with `p ∤ 6kℓ` (good reduction of `E^{(k)}`) and `(k/p) = 1`
(`p` split in `K`). Elliot derives it inside the assumed absence of a nonempty unit seed; see
`appGCongruence_of_traceData` for that derivation from its modular-forms inputs. -/
def AppGCongruence (ℓ : ℕ) (k : ℤ) (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ 6 * (k * ℓ) → jacobiSym k p = 1 →
    (8 : ℤ) ∣ (p : ℤ) + 1 - (ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p

/-- **The App G congruence fails**: some prime of `AppGCongruence`'s range violates it
(`PROVED`). -/
theorem not_appGCongruence {ℓ : ℕ} (hℓ_pos : 0 < ℓ) (hℓ_sf : Squarefree ℓ) (hℓ12 : ℓ % 12 = 11)
    {k : ℤ} (hk_odd : Odd k) (hk_sf : Squarefree k) {q₀ : ℕ} (hq₀ : q₀.Prime)
    (hq₀k : (q₀ : ℤ) ∣ k) (hq₀ℓ : ¬ q₀ ∣ 2 * ℓ) (S : Finset ℕ) : ¬ AppGCongruence ℓ k S := by
  intro hG
  obtain ⟨p, hpn, hp, -, -, hJk, hp6, -, h8⟩ :=
    exists_ksplit_prime_v2_eq_two hℓ_pos hℓ_sf hℓ12 hk_odd hk_sf hq₀ hq₀k hq₀ℓ (S.sup id)
  have hpS : p ∉ S := fun h => absurd (Finset.le_sup (f := id) h) (by simpa using hpn)
  exact h8 (hG p hp hpS hp6 hJk)

/-- **Lemma `ex:sec7-ksplit-seed` (The nonempty seed for the present curve)** (tex 2628–2654;
`PROVED` from the `ELLIOT` input `AppGCongruence`): for `E = E_ℓ` and the chosen `k`, `K`, the
positive even source for `E^{(k)}`, normalized at index one, has a nonempty unit seed consisting of
`K`-split primes. `NoSeed` is the proposition that no such nonempty unit exists (the source and its
seeds are not formalized here; `NoSeed` is the abstract statement the App G calculation
refutes). If `NoSeed` forced `AppGCongruence` (tex 2636–2641), the prime of
`exists_ksplit_prime_v2_eq_two`, chosen outside `S`, would contradict it (tex 2643–2651). -/
theorem ksplit_seed {ℓ : ℕ} (hℓ_pos : 0 < ℓ) (hℓ_sf : Squarefree ℓ) (hℓ12 : ℓ % 12 = 11)
    {k : ℤ} (hk_odd : Odd k) (hk_sf : Squarefree k) {q₀ : ℕ} (hq₀ : q₀.Prime)
    (hq₀k : (q₀ : ℤ) ∣ k) (hq₀ℓ : ¬ q₀ ∣ 2 * ℓ) (S : Finset ℕ) (NoSeed : Prop)
    (hG : NoSeed → AppGCongruence ℓ k S) : ¬ NoSeed := fun h =>
  not_appGCongruence hℓ_pos hℓ_sf hℓ12 hk_odd hk_sf hq₀ hq₀k hq₀ℓ S (hG h)

/-- **Elliot's App G calculation gives the congruence** (`PROVED` from the `ELLIOT` interface
`NoSeedTraceData`, tex 10319–10481): if every prime of `AppGCongruence`'s range carries the no-seed
trace data of the transported source with `a_p = a_p(E^{(k)})`, then `AppGCongruence` holds. The
integrality input `4 ∣ p + 1 − a_p` is full rational two-torsion of `E^{(k)}` mod `p`
(`four_dvd_card`, tex 10475–10476). -/
theorem appGCongruence_of_traceData {L : Type*} [Field L] [CharZero L] (O : Subring L) {ℓ : ℕ}
    {k : ℤ} {S : Finset ℕ}
    (hD : ∀ p : ℕ, ∀ hp : p.Prime, p ∉ S → ¬ (p : ℤ) ∣ 6 * (k * ℓ) → jacobiSym k p = 1 →
      Nonempty (@NoSeedTraceData L _ O p ⟨hp⟩
        ((ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p))) :
    AppGCongruence ℓ k S := by
  intro p hp hpS hp6 hJk
  have := Fact.mk hp
  obtain ⟨D⟩ := hD p hp hpS hp6 hJk
  have hp2 : p ≠ 2 := fun h => hp6 (by rw [h]; exact ⟨3 * (k * ℓ), by push_cast; ring⟩)
  have hp3 : p ≠ 3 := fun h => hp6 (by rw [h]; exact ⟨2 * (k * ℓ), by push_cast; ring⟩)
  have hnd : ∀ q : ℕ, q.Prime → q ≠ p → ((q : ℕ) : ZMod p) ≠ 0 := fun q hq hqp h => by
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp h).symm
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := hnd 2 Nat.prime_two (Ne.symm hp2); exact_mod_cast this
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := hnd 3 Nat.prime_three (Ne.symm hp3); exact_mod_cast this
  have hm0 : (((k * ℓ : ℤ)) : ZMod p) ≠ 0 := fun h =>
    hp6 (Dvd.dvd.mul_left ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h) 6)
  have h4card := four_dvd_card h2 h3 hm0
  have h4 : (4 : ℤ) ∣ (ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p - p - 1 := by
    rw [LFunction_curve_apply_prime (k * ℓ) p hp6]
    have : (4 : ℤ) ∣ (Nat.card (curveF (((k * ℓ : ℤ)) : ZMod p)).toAffine.Point : ℤ) := by
      exact_mod_cast h4card
    rw [show (p : ℤ) + 1 - (Nat.card (curveF (((k * ℓ : ℤ)) : ZMod p)).toAffine.Point : ℤ)
      - p - 1 = -(Nat.card (curveF (((k * ℓ : ℤ)) : ZMod p)).toAffine.Point : ℤ) by ring]
    exact this.neg_right
  have h8 := D.cong_eight hp2 h4
  rw [show (p : ℤ) + 1 - (ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p =
    -((ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p - p - 1) by ring]
  exact h8.neg_right

/-- **The nonempty `K`-split seed from Elliot's App G calculation** (`PROVED` from the `ELLIOT`
interface `NoSeedTraceData`; Proposition `ex:app-nonempty-seeds`, tex 10259–10507, nonempty even
seed part): if the absence of a nonempty `K`-split unit seed (`NoSeed`) gave the no-seed trace data
at every fresh good `K`-split prime outside the support, the prime of
`exists_ksplit_prime_v2_eq_two` would contradict `a_p ≡ p + 1 (mod 8)`. -/
theorem app_nonempty_seed {L : Type*} [Field L] [CharZero L] (O : Subring L) {ℓ : ℕ}
    (hℓ_pos : 0 < ℓ) (hℓ_sf : Squarefree ℓ) (hℓ12 : ℓ % 12 = 11) {k : ℤ} (hk_odd : Odd k)
    (hk_sf : Squarefree k) {q₀ : ℕ} (hq₀ : q₀.Prime) (hq₀k : (q₀ : ℤ) ∣ k)
    (hq₀ℓ : ¬ q₀ ∣ 2 * ℓ) (S : Finset ℕ) (NoSeed : Prop)
    (hD : NoSeed → ∀ p : ℕ, ∀ hp : p.Prime, p ∉ S → ¬ (p : ℤ) ∣ 6 * (k * ℓ) →
      jacobiSym k p = 1 → Nonempty (@NoSeedTraceData L _ O p ⟨hp⟩
        ((ZInQ.Manuscript.curve ((k * ℓ : ℤ) : ℚ)).LFunction p))) : ¬ NoSeed :=
  ksplit_seed hℓ_pos hℓ_sf hℓ12 hk_odd hk_sf hq₀ hq₀k hq₀ℓ S NoSeed fun h =>
    appGCongruence_of_traceData O (hD h)

/-! ### Non-vacuity: the hypotheses hold for `ℓ = 11`, `k = −7`, `q₀ = 7` -/

/-- The manuscript's hypotheses are satisfiable: `ℓ = 11`, `k = −7` (`K = ℚ(√−7)`, ramified only at
`7 ∤ 22`), so `exists_ksplit_prime_v2_eq_two` applies (`PROVED`). -/
theorem exists_ksplit_prime_example (n : ℕ) :
    ∃ p : ℕ, n < p ∧ p.Prime ∧ p % 4 = 1 ∧ jacobiSym (11 : ℤ) p = -1 ∧ jacobiSym (-7) p = 1 ∧
      ¬ (p : ℤ) ∣ 6 * (-7 * 11) ∧
      (4 : ℤ) ∣ (p : ℤ) + 1 - (ZInQ.Manuscript.curve ((-7 * 11 : ℤ) : ℚ)).LFunction p ∧
      ¬ (8 : ℤ) ∣ (p : ℤ) + 1 - (ZInQ.Manuscript.curve ((-7 * 11 : ℤ) : ℚ)).LFunction p := by
  have h11 : Nat.Prime 11 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have hsf : Squarefree (-7 : ℤ) := by
    rw [← Int.squarefree_natAbs]
    exact (Nat.prime_iff.mp h7).squarefree
  have := exists_ksplit_prime_v2_eq_two (ℓ := 11) (k := -7) (q₀ := 7) (by norm_num)
    (Nat.prime_iff.mp h11).squarefree (by norm_num) (by decide) hsf h7 (by norm_num)
    (by norm_num) n
  simpa using this

end ZInQ.Manuscript.RC.KSplit

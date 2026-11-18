import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.InputsNonVacuity
import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.Squarefree

/-!
# EvenUpper, part 9: the Rédei witnesses under the corrected shapes

The integration team's final review showed RC0's round-3 leaves uninhabitable. The corrected
shapes, as RC0 states them:
* `PreparedSpec`: `h` positive, squarefree, `≡ 1 (mod 8)` and prime to the support;
* clause 4 of the auxiliary factor: seeds only at the *prepared types*. These are the total types
  of the negative `d ≡ 1 (mod 8)`, squarefree, prime to `S`, with `L(E^{(d)}, 1) ≠ 0`;
* clause 5: only for `d < 0`, squarefree, prime to the support.

This file gives a non-vacuous instance of all of them. Partitionability holds at the negative
squarefree parameter `d = −7 ≡ 1 (mod 8)`, which is prime to `S = {2}`. All `PROVED`.

* `coefficientRules_filt`: the coefficient rules pass to a filtered symbol `A|_{total = τ}`
  (flips, contractions and isomorphisms keep the total type).
* `total_primeConfig`: for the sign type data, the total type of an odd squarefree `n` is
  `(n − 1)/2 mod 2`. Hence every prepared type is `1` (`preparedType_eq_one`): `d < 0` and
  `d ≡ 1 (mod 8)` give `|d| ≡ 7 (mod 8)`. The analytic-rank condition is not needed for this.
* `W₂ ℓ`: RC0's toy data with `S = {2}`, prepared filter `{1}`, and the Rédei partitionability
  predicate on the filter. Proved for it:
  * the corrected `PreparedSpec` (`preparedSpec_W₂`);
  * every corrected clause of the auxiliary factor (`auxClauses_W₂`), with the type data
    `signTypeData` and the sources `Afam` (the filtered Rédei symbol at type `1`, zero at type
    `0`);
  * `W₂.Partitionable (−7)` (`partitionable_W₂_neg7`);
  * `EvenUpperInputsAt (W₂ ℓ)` (`evenUpperInputsAt_W₂`);
  * squarefree realized cubes based at `−7` (`realized_cubes_redei_neg7`).
-/

namespace ZInQ.Contrib.CloudB3RC53.EvenUpper

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
  ZInQ.Manuscript.RC.Symbols ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
  Finset

/-! ### Filtered symbols -/

section Filt

variable {L : Type*} [AddCommGroup L]

theorem total_flip (Γ : Config L) (v w : ℕ) : (Γ.flip v w).total = Γ.total := rfl

theorem total_contract (Γ : Config L) {v w : ℕ} (hv : v ∈ Γ.V) (hw : w ∈ Γ.V) (hvw : v ≠ w) :
    (Γ.contract v w).total = Γ.total := by
  classical
  unfold Config.total
  simp only [Config.contract]
  have hvE : v ∈ Γ.V.erase w := Finset.mem_erase.2 ⟨hvw, hv⟩
  rw [← Finset.add_sum_erase Γ.V Γ.t hw]
  have : ∀ x ∈ Γ.V.erase w, Function.update Γ.t v (Γ.t v + Γ.t w) x =
      Γ.t x + (if x = v then Γ.t w else 0) := by
    intro x _
    by_cases hx : x = v
    · subst hx; simp
    · simp [Function.update_of_ne hx, hx]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq' _ v]
  simp only [hvE, ↓reduceIte]
  abel

theorem total_iso {Γ Δ : Config L} (h : Γ.IsIso Δ) : Γ.total = Δ.total := by
  obtain ⟨e, ht, -⟩ := h
  unfold Config.total
  rw [← Finset.sum_coe_sort Γ.V, ← Finset.sum_coe_sort Δ.V, ← e.sum_comp]
  exact Finset.sum_congr rfl fun x _ => (ht x).symm

open Classical in
/-- The symbol `A` restricted to the total type `τ`. -/
noncomputable def filt (A : Config L → ZMod 2) (τ : L) (Γ : Config L) : ZMod 2 := if Γ.total = τ then A Γ else 0

theorem filt_vanishes (A : Config L → ZMod 2) (τ : L) : VanishesOffFilter (filt A τ) τ := by
  intro Γ h
  unfold filt at h
  by_contra hne
  rw [if_neg hne] at h
  exact zero_ne_one h

/-- **The rules pass to a filtered symbol** (`PROVED`). -/
theorem coefficientRules_filt {ε : L →+ ZMod 2} {A : Config L → ZMod 2}
    (hA : CoefficientRules ε A) (τ : L) : CoefficientRules ε (filt A τ) where
  graph_dependence Γ Δ hΓ h := by
    unfold filt; rw [total_iso h, hA.graph_dependence Γ Δ hΓ h]
  contraction Γ hΓ v hv w hw hvw := by
    unfold filt
    rw [total_flip, total_contract Γ hv hw hvw]
    split_ifs
    · exact hA.contraction Γ hΓ v hv w hw hvw
    · simp
  primary_isolation Γ hΓ v hv ht hz := by
    unfold filt; split_ifs
    · exact hA.primary_isolation Γ hΓ v hv ht hz
    · rfl

end Filt

/-! ### Total types for the sign type data -/

theorem half_mul_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    (((a * b) / 2 : ℕ) : ZMod 2) = ((a / 2 : ℕ) : ZMod 2) + ((b / 2 : ℕ) : ZMod 2) := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have e1 : (2 * i + 1) * (2 * j + 1) / 2 = 2 * (i * j) + i + j := by
    rw [show (2 * i + 1) * (2 * j + 1) = 2 * (2 * (i * j) + i + j) + 1 by ring]; omega
  have e2 : (2 * i + 1) / 2 = i := by omega
  have e3 : (2 * j + 1) / 2 = j := by omega
  rw [e1, e2, e3]
  push_cast
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]

theorem sum_half_eq (s : Finset ℕ) (hs : ∀ p ∈ s, Odd p) :
    ∑ p ∈ s, ((p / 2 : ℕ) : ZMod 2) = (((∏ p ∈ s, p) / 2 : ℕ) : ZMod 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      ih fun p hp => hs p (Finset.mem_insert_of_mem hp),
      half_mul_odd (hs a (Finset.mem_insert_self _ _))
        (Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one
          fun p hp => hs p (Finset.mem_insert_of_mem hp))]

/-- **The total type of an odd squarefree parameter** (`PROVED`): `(n − 1)/2 mod 2`. -/
theorem total_primeConfig {n : ℕ} (hsq : Squarefree n) (hodd : Odd n) :
    (primeConfig n.primeFactors signTypeData.typ).total = ((n / 2 : ℕ) : ZMod 2) := by
  unfold Config.total
  show ∑ p ∈ n.primeFactors, ((p / 2 : ℕ) : ZMod 2) = _
  rw [sum_half_eq _ fun p hp => (Nat.prime_of_mem_primeFactors hp).odd_of_ne_two (fun h2 => by
    rw [h2] at hp
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))),
    Nat.prod_primeFactors_of_squarefree hsq]

/-- **Every prepared type is `1`** (`PROVED`): a negative squarefree `d ≡ 1 (mod 8)` has
`|d| ≡ 7 (mod 8)`, so an odd number of primes `≡ 3 (mod 4)`. -/
theorem total_eq_one_of_filter {d : ℤ} (hneg : d < 0) (h8 : d % 8 = 1) (hsq : Squarefree d) :
    (primeConfig d.natAbs.primeFactors signTypeData.typ).total = 1 := by
  have hn : (d.natAbs : ℤ) = -d := by omega
  have h7 : d.natAbs % 8 = 7 := by omega
  rw [total_primeConfig (Int.squarefree_natAbs.mpr hsq) (Nat.odd_iff.mpr (by omega))]
  have : d.natAbs / 2 % 2 = 1 := by omega
  rw [← Nat.mod_add_div (d.natAbs / 2) 2, this]
  push_cast
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]

/-! ### The instance -/

/-- The sources: the filtered Rédei symbol at type `1`, zero at type `0`. -/
noncomputable def Afam (τ : ZMod 2) : Config (ZMod 2) → ZMod 2 :=
  if τ = 1 then filt (symb signTypeData redeiReading) 1 else fun _ => 0

/-- The Rédei partitionability predicate on the corrected filter. -/
def RedeiPart (d : ℤ) : Prop :=
  d < 0 ∧ Squarefree d ∧ (∀ p ∈ ({2} : Finset ℕ), ¬ (p : ℤ) ∣ d) ∧
    IsPartitionable (AddMonoidHom.id (ZMod 2))
      (Afam (primeConfig d.natAbs.primeFactors signTypeData.typ).total)
      (primeConfig d.natAbs.primeFactors signTypeData.typ)

/-- RC0's toy data with support `{2}`, prepared filter `{1}` and the Rédei partitionability. -/
noncomputable def W₂ (ℓ : ℕ) : WData ℓ :=
  { toyW ℓ with S := {2}, prepared := fun h => h = 1, Partitionable := RedeiPart }

/-- **The corrected `PreparedSpec`** (`PROVED`). -/
theorem preparedSpec_W₂ (ℓ : ℕ) : ∀ h : ℤ, (W₂ ℓ).prepared h →
    0 < h ∧ Squarefree h ∧ h % 8 = 1 ∧ ∀ p ∈ (W₂ ℓ).S, ¬ (p : ℤ) ∣ h := by
  rintro h rfl
  refine ⟨one_pos, squarefree_one, rfl, fun p hp => ?_⟩
  rw [show (W₂ ℓ).S = {2} from rfl, Finset.mem_singleton] at hp
  subst hp
  decide

/-- RC0's `PreparedType`, with the data of `W₂`. -/
def PreparedTypeW (ℓ : ℕ) (τ : ZMod 2) : Prop :=
  ∃ d : ℤ, d < 0 ∧ d % 8 = 1 ∧ Squarefree d ∧ (∀ p ∈ (W₂ ℓ).S, ¬ (p : ℤ) ∣ d) ∧
    AnalyticRank (Etw ℓ d) 0 ∧ (primeConfig d.natAbs.primeFactors signTypeData.typ).total = τ

theorem preparedType_eq_one {ℓ : ℕ} {τ : ZMod 2} (h : PreparedTypeW ℓ τ) : τ = 1 := by
  obtain ⟨d, hneg, h8, hsq, -, -, rfl⟩ := h
  exact total_eq_one_of_filter hneg h8 hsq

/-- A prime `q ≡ 3 (mod 4)` (type one) is a partitionable list for the Rédei symbol, filtered or
not (`PROVED`). -/
theorem redei_partitionable_prime {q : ℕ} (hq : signTypeData.Good q) (ht : signTypeData.typ q = 1)
    (A : Config (ZMod 2) → ZMod 2)
    (hA : ∀ Γ : Config (ZMod 2), Γ.Compatible (AddMonoidHom.id (ZMod 2)) → Γ.total = 1 →
      A Γ = redei (AddMonoidHom.id (ZMod 2)) Γ) :
    IsPartitionable (AddMonoidHom.id (ZMod 2)) A (primeConfig {q} signTypeData.typ) := by
  classical
  set Γ := primeConfig ({q} : Finset ℕ) signTypeData.typ with hΓ
  have hf0 : IsReal signTypeData Γ id :=
    ⟨Set.injOn_id _, fun v hv => ⟨by rw [Finset.mem_singleton.1 hv]; exact hq, rfl⟩,
      fun v _ w _ _ => rfl⟩
  have hc : Γ.Compatible (AddMonoidHom.id (ZMod 2)) := compatible_of_real signTypeData hf0
  refine ⟨by simp [hΓ, primeConfig], ∅, ⟨Finset.empty_subset _, ?_⟩, ?_⟩
  · simp [ncomp, hΓ, primeConfig]
  · set r := rep Γ.V ∅ q
    have hV : (Γ.contractBy ∅).V = {r} := by
      simp [Config.contractBy, hΓ, primeConfig, r]
    have ht' : (Γ.contractBy ∅).t r = signTypeData.typ q := by
      simp [Config.contractBy, hΓ, primeConfig, r, Finset.filter_singleton]
    have htot : (Γ.contractBy ∅).total = 1 := by
      unfold Config.total; rw [hV, Finset.sum_singleton, ht', ht]
    rw [hA _ (hc.contractBy ∅) htot, redei_singleton _ hV, ht', ht]
    rfl

theorem Afam_one_eq (Γ : Config (ZMod 2)) (hΓ : Γ.Compatible (AddMonoidHom.id (ZMod 2)))
    (ht : Γ.total = 1) : Afam 1 Γ = redei (AddMonoidHom.id (ZMod 2)) Γ := by
  unfold Afam filt
  rw [if_pos rfl, if_pos ht]
  exact symb_primeReading signTypeData _ (fun _ _ h => redei_iso _ h) hΓ

theorem good_seven : signTypeData.Good 7 := ⟨by norm_num, by decide⟩

/-- **`−7` is partitionable in `W₂`** (`PROVED`): negative, `≡ 1 (mod 8)`, squarefree, odd, and
its prime `7 ≡ 3 (mod 4)` is a partitionable list. -/
theorem partitionable_W₂_neg7 (ℓ : ℕ) : (W₂ ℓ).Partitionable (-7) := by
  have hpf : (-7 : ℤ).natAbs.primeFactors = {7} := (by norm_num : Nat.Prime 7).primeFactors
  have ht7 : signTypeData.typ 7 = 1 := rfl
  refine ⟨by norm_num, Int.squarefree_natAbs.mp (by norm_num : Nat.Prime 7).squarefree,
    fun p hp => ?_, ?_⟩
  · rw [Finset.mem_singleton.1 hp]; decide
  · rw [hpf]
    have htot : (primeConfig ({7} : Finset ℕ) signTypeData.typ).total = 1 := by
      simp [Config.total, primeConfig, ht7]
    rw [htot]
    exact redei_partitionable_prime good_seven ht7 _ (fun Γ hΓ ht => Afam_one_eq Γ hΓ ht)

theorem neg7_mod8 : (-7 : ℤ) % 8 = 1 := by decide

/-- **Every corrected clause of the auxiliary factor holds for `W₂`** (`PROVED`), with the type
data `signTypeData` and the sources `Afam`: the conductor is supported on `S`; the rules; zero off
the filter; unit seeds at every prepared type; clause 5 on the filter. -/
theorem auxClauses_W₂ (ℓ : ℕ) :
    (∀ p : ℕ, p.Prime → p ∣ signTypeData.m → p ∈ (W₂ ℓ).S) ∧
    (∀ τ, CoefficientRules (AddMonoidHom.id (ZMod 2)) (Afam τ)) ∧
    (∀ τ, VanishesOffFilter (Afam τ) τ) ∧
    (∀ τ, PreparedTypeW ℓ τ → ∃ Γ, IsUnitSeed (AddMonoidHom.id (ZMod 2)) (Afam τ) Γ) ∧
    ∀ d : ℤ, d < 0 → Squarefree d → (∀ p ∈ (W₂ ℓ).S, ¬ (p : ℤ) ∣ d) →
      IsPartitionable (AddMonoidHom.id (ZMod 2))
        (Afam (primeConfig d.natAbs.primeFactors signTypeData.typ).total)
        (primeConfig d.natAbs.primeFactors signTypeData.typ) → (W₂ ℓ).Partitionable d := by
  refine ⟨fun p hp hpm => ?_, fun τ => ?_, fun τ => ?_, fun τ hτ => ?_,
    fun d hneg hsq hS hpart => ⟨hneg, hsq, hS, hpart⟩⟩
  · have hm : signTypeData.m = 2 ^ 2 := rfl
    rw [hm] at hpm
    rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpm)]
    exact Finset.mem_singleton_self 2
  · unfold Afam; split_ifs
    · exact coefficientRules_filt redeiReading_rules 1
    · exact Wiring.coefficientRules_zero _
  · unfold Afam; split_ifs with h
    · subst h; exact filt_vanishes _ 1
    · intro Γ h1; exact absurd h1 zero_ne_one
  · rw [preparedType_eq_one hτ]
    set Γ := primeConfig ({3} : Finset ℕ) signTypeData.typ
    have hf0 : IsReal signTypeData Γ id :=
      ⟨Set.injOn_id _, fun v hv => ⟨by rw [Finset.mem_singleton.1 hv]; exact good_three, rfl⟩,
        fun v _ w _ _ => rfl⟩
    have hc : Γ.Compatible (AddMonoidHom.id (ZMod 2)) := compatible_of_real signTypeData hf0
    have ht : Γ.total = 1 := by simp [Γ, Config.total, primeConfig]; rfl
    refine ⟨Γ, hc, ?_⟩
    rw [Afam_one_eq Γ hc ht, redei_singleton _ (r := 3) rfl]
    rfl

/-- **`EvenUpperInputsAt` for `W₂`** (`PROVED`; as for `redeiW`, `L_* = 1`). -/
theorem evenUpperInputsAt_W₂ (ℓ : ℕ) : EvenUpperInputsAt (W₂ ℓ) := by
  have hL : ∀ p, (W₂ ℓ).Lstar p = 1 := fun _ => rfl
  refine ⟨0, 0, fun d hd0 _ _ => ?_⟩
  refine ⟨fun p => p ≠ 0 ∧ (W₂ ℓ).Lstar p ≠ 0 ∧
      padicValRat 2 ((W₂ ℓ).Lstar p) ≤ 2 * omega p + 0,
    fun p => (2 : ℚ_[2]) ^ (-(2 * (omega p : ℤ) + (shaLength (Etw ℓ p) : ℤ))),
    fun p hp => hp, fun p _ _ => ?_, d, ⟨hd0, ?_, ?_⟩, Or.inl rfl⟩
  · rw [hL]
    refine ⟨⟨fun h => absurd h (zpow_ne_zero _ two_ne_zero), fun h => absurd h one_ne_zero⟩,
      fun _ => ?_⟩
    rw [Padic.valuation_zpow]
    have h2 : (2 : ℚ_[2]).valuation = 1 := by simp
    rw [h2, padicValRat.one, mul_one]
    have h0 : ∀ a b : ℤ, -(2 * a + b) - (0 - 2 * a - b) = 0 := fun a b => by ring
    rw [h0, abs_zero]
  · rw [hL]; exact one_ne_zero
  · rw [hL, padicValRat.one]
    have : (0 : ℤ) ≤ omega d := Int.natCast_nonneg _
    omega

/-- **Squarefree realized cubes based at `−7`** (`PROVED`, from `realized_cubes_sq`): for every
`b ≥ 1` a binary family based at `−7`, every parameter `−7·Q_x` squarefree with `Q_x` prime to
`7`, and Rédei reading one at every nonzero address. -/
theorem realized_cubes_redei_neg7 (b : ℕ) (hb : 1 ≤ b) :
    ∃ fam : ZInQ.Manuscript.RC.Even.BinaryFamily 1, fam.b = b ∧ fam.h 0 = -7 ∧
      (∀ x, ∃ Q : ℤ, 0 < Q ∧ fam.h x = -7 * Q ∧ IsCoprime (-7) Q ∧ Squarefree (fam.h x)) ∧
      ∀ x, x ≠ 0 → ∃ V : Finset ℕ, (∀ p ∈ V, signTypeData.Good p) ∧ redeiReading V = 1 ∧
        fam.h x = -∏ p ∈ V, (p : ℤ) := by
  have hpf : (-7 : ℤ).natAbs.primeFactors = {7} := (by norm_num : Nat.Prime 7).primeFactors
  have hsq : Squarefree (-7 : ℤ) := Int.squarefree_natAbs.mp (by norm_num : Nat.Prime 7).squarefree
  have hgood : ∀ p ∈ (-7 : ℤ).natAbs.primeFactors, signTypeData.Good p ∧ Nat.Coprime p 1 := by
    rw [hpf]
    intro p hp
    rw [Finset.mem_singleton.1 hp]
    exact ⟨good_seven, Nat.coprime_one_right 7⟩
  have hpart : IsPartitionable (AddMonoidHom.id (ZMod 2)) (symb signTypeData redeiReading)
      (primeConfig (-7 : ℤ).natAbs.primeFactors signTypeData.typ) := by
    rw [hpf]
    exact redei_partitionable_prime good_seven rfl _ (fun Γ hΓ _ =>
      symb_primeReading signTypeData _ (fun _ _ h => redei_iso _ h) hΓ)
  obtain ⟨fam, hb', h0, hfac, hu⟩ := realized_cubes_sq signTypeData redeiReading redeiReading_fixedU
    redeiReading_rules (fun q _ hq => signTypeData_typ_one q hq) one_pos
    (fun h => ∃ V : Finset ℕ, (∀ p ∈ V, signTypeData.Good p) ∧ redeiReading V = 1 ∧
      h = -∏ p ∈ V, (p : ℤ)) (-7) hsq hgood hpart
    (fun V hV h1 => ⟨V, hV, h1, by rw [show (-7 : ℤ).sign = -1 from rfl, neg_one_mul]⟩) b hb
  exact ⟨fam, hb', h0, hfac, hu⟩

end ZInQ.Contrib.CloudB3RC53.EvenUpper

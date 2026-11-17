import ZInQKernel.Contrib.OneProof.RC.Symbols.Core

/-!
# Lane RC2: finite realization by primes (tex 2031–2048, 2151–2174)

Manuscript: the residue bits and the reciprocity compatibility of Definition
`ex:sec7-typed-graph` (tex 2031–2041) and Lemma `ex:sec7-realization` with its proof
(tex 2151–2174).

* `legBit`: the additive Legendre bit `z = 0` or `1` as `(a/q) = 1` or `-1`.
* `legBit_reciprocity`: `z_{pq} + z_{qp} = ε_p ε_q` with `ε_p = (p - 1)/2 mod 2`, from quadratic
  reciprocity.
* `primeConfig_compatible`: the typed graph read off distinct odd primes is compatible.
* `exists_prime_step`: one realization step. A prescribed bit at an odd prime `p` is a nonzero
  residue class modulo `p`; the Chinese remainder theorem combines these classes with a reduced
  class modulo `m`; Dirichlet's theorem gives a prime in the combined reduced class, above any
  bound.
* `finite_realization`: the new primes are chosen successively; the forward bit of a new prime at
  an earlier new prime is a residue condition modulo that earlier prime.
* `product_template`: a fresh prime with the class of the product and prescribed external bits.

The type of a new vertex is modelled by a reduced residue class at a modulus `m` with `2 ∣ m`;
old primes are coprime to `m`, hence odd.
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset

open Classical in
/-- Residue bit `z = 0` or `1` as `(a/q) = 1` or `-1` (tex 2033–2034). -/
noncomputable def legBit (a : ℤ) (q : ℕ) : ZMod 2 := if IsSquare (a : ZMod q) then 0 else 1

/-- A square residue has bit zero (tex 2033–2034). Kind: PROVED. -/
theorem legBit_of_isSquare {a : ℤ} {q : ℕ} (h : IsSquare (a : ZMod q)) : legBit a q = 0 := by
  unfold legBit; rw [ite_eq_left h]

/-- A nonsquare residue has bit one (tex 2033–2034). Kind: PROVED. -/
theorem legBit_of_not_isSquare {a : ℤ} {q : ℕ} (h : ¬ IsSquare (a : ZMod q)) :
    legBit a q = 1 := by
  unfold legBit; rw [ite_eq_right h]

/-- Equal square-ness gives equal bits (tex 2033–2034). Kind: PROVED. -/
theorem legBit_congr {a b : ℤ} {q r : ℕ} (h : IsSquare (a : ZMod q) ↔ IsSquare (b : ZMod r)) :
    legBit a q = legBit b r := by
  unfold legBit
  by_cases hb : IsSquare (b : ZMod r)
  · rw [ite_eq_left (h.mpr hb), ite_eq_left hb]
  · rw [ite_eq_right (fun h' => hb (h.mp h')), ite_eq_right hb]

/-- Opposite square-ness gives opposite bits (tex 2033–2034). Kind: PROVED. -/
theorem legBit_congr_not {a b : ℤ} {q r : ℕ}
    (h : IsSquare (a : ZMod q) ↔ ¬ IsSquare (b : ZMod r)) : legBit a q = legBit b r + 1 := by
  unfold legBit
  by_cases hb : IsSquare (b : ZMod r)
  · rw [ite_eq_right (fun h' => h.mp h' hb), ite_eq_left hb]; decide
  · rw [ite_eq_left (h.mpr hb), ite_eq_right hb]; decide

/-- Characteristic two: `x + x = 0` in `ZMod 2` (auxiliary to tex 2037–2041). Kind: PROVED. -/
theorem zmod2_add_self' (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

/-- The sign coordinate `ε_p = (p - 1)/2 mod 2` of an odd `p`, read as `p / 2` (tex 2038–2039):
it is one exactly when `p ≡ 3 (mod 4)`. Kind: PROVED. -/
theorem half_cast_eq (p : ℕ) (hp : p % 2 = 1) :
    ((p / 2 : ℕ) : ZMod 2) = if p % 4 = 3 then 1 else 0 := by
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · rw [ite_eq_right (by omega), ZMod.natCast_eq_zero_iff_even]
    exact ⟨p / 4, by omega⟩
  · rw [ite_eq_left h, ZMod.natCast_eq_one_iff_odd]
    exact ⟨p / 4, by omega⟩

/-- Reverse bits by reciprocity (tex 2037–2041). Kind: PROVED (quadratic reciprocity). -/
theorem legBit_reciprocity {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) : legBit p q + legBit q p = ((p / 2 : ℕ) : ZMod 2) * ((q / 2 : ℕ) : ZMod 2) := by
  have := Fact.mk hp
  have := Fact.mk hq
  have hpo : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hqo : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  rw [half_cast_eq p hpo, half_cast_eq q hqo]
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with hp4 | hp4
  · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := q) hp4 hq2
    have h' : legBit p q = legBit q p :=
      legBit_congr (by rw [Int.cast_natCast, Int.cast_natCast]; exact h.symm)
    rw [h', zmod2_add_self', ite_eq_right (by omega), zero_mul]
  · rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with hq4 | hq4
    · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := q) (q := p) hq4 hp2
      have h' : legBit p q = legBit q p :=
        legBit_congr (by rw [Int.cast_natCast, Int.cast_natCast]; exact h)
      rw [h', zmod2_add_self', ite_eq_right (show ¬ q % 4 = 3 by omega), mul_zero]
    · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := q) (q := p) hq4 hp4
        (Ne.symm hpq)
      have h' : legBit p q = legBit q p + 1 :=
        legBit_congr_not (by rw [Int.cast_natCast, Int.cast_natCast]; exact h)
      rw [h', ite_eq_left hp4, ite_eq_left hq4, add_right_comm, zmod2_add_self', zero_add, mul_one]

/-- The typed graph of distinct odd primes is compatible. -/
noncomputable def primeConfig {L : Type*} (V : Finset ℕ) (t : ℕ → L) : Config L :=
  ⟨V, t, fun v w => legBit v w⟩

/-- The typed graph of distinct odd primes, with sign coordinates `ε (t p) = (p - 1)/2 mod 2`, is
compatible (tex 2031–2041). Kind: PROVED. -/
theorem primeConfig_compatible {L : Type*} [AddCommGroup L] (ε : L →+ ZMod 2) (V : Finset ℕ)
    (hV : ∀ p ∈ V, p.Prime ∧ p ≠ 2) (t : ℕ → L) (ht : ∀ p ∈ V, ε (t p) = ((p / 2 : ℕ) : ZMod 2)) :
    (primeConfig V t).Compatible ε := by
  intro v hv w hw hvw
  change legBit v w + legBit w v = ε (t v) * ε (t w)
  rw [ht v hv, ht w hw]
  exact legBit_reciprocity (hV v hv).1 (hV w hw).1 (hV v hv).2 (hV w hw).2 hvw

/-- A prescribed residue bit at an odd prime is a nonzero residue class there (tex 2164–2165).
Kind: PROVED. -/
theorem exists_residue_bit {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (b : ZMod 2) :
    ∃ a : ℕ, ¬ p ∣ a ∧ legBit a p = b := by
  have := Fact.mk hp
  have hb : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hb with rfl | rfl
  · exact ⟨1, fun h => hp.one_lt.ne' (Nat.dvd_one.mp h),
      legBit_of_isSquare ⟨1, by rw [Nat.cast_one, Int.cast_one, mul_one]⟩⟩
  · obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
    refine ⟨x.val, fun h => hx ?_, legBit_of_not_isSquare ?_⟩
    · have : (x.val : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [ZMod.natCast_zmod_val] at this
      rw [this]; exact ⟨0, by rw [mul_zero]⟩
    · rwa [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- A prime coprime to an even modulus is odd (the modulus of the type contains two, tex
2162–2163). Kind: PROVED. -/
theorem ne_two_of_coprime_even {m p : ℕ} (h2 : 2 ∣ m) (hp : Nat.Coprime p m) : p ≠ 2 := by
  rintro rfl
  exact absurd (Nat.Coprime.eq_one_of_dvd hp h2) (by decide)

/-- **One realization step** (tex 2162–2169): a prime above any bound `B`, in a prescribed
reduced class modulo `m` (with `2 ∣ m`), with prescribed residue bits at finitely many primes
coprime to `m`. Each bit is a nonzero residue class at its prime, the Chinese remainder theorem
combines these classes with the class modulo `m`, and Dirichlet's theorem supplies a prime in the
resulting reduced class beyond `B`. Kind: PROVED (Dirichlet's theorem from Mathlib). -/
theorem exists_prime_step (m : ℕ) (hm : 0 < m) (h2 : 2 ∣ m) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ Nat.Coprime p m) (c : ZMod m) (hc : IsUnit c)
    (b : ℕ → ZMod 2) (B : ℕ) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧ ((q : ℕ) : ZMod m) = c ∧ ∀ p ∈ S, legBit q p = b p := by
  classical
  have : NeZero m := ⟨hm.ne'⟩
  have hres : ∀ p ∈ S, ∃ a : ℕ, ¬ p ∣ a ∧ legBit a p = b p := fun p hp =>
    exists_residue_bit (hS p hp).1 (ne_two_of_coprime_even h2 (hS p hp).2) (b p)
  choose! a ha using hres
  -- the Chinese remainder theorem at the primes of `S`
  have hs : ∀ p ∈ S, id p ≠ 0 := fun p hp => (hS p hp).1.ne_zero
  have pp : Set.Pairwise (S : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro p hp p' hp' hne
    exact (Nat.coprime_primes (hS p hp).1 (hS p' hp').1).mpr hne
  obtain ⟨k₁, hk₁⟩ := Nat.chineseRemainderOfFinset a id S hs pp
  have hcopN : Nat.Coprime m (∏ p ∈ S, p) :=
    Nat.Coprime.prod_right fun p hp => Nat.Coprime.symm (hS p hp).2
  -- combine with the reduced class modulo `m`
  obtain ⟨k, hkm, hkN⟩ := Nat.chineseRemainder hcopN c.val k₁
  have hkq : ∀ p ∈ S, k ≡ a p [MOD p] := fun p hp =>
    (Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem (fun p => p) hp) hkN).trans (hk₁ p hp)
  have hcval : Nat.Coprime c.val m := by
    obtain ⟨u, rfl⟩ := hc
    exact ZMod.val_coe_unit_coprime u
  have hkcop : Nat.Coprime k (m * ∏ p ∈ S, p) := by
    refine Nat.Coprime.mul_right ?_ (Nat.Coprime.prod_right fun p hp => ?_)
    · change Nat.gcd k m = 1
      rw [Nat.ModEq.gcd_eq hkm]; exact hcval
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hS p hp).1]
      intro h
      exact (ha p hp).1 (Nat.modEq_zero_iff_dvd.mp
        ((hkq p hp).symm.trans (Nat.modEq_zero_iff_dvd.mpr h)))
  have hpos : 0 < m * ∏ p ∈ S, p :=
    Nat.mul_pos hm (Finset.prod_pos fun p hp => (hS p hp).1.pos)
  have : NeZero (m * ∏ p ∈ S, p) := ⟨hpos.ne'⟩
  -- Dirichlet's theorem
  obtain ⟨q, hqB, hq, hqk⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((ZMod.isUnit_iff_coprime k (m * ∏ p ∈ S, p)).mpr hkcop) B
  have hqk' : q ≡ k [MOD m * ∏ p ∈ S, p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hqk
  refine ⟨q, hqB, hq, ?_, fun p hp => ?_⟩
  · have : q ≡ c.val [MOD m] := (Nat.ModEq.of_dvd (Dvd.intro _ rfl) hqk').trans hkm
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr this, ZMod.natCast_zmod_val]
  · have hqp : q ≡ a p [MOD p] :=
      (Nat.ModEq.of_dvd ((Finset.dvd_prod_of_mem (fun p => p) hp).trans (Dvd.intro_left m rfl))
        hqk').trans (hkq p hp)
    rw [← (ha p hp).2]
    apply legBit_congr
    rw [Int.cast_natCast, Int.cast_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hqp]

/-- A natural number above the maximum of a finite set is not in it (avoidance, tex 2168–2169).
Kind: PROVED. -/
theorem not_mem_of_sup_lt {s : Finset ℕ} {x : ℕ} (h : s.sup id < x) : x ∉ s := fun hx =>
  absurd (Finset.le_sup (f := id) hx) (not_le.mpr h)

/-- Successive choice of the new primes (tex 2163–2169), indexed by `ℕ`: the first `k` new primes
are distinct, fresh (outside the old primes and the avoidance set), in their reduced classes,
with the prescribed bits at the old primes and at the earlier new primes. Kind: PROVED. -/
theorem finite_realization_nat (m : ℕ) (hm : 0 < m) (h2 : 2 ∣ m) (old : Finset ℕ)
    (hold : ∀ p ∈ old, p.Prime ∧ Nat.Coprime p m) (avoid : Finset ℕ)
    (cls : ℕ → ZMod m) (hcls : ∀ i, IsUnit (cls i))
    (bitOld : ℕ → ℕ → ZMod 2) (bitNew : ℕ → ℕ → ZMod 2) (k : ℕ) :
    ∃ q : ℕ → ℕ, (∀ i < k, ∀ j < k, q i = q j → i = j) ∧
      (∀ i < k, (q i).Prime ∧ q i ∉ old ∧ q i ∉ avoid ∧ ((q i : ℕ) : ZMod m) = cls i) ∧
      (∀ i < k, ∀ p ∈ old, legBit (q i) p = bitOld i p) ∧
      (∀ i < k, ∀ j < i, legBit (q i) (q j) = bitNew i j) := by
  classical
  induction k with
  | zero =>
    exact ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨q, hinj, hq, hqold, hqnew⟩ := ih
    -- the primes at which bits are prescribed: the old primes and the earlier new primes
    have hS : ∀ p ∈ old ∪ (Finset.range k).image q, p.Prime ∧ Nat.Coprime p m := by
      intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact hold p h
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
        have hj' := Finset.mem_range.mp hj
        refine ⟨(hq j hj').1, ?_⟩
        exact (ZMod.isUnit_iff_coprime (q j) m).mp (by rw [(hq j hj').2.2.2]; exact hcls j)
    let b : ℕ → ZMod 2 := fun p => if p ∈ old then bitOld k p else
      if h : ∃ j, j < k ∧ q j = p then bitNew k (Classical.choose h) else 0
    obtain ⟨x, hxB, hx, hxc, hxb⟩ := exists_prime_step m hm h2 _ hS (cls k) (hcls k) b
      ((old ∪ (Finset.range k).image q ∪ avoid).sup id)
    have hxfresh := not_mem_of_sup_lt hxB
    have hxold : x ∉ old := fun h => hxfresh (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hxavoid : x ∉ avoid := fun h => hxfresh (Finset.mem_union_right _ h)
    have hxq : ∀ j < k, q j ≠ x := fun j hj h => hxfresh (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, h⟩)))
    have hqold' : ∀ j < k, q j ∉ old := fun j hj => (hq j hj).2.1
    refine ⟨Function.update q k x, ?_, ?_, ?_, ?_⟩
    · intro i hi j hj hij
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · rw [Function.update_of_ne (Nat.ne_of_lt hi'), Function.update_of_ne (Nat.ne_of_lt hj')]
          at hij
        exact hinj i hi' j hj' hij
      · rw [Function.update_of_ne (Nat.ne_of_lt hi'), Function.update_self] at hij
        exact absurd hij (hxq i hi')
      · rw [Function.update_self, Function.update_of_ne (Nat.ne_of_lt hj')] at hij
        exact absurd hij.symm (hxq j hj')
      · rfl
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · rw [Function.update_of_ne (Nat.ne_of_lt hi')]; exact hq i hi'
      · rw [Function.update_self]; exact ⟨hx, hxold, hxavoid, hxc⟩
    · intro i hi p hp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · rw [Function.update_of_ne (Nat.ne_of_lt hi')]; exact hqold i hi' p hp
      · rw [Function.update_self, hxb p (Finset.mem_union_left _ hp)]
        change (if p ∈ old then bitOld i p else _) = _
        rw [ite_eq_left hp]
    · intro i hi j hji
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · rw [Function.update_of_ne (Nat.ne_of_lt hi'),
          Function.update_of_ne (Nat.ne_of_lt (hji.trans hi'))]
        exact hqnew i hi' j hji
      · rw [Function.update_self, Function.update_of_ne (Nat.ne_of_lt hji),
          hxb (q j) (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hji, rfl⟩))]
        have hex : ∃ j', j' < i ∧ q j' = q j := ⟨j, hji, rfl⟩
        change (if q j ∈ old then bitOld i (q j) else
          if h : ∃ j', j' < i ∧ q j' = q j then bitNew i (Classical.choose h) else 0) = _
        rw [ite_eq_right (hqold' j hji), dite_eq_left hex]
        have hc := Classical.choose_spec hex
        rw [hinj _ hc.1 j hji hc.2]

/-- Finite realization (`ex:sec7-realization`, tex 2151–2174). Kind: PROVED (Chinese remainder
theorem and Dirichlet's theorem, choosing the new primes successively). -/
theorem finite_realization (m : ℕ) (hm : 0 < m) (h2 : 2 ∣ m) (old : Finset ℕ)
    (hold : ∀ p ∈ old, p.Prime ∧ Nat.Coprime p m) (avoid : Finset ℕ) (n : ℕ)
    (cls : Fin n → ZMod m) (hcls : ∀ i, IsUnit (cls i))
    (bitOld : Fin n → ℕ → ZMod 2) (bitNew : Fin n → Fin n → ZMod 2) :
    ∃ q : Fin n → ℕ, Function.Injective q ∧
      (∀ i, (q i).Prime ∧ q i ∉ old ∧ q i ∉ avoid ∧ ((q i : ℕ) : ZMod m) = cls i) ∧
      (∀ i, ∀ p ∈ old, legBit (q i) p = bitOld i p) ∧
      (∀ i j, j < i → legBit (q i) (q j) = bitNew i j) := by
  classical
  obtain ⟨q, hinj, hq, hqold, hqnew⟩ := finite_realization_nat m hm h2 old hold avoid
    (fun i => if h : i < n then cls ⟨i, h⟩ else 1)
    (fun i => by
      split_ifs with h
      · exact hcls _
      · exact isUnit_one)
    (fun i p => if h : i < n then bitOld ⟨i, h⟩ p else 0)
    (fun i j => if h : i < n ∧ j < n then bitNew ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) n
  refine ⟨fun i => q i, fun i j h => Fin.ext (hinj i i.isLt j j.isLt h), fun i => ?_,
    fun i p hp => ?_, fun i j hji => ?_⟩
  · have h := hq i i.isLt
    rwa [dite_eq_left i.isLt] at h
  · have h := hqold i i.isLt p hp
    rwa [dite_eq_left i.isLt] at h
  · have h := hqnew i i.isLt j hji
    rwa [dite_eq_left ⟨i.isLt, j.isLt⟩] at h

/-- A product template is replaced by a fresh prime with the same type and all external
incidences (tex 2157–2159, 2170–2173). Kind: PROVED (the realization step with the class of the
product and the summed external bits). -/
theorem product_template (m : ℕ) (hm : 0 < m) (h2 : 2 ∣ m) (old : Finset ℕ)
    (hold : ∀ p ∈ old, p.Prime ∧ Nat.Coprime p m) (P : Finset ℕ)
    (hP : ∀ r ∈ P, r.Prime ∧ Nat.Coprime r m) (avoid : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ old ∧ q ∉ P ∧ q ∉ avoid ∧
      ((q : ℕ) : ZMod m) = ∏ r ∈ P, (r : ZMod m) ∧
      ∀ p ∈ old, p ∉ P → legBit q p = ∑ r ∈ P, legBit r p := by
  classical
  have hc : IsUnit (∏ r ∈ P, (r : ZMod m)) := by
    rw [← Nat.cast_prod]
    exact (ZMod.isUnit_iff_coprime _ m).mpr (Nat.Coprime.prod_left fun r hr => (hP r hr).2)
  obtain ⟨q, hqB, hq, hqc, hqb⟩ := exists_prime_step m hm h2 old hold _ hc
    (fun p => ∑ r ∈ P, legBit r p) ((old ∪ P ∪ avoid).sup id)
  have hfresh := not_mem_of_sup_lt hqB
  exact ⟨q, hq, fun h => hfresh (Finset.mem_union_left _ (Finset.mem_union_left _ h)),
    fun h => hfresh (Finset.mem_union_left _ (Finset.mem_union_right _ h)),
    fun h => hfresh (Finset.mem_union_right _ h), hqc, fun p hp _ => hqb p hp⟩

end ZInQ.Manuscript.RC.Symbols

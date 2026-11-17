import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Basic
import ZInQKernel.RouteK.Selmer.Bits
import ZInQKernel.RouteK.Selmer.PadicSquare

/-!
# Lane RC13 (nonvanishing), part 2: the CRT and Dirichlet realization (PROVED)

* Squareclass calculus in `ℚ_p` (`IsSquareAt`), with Hensel's lemma at odd `p` and the mod-`8`
  criterion at `2` (the tree's Route K lemmas `isSquare_intCast_div_of_residue`,
  `isSquare_intCast_div_two_adic`, `isSquare_two_adic_intCast_iff`, `isSquare_coe_iff_toZMod`).
* `SignedUnitFilter.exists_signed_prime`: **"By CRT and Dirichlet choose one signed prime `q₀`
  in its classes, outside `S ∪ B`"** (tex 1984–1985, 10016–10017): Mathlib's Chinese remainder
  isomorphism `ZMod.prodEquivPi` and Dirichlet's theorem `Nat.forall_exists_prime_gt_and_eq_mod`.
  In particular every signed unit filter is nonempty.
* `SignedUnitFilter.mem_mul`: **"Then `q₀d` has the prescribed original classes"** (tex 1989–1990,
  10027–10028): a positive `d` split at every `p ∈ S` does not change the classes.

Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Nonvanishing

open ZInQ.RouteK.Selmer

/-! ### Squareclasses in `ℚ_p` -/

theorem isSquareAt_mul {p : ℕ} {x y : ℚ} (hx : IsSquareAt p x) (hy : IsSquareAt p y) :
    IsSquareAt p (x * y) := by
  intro hp; rw [Rat.cast_mul]; exact (hx hp).mul (hy hp)

theorem isSquareAt_div {p : ℕ} {x y : ℚ} (hx : IsSquareAt p x) (hy : IsSquareAt p y) :
    IsSquareAt p (x / y) := by
  intro hp; rw [Rat.cast_div]; exact (hx hp).div (hy hp)

theorem isSquareAt_sq {p : ℕ} (x : ℚ) : IsSquareAt p (x ^ 2) := by
  intro _; rw [Rat.cast_pow]; exact ⟨(x : ℚ_[p]), sq _⟩

theorem intCast_dvd_iff_of_modEq {p : ℕ} {a b : ℤ} (h : a ≡ b [ZMOD p]) :
    (p : ℤ) ∣ a ↔ (p : ℤ) ∣ b := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr h]

/-- **Hensel at odd `p`**: `a ≡ b (mod p)` with `p ∤ b` makes `a/b` a square in `ℚ_p`. PROVED. -/
theorem isSquareAt_div_of_modEq {p : ℕ} (hp2 : p ≠ 2) {a b : ℤ}
    (hb : ¬ (p : ℤ) ∣ b) (h : a ≡ b [ZMOD p]) : IsSquareAt p ((a : ℚ) / b) := by
  intro _
  have ha : ¬ (p : ℤ) ∣ a := fun hd => hb ((intCast_dvd_iff_of_modEq h).mp hd)
  have hab : ((a : ℤ) : ZMod p) = (b : ZMod p) := (ZMod.intCast_eq_intCast_iff _ _ _).mpr h
  have hsq : IsSquare ((a * b : ℤ) : ZMod p) := ⟨(b : ZMod p), by push_cast; rw [hab]⟩
  have := isSquare_intCast_div_of_residue hp2 ha hb hsq
  simpa [Rat.cast_div, Rat.cast_intCast] using this

/-- **The mod-`8` criterion at `2`**: `a ≡ b (mod 8)` with `b` odd makes `a/b` a square in `ℚ₂`.
PROVED. -/
theorem isSquareAt_two_div_of_modEq {a b : ℤ} (hb : Odd b) (h : a ≡ b [ZMOD 8]) :
    IsSquareAt 2 ((a : ℚ) / b) := by
  intro _
  have := isSquare_intCast_div_two_adic hb h
  simpa [Rat.cast_div, Rat.cast_intCast] using this

/-- A prime split in `ℚ(√d)` sees `d` as a square of `ℚ_p`. PROVED. -/
theorem isSquareAt_of_splitsIn {d : ℤ} {p : ℕ} (hp : p.Prime) (h : SplitsIn d p) :
    IsSquareAt p (d : ℚ) := by
  by_cases hp2 : p = 2
  · subst hp2
    have h8 : d ≡ 1 [ZMOD 8] := by
      have := h.two
      unfold Int.ModEq; omega
    have := isSquareAt_two_div_of_modEq (a := d) (b := 1) odd_one h8
    simpa using this
  · intro _
    obtain ⟨hnd, hsq⟩ := h.2 hp2
    have := isSquare_intCast_of_residue hp2 hnd hsq
    simpa using this


theorem odd_iff_not_two_dvd {u : ℤ} : Odd u ↔ ¬ ((2 : ℕ) : ℤ) ∣ u := by
  rw [Nat.cast_ofNat, ← even_iff_two_dvd, Int.not_even_iff_odd]

/-- **Converse at `2`**: two odd integers in the same squareclass of `ℚ₂` agree mod `8`. PROVED. -/
theorem modEq_eight_of_isSquareAt_two {u v : ℤ} (hu : Odd u) (hv : Odd v)
    (h : IsSquareAt 2 ((u : ℚ) / v)) : u ≡ v [ZMOD 8] := by
  have hv0' : v ≠ 0 := by rintro rfl; norm_num at hv
  have hv0 : (v : ℚ) ≠ 0 := by exact_mod_cast hv0'
  have hsq : IsSquareAt 2 ((u * v : ℤ) : ℚ) := by
    have : ((u * v : ℤ) : ℚ) = ((u : ℚ) / v) * (v : ℚ) ^ 2 := by push_cast; field_simp
    rw [this]; exact isSquareAt_mul h (isSquareAt_sq _)
  have h2 : IsSquare (((u * v : ℤ) : ℚ) : ℚ_[2]) := hsq inferInstance
  rw [Rat.cast_intCast, isSquare_two_adic_intCast_iff (hu.mul hv)] at h2
  have hv8 : (v : ZMod 8) * (v : ZMod 8) = 1 := by
    obtain ⟨k, rfl⟩ := hv
    push_cast
    generalize (k : ZMod 8) = x
    revert x; decide
  have hcalc : (u : ZMod 8) = (v : ZMod 8) := by
    calc (u : ZMod 8) = (u : ZMod 8) * ((v : ZMod 8) * (v : ZMod 8)) := by rw [hv8, mul_one]
      _ = ((u * v : ℤ) : ZMod 8) * (v : ZMod 8) := by push_cast; ring
      _ = (v : ZMod 8) := by rw [h2, one_mul]
  have := (ZMod.intCast_eq_intCast_iff u v 8).mp hcalc
  simpa using this

/-- **Converse at every prime**: an integer prime to `p` and a square of `ℚ_p` makes `p` split in
`ℚ(√d)`. PROVED. -/
theorem splitsIn_of_isSquareAt {d : ℤ} {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ d)
    (h : IsSquareAt p (d : ℚ)) : SplitsIn d p := by
  have : Fact p.Prime := ⟨hp⟩
  have hu : ‖(d : ℤ_[p])‖ = 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_intCast]; exact padic_norm_intCast_eq_one hd
  refine ⟨fun hp2 => ?_, fun hp2 => ⟨hd, ?_⟩⟩
  · subst hp2
    have hodd : Odd d := odd_iff_not_two_dvd.mpr hd
    have h2 : IsSquare ((d : ℚ) : ℚ_[2]) := h inferInstance
    rw [Rat.cast_intCast, isSquare_two_adic_intCast_iff hodd] at h2
    have h3 : ((d : ℤ) : ZMod 8) = ((1 : ℤ) : ZMod 8) := by simpa using h2
    have h4 := (ZMod.intCast_eq_intCast_iff d 1 8).mp h3
    have h5 : d ≡ 1 [ZMOD 8] := by simpa using h4
    unfold Int.ModEq at h5; omega
  · have h2 : IsSquare ((d : ℚ) : ℚ_[p]) := h inferInstance
    rw [Rat.cast_intCast, ← PadicInt.coe_intCast, isSquare_coe_iff_toZMod hp2 hu,
      map_intCast] at h2
    exact h2

/-! ### Signed unit filters: membership -/

namespace SignedUnitFilter

variable (Φ : SignedUnitFilter)

theorem Mem.ne_zero {Φ : SignedUnitFilter} {u : ℤ} (h : Φ.Mem u) : u ≠ 0 := h.1

theorem Mem.not_dvd {Φ : SignedUnitFilter} {u : ℤ} (h : Φ.Mem u) {p : ℕ} (hp : p ∈ Φ.S) :
    ¬ (p : ℤ) ∣ u := (h.2.2 p hp).1

theorem Mem.isSquareAt {Φ : SignedUnitFilter} {u : ℤ} (h : Φ.Mem u) {p : ℕ} (hp : p ∈ Φ.S) :
    IsSquareAt p ((u : ℚ) / Φ.cls p) := (h.2.2 p hp).2

theorem Mem.odd {Φ : SignedUnitFilter} {u : ℤ} (h : Φ.Mem u) (h2 : 2 ∈ Φ.S) : Odd u :=
  odd_iff_not_two_dvd.mpr (h.not_dvd h2)

theorem cls_ne_zero {p : ℕ} (hp : p ∈ Φ.S) : (Φ.cls p : ℚ) ≠ 0 := by
  intro h0
  have : Φ.cls p = 0 := by exact_mod_cast h0
  exact Φ.cls_unit p hp (this ▸ dvd_zero _)

/-- Two members of a filter are in the same squareclass of `ℚ_p` at every `p ∈ S`. PROVED. -/
theorem Mem.isSquareAt_ratio {Φ : SignedUnitFilter} {u u' : ℤ} (hu : Φ.Mem u) (hu' : Φ.Mem u')
    {p : ℕ} (hp : p ∈ Φ.S) : IsSquareAt p ((u' : ℚ) / u) := by
  have := Nonvanishing.isSquareAt_div (hu'.isSquareAt hp) (hu.isSquareAt hp)
  rwa [div_div_div_cancel_right₀ (Φ.cls_ne_zero hp)] at this

/-- **"Then `q₀d` has the prescribed original classes"** (tex 1989–1990, 10027–10028): a positive
`d` split at every prime of `S` keeps a member a member. PROVED. -/
theorem mem_mul {q d : ℤ} (hq : Φ.Mem q) (hd : 0 < d) (hsplit : ∀ p ∈ Φ.S, SplitsIn d p) :
    Φ.Mem (q * d) := by
  refine ⟨mul_ne_zero hq.ne_zero hd.ne', by rw [sign_mul_of_pos hd]; exact hq.2.1,
    fun p hp => ⟨?_, ?_⟩⟩
  · have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Φ.prime_of_mem p hp)
    intro hdvd
    rcases hpZ.dvd_or_dvd hdvd with h | h
    · exact hq.not_dvd hp h
    · exact (hsplit p hp).not_dvd (Φ.prime_of_mem p hp) h
  · have : ((q * d : ℤ) : ℚ) / Φ.cls p = ((q : ℚ) / Φ.cls p) * (d : ℚ) := by push_cast; ring
    rw [this]
    exact isSquareAt_mul (hq.isSquareAt hp)
      (isSquareAt_of_splitsIn (Φ.prime_of_mem p hp) (hsplit p hp))

/-! ### The signed prime `q₀` -/

/-- The Chinese-remainder moduli: `8` at `2`, `p` at an odd prime `p`. -/
def crtMod (p : ℕ) : ℕ := if p = 2 then 8 else p

theorem crtMod_ne_zero {p : ℕ} (hp : p.Prime) : crtMod p ≠ 0 := by
  unfold crtMod; split_ifs <;> [norm_num; exact hp.ne_zero]

theorem crtMod_coprime {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p') :
    Nat.Coprime (crtMod p) (crtMod p') := by
  unfold crtMod
  split_ifs with h1 h2 h2
  · exact absurd (h1.trans h2.symm) hne
  · subst h1
    exact Nat.Coprime.pow_left 3 ((Nat.coprime_primes Nat.prime_two hp').mpr hne)
  · subst h2
    exact Nat.Coprime.pow_right 3 ((Nat.coprime_primes hp Nat.prime_two).mpr hne)
  · exact (Nat.coprime_primes hp hp').mpr hne

theorem isCoprime_crtMod {p : ℕ} (hp : p.Prime) {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) :
    IsCoprime c (crtMod p : ℤ) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcp : IsCoprime c (p : ℤ) := ((Prime.coprime_iff_not_dvd hpZ).mpr hc).symm
  unfold crtMod
  split_ifs with h2
  · subst h2
    have : ((8 : ℕ) : ℤ) = (2 : ℤ) ^ 3 := by norm_num
    rw [this]; exact IsCoprime.pow_right (by simpa using hcp)
  · exact hcp

theorem sign_unit_mul {σ : ℤˣ} {q : ℕ} (hq : 0 < q) : Int.sign ((σ : ℤ) * q) = (σ : ℤ) := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  rcases Int.units_eq_one_or σ with rfl | rfl
  · simp only [Units.val_one, one_mul]; exact Int.sign_eq_one_of_pos hq'
  · simp only [Units.val_neg, Units.val_one, neg_mul, one_mul]
    exact Int.sign_eq_neg_one_of_neg (by omega)

/-- **The signed prime `q₀` (CRT and Dirichlet; tex 1984–1985, 10016–10017).** Every signed unit
filter contains a signed prime `σq` (`σ` the filter's sign), with `q` outside a prescribed finite
set `X` and outside `S`. In particular the filter is nonempty. PROVED. -/
theorem exists_signed_prime (X : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ X ∧ q ∉ Φ.S ∧ Φ.Mem ((Φ.sign : ℤ) * q) := by
  classical
  set m : Φ.S → ℕ := fun i => crtMod i with hm_def
  have hm0 : ∀ i, m i ≠ 0 := fun i => crtMod_ne_zero (Φ.prime_of_mem i i.2)
  have hcop : Pairwise (Function.onFun Nat.Coprime m) := by
    intro i j hij
    exact crtMod_coprime (Φ.prime_of_mem i i.2) (Φ.prime_of_mem j j.2)
      (fun h => hij (Subtype.ext h))
  have hM : (∏ i, m i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hm0 i
  have : NeZero (∏ i, m i) := ⟨hM⟩
  let e := ZMod.prodEquivPi m hcop
  let x : (i : Φ.S) → ZMod (m i) := fun i => (((Φ.sign : ℤ) * Φ.cls i : ℤ) : ZMod (m i))
  have hx : IsUnit x := by
    rw [Pi.isUnit_iff]
    intro i
    rw [ZMod.coe_int_isUnit_iff_isCoprime]
    have h1 : IsCoprime (Φ.cls i) (crtMod i : ℤ) :=
      isCoprime_crtMod (Φ.prime_of_mem i i.2) (Φ.cls_unit i i.2)
    have h0 : IsCoprime (Φ.sign : ℤ) (crtMod i : ℤ) := by
      rcases Int.units_eq_one_or Φ.sign with h | h <;> rw [h]
      · exact isCoprime_one_left
      · exact isCoprime_one_left.neg_left
    exact (IsCoprime.mul_left h0 h1).symm
  have hy : IsUnit (e.symm x) := hx.map e.symm
  obtain ⟨q, hqn, hq, hqy⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod hy (X.sup id + Φ.S.sup id)
  have hcong : ∀ i : Φ.S, (q : ZMod (m i)) = (((Φ.sign : ℤ) * Φ.cls i : ℤ) : ZMod (m i)) := by
    intro i
    have h1 := congrFun (congrArg e hqy) i
    rw [RingEquiv.apply_symm_apply] at h1
    simp only [e, ZMod.prodEquivPi_apply, map_natCast] at h1
    exact h1
  have hqX : q ∉ X := by
    intro hm
    have : q ≤ X.sup id := Finset.le_sup (f := id) hm
    omega
  have hqS : q ∉ Φ.S := by
    intro hm
    have : q ≤ Φ.S.sup id := Finset.le_sup (f := id) hm
    omega
  refine ⟨q, hq, hqX, hqS, ?_, sign_unit_mul hq.pos, fun p hp => ⟨?_, ?_⟩⟩
  · refine mul_ne_zero (Units.ne_zero _) ?_
    exact_mod_cast hq.ne_zero
  · intro hdvd
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Φ.prime_of_mem p hp)
    have hpq : (p : ℤ) ∣ q := by
      rcases hpZ.dvd_or_dvd hdvd with h | h
      · exact absurd (isUnit_of_dvd_unit h (Units.isUnit Φ.sign)) hpZ.not_isUnit
      · exact h
    have hpq' : p ∣ q := by exact_mod_cast hpq
    have := (Nat.prime_dvd_prime_iff_eq (Φ.prime_of_mem p hp) hq).mp hpq'
    exact hqS (this ▸ hp)
  · -- `σq ≡ cls p` modulo `crtMod p`
    have hc := hcong ⟨p, hp⟩
    have hσ : ((Φ.sign : ℤ) : ZMod (crtMod p)) * ((Φ.sign : ℤ) : ZMod (crtMod p)) = 1 := by
      rcases Int.units_eq_one_or Φ.sign with h | h <;> rw [h] <;> simp
    have hmod : ((Φ.sign : ℤ) * q : ℤ) ≡ Φ.cls p [ZMOD (crtMod p)] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      have hc' : ((q : ℕ) : ZMod (crtMod p)) =
          ((Φ.sign : ℤ) : ZMod (crtMod p)) * (Φ.cls p : ZMod (crtMod p)) := by
        have := hc; push_cast at this ⊢; exact this
      push_cast
      rw [hc', ← mul_assoc, hσ, one_mul]
    by_cases hp2 : p = 2
    · subst hp2
      have hmod8 : ((Φ.sign : ℤ) * q : ℤ) ≡ Φ.cls 2 [ZMOD 8] := by
        simpa [crtMod] using hmod
      have hodd : Odd (Φ.cls 2) := odd_iff_not_two_dvd.mpr (Φ.cls_unit 2 hp)
      exact isSquareAt_two_div_of_modEq hodd hmod8
    · have hmodp : ((Φ.sign : ℤ) * q : ℤ) ≡ Φ.cls p [ZMOD p] := by
        simpa [crtMod, hp2] using hmod
      exact isSquareAt_div_of_modEq hp2 (Φ.cls_unit p hp) hmodp

end SignedUnitFilter

end ZInQ.Manuscript.RC.Nonvanishing

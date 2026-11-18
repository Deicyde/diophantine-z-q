import ZInQKernel.Contrib.PoleRC.LocalTorsion
import ZInQKernel.RouteK.Selmer.Two

/-!
# The local images at `3` and at the primes `q ∣ ℓ`, `q ≠ 2, 3`: `LocalThree` and `LocalBad`

Both Props of `Count.lean` are proved here as stated, both directions.

S12 (`parity-frozen-4eaee875.tex`) lines 349–357:

* at a support prime `q_i ∣ ℓ`, "the valuation pairs of `τ₁` and `τ₂` are `(1, 0)` and `(0, 1)`
  modulo 2; therefore they generate the entire local image, again by its order four";
* at `3`, "`ℓ` is a unit nonsquare and `−ℓ` is a square. Thus `τ₁` and `τ₂` have independent
  first-coordinate classes and square second coordinates. The local image at `3` is
  consequently `(ℚ₃*/ℚ₃*²) × {1}`" (S12 (par:local-three)).

Map from the Lean steps to S12:

* "if" halves (`localThree_suff`, `localBad_suff`): the generation statement, i.e. the torsion
  classes `τ₁`, `τ₂`, `τ₁τ₂` and `1` lie in the local image (S12 lines 318–324, 349–357). The
  Lean proof writes the given square class as a torsion class (`locM_of_torsion`):
  at `3` by the residue of `a` and of `a/3` mod `3` (`ℓ ≡ 2` makes `ℓ` the unit nonsquare,
  `−ℓ ≡ 1` a square, S12 line 352); at `q ∣ ℓ` by `sqEq_of_qcls_eq`, the converse of
  `qcls_eq_of_sqEq` (square classes of squarefree integers at an odd prime are read off from the
  valuation parity and the Legendre symbol of the unit part, Hensel's lemma).
* "only if" halves: S12 obtains them from the order four of `E_ℓ(ℚ_q)/2E_ℓ(ℚ_q)` (S12 lines
  330–338, an open formal subgroup). DEPARTURE (more elementary, already in the branch): the
  Lean proofs `localThree_nec` and `locM_bad_classes` (`LocalP.lean`) are direct `q`-adic
  valuation arguments on the witness `x`, with no formal group and no counting. For `LocalBad`
  as stated (no hypothesis `3 ∤ ℓ`) the branch's `localBad_nec` assumes `ℓ ≡ 11 (mod 12)`;
  `localBad_nec'` below removes that hypothesis (the class `3ℓ` is represented by `ℓ/3` when
  `3 ∣ ℓ`, `exists_rep_three_mul`).
-/

namespace ZInQ.Manuscript.PoleRC

open ZInQ.RouteK.Selmer

/-! ### `LocalThree` -/

theorem intCast_zmod_eq_of_emod {n : ℕ} {c r : ℤ} (h : c % (n : ℤ) = r) :
    (c : ZMod n) = (r : ZMod n) := by
  rw [← ZMod.intCast_mod c n, h]

/-- An integer `≡ 1 (mod 3)` is a square in `ℚ₃` (Hensel). -/
theorem isSquare_three_adic_of_mod {c : ℤ} (h : c % 3 = 1) : IsSquare (c : ℚ_[3]) := by
  have hc : ¬ ((3 : ℕ) : ℤ) ∣ c := by
    intro h'
    have : (3 : ℤ) ∣ c := by exact_mod_cast h'
    omega
  refine isSquare_intCast_of_residue (p := 3) (by norm_num) hc ⟨1, ?_⟩
  rw [mul_one, intCast_zmod_eq_of_emod (n := 3) (r := 1) (by simpa using h)]
  simp

/-- Two integers whose product is `≡ 1 (mod 3)` have the same class in `ℚ₃*/ℚ₃*²`. -/
theorem sqEq_three_adic {u w : ℤ} (h : (u * w) % 3 = 1) : SqEq (u : ℚ_[3]) (w : ℚ_[3]) := by
  have hu : u ≠ 0 := by rintro rfl; simp at h
  have hw : w ≠ 0 := by rintro rfl; simp at h
  refine (sqEq_iff_isSquare_mul (Int.cast_ne_zero.mpr hu) (Int.cast_ne_zero.mpr hw)).mpr ?_
  have := isSquare_three_adic_of_mod h
  push_cast at this
  exact this

/-- **`LocalThree`, "if"** (S12 lines 351–357): for `ℓ ≡ 2 (mod 3)` and `b ≡ 1 (mod 3)`, every
class `(a, b)` is in the image: `a` is in the class of `1`, `ℓ`, `3` or `3ℓ`, and `b ≡ 1 ≡ −ℓ`. -/
theorem localThree_suff {ℓ : ℕ} {a b : ℤ} (h3 : ℓ % 3 = 2) (ha : Squarefree a)
    (hb3 : b % 3 = 1) : LocM ℚ_[3] ℓ a b := by
  have hℓ0 : ((ℓ : ℕ) : ℚ_[3]) ≠ 0 := by
    have : ℓ ≠ 0 := by omega
    exact_mod_cast this
  have h30 : (3 : ℚ_[3]) ≠ 0 := by norm_num
  have hℓ3 : (ℓ : ℤ) % 3 = 2 := by omega
  have eL : (((ℓ : ℤ)) : ℚ_[3]) = (ℓ : ℚ_[3]) := Int.cast_natCast ℓ
  have hb1 : SqEq (b : ℚ_[3]) ((1 : ℤ) : ℚ_[3]) := sqEq_three_adic (by simpa using hb3)
  have hbl : SqEq (b : ℚ_[3]) (((-(ℓ : ℤ)) : ℤ) : ℚ_[3]) :=
    hb1.trans (sqEq_three_adic (by omega)).symm
  rw [Int.cast_one] at hb1
  rw [Int.cast_neg, eL] at hbl
  apply locM_of_torsion h30 hℓ0
  by_cases h3a : (3 : ℤ) ∣ a
  · obtain ⟨c, rfl⟩ := h3a
    have hc3 : c % 3 ≠ 0 := by
      intro h0
      have h9 : (3 : ℤ) * 3 ∣ 3 * c := mul_dvd_mul_left 3 (Int.dvd_of_emod_eq_zero h0)
      have := ha _ h9
      rw [Int.isUnit_iff] at this
      omega
    have hcast : (((3 * c : ℤ)) : ℚ_[3]) = 3 * (c : ℚ_[3]) := by push_cast; ring
    rw [hcast]
    rcases (by omega : c % 3 = 1 ∨ c % 3 = 2) with hc | hc
    · -- `a = 3c ≡ 3`
      right; right; left
      refine ⟨?_, hbl⟩
      have := (SqEq.refl (3 : ℚ_[3])).mul (sqEq_three_adic (u := c) (w := 1) (by simpa using hc))
      simpa using this
    · -- `a = 3c ≡ 3ℓ`
      right; right; right
      refine ⟨?_, hbl⟩
      have hcl : (c * (ℓ : ℤ)) % 3 = 1 := by rw [Int.mul_emod, hc, hℓ3]; norm_num
      have := (SqEq.refl (3 : ℚ_[3])).mul (sqEq_three_adic hcl)
      rwa [eL] at this
  · rcases (by omega : a % 3 = 1 ∨ a % 3 = 2) with ha3 | ha3
    · left
      refine ⟨?_, hb1⟩
      have := sqEq_three_adic (u := a) (w := 1) (by simpa using ha3)
      simpa using this
    · right; left
      refine ⟨?_, hb1⟩
      have hal : (a * (ℓ : ℤ)) % 3 = 1 := by rw [Int.mul_emod, ha3, hℓ3]; norm_num
      have := sqEq_three_adic hal
      rwa [eL] at this

/-- **`LocalThree` holds** (S12 lines 351–357, (par:local-three)). -/
theorem localThree : LocalThree := fun _ _ _ _ h3 ha hb =>
  ⟨localThree_nec h3 ha hb, localThree_suff h3 ha⟩

/-! ### `LocalBad` -/

section Bad

variable {q : ℕ} [hq : Fact q.Prime]

/-- Equal Legendre symbols of two `q`-adic units make their product a square in `ℚ_q`. -/
theorem isSquare_of_lsym_eq (hq2 : q ≠ 2) {u w : ℤ} (hu : ¬ (q : ℤ) ∣ u) (hw : ¬ (q : ℤ) ∣ w)
    (h : lsym u q = lsym w q) : IsSquare (((u * w : ℤ)) : ℚ_[q]) := by
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq.out
  have hnd : ¬ (q : ℤ) ∣ u * w := fun h' => (hqp.dvd_or_dvd h').elim hu hw
  refine isSquare_intCast_of_residue hq2 hnd ?_
  have hm := lsym_mul q (intCast_ne_zero_of_not_dvd hu) (intCast_ne_zero_of_not_dvd hw)
  rw [h, zmod2_add_self] at hm
  by_contra hns
  rw [lsym_of_not_isSquare hns] at hm
  exact one_ne_zero hm

/-- **Equal `qcls` give equal square classes in `ℚ_q`** (squarefree integers, `q` odd): the
converse of `qcls_eq_of_sqEq`. -/
theorem sqEq_of_qcls_eq (hq2 : q ≠ 2) {u w : ℤ} (hu : Squarefree u) (hw : Squarefree w)
    (h : qcls q u = qcls q w) : SqEq (u : ℚ_[q]) (w : ℚ_[q]) := by
  have hu0 : (u : ℚ_[q]) ≠ 0 := Int.cast_ne_zero.mpr hu.ne_zero
  have hw0 : (w : ℚ_[q]) ≠ 0 := Int.cast_ne_zero.mpr hw.ne_zero
  have hq0 : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hq.out.ne_zero
  rw [sqEq_iff_isSquare_mul hu0 hw0]
  unfold qcls at h
  by_cases h1 : (q : ℤ) ∣ u <;> by_cases h2 : (q : ℤ) ∣ w
  · rw [if_pos h1, if_pos h2] at h
    have hl : lsym (u / q) q = lsym (w / q) q := (Prod.ext_iff.mp h).2
    have hs := isSquare_of_lsym_eq hq2 (not_dvd_div_of_squarefree hq.out hu h1)
      (not_dvd_div_of_squarefree hq.out hw h2) hl
    obtain ⟨u', rfl⟩ := h1
    obtain ⟨w', rfl⟩ := h2
    rw [Int.mul_ediv_cancel_left _ hq0, Int.mul_ediv_cancel_left _ hq0] at hs
    have e : (((q * u' : ℤ)) : ℚ_[q]) * (((q * w' : ℤ)) : ℚ_[q]) =
        ((u' * w' : ℤ) : ℚ_[q]) * ((q : ℤ) : ℚ_[q]) ^ 2 := by push_cast; ring
    rw [e, isSquare_mul_sq_iff (Int.cast_ne_zero.mpr hq0)]
    exact hs
  · rw [if_pos h1, if_neg h2] at h
    exact absurd (Prod.ext_iff.mp h).1 one_ne_zero
  · rw [if_neg h1, if_pos h2] at h
    exact absurd (Prod.ext_iff.mp h).1 zero_ne_one
  · rw [if_neg h1, if_neg h2] at h
    have hl : lsym u q = lsym w q := (Prod.ext_iff.mp h).2
    have := isSquare_of_lsym_eq hq2 h1 h2 hl
    push_cast at this
    exact this

theorem zmod2sq_add_add_self (x y : ZMod 2 × ZMod 2) : y + x + y = x := by
  revert x y; decide

/-- **The class of `3ℓ` by a squarefree integer** whose `qcls` is `qcls ℓ + qcls 3`: `3ℓ` itself
if `3 ∤ ℓ`, and `ℓ/3` if `3 ∣ ℓ` (`3ℓ = 9 · ℓ/3`). -/
theorem exists_rep_three_mul {ℓ : ℕ} (hsf : Squarefree ℓ) :
    ∃ c : ℤ, Squarefree c ∧ SqEq ((3 : ℚ_[q]) * ((ℓ : ℤ) : ℚ_[q])) (c : ℚ_[q]) ∧
      qcls q c = qcls q ℓ + qcls q 3 := by
  have hsfZ : Squarefree (ℓ : ℤ) := Int.squarefree_natCast.mpr hsf
  by_cases h3 : (3 : ℤ) ∣ (ℓ : ℤ)
  · obtain ⟨m, hm⟩ := h3
    have hmsf : Squarefree m := by rw [hm] at hsfZ; exact Squarefree.of_mul_right hsfZ
    refine ⟨m, hmsf, ⟨3, by norm_num, ?_⟩, ?_⟩
    · have : (((ℓ : ℤ)) : ℚ_[q]) = 3 * (m : ℚ_[q]) := by rw [hm]; push_cast; ring
      rw [this]; ring
    · have hq3 := qcls_mul q (x := 3) (y := m) (by rw [← hm]; exact hsfZ)
      rw [← hm] at hq3
      rw [hq3, zmod2sq_add_add_self]
  · have h3' : ¬ 3 ∣ ℓ := fun h => h3 (by exact_mod_cast h)
    have hsf3l : Squarefree (3 * (ℓ : ℤ)) := by
      rw [← Int.squarefree_natAbs, Int.natAbs_mul, Nat.squarefree_mul_iff]
      refine ⟨?_, Nat.prime_three.squarefree, by simpa using hsf⟩
      rw [show (3 : ℤ).natAbs = 3 from rfl, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      simpa using h3'
    refine ⟨3 * ℓ, hsf3l, ⟨1, one_ne_zero, by push_cast; ring⟩, ?_⟩
    rw [qcls_mul q hsf3l, add_comm]

/-- **`LocalBad`, "only if"**, for every squarefree `ℓ` (no congruence condition): the branch's
`localBad_nec` with the class `3ℓ` represented by `exists_rep_three_mul`. -/
theorem localBad_nec' {ℓ : ℕ} {a b : ℤ} (hsf : Squarefree ℓ) (hql : q ∣ ℓ)
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) (ha : Squarefree a) (hb : Squarefree b)
    (h : LocM ℚ_[q] ℓ a b) : ∃ e₁ e₂ : ZMod 2,
      qcls q a = e₁ • qcls q ℓ + e₂ • qcls q 3 ∧ qcls q b = e₂ • qcls q (-(ℓ : ℤ)) := by
  have hsfZ : Squarefree (ℓ : ℤ) := Int.squarefree_natCast.mpr hsf
  have hsf3 : Squarefree (3 : ℤ) := Int.prime_three.squarefree
  have hsfn : Squarefree (-(ℓ : ℤ)) := by rw [← Int.squarefree_natAbs]; simpa using hsf
  have hsf1 : Squarefree (1 : ℤ) := squarefree_one
  have hqZ : (q : ℤ) ∣ (ℓ : ℤ) := by exact_mod_cast hql
  have hL : ‖((ℓ : ℤ) : ℚ_[q])‖ < 1 := Padic.norm_intCast_lt_one_iff.mpr hqZ
  have hL0 : ((ℓ : ℤ) : ℚ_[q]) ≠ 0 := Int.cast_ne_zero.mpr (by exact_mod_cast hsf.ne_zero)
  have hvL : (((ℓ : ℤ)) : ℚ_[q]).valuation = 1 := by
    rw [Padic.valuation_intCast]
    obtain ⟨m, hm⟩ := hqZ
    have hm' : ¬ (q : ℤ) ∣ m := by
      have := not_dvd_div_of_squarefree hq.out hsfZ ⟨m, hm⟩
      rwa [hm, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr hq.out.ne_zero)] at this
    rw [hm, padicValInt_q_mul hm']; rfl
  have hA0 : (a : ℚ_[q]) ≠ 0 := Int.cast_ne_zero.mpr ha.ne_zero
  have hB0 : (b : ℚ_[q]) ≠ 0 := Int.cast_ne_zero.mpr hb.ne_zero
  have h' : LocM ℚ_[q] ((ℓ : ℤ) : ℚ_[q]) a b := by simpa using h
  have c1 : (1 : ℚ_[q]) = ((1 : ℤ) : ℚ_[q]) := by simp
  have c3 : (3 : ℚ_[q]) = ((3 : ℤ) : ℚ_[q]) := by simp
  have cnl : -((ℓ : ℤ) : ℚ_[q]) = ((-(ℓ : ℤ) : ℤ) : ℚ_[q]) := by push_cast; ring
  have q1 : qcls q 1 = 0 := qcls_one q
  obtain ⟨c, hc, hc3, hcq⟩ := exists_rep_three_mul (q := q) hsf
  rcases locM_bad_classes hq2 hq3 hL hL0 hvL hA0 hB0 h' with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ |
    ⟨ha', hb'⟩ | ⟨ha', hb'⟩
  · rw [c1] at ha' hb'
    refine ⟨0, 0, ?_, ?_⟩
    · rw [qcls_eq_of_sqEq ha hsf1 ha', q1]; simp
    · rw [qcls_eq_of_sqEq hb hsf1 hb', q1]; simp
  · rw [c1] at hb'
    refine ⟨1, 0, ?_, ?_⟩
    · rw [qcls_eq_of_sqEq ha hsfZ ha']; simp
    · rw [qcls_eq_of_sqEq hb hsf1 hb', q1]; simp
  · rw [c3] at ha'; rw [cnl] at hb'
    refine ⟨0, 1, ?_, ?_⟩
    · rw [qcls_eq_of_sqEq ha hsf3 ha']; simp
    · rw [qcls_eq_of_sqEq hb hsfn hb']; simp
  · rw [cnl] at hb'
    refine ⟨1, 1, ?_, ?_⟩
    · rw [qcls_eq_of_sqEq ha hc (ha'.trans hc3), hcq]; simp
    · rw [qcls_eq_of_sqEq hb hsfn hb']; simp

/-- **`LocalBad`, "if"** (S12 lines 349–351: `τ₁`, `τ₂` generate the local image at `q_i`): a
pair in the `qcls`-span of `(ℓ, 1)` and `(3, −ℓ)` is the class of a torsion point. -/
theorem localBad_suff {ℓ : ℕ} {a b : ℤ} (hsf : Squarefree ℓ) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (ha : Squarefree a) (hb : Squarefree b)
    (h : ∃ e₁ e₂ : ZMod 2, qcls q a = e₁ • qcls q ℓ + e₂ • qcls q 3 ∧
      qcls q b = e₂ • qcls q (-(ℓ : ℤ))) : LocM ℚ_[q] ℓ a b := by
  obtain ⟨e₁, e₂, h1, h2⟩ := h
  have hsfZ : Squarefree (ℓ : ℤ) := Int.squarefree_natCast.mpr hsf
  have hsf3 : Squarefree (3 : ℤ) := Int.prime_three.squarefree
  have hsfn : Squarefree (-(ℓ : ℤ)) := by rw [← Int.squarefree_natAbs]; simpa using hsf
  have hsf1 : Squarefree (1 : ℤ) := squarefree_one
  have hℓ0 : ((ℓ : ℕ) : ℚ_[q]) ≠ 0 := by exact_mod_cast hsf.ne_zero
  have h30 : (3 : ℚ_[q]) ≠ 0 := by
    have := padic_norm_three (p := q) hq3
    intro h0; rw [h0, norm_zero] at this; exact zero_ne_one this
  obtain ⟨c, hc, hc3, hcq⟩ := exists_rep_three_mul (q := q) hsf
  have e1 : ((1 : ℤ) : ℚ_[q]) = 1 := by simp
  have e3 : ((3 : ℤ) : ℚ_[q]) = 3 := by simp
  have eL : (((ℓ : ℤ)) : ℚ_[q]) = (ℓ : ℚ_[q]) := Int.cast_natCast ℓ
  have enl : ((-(ℓ : ℤ) : ℤ) : ℚ_[q]) = -(ℓ : ℚ_[q]) := by push_cast; ring
  rw [eL] at hc3
  apply locM_of_torsion h30 hℓ0
  rcases ZInQ.Manuscript.PoleRC.zmod2_cases e₁ with rfl | rfl <;>
    rcases ZInQ.Manuscript.PoleRC.zmod2_cases e₂ with rfl | rfl <;>
    simp only [zero_smul, one_smul, add_zero, zero_add] at h1 h2
  · left
    rw [← qcls_one q] at h1 h2
    exact ⟨(sqEq_of_qcls_eq hq2 ha hsf1 h1).trans_eq e1,
      (sqEq_of_qcls_eq hq2 hb hsf1 h2).trans_eq e1⟩
  · right; right; left
    exact ⟨(sqEq_of_qcls_eq hq2 ha hsf3 h1).trans_eq e3,
      (sqEq_of_qcls_eq hq2 hb hsfn h2).trans_eq enl⟩
  · right; left
    rw [← qcls_one q] at h2
    exact ⟨(sqEq_of_qcls_eq hq2 ha hsfZ h1).trans_eq eL,
      (sqEq_of_qcls_eq hq2 hb hsf1 h2).trans_eq e1⟩
  · right; right; right
    rw [← hcq] at h1
    exact ⟨(sqEq_of_qcls_eq hq2 ha hc h1).trans hc3.symm,
      (sqEq_of_qcls_eq hq2 hb hsfn h2).trans_eq enl⟩

end Bad

/-- **`LocalBad` holds** (S12 lines 349–351), for every squarefree `ℓ` and `q ∣ ℓ`, `q ≠ 2, 3`. -/
theorem localBad : LocalBad := fun _ _ _ _ _ hsf hql hq2 hq3 ha hb =>
  ⟨localBad_nec' hsf hql hq2 hq3 ha hb, localBad_suff hsf hq2 hq3 ha hb⟩

end ZInQ.Manuscript.PoleRC

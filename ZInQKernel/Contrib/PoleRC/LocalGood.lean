import ZInQKernel.Contrib.PoleRC.KummerF
import ZInQKernel.Contrib.PoleRC.LocalTorsion
import ZInQKernel.RouteK.Selmer.Two

/-!
# The local image at a prime of good reduction: `LocalGood`

For `p ∤ 6ℓ` (`ℓ` squarefree) and squarefree `a, b`: `LocM ℚ_p ℓ a b ↔ p ∤ a ∧ p ∤ b`.

S12 (`parity-frozen-4eaee875.tex`):

* lines 340–344 (the "only if" half): "At an odd prime `q ∤ 3l`, the roots are integral and
  pairwise distinct modulo `q`. If `v_q(x) < 0`, all three factors have that valuation, which must
  be even. If `x` is integral, at most one factor has positive valuation, and that valuation must
  be even. The replacement classes at the roots are units as well." This is the branch's
  `localGood_nec` (`LocalP.lean`), a direct `p`-adic valuation argument.
* lines 330–338 and 345–347 (the "if" half): `E_l(ℚ_q)/2E_l(ℚ_q)` has order four ("choose an open
  formal subgroup `H` on which multiplication by `2` is an isomorphism. The quotient
  `G = E_l(ℚ_q)/H` is finite ... Finally `|G/2G| = |G[2]| = 4`"), and the image, contained in the
  unramified subgroup of order four, is all of it.

The Lean proof of the "if" half (`localGood_suff`) keeps S12's counting `|G/2G| = |G[2]| = 4` for
a finite abelian group `G`, with `G = E_ℓ(𝔽_p)`, the points of the reduction (for good reduction
this is `E_ℓ(ℚ_p)/E₁(ℚ_p)`, S12's `G` for the formal subgroup `H = E₁`):

1. `card_range_eq_card_ker_two`: for finite `G` and a homomorphism `δ` with `ker δ = 2G`,
   `#δ(G) = #G[2]` (S12 line 338);
2. `deltaHomF_ker` (`KummerF.lean`): the Kummer map `δ` of `E_ℓ(𝔽_p)` has kernel `2E_ℓ(𝔽_p)`
   (Silverman X.1.4 over `𝔽_p`, S12 line 241); `four_le_card_ker_two`: `#E_ℓ(𝔽_p)[2] ≥ 4`
   (the roots `0, ℓ, −3ℓ` are distinct mod `p`, S12 line 340);
3. `card_sqClass_sq_le`: `#(𝔽_p*/𝔽_p*²)² ≤ 4`; hence `δ` is onto (`deltaHomF_surjective`);
4. Hensel (`isSquare_intCast_of_residue`): a point of `E_ℓ(𝔽_p)` with Kummer classes
   `(ā, b̄)` lifts to a witness `x ∈ ℤ` of `LocM ℚ_p ℓ a b`, or `(a, b)` is a torsion class.

DEPARTURE (minimal, labelled): S12's step "`E(ℚ_q)/2E(ℚ_q) ≅ G/2G`" (which needs the formal
group `H` to be uniquely 2-divisible) is replaced by the Hensel lifting of step 4; no formal group
is used. The counting step and the containment in the unramified subgroup are S12's.
-/

namespace ZInQ.Manuscript.PoleRC

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent ZInQ.RouteK.Selmer

/-! ### Finite groups and finite fields -/

/-- A point as an element of `Option (F × F)`. -/
def pointXY {F : Type*} [CommRing F] {W : WeierstrassCurve.Affine F} : W.Point → Option (F × F)
  | .zero => none
  | .some x y _ => some (x, y)

theorem pointXY_injective {F : Type*} [CommRing F] {W : WeierstrassCurve.Affine F} :
    Function.Injective (pointXY (W := W)) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hf
  · rfl
  · simp [pointXY] at hf
  · simp [pointXY] at hf
  · simp only [pointXY, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    rfl

instance finite_point {F : Type*} [CommRing F] [Finite F] (W : WeierstrassCurve.Affine F) :
    Finite W.Point :=
  Finite.of_injective _ pointXY_injective

/-- **S12 line 338 for a finite group**: if `ker δ = 2G` then `#δ(G) = #G[2]`
(`|G/2G| = |G[2]|`). -/
theorem card_range_eq_card_ker_two {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Finite G]
    (δ : G →+ H) (hker : δ.ker = (nsmulAddMonoidHom 2 : G →+ G).range) :
    Nat.card δ.range = Nat.card (nsmulAddMonoidHom 2 : G →+ G).ker := by
  set φ : G →+ G := nsmulAddMonoidHom 2
  have e1 : Nat.card G = Nat.card δ.range * Nat.card δ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup δ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange δ).toEquiv]
  have e2 : Nat.card G = Nat.card φ.range * Nat.card φ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv]
  rw [hker] at e1
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  have h : Nat.card δ.range * Nat.card φ.range = Nat.card φ.ker * Nat.card φ.range := by
    rw [← e1, e2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos h

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- In a finite field, every square class is `1` or the class of a fixed nonsquare. -/
theorem sqClass_eq_one_or {g : F} (hg : ¬ IsSquare g) (c : SqClass F) : c = 1 ∨ c = sqc g := by
  obtain ⟨u, rfl⟩ := SqClass.mk_surjective c
  rw [← sqc_units]
  have hu : (u : F) ≠ 0 := u.ne_zero
  have hg0 : g ≠ 0 := by rintro rfl; exact hg ⟨0, by ring⟩
  by_cases hsq : IsSquare (u : F)
  · left; exact (sqc_eq_one_iff hu).mpr hsq
  · right
    have hug : IsSquare ((u : F) * g) := by
      have h1 := quadraticChar_neg_one_iff_not_isSquare.mpr hsq
      have h2 := quadraticChar_neg_one_iff_not_isSquare.mpr hg
      refine (quadraticChar_one_iff_isSquare (mul_ne_zero hu hg0)).mp ?_
      rw [map_mul, h1, h2]; norm_num
    have h1 := (sqc_eq_one_iff (mul_ne_zero hu hg0)).mpr hug
    rw [sqc_mul hu hg0] at h1
    calc sqc (u : F) = sqc (u : F) * (sqc g * sqc g) := by rw [SqClass.mul_self, mul_one]
      _ = (sqc (u : F) * sqc g) * sqc g := by rw [mul_assoc]
      _ = sqc g := by rw [h1, one_mul]

theorem surjective_bool_sqClass {g : F} (hg : ¬ IsSquare g) :
    Function.Surjective (fun ij : Bool × Bool => Additive.ofMul
      ((if ij.1 then sqc g else 1, if ij.2 then sqc g else 1) : SqClass F × SqClass F)) := by
  intro c
  rcases sqClass_eq_one_or hg (Additive.toMul c).1 with h1 | h1 <;>
    rcases sqClass_eq_one_or hg (Additive.toMul c).2 with h2 | h2
  · exact ⟨(false, false), Additive.toMul.injective (Prod.ext (by simp [h1]) (by simp [h2]))⟩
  · exact ⟨(false, true), Additive.toMul.injective (Prod.ext (by simp [h1]) (by simp [h2]))⟩
  · exact ⟨(true, false), Additive.toMul.injective (Prod.ext (by simp [h1]) (by simp [h2]))⟩
  · exact ⟨(true, true), Additive.toMul.injective (Prod.ext (by simp [h1]) (by simp [h2]))⟩

/-- **The Kummer map of `E_ℓ(𝔽)` is onto `(𝔽*/𝔽*²)²`** for a finite field `𝔽` of characteristic
not `2, 3` and `ℓ ≠ 0` (S12 lines 330–338 with `G = E_ℓ(𝔽)`). -/
theorem deltaHomF_surjective (hF : ringChar F ≠ 2) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {ℓ : F} (hℓ : ℓ ≠ 0) : Function.Surjective (deltaHomF h2 h3 hℓ) := by
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare hF
  have hs := surjective_bool_sqClass hg
  haveI : Finite (Additive (SqClass F × SqClass F)) := Finite.of_surjective _ hs
  have hrange : (deltaHomF h2 h3 hℓ).range = ⊤ := by
    apply AddSubgroup.eq_top_of_le_card
    calc Nat.card (Additive (SqClass F × SqClass F)) ≤ Nat.card (Bool × Bool) :=
          Nat.card_le_card_of_surjective _ hs
      _ = 4 := by simp
      _ ≤ Nat.card (nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).ker :=
          four_le_card_ker_two h2 h3 hℓ
      _ = Nat.card (deltaHomF h2 h3 hℓ).range :=
          (card_range_eq_card_ker_two _ (deltaHomF_ker h2 h3 hℓ)).symm
  intro t
  exact AddMonoidHom.mem_range.mp (hrange ▸ AddSubgroup.mem_top t)

end FiniteField

/-! ### From `𝔽_p` to `ℚ_p` (Hensel) -/

section Lift

variable {p : ℕ} [hp : Fact p.Prime]

theorem isSquare_div_of_sqEq {K : Type*} [Field K] {u v : K} (hv : v ≠ 0) (h : SqEq u v) :
    IsSquare (u / v) := by
  obtain ⟨s, -, rfl⟩ := h
  exact ⟨s, by field_simp⟩

/-- Equal square classes mod `p` of two integers prime to `p` give equal classes in `ℚ_p`. -/
theorem sqEq_padic_of_sqc_eq (hp2 : p ≠ 2) {u w : ℤ} (hu : ¬ (p : ℤ) ∣ u) (hw : ¬ (p : ℤ) ∣ w)
    (h : sqc (u : ZMod p) = sqc (w : ZMod p)) : SqEq (u : ℚ_[p]) (w : ℚ_[p]) := by
  have hu0 : (u : ZMod p) ≠ 0 := intCast_ne_zero_of_not_dvd hu
  have hw0 : (w : ZMod p) ≠ 0 := intCast_ne_zero_of_not_dvd hw
  have hqp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have h1 : sqc (((u * w : ℤ)) : ZMod p) = 1 := by
    push_cast
    rw [sqc_mul hu0 hw0, h, SqClass.mul_self]
  have hres : IsSquare (((u * w : ℤ)) : ZMod p) :=
    (sqc_eq_one_iff (by push_cast; exact mul_ne_zero hu0 hw0)).mp h1
  have hsq := isSquare_intCast_of_residue hp2 (fun h' => (hqp.dvd_or_dvd h').elim hu hw) hres
  push_cast at hsq
  exact (sqEq_iff_isSquare_mul (Int.cast_ne_zero.mpr fun h0 => hu (by rw [h0]; exact dvd_zero _))
    (Int.cast_ne_zero.mpr fun h0 => hw (by rw [h0]; exact dvd_zero _))).mpr hsq

theorem not_dvd_of_zmod_ne_zero {m : ℤ} (h : (m : ZMod p) ≠ 0) : ¬ (p : ℤ) ∣ m :=
  fun h' => h ((ZMod.intCast_zmod_eq_zero_iff_dvd m p).mpr h')

theorem sqClass_eq_mul_of_mul_mul {F : Type*} [Field F] {a b c : SqClass F}
    (h : a * b * c = 1) : a = b * c := by
  calc a = a * ((b * c) * (b * c)) := by rw [SqClass.mul_self, mul_one]
    _ = (a * b * c) * (b * c) := by simp only [mul_assoc]
    _ = b * c := by rw [h, one_mul]

/-- **`LocalGood`, "if"** (S12 lines 330–347): at `p ∤ 6ℓ`, every unramified class is a local
Kummer class. -/
theorem localGood_suff {ℓ : ℕ} {a b : ℤ} (hp6 : ¬ p ∣ 6 * ℓ) (ha : ¬ (p : ℤ) ∣ a)
    (hb : ¬ (p : ℤ) ∣ b) : LocM ℚ_[p] ℓ a b := by
  have hp2 : p ≠ 2 := by rintro rfl; exact hp6 (Dvd.intro (3 * ℓ) (by ring))
  have hp3 : p ≠ 3 := by rintro rfl; exact hp6 (Dvd.intro (2 * ℓ) (by ring))
  have hpl : ¬ (p : ℤ) ∣ (ℓ : ℤ) := fun h' => hp6 (Dvd.dvd.mul_left (by exact_mod_cast h') 6)
  have hqp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hnd : ∀ n : ℕ, n.Prime → n ≠ p → ¬ (p : ℤ) ∣ (n : ℤ) := fun n hn hnp h' =>
    hnp ((Nat.prime_dvd_prime_iff_eq hp.out hn).mp (by exact_mod_cast h')).symm
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := intCast_ne_zero_of_not_dvd (hnd 2 Nat.prime_two (Ne.symm hp2)); simpa using this
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := intCast_ne_zero_of_not_dvd (hnd 3 Nat.prime_three (Ne.symm hp3)); simpa using this
  set L : ZMod p := ((ℓ : ℤ) : ZMod p) with hLdef
  have hℓ : L ≠ 0 := intCast_ne_zero_of_not_dvd hpl
  have hA : (a : ZMod p) ≠ 0 := intCast_ne_zero_of_not_dvd ha
  have hB : (b : ZMod p) ≠ 0 := intCast_ne_zero_of_not_dvd hb
  -- `ℚ_p` facts
  have hℓ0 : ((ℓ : ℕ) : ℚ_[p]) ≠ 0 := by
    have : ((ℓ : ℤ) : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr fun h0 => hpl (by rw [h0]; exact dvd_zero _)
    simpa using this
  have h30 : (3 : ℚ_[p]) ≠ 0 := by norm_num
  have eL : (((ℓ : ℤ)) : ℚ_[p]) = (ℓ : ℚ_[p]) := Int.cast_natCast ℓ
  have hsf3 : ¬ (p : ℤ) ∣ 3 := by simpa using hnd 3 Nat.prime_three (Ne.symm hp3)
  have hsfn : ¬ (p : ℤ) ∣ -(ℓ : ℤ) := by rwa [dvd_neg]
  have hsf3l : ¬ (p : ℤ) ∣ 3 * (ℓ : ℤ) := fun h' => (hqp.dvd_or_dvd h').elim hsf3 hpl
  have hsf1 : ¬ (p : ℤ) ∣ 1 := fun h' => hqp.not_unit (isUnit_of_dvd_one h')
  -- the point of `E_ℓ(𝔽_p)` with Kummer classes `(ā, b̄)`
  obtain ⟨P, hP⟩ := deltaHomF_surjective hF h2 h3 hℓ
    (Additive.ofMul (sqc ((a : ℤ) : ZMod p), sqc ((b : ℤ) : ZMod p)))
  have hP' : deltaF L P = (sqc ((a : ℤ) : ZMod p), sqc ((b : ℤ) : ZMod p)) :=
    congrArg Additive.toMul hP
  rcases P with _ | ⟨x, y, h⟩
  · -- `P = O`: `a` and `b` are squares mod `p`
    have k1' : sqc ((a : ℤ) : ZMod p) = 1 := (congrArg Prod.fst hP').symm
    have k2' : sqc ((b : ℤ) : ZMod p) = 1 := (congrArg Prod.snd hP').symm
    have k1 : sqc ((a : ℤ) : ZMod p) = sqc (((1 : ℤ)) : ZMod p) := by rw [k1']; simp
    have k2 : sqc ((b : ℤ) : ZMod p) = sqc (((1 : ℤ)) : ZMod p) := by rw [k2']; simp
    apply locM_of_torsion h30 hℓ0
    left
    exact ⟨(sqEq_padic_of_sqc_eq hp2 ha hsf1 k1).trans_eq (by simp),
      (sqEq_padic_of_sqc_eq hp2 hb hsf1 k2).trans_eq (by simp)⟩
  simp only [deltaF_def, Prod.mk.injEq] at hP'
  obtain ⟨k1, k2⟩ := hP'
  have h3ℓ : -3 * L ≠ L := fun h0 =>
    mul_ne_zero (mul_ne_zero h2 h2) hℓ (by linear_combination -h0)
  by_cases hx3 : x = -3 * L
  · -- `(−3ℓ, 0)` mod `p`: the class `τ₂ = (3, −ℓ)`
    rw [kumF_some_eq _ hx3, fdF_neg3, show (12 : ZMod p) * L ^ 2 = 3 * (2 * L) ^ 2 by ring,
      sqc_mul_sq _ (mul_ne_zero h2 hℓ)] at k1
    rw [kumF_some_of_ne _ (by rw [hx3]; exact h3ℓ), hx3,
      show -3 * L - L = -L * 2 ^ 2 by ring, sqc_mul_sq _ h2] at k2
    apply locM_of_torsion h30 hℓ0
    right; right; left
    refine ⟨(sqEq_padic_of_sqc_eq hp2 ha hsf3 ?_).trans_eq (by simp),
      (sqEq_padic_of_sqc_eq hp2 hb hsfn ?_).trans_eq (by simp)⟩
    · rw [← k1]; simp
    · rw [← k2]; simp [hLdef]
  by_cases hx1 : x = L
  · -- `(ℓ, 0)` mod `p`: the class `τ₁ = (ℓ, 1)`
    rw [kumF_some_of_ne _ hx3, hx1, show L - -3 * L = L * 2 ^ 2 by ring, sqc_mul_sq _ h2] at k1
    rw [kumF_some_eq _ hx1, fdF_ell, show (4 : ZMod p) * L ^ 2 = 1 * (2 * L) ^ 2 by ring,
      sqc_mul_sq _ (mul_ne_zero h2 hℓ), sqc_one] at k2
    apply locM_of_torsion h30 hℓ0
    right; left
    refine ⟨(sqEq_padic_of_sqc_eq hp2 ha hpl ?_).trans_eq eL,
      (sqEq_padic_of_sqc_eq hp2 hb hsf1 ?_).trans_eq (by simp)⟩
    · rw [← k1]
    · rw [← k2]; simp
  by_cases hx0 : x = 0
  · -- `(0, 0)` mod `p`: the class `τ₁τ₂ = (3ℓ, −ℓ)`
    rw [kumF_some_of_ne _ hx3, hx0, show (0 : ZMod p) - -3 * L = 3 * L by ring] at k1
    rw [kumF_some_of_ne _ hx1, hx0, zero_sub] at k2
    apply locM_of_torsion h30 hℓ0
    right; right; right
    refine ⟨(sqEq_padic_of_sqc_eq hp2 ha hsf3l ?_).trans_eq (by push_cast; ring),
      (sqEq_padic_of_sqc_eq hp2 hb hsfn ?_).trans_eq (by simp)⟩
    · rw [← k1]; simp [hLdef]
    · rw [← k2]; simp [hLdef]
  -- a non-torsion point of `E_ℓ(𝔽_p)`: lift its abscissa (Hensel)
  rw [kumF_some_of_ne _ hx3, show x - -3 * L = x + 3 * L by ring] at k1
  rw [kumF_some_of_ne _ hx1] at k2
  have hxa : x + 3 * L ≠ 0 := fun h0 => hx3 (by linear_combination h0)
  have hxb : x - L ≠ 0 := sub_ne_zero.mpr hx1
  have heq : y ^ 2 = x * (x - L) * (x + 3 * L) := by
    have := (curveF_equation_iff x y).mp h.1; rw [this]; ring
  have hy : y ≠ 0 := by
    intro h0
    rw [h0] at heq
    have : x * (x - L) * (x + 3 * L) = 0 := by rw [← heq]; ring
    rcases mul_eq_zero.mp this with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact hx0 h''
      · exact hxb h''
    · exact hxa h'
  have k3 : sqc x = sqc ((((a * b : ℤ)) : ZMod p)) := by
    have h1 : sqc x * sqc (x - L) * sqc (x + 3 * L) = 1 := by
      rw [← sqc_mul hx0 hxb, ← sqc_mul (mul_ne_zero hx0 hxb) hxa, ← heq, sqc_sq]
    rw [sqClass_eq_mul_of_mul_mul h1, k1, k2]
    push_cast
    rw [sqc_mul hA hB, mul_comm]
  obtain ⟨X, hX⟩ : ∃ X : ℤ, (X : ZMod p) = x := ⟨x.val, by simp⟩
  have c1 : (((X + 3 * ℓ : ℤ)) : ZMod p) = x + 3 * L := by rw [hLdef]; push_cast; rw [hX]
  have c2 : (((X - ℓ : ℤ)) : ZMod p) = x - L := by rw [hLdef]; push_cast; rw [hX]
  have nd1 : ¬ (p : ℤ) ∣ X + 3 * ℓ := not_dvd_of_zmod_ne_zero (by rw [c1]; exact hxa)
  have nd2 : ¬ (p : ℤ) ∣ X - ℓ := not_dvd_of_zmod_ne_zero (by rw [c2]; exact hxb)
  have nd3 : ¬ (p : ℤ) ∣ X := not_dvd_of_zmod_ne_zero (by rw [hX]; exact hx0)
  have nd4 : ¬ (p : ℤ) ∣ a * b := fun h' => (hqp.dvd_or_dvd h').elim ha hb
  have s1 := sqEq_padic_of_sqc_eq hp2 nd1 ha (by rw [c1]; exact k1)
  have s2 := sqEq_padic_of_sqc_eq hp2 nd2 hb (by rw [c2]; exact k2)
  have s3 := sqEq_padic_of_sqc_eq hp2 nd3 nd4 (by rw [hX]; exact k3)
  have hA0 : (a : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr fun h0 => ha (by rw [h0]; exact dvd_zero _)
  have hB0 : (b : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr fun h0 => hb (by rw [h0]; exact dvd_zero _)
  refine Or.inr ⟨(X : ℚ_[p]), ?_, ?_, ?_⟩
  · have := isSquare_div_of_sqEq hA0 s1; push_cast at this; exact this
  · have := isSquare_div_of_sqEq hB0 s2; push_cast at this; exact this
  · have := isSquare_div_of_sqEq (by push_cast; exact mul_ne_zero hA0 hB0) s3
    push_cast at this; exact this

end Lift

/-- **`LocalGood` holds** (S12 lines 330–347): at `p ∤ 6ℓ` the local image is the unramified
subgroup. -/
theorem localGood : LocalGood := by
  intro ℓ p _ a b _ hp6 ha hb
  exact ⟨localGood_nec hp6 ha hb, fun h => localGood_suff hp6 h.1 h.2⟩

end ZInQ.Manuscript.PoleRC

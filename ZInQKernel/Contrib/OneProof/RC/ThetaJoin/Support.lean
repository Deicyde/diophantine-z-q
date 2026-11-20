import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Schwartz

/-! Rational intersection for the Appendix F weight support, separately from the
fields of `PMLocal`. This file does not use the (O.7) coefficient comparison. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler
open scoped Quaternion

variable {a b : ℚ} {R : Order a b} {O : Type} [CommRing O]

/-- The integral affine generator of the quadratic order (tex 9123–9129). -/
def HalfIntegral (T : Order a b) (x : B a b) : Prop :=
  ∃ t : T.ring, 2 * (t : B a b) - 1 = x

/-- The affine generator as a rational quaternion. -/
def affineGenerator (x : B a b) : B a b := (2⁻¹ : ℚ) • (x + 1)

theorem halfIntegral_iff (T : Order a b) (x : B a b) :
    HalfIntegral T x ↔ affineGenerator x ∈ T.ring := by
  have hd (t : B a b) : (2 : B a b) * t = (2 : ℚ) • t := by
    rw [Algebra.smul_def, map_ofNat]
  have ht : (2 : ℚ) • affineGenerator x = x + 1 := by
    rw [affineGenerator, smul_smul]
    norm_num
  constructor
  · rintro ⟨t, ht'⟩
    have he : (t : B a b) = affineGenerator x := by
      apply smul_right_injective _ (by norm_num : (2 : ℚ) ≠ 0)
      have hz := congrArg (fun y : B a b => y + 1) ht'
      simpa only [sub_add_cancel, ht, hd] using hz
    rw [← he]
    exact t.prop
  · intro hx
    exact ⟨⟨affineGenerator x, hx⟩, by rw [hd, ht, add_sub_cancel_right]⟩

/-- Rational intersection at the chosen adelic representative (tex 9123–9129). -/
theorem halfIntegral_iff_local (ha : a < 0) (hb : b < 0)
    (z : ClassSet R) (x : B a b) :
    HalfIntegral ((representative z).val.leftOrder ha hb) x ↔
      ∀ q : Prime, atRep (classRepresentative z) q (affineGenerator x) ∈ R.completion q.val := by
  rw [halfIntegral_iff]
  change affineGenerator x ∈ (representative z).val.leftRing ↔ _
  rw [← fromAdelic_classRepresentative z]
  exact mem_leftRing_iff (classRepresentative z) (affineGenerator x)

/-- Put together the separate local support tests. The forward implication needs
the local affine membership tests at exceptional primes; the backward implication
additionally uses integrality of the vector itself at every prime. -/
theorem weightAt_support_iff_affine [IsDomain O]
    (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (z : FiniteUnits R) (x : B a b)
    (hBad : ∀ q ∈ A.places, w q (atRep z q x) ≠ 0 ↔
      atRep z q (affineGenerator x) ∈ R.completion q.val)
    (hGood : ∀ q ∉ A.places, atRep z q x ∈ R.completion q.val ↔
      atRep z q (affineGenerator x) ∈ R.completion q.val)
    (hInt : (∀ q : Prime, atRep z q (affineGenerator x) ∈ R.completion q.val) →
      x ∈ (fromAdelic z).val.leftRing) :
    weightAt A w z x ≠ 0 ↔
      ∀ q : Prime, atRep z q (affineGenerator x) ∈ R.completion q.val := by
  classical
  constructor
  · intro hw
    have hx : x ∈ (fromAdelic z).val.leftRing := by
      by_contra hh
      exact hw (ite_eq_right hh)
    have hp : ∏ q ∈ A.places, w q (atRep z q x) ≠ 0 := by
      simpa only [weightAt, ite_eq_left hx] using hw
    intro q
    by_cases hq : q ∈ A.places
    · exact (hBad q hq).mp ((Finset.prod_ne_zero_iff.mp hp) q hq)
    · exact (hGood q hq).mp ((mem_leftRing_iff z x).mp hx q)
  · intro hx
    simpa only [weightAt, ite_eq_left (hInt hx)] using
      Finset.prod_ne_zero_iff.mpr (fun q hq => (hBad q hq).mpr (hx q))

theorem atRep_affine_twice (z : FiniteUnits R) (q : Prime) (x : B a b) :
    2 • atRep z q (affineGenerator x) = atRep z q x + 1 := by
  have h : 2 • affineGenerator x = x + 1 := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, affineGenerator, smul_smul]
    norm_num
  rw [← atRep_nsmul, h]
  unfold atRep
  rw [map_add, map_one, mul_add, mul_one, add_mul, Units.inv_mul]

/-- At an odd place the affine generator is integral exactly when the vector is. -/
theorem affine_mem_at_odd (z : FiniteUnits R) (q : Prime) (hq : q.val ≠ 2) (x : B a b) :
    atRep z q x ∈ R.completion q.val ↔ atRep z q (affineGenerator x) ∈ R.completion q.val := by
  let T := R.completion q.val
  have hd : ¬ q.val ∣ 2 := fun h => hq ((Nat.prime_dvd_prime_iff_eq q.prop Nat.prime_two).mp h)
  let v := PhaseData.natUnit q 2 hd
  constructor
  · intro hx
    have ht := T.add_mem hx T.one_mem
    rw [← atRep_affine_twice, ← Nat.cast_smul_eq_nsmul ℤ_[q.val],
      ← PhaseData.natUnit_val q 2 hd] at ht
    change (v : ℤ_[q.val]) • atRep z q (affineGenerator x) ∈ T.toSubmodule at ht
    have hh := T.toSubmodule.smul_mem ((v⁻¹ : ℤ_[q.val]ˣ) : ℤ_[q.val]) ht
    exact (congrArg (fun y : Bp q.val a b => y ∈ T.toSubmodule)
      (localUnit_smul_cancel q v (atRep z q (affineGenerator x)))).mp hh
  · intro ht
    have he := T.toSubmodule.nsmul_mem ht 2
    rw [atRep_affine_twice] at he
    simpa only [add_sub_cancel_right] using T.sub_mem he T.one_mem

/-- The affine generator belongs to the rational class order on exactly
the support cut out by the placewise tests. -/
theorem weight_support_iff_halfIntegral [IsDomain O]
    (ha : a < 0) (hb : b < 0)
    (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (h₂ : (⟨2, Nat.prime_two⟩ : Prime) ∈ A.places) (i : ClassSet R) (x : B a b)
    (hBad : ∀ q ∈ A.places, w q (atRep (classRepresentative i) q x) ≠ 0 ↔
      atRep (classRepresentative i) q (affineGenerator x) ∈ R.completion q.val) :
    weight A w i x ≠ 0 ↔ HalfIntegral ((representative i).val.leftOrder ha hb) x := by
  rw [halfIntegral_iff_local]
  apply weightAt_support_iff_affine A w _ _ hBad
  · intro q hq
    apply affine_mem_at_odd _ q _ x
    intro he
    have he' : q = (⟨2, Nat.prime_two⟩ : Prime) := Subtype.ext he
    exact hq (he'.symm ▸ h₂)
  · intro hx
    apply (mem_leftRing_iff _ _).mpr
    intro q
    have he := (R.completion q.val).toSubmodule.nsmul_mem (hx q) 2
    rw [atRep_affine_twice] at he
    change atRep (classRepresentative i) q x ∈ R.completion q.val
    simpa only [add_sub_cancel_right] using
      (R.completion q.val).sub_mem he (R.completion q.val).one_mem

section Filtered

variable {ell m N : ℕ} [Fact ell.Prime] (h : ell % 4 = 3) (hN : 0 < N)
variable (C : LevelRoots O N) (hne : 2 * m * N * ell ≠ 0)

/-- Conditions listed in the late request, before imposing the original odd filter. -/
def RequestedIndices (D : ℕ) (k : ℤ) : Prop :=
  0 < D ∧ Squarefree D ∧ D.Coprime m ∧ jacobiSym (D : ℤ) ell = 1 ∧
    (D : ℤ) * -(m : ℤ) = 4 * k + 1 ∧
    Int.ModEq 8 ((D : ℤ) * -(m : ℤ)) 1

/-- The missing level restriction from the odd filter used in tex 9122. -/
def LevelFilter (D : ℕ) : Prop :=
  D.Coprime N ∧ ∀ q, q.Prime → q ≠ 2 → q ∣ N →
    jacobiSym ((D : ℤ) * -(m : ℤ)) q = 1

/-- The exact support comparison on the indices listed in the request.
This proposition is not used as an assumption: without the level filter it
fails (see the report's counterexample). -/
def RequestedSupport : Prop :=
  ∀ (z : ClassSet (levelOrder ell h N hN)) (D : ℕ) (k : ℤ),
    RequestedIndices (ell := ell) (m := m) D k →
    ∀ (x : B (-1) (-(ell : ℚ))), x.re = 0 → Visibility.nrd x = (m * D : ℕ) →
      schwartz h C m hN hne z x ≠ 0 ↔
        HalfIntegral ((representative z).val.leftOrder (by norm_num)
          (neg_lt_zero.mpr (Nat.cast_pos.mpr (Fact.out : ell.Prime).pos))) x

/-- The support statement used for the manuscript's eligible sphere. Any
additional unit-squareclass sieves require their own admissibility tests. -/
def FilteredSupport : Prop :=
  ∀ (z : ClassSet (levelOrder ell h N hN)) (D : ℕ) (k : ℤ),
    RequestedIndices (ell := ell) (m := m) D k → LevelFilter (N := N) (m := m) D →
    ∀ (x : B (-1) (-(ell : ℚ))), x.re = 0 → Visibility.nrd x = (m * D : ℕ) →
      schwartz h C m hN hne z x ≠ 0 ↔
        HalfIntegral ((representative z).val.leftOrder (by norm_num)
          (neg_lt_zero.mpr (Nat.cast_pos.mpr (Fact.out : ell.Prime).pos))) x

end Filtered

end ZInQ.Manuscript.RC.ThetaJoin

import ZInQKernel.Contrib.Mobius.Glue

/-!
# shimura-split, Part 6: `PairsLift` (every QM pair over `ℚ̄` has a level-3 structure) from T5

coarse-factor's `PairsLift` (`∀ Q : QMPair ℚ̄, ∃ P : QML3 ℚ̄, [P.forget] = [Q]`) is the clause "the forgetful
map `Y₃ → X₆` is onto `X₆(ℚ̄)`" of the moduli rows. It is proved here from the kernel's T5
(`ObjBridge.TorsionStructure`, `A(K̄)[n] ≅ (ℤ/n)^{2g}`), which the bundle already carries.

* **Algebra of `𝒪/3𝒪`.** For `a ∈ 𝒪` with `3 ∤ nrd(a)`, `a` has a left inverse modulo `3𝒪` (`nrd(a)·ā`);
  for `3 | nrd(a)`, `a j ∈ 3𝒪` (the kernel's `three_dvd_mulCoord_ej`), so `a = b j` with `b ∈ 𝒪`
  (`j² = −3`).
* **A good point.** Some `v ∈ A(ℚ̄)` has `3v = 0` and `jv ≠ 0`: otherwise `j` kills `A[3]`, so for `9w = 0`,
  `jw ∈ A[3]` and `3w = −j²w = 0`, i.e. `A[9] = A[3]`, against `|A[9]| = 9⁴ > 3⁴ = |A[3]|` (T5; points over
  `ℚ̄` and over its algebraic closure agree, `bcPt_surjective_algClosed`).
* **The level structure** `η(a) = a·v` has kernel exactly `3𝒪`.
-/

set_option linter.all false

noncomputable section

namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV PkgI3 LeafQM.AV.Pin.NormO ObjBridge

/-! ## §1 `𝒪` modulo `3` -/

theorem mulCoord_smul_left (z : ℤ) (m n : Fin 4 → ℤ) :
    mulCoord (fun l => z * m l) n = fun l => z * mulCoord m n l := by
  funext l; fin_cases l <;> simp [mulCoord] <;> ring

theorem sq_sub_one_mod3 (z : ℤ) (h : ¬ (3 : ℤ) ∣ z) : (3 : ℤ) ∣ z ^ 2 - 1 := by
  have h' : (z : ZMod 3) ≠ 0 := fun h0 => h ((ZMod.intCast_zmod_eq_zero_iff_dvd z 3).1 h0)
  have key : ∀ x : ZMod 3, x ≠ 0 → x ^ 2 - 1 = 0 := by decide
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1
  push_cast
  exact key _ h'

theorem coe_three_mul (k : O) : ((3 * k : O) : B) = 3 * (k : B) := by
  push_cast; rfl

/-- **Left inverse modulo `3𝒪`** when `3 ∤ nrd(a)`: `(nrd(a) ā) a = nrd(a)² ≡ 1`. -/
theorem left_inv_mod3 {a : O} {n : Fin 4 → ℤ} (hn : (a : B) = ofInt n) (h : ¬ (3 : ℤ) ∣ nrdZ n) :
    ∃ b k : O, b * a = 1 + 3 * k := by
  obtain ⟨t, ht⟩ := sq_sub_one_mod3 _ h
  refine ⟨⟨ofInt (fun l => nrdZ n * conjC n l), ⟨_, rfl⟩⟩, ⟨ofInt ![t, 0, 0, 0], ⟨_, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  rw [Subring.coe_mul, Subring.coe_add, Subring.coe_one, coe_three_mul, hn]
  change ofInt _ * ofInt n = 1 + 3 * ofInt ![t, 0, 0, 0]
  rw [ofInt_mul, mulCoord_smul_left, mulCoord_conjC', three_mul_ofInt, ← ofInt_one, ofInt_add]
  congr 1
  funext l
  fin_cases l <;> simp <;> linarith

/-- **`a j ∈ 3𝒪` when `3 | nrd(a)`.** -/
theorem mul_oj_of_dvd {a : O} {n : Fin 4 → ℤ} (hn : (a : B) = ofInt n) (h : (3 : ℤ) ∣ nrdZ n) :
    ∃ m : Fin 4 → ℤ, a * oj = 3 * ⟨ofInt m, ⟨m, rfl⟩⟩ := by
  have hd := three_dvd_mulCoord_ej n h
  refine ⟨fun l => mulCoord n ej l / 3, ?_⟩
  apply Subtype.ext
  rw [Subring.coe_mul, coe_three_mul, hn]
  change ofInt n * ofInt ej = 3 * ofInt _
  rw [ofInt_mul, three_mul_ofInt]
  congr 1
  funext l
  exact (Int.mul_ediv_cancel' (hd l)).symm

theorem three_mul_cancel {x y : O} (h : 3 * x = 3 * y) : x = y := by
  apply Subtype.ext
  have h' := congrArg (fun z : O => (z : B)) h
  simp only [coe_three_mul] at h'
  have h3 : (3 : B) = algebraMap ℚ B 3 := by simp
  rw [h3, ← Algebra.smul_def, ← Algebra.smul_def] at h'
  exact smul_right_injective B (by norm_num : (3 : ℚ) ≠ 0) h'


/-! ## §2 Points over `ℚ̄` and over its algebraic closure -/

/-- Over an algebraically closed field, every point over the algebraic closure comes from a point over the
field (`Spec K̄ → Spec K` is an isomorphism). -/
theorem bcPt_surjective_algClosed (A : AbVar Qbar) : Function.Surjective (bcPt A) := by
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Qbar) (K := AlgebraicClosure Qbar)
  let e := RingEquiv.ofBijective (algebraMap Qbar (AlgebraicClosure Qbar)) hbij
  haveI : IsIso (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar))) :=
    (e.toCommRingCatIso).isIso_hom
  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar)))) :=
    inferInstance
  haveI : IsIso (toKbar Qbar) := by
    haveI : IsIso ((Over.forget _).map (toKbar Qbar)) := by
      change IsIso (Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar))))
      infer_instance
    exact isIso_of_reflects_iso _ (Over.forget _)
  intro z
  exact ⟨inv (toKbar Qbar) ≫ z, by simp [bcPt]⟩

theorem bcPt_pow (A : AbVar Qbar) (y : A.Pt Qbar) (n : ℕ) : bcPt A (y ^ n) = bcPt A y ^ n := by
  rw [bcPt, bcPt, MonObj.comp_pow]

theorem bcPt_one (A : AbVar Qbar) : bcPt A 1 = 1 := by
  rw [bcPt]; exact MonObj.comp_one _

/-! ## §3 A point killed by `3` and not by `j` -/

theorem act_three {A : AbVar Qbar} (q : QMStr A) (v : Additive (A.Pt Qbar)) :
    qmAct q Qbar 3 v = 3 • v := by
  rw [map_ofNat]; rfl

theorem act_mul {A : AbVar Qbar} (q : QMStr A) (a b : O) (v : Additive (A.Pt Qbar)) :
    qmAct q Qbar (a * b) v = qmAct q Qbar a (qmAct q Qbar b v) := by
  rw [map_mul]; rfl

/-- **Some `v ∈ A(ℚ̄)` has `3v = 0` and `jv ≠ 0`** (T5). -/
theorem exists_good_point (hT : ObjBridge.TorsionStructure) (Q : QMPair Qbar) :
    ∃ v : Additive (Q.A.Pt Qbar), 3 • v = 0 ∧ qmAct Q.q Qbar oj v ≠ 0 := by
  by_contra H
  push Not at H
  set act := qmAct Q.q Qbar with hact
  -- `A[9] = A[3]`
  have h9 : ∀ w : Additive (Q.A.Pt Qbar), 9 • w = 0 → 3 • w = 0 := by
    intro w hw
    have h1 : act oj (3 • w) = 0 := H _ (by rw [← mul_nsmul']; exact hw)
    rw [map_nsmul] at h1
    have h2 : act oj (act oj w) = 0 := H _ h1
    have h3 : act (oj * oj) w = -(act 3 w) := by rw [oj_mul_oj, map_neg]; rfl
    rw [← act_mul, h3, act_three, neg_eq_zero] at h2
    exact h2
  -- counting with T5 over `ℚ̄̄`
  have hdim : ObjBridge.dim (toGrp Q.A) = ((2 : ℕ) : WithBot ℕ∞) := by
    change Q.A.dim = _
    rw [Q.surface]; rfl
  obtain ⟨e3, -⟩ := hT Qbar (toGrp Q.A) 2 3 hdim (by norm_num) (Nat.cast_ne_zero.mpr (by norm_num))
  obtain ⟨e9, -⟩ := hT Qbar (toGrp Q.A) 2 9 hdim (by norm_num) (Nat.cast_ne_zero.mpr (by norm_num))
  have hsub : ∀ x : PkgI2.Pts (toGrp Q.A) (AlgebraicClosure Qbar), x ^ 9 = 1 → x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, rfl⟩ := bcPt_surjective_algClosed Q.A x
    rw [← bcPt_pow] at hx ⊢
    rw [← bcPt_one] at hx ⊢
    have hy9 : y ^ 9 = 1 := bcPt_injective Q.A hx
    have hy3 : 3 • Additive.ofMul y = 0 := h9 _ (by rw [← ofMul_pow, hy9]; rfl)
    rw [← ofMul_pow] at hy3
    exact congrArg (bcPt Q.A) (Additive.ofMul.injective (hy3.trans ofMul_one.symm))
  let f : PkgI2.torsion (toGrp Q.A) (AlgebraicClosure Qbar) 9 →
      PkgI2.torsion (toGrp Q.A) (AlgebraicClosure Qbar) 3 := fun x => ⟨x.1, hsub x.1 x.2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have := congrArg (fun z : PkgI2.torsion (toGrp Q.A) (AlgebraicClosure Qbar) 3 =>
      (z : PkgI2.Pts (toGrp Q.A) (AlgebraicClosure Qbar))) h
    exact this
  haveI : Finite (PkgI2.torsion (toGrp Q.A) (AlgebraicClosure Qbar) 3) := Finite.of_equiv _ e3.symm
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_congr e9, Nat.card_congr e3] at hle
  simp at hle


/-! ## §4 The level structure `η(a) = a·v` -/

/-- If `3v = 0` and `jv ≠ 0`, then `a·v = 0` only for `a ∈ 3𝒪`. -/
theorem ker_of_good {A : AbVar Qbar} (q : QMStr A) (v : Additive (A.Pt Qbar)) (h3 : 3 • v = 0)
    (hj : qmAct q Qbar oj v ≠ 0) (a : O) (ha : qmAct q Qbar a v = 0) : ∃ b : O, a = 3 * b := by
  set act := qmAct q Qbar with hact
  -- an element with a left inverse modulo `3` kills only what it kills times a unit
  have unit_kill : ∀ (b c k : O) (w : Additive (A.Pt Qbar)), c * b = 1 + 3 * k → 3 • w = 0 →
      act b w = 0 → w = 0 := by
    intro b c k w hcb hw hb
    have e : act (c * b) w = act (1 + 3 * k) w := by rw [hcb]
    rw [act_mul, hb, map_zero, map_add, map_one] at e
    have e2 : act (3 * k) w = 0 := by
      rw [show (3 : O) * k = k * 3 from ((Nat.cast_commute 3 k).eq), act_mul, act_three, hw, map_zero]
    change (0 : Additive (A.Pt Qbar)) = w + act (3 * k) w at e
    rw [e2, add_zero] at e
    exact e.symm
  have h3j : 3 • act oj v = 0 := by rw [← map_nsmul, h3, map_zero]
  obtain ⟨n, hn⟩ := a.2
  by_cases hd : (3 : ℤ) ∣ nrdZ n
  · obtain ⟨m, hm⟩ := mul_oj_of_dvd hn hd
    set k : O := ⟨ofInt m, ⟨m, rfl⟩⟩
    -- `a = (-k) j`
    have hak : a = -k * oj := by
      apply three_mul_cancel
      have e : a * oj * oj = 3 * k * oj := by rw [hm]
      rw [_root_.mul_assoc, oj_mul_oj] at e
      calc 3 * a = -(a * -3) := by noncomm_ring
        _ = -(3 * k * oj) := by rw [e]
        _ = 3 * (-k * oj) := by noncomm_ring
    have hkn : ((-k : O) : B) = ofInt (-m) := by
      rw [Subring.coe_neg, ← ofInt_neg]
    by_cases hd' : (3 : ℤ) ∣ nrdZ (-m)
    · obtain ⟨m', hm'⟩ := mul_oj_of_dvd hkn hd'
      exact ⟨_, hak.trans hm'⟩
    · obtain ⟨c, k', hck⟩ := left_inv_mod3 hkn hd'
      exfalso
      apply hj
      refine unit_kill (-k) c k' (act oj v) hck h3j ?_
      rw [← act_mul, ← hak]; exact ha
  · obtain ⟨c, k', hck⟩ := left_inv_mod3 hn hd
    exfalso
    apply hj
    rw [unit_kill a c k' v hck h3 ha, map_zero]

/-- **A level-3 structure on a QM pair over `ℚ̄`** (T5). -/
theorem exists_level3 (hT : ObjBridge.TorsionStructure) (Q : QMPair Qbar) : Nonempty (Level3 Q.q) := by
  obtain ⟨v, h3, hj⟩ := exists_good_point hT Q
  refine ⟨{ eta := ?_, linear := ?_, ker := ?_ }⟩
  · exact { toFun := fun a => qmAct Q.q Qbar a v, map_zero' := by simp,
            map_add' := fun a b => by rw [map_add]; rfl }
  · intro a b
    exact act_mul Q.q a b v
  · intro a
    constructor
    · exact ker_of_good Q.q v h3 hj a
    · rintro ⟨b, rfl⟩
      change qmAct Q.q Qbar (3 * b) v = 0
      rw [show (3 : O) * b = b * 3 from ((Nat.cast_commute 3 b).eq), act_mul, act_three, h3, map_zero]

/-- **coarse-factor's `PairsLift` from T5** (the body of `HDec.QMSplit.Moduli.PairsLift`, verbatim). -/
theorem pairsLift_of_T5 (hT : ObjBridge.TorsionStructure) :
    ∀ Q : QMPair Qbar, ∃ P : QML3 Qbar, Quotient.mk (pairSetoid Qbar) P.forget = Quotient.mk _ Q := by
  intro Q
  obtain ⟨e⟩ := exists_level3 hT Q
  exact ⟨⟨Q.A, Q.surface, Q.q, e⟩, rfl⟩

end ShimuraSplit

#print axioms ShimuraSplit.pairsLift_of_T5

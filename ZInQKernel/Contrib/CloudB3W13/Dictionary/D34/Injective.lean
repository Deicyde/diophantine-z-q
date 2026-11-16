/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D34.Basic

/-!
# W13 dictionary D3/D4, part 2: injectivity of `𝒪 → End_K(A)` from the level structure

Suppose `act (toΛ 3)` (multiplication by `3`) is dominant; part 3 proves this from étaleness. Then
`End_K(A)` has no `3`-torsion along the image of `iota`, by Mathlib's
`ext_of_isDominant_of_isSeparated` (`A` reduced, `A → Spec K` separated). If `iota c = 0`, then
`c · P = 0`, so `c ∈ 3𝒪` (`FullLevel.annihilator`, `mem_three_of_ptHom_eq_one`), and `c = 3 c'`
with `iota c' = 0`. Hence `c ∈ 3^k 𝒪` for every `k`, and `c = 0` because the coordinates of `𝒪`
lie in `½ℤ`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D34

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped Quaternion CategoryTheory.MonObj
open ZInQ.Contrib.CloudW03NeronSurj ZInQ.Contrib.CloudW03NeronSurj.FLT
open ZInQ.Contrib.CloudB2Shimura.Dictionary

section Arithmetic

lemma coe_three_pow_mul (k : ℕ) (d : LeafQM.O) :
    (((3 : LeafQM.O) ^ k * d : LeafQM.O) : ℍ[ℚ, 2, -3]) = ((3 : ℚ) ^ k) • (d : ℍ[ℚ, 2, -3]) := by
  rw [Algebra.smul_def, map_pow, map_ofNat]
  push_cast
  rw [show ((3 : LeafQM.O) : ℍ[ℚ, 2, -3]) = 3 from map_ofNat LeafQM.O.subtype 3]

lemma two_mul_components (d : LeafQM.O) :
    (∃ z : ℤ, 2 * (d : ℍ[ℚ, 2, -3]).re = z) ∧ (∃ z : ℤ, 2 * (d : ℍ[ℚ, 2, -3]).imI = z) ∧
      (∃ z : ℤ, 2 * (d : ℍ[ℚ, 2, -3]).imJ = z) ∧ (∃ z : ℤ, 2 * (d : ℍ[ℚ, 2, -3]).imK = z) := by
  obtain ⟨n, hn⟩ := d.2
  have hn' : (d : ℍ[ℚ, 2, -3]) = LeafQM.ofInt n := hn
  refine ⟨⟨2 * n 0 + n 2, ?_⟩, ⟨2 * n 1 + n 3, ?_⟩, ⟨n 2, ?_⟩, ⟨n 3, ?_⟩⟩ <;>
    rw [hn'] <;> simp [LeafQM.ofInt] <;> ring

lemma comp_eq_zero_of_forall (c : LeafQM.O) (H : ∀ k : ℕ, ∃ d : LeafQM.O, c = 3 ^ k * d)
    (π : ℍ[ℚ, 2, -3] → ℚ) (hπ : ∀ (r : ℚ) (x : ℍ[ℚ, 2, -3]), π (r • x) = r * π x)
    (hint : ∀ d : LeafQM.O, ∃ z : ℤ, 2 * π d = z) : π c = 0 := by
  obtain ⟨m, hm⟩ := hint c
  have hdvd : ∀ k : ℕ, (3 : ℤ) ^ k ∣ m := by
    intro k
    obtain ⟨d, hd⟩ := H k
    obtain ⟨z, hz⟩ := hint d
    refine ⟨z, ?_⟩
    have h1 : (m : ℚ) = 3 ^ k * z := by
      rw [← hm, ← hz, hd, coe_three_pow_mul, hπ]
      ring
    exact_mod_cast h1
  have hm0 : m = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd m.natAbs)
    rw [Int.natAbs_pow]
    exact Nat.lt_pow_self (by norm_num)
  rw [hm0, Int.cast_zero] at hm
  linarith

/-- An element of `𝒪` divisible by every power of `3` is zero. -/
lemma eq_zero_of_forall_three_pow (c : LeafQM.O) (H : ∀ k : ℕ, ∃ d : LeafQM.O, c = 3 ^ k * d) :
    c = 0 := by
  apply Subtype.ext
  change (c : ℍ[ℚ, 2, -3]) = 0
  ext
  · exact comp_eq_zero_of_forall c H _ (fun r x => by rw [QuaternionAlgebra.re_smul, smul_eq_mul])
      (fun d => (two_mul_components d).1)
  · exact comp_eq_zero_of_forall c H _ (fun r x => by rw [QuaternionAlgebra.imI_smul, smul_eq_mul])
      (fun d => (two_mul_components d).2.1)
  · exact comp_eq_zero_of_forall c H _ (fun r x => by rw [QuaternionAlgebra.imJ_smul, smul_eq_mul])
      (fun d => (two_mul_components d).2.2.1)
  · exact comp_eq_zero_of_forall c H _ (fun r x => by rw [QuaternionAlgebra.imK_smul, smul_eq_mul])
      (fun d => (two_mul_components d).2.2.2)

end Arithmetic

section Injective

variable {K : Type} [Field K] (u : FLTL3 K) (h : AbVarProps u.1)

/-- `iota c = 0` forces `c · P = 0`, hence `c ∈ 3𝒪`. -/
lemma mem_three_of_iota_eq_zero (c : LeafQM.O) (hc : iota u.1 h c = 0) :
    ∃ b : LeafQM.O, c = 3 * b := by
  apply mem_three_of_ptHom_eq_one u c
  letI := u.1.L.grpObjOverMk
  have e := ptHom_mul u c 1
  rw [mul_one] at e
  have h1 : actHom u.1 (toΛ c) = 1 := congrArg PkgI3.AbVar.Hom.hom hc
  rw [e, h1, MonObj.comp_one]

lemma isIntegral_A (h : AbVarProps u.1) : IsIntegral u.1.A :=
  haveI : GeometricallyIntegral (Over.mk u.1.f).hom := h.2.2
  GeometricallyIntegral.isIntegral_of_subsingleton (Over.mk u.1.f).hom

/-- No `3`-torsion along `iota`, given that multiplication by `3` is dominant. -/
lemma iota_eq_zero_of_three_mul [IsDominant (u.1.act (toΛ 3))] (c : LeafQM.O)
    (hc : iota u.1 h (3 * c) = 0) : iota u.1 h c = 0 := by
  haveI : IsIntegral (Over.mk u.1.f).left := isIntegral_A u h
  haveI : IsProper u.1.f := h.1
  letI := u.1.L.grpObjOverMk
  have hcomm : (3 : LeafQM.O) * c = c * 3 := (Nat.cast_commute 3 c).eq
  rw [hcomm, map_mul] at hc
  have h1 := congrArg PkgI3.AbVar.Hom.hom hc
  change actHom u.1 (toΛ 3) ≫ actHom u.1 (toΛ c) = 1 at h1
  apply PkgI3.AbVar.Hom.ext'
  change actHom u.1 (toΛ c) = (1 : Over.mk u.1.f ⟶ Over.mk u.1.f)
  apply Over.OverMorphism.ext
  refine ext_of_isDominant_of_isSeparated u.1.f ?_ (u.1.act (toΛ 3)) ?_
  · rw [actHom_left, u.1.act_over]
    exact (Over.w (1 : Over.mk u.1.f ⟶ Over.mk u.1.f)).symm
  · have h2 := congrArg CommaMorphism.left h1
    have h3 : actHom u.1 (toΛ 3) ≫ (1 : Over.mk u.1.f ⟶ Over.mk u.1.f) = 1 := MonObj.comp_one _
    have h4 := congrArg CommaMorphism.left h3
    simp only [Over.comp_left, actHom_left] at h2 h4
    exact h2.trans h4.symm

/-- **The action `𝒪 → End_K(A)` is injective** (given that multiplication by `3` is dominant). -/
lemma iota_injective [IsDominant (u.1.act (toΛ 3))] : Function.Injective (iota u.1 h) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have key : ∀ k : ℕ, ∃ d : LeafQM.O, c = 3 ^ k * d ∧ iota u.1 h d = 0 := by
    intro k
    induction k with
    | zero => exact ⟨c, by simp, hc⟩
    | succ k ih =>
      obtain ⟨d, hd, hd0⟩ := ih
      obtain ⟨b, rfl⟩ := mem_three_of_iota_eq_zero u h d hd0
      exact ⟨b, by rw [hd, pow_succ, mul_assoc], iota_eq_zero_of_three_mul u h b hd0⟩
  exact eq_zero_of_forall_three_pow c (fun k => (key k).imp fun _ hd => hd.1)

end Injective

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D34

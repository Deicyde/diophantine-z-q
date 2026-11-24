import ZInQKernel.Contrib.CloudR2CM.SerreTate.NOSAdapter
import ZInQKernel.Contrib.CloudR2CM.SerreTate.RigidityProof
import ZInQKernel.Contrib.AbVarBC.Main
import ZInQKernel.Contrib.AbVarBC.Torsion
import ZInQKernel.Contrib.OneProof.NeronOggShafarevich
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# P3: the adapter to the converse of the Néron–Ogg–Shafarevich criterion

* `exists_pow_eq_of_charZero`: in characteristic `0`, `A(K̄)` is `ℓ`-divisible. Multiplication by
  `ℓ` is finite and surjective (`ZInQ.Contrib.AbVarBC.mulIsogeny`); the fibre over a point `y` is
  a nonempty finite `K̄`-scheme, and a point of it over its residue field descends to a
  `K̄`-point (`ZInQ.Contrib.AbVarBC.exists_lift_of_isFinite`).
* `exists_tate_coord_eq`: every point of `A(K̄)` killed by `ℓⁿ` is the `n`-th coordinate of an
  element of `T_ℓ(A)` (successive `ℓ`-th roots).
* `p3ConverseInput_proof`: `P3ConverseInput`. If inertia acts trivially on `T_ℓ(A)`, it fixes
  every `A(K̄)[ℓⁿ]`, and the powers `ℓⁿ⁺¹` form an infinite set of integers invertible at `O`.
* `p3GoodReduction_of_converse`: **conditional**. `P3GoodReduction` from `P3ConverseInput` and the
  converse of the criterion, `NOSProof.NOSConverseSep`, which is an explicit premise here (a
  statement, not a proof).
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace HDec.CMSerreTate

section Divisibility

variable {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)

/-- **Divisibility of `A(K̄)` in characteristic `0`.** -/
theorem exists_pow_eq_of_charZero [CharZero K] (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (y : A.Pt (AlgebraicClosure K)) : ∃ z : A.Pt (AlgebraicClosure K), z ^ ℓ = y := by
  obtain ⟨hfin, hsurj⟩ := _root_.ZInQ.Contrib.AbVarBC.mulIsogeny K A ((ℓ : ℕ) : ℤ)
    (by exact_mod_cast hℓ)
  let fN : A.X.left ⟶ A.X.left := ((((ℓ : ℕ) : ℤ) : _root_.PkgI3.AbVar.End A)).hom.left
  haveI : IsFinite fN := hfin
  have hw : fN ≫ A.X.hom = A.X.hom :=
    Over.w ((((ℓ : ℕ) : ℤ) : _root_.PkgI3.AbVar.End A)).hom
  let y₀ : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ A.X.left := y.left
  have hy₀ : y₀ ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) :=
    Over.w y
  haveI : IsFinite (pullback.snd fN y₀) := inferInstance
  obtain ⟨a, ha⟩ := hsurj.surj (y₀ (IsLocalRing.closedPoint (AlgebraicClosure K)))
  obtain ⟨zp, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := fN) (g := y₀) a
    (IsLocalRing.closedPoint (AlgebraicClosure K)) ha
  letI : Algebra (AlgebraicClosure K) ((pullback fN y₀).residueField zp) :=
    (Spec.preimage ((pullback fN y₀).fromSpecResidueField zp ≫
      pullback.snd fN y₀)).hom.toAlgebra
  have hq : (pullback fN y₀).fromSpecResidueField zp ≫ pullback.snd fN y₀ =
      Spec.map (CommRingCat.ofHom
        (algebraMap (AlgebraicClosure K) ((pullback fN y₀).residueField zp))) :=
    (Spec.map_preimage _).symm
  have hlift := _root_.ZInQ.Contrib.AbVarBC.exists_lift_of_isFinite
    (Algebra.ofId (AlgebraicClosure K) ((pullback fN y₀).residueField zp))
    (pullback.snd fN y₀) ((pullback fN y₀).fromSpecResidueField zp) hq
  obtain ⟨p, -, hp⟩ := hlift
  have hp' : p ≫ pullback.snd fN y₀ = 𝟙 _ := by
    rw [hp, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hsq : (p ≫ pullback.fst fN y₀) ≫ fN = y₀ := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp', Category.id_comp]
  have hw0 : (p ≫ pullback.fst fN y₀) ≫ A.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) := by
    rw [← hw, ← Category.assoc, hsq, hy₀]
  refine ⟨Over.homMk (p ≫ pullback.fst fN y₀) hw0, ?_⟩
  rw [← _root_.ZInQ.Contrib.AbVarBC.comp_natCast_hom A]
  apply Over.OverMorphism.ext
  exact hsq

/-- **Torsion points are coordinates of the Tate module.** A point of `A(K̄)` killed by `ℓⁿ` is
the `n`-th coordinate of an element of `T_ℓ(A)`. -/
theorem exists_tate_coord_eq [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (x : A.Pt (AlgebraicClosure K)) (hx : x ^ (ℓ ^ n) = 1) :
    ∃ t : _root_.ReductSplit.TΩ A (AlgebraicClosure K) ℓ, t.1 n = Additive.ofMul x := by
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  choose r hr using fun y : A.Pt (AlgebraicClosure K) => exists_pow_eq_of_charZero A ℓ hℓ y
  let s : ℕ → A.Pt (AlgebraicClosure K) := fun j =>
    Nat.rec (motive := fun _ => A.Pt (AlgebraicClosure K)) x (fun _ y => r y) j
  have hs0 : s 0 = x := rfl
  have hs : ∀ j : ℕ, s (j + 1) ^ ℓ = s j := fun j => hr (s j)
  have hpow : ∀ j : ℕ, s j ^ (ℓ ^ j) = x := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_one, hs0]
    | succ j ih => rw [pow_succ', pow_mul, hs, ih]
  refine ⟨⟨fun j => Additive.ofMul (s j ^ (ℓ ^ n)), ?_, ?_⟩, ?_⟩
  · show Additive.ofMul (s 0 ^ (ℓ ^ n)) = 0
    rw [hs0, hx]
    rfl
  · intro j
    show ℓ • Additive.ofMul (s (j + 1) ^ (ℓ ^ n)) = Additive.ofMul (s j ^ (ℓ ^ n))
    rw [← ofMul_pow, ← pow_mul, mul_comm, pow_mul, hs]
  · show Additive.ofMul (s n ^ (ℓ ^ n)) = Additive.ofMul x
    rw [hpow]

end Divisibility

/-- **P3, the adapter to the converse's input.** -/
theorem p3ConverseInput_proof : P3ConverseInput := by
  intro K _ _ O _ w hw A ℓ _ hℓ htriv
  have hfix : ∀ n : ℕ, ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      _root_.PkgI2.IsInertia w σ → ∀ x : A.Pt (AlgebraicClosure K), x ^ (ℓ ^ n) = 1 →
        A.galAct σ x = x := by
    intro n σ hσ x hx
    obtain ⟨t, ht⟩ := exists_tate_coord_eq A ℓ n x hx
    have h : (_root_.ReductSplit.galTΩ A ℓ σ t).1 n = t.1 n :=
      congrArg (fun u : _root_.ReductSplit.TΩ A (AlgebraicClosure K) ℓ => u.1 n) (htriv σ hσ t)
    rw [galTΩ_apply_coord, ht, toMul_ofMul] at h
    exact Additive.ofMul.injective h
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ℓ ^ (n + 1))
    ((Nat.pow_right_injective (Fact.out : ℓ.Prime).two_le).comp Nat.succ_injective) ?_
  intro n
  show 0 < ℓ ^ (n + 1) ∧ IsUnit ((ℓ ^ (n + 1) : ℕ) : O) ∧
    _root_.PkgI2.InertiaTrivialOn (_root_.ObjBridge.toGrp A) w (ℓ ^ (n + 1))
  refine ⟨pow_pos (Fact.out : ℓ.Prime).pos _, ?_, ?_⟩
  · rw [Nat.cast_pow]
    exact hℓ.pow _
  · intro σ hσ x hx
    exact hfix (n + 1) σ hσ x hx

/-- **P3, good reduction at one place, CONDITIONAL** on the converse of the criterion of
Néron–Ogg–Shafarevich, `NOSProof.NOSConverseSep`, which is an explicit premise (a statement, not
a proof). It is applied at `K_s = K̄` (a number field is perfect) to `ObjBridge.toGrp A`. -/
theorem p3GoodReduction_of_converse (hconv : _root_.NOSProof.NOSConverseSep) :
    P3GoodReduction := by
  intro K _ _ O _ w hw A ℓ _ hℓ htriv
  exact hconv K O (AlgebraicClosure K) w hw (_root_.ObjBridge.toGrp A)
    (p3ConverseInput_proof K O w hw A ℓ hℓ htriv)

end HDec.CMSerreTate

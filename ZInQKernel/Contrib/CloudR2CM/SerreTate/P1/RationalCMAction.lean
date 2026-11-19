import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.CompletedTateAction
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.CMOrderRationalization
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The full faithful quadratic tensor action on the original Tate space

The completed integral End action is rationalized on every tensor. Exact
scalar-cancellation comparisons identify it with the original rational
End action. The actual order equivalence then gives the full quadratic
algebra action, preserving all factors at split primes.
-/

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj TensorProduct

namespace HDec.CMSerreTate.P1

/-- The original base-End action on the original rational Tate module. -/
def rationalEndIntAlgHom {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] : _root_.PkgI3.AbVar.End A →ₐ[ℤ] Module.End ℚ_[ℓ] (A.V ℓ) :=
  ((_root_.Module.End.baseChangeHom ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ)).restrictScalars ℤ).comp
    (tateEndIntAlgHom A ℓ)

/-- Direct rational scalar extension of the same End-ring action. -/
def directRationalEndAction {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] : ℚ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A →ₐ[ℚ_[ℓ]]
      Module.End ℚ_[ℓ] (A.V ℓ) :=
  (AlgHom.liftEquiv ℤ ℚ_[ℓ] (_root_.PkgI3.AbVar.End A) (Module.End ℚ_[ℓ] (A.V ℓ)))
    (rationalEndIntAlgHom A ℓ)

theorem directRationalEndAction_tmul {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (a : ℚ_[ℓ]) (f : _root_.PkgI3.AbVar.End A) :
    directRationalEndAction A ℓ (a ⊗ₜ[ℤ] f) =
      a • (_root_.PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ] := rfl

/-- The actual rational End ring acting on the actual rational Tate space. -/
def rationalEndAction {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] : A.End0 →ₐ[ℚ] Module.End ℚ_[ℓ] (A.V ℓ) :=
  (AlgHom.liftEquiv ℤ ℚ (_root_.PkgI3.AbVar.End A) (Module.End ℚ_[ℓ] (A.V ℓ)))
    (rationalEndIntAlgHom A ℓ)

theorem rationalEndAction_tmul {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ) (f : _root_.PkgI3.AbVar.End A) :
    rationalEndAction A ℓ (q ⊗ₜ[ℤ] f) =
      q • (_root_.PkgI3.AbVar.homT (ℓ := ℓ) f).baseChange ℚ_[ℓ] := rfl

/-- Scalar extension of the full rational End ring. -/
def rationalEndCompletionAction {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] : ℚ_[ℓ] ⊗[ℚ] A.End0 →ₐ[ℚ_[ℓ]] Module.End ℚ_[ℓ] (A.V ℓ) :=
  (AlgHom.liftEquiv ℚ ℚ_[ℓ] A.End0 (Module.End ℚ_[ℓ] (A.V ℓ))) (rationalEndAction A ℓ)

theorem rationalEndCompletionAction_tmul {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (a : ℚ_[ℓ]) (x : A.End0) :
    rationalEndCompletionAction A ℓ (a ⊗ₜ[ℚ] x) = a • rationalEndAction A ℓ x := rfl

/-- Exact cancellation of the integral intermediate scalar ring. -/
def completionCancel {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A) ≃ₗ[ℚ_[ℓ]]
      ℚ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ]
    (_root_.PkgI3.AbVar.End A)

/-- Exact cancellation of the rational intermediate scalar field. -/
def rationalCancel {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] : ℚ_[ℓ] ⊗[ℚ] A.End0 ≃ₗ[ℚ_[ℓ]]
      ℚ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℚ_[ℓ] ℚ_[ℓ]
    (_root_.PkgI3.AbVar.End A)

/-- The faithful integral completion gives the very same direct rational
End action after exact scalar cancellation. -/
theorem rationalCompletedEndAction_eq_direct {K : Type} [Field K]
    (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (x : ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A)) :
    rationalCompletedEndAction A ℓ x = directRationalEndAction A ℓ (completionCancel A ℓ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction x using TensorProduct.inductionOn with
      | tmul z f =>
          simp only [rationalCompletedEndAction_tmul, tateEndCompleted_tmul,
            completionCancel, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            directRationalEndAction_tmul, LinearMap.baseChange_smul]
          rw [smul_comm a z, smul_assoc]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The rational End completion agrees with that same faithful action. -/
theorem rationalEndCompletionAction_eq_direct {K : Type} [Field K]
    (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (x : ℚ_[ℓ] ⊗[ℚ] A.End0) :
    rationalEndCompletionAction A ℓ x = directRationalEndAction A ℓ (rationalCancel A ℓ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction x using TensorProduct.inductionOn with
      | tmul q f =>
          simp only [rationalEndCompletionAction_tmul, rationalEndAction_tmul,
            rationalCancel, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            directRationalEndAction_tmul]
          rw [smul_comm a q, smul_assoc]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Faithfulness of the whole direct rationalized End action. -/
theorem directRationalEndAction_injective {K : Type} [Field K] [NumberField K]
    (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    Function.Injective (directRationalEndAction A ℓ) := by
  intro x y hxy
  apply (completionCancel A ℓ).symm.injective
  apply rationalCompletedEndAction_injective A ℓ hℓ
  simpa only [rationalCompletedEndAction_eq_direct, LinearEquiv.apply_symm_apply] using hxy

/-- Faithfulness of the entire completed rational End algebra, not only
of the original field elements before completion. -/
theorem rationalEndCompletionAction_injective {K : Type} [Field K] [NumberField K]
    (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    Function.Injective (rationalEndCompletionAction A ℓ) := by
  intro x y hxy
  apply (rationalCancel A ℓ).injective
  apply directRationalEndAction_injective A ℓ hℓ
  simpa only [rationalEndCompletionAction_eq_direct] using hxy

/-- The whole Galois image commutes with every element of the faithful
rationalized integral completion. -/
theorem galRep_commute_completed {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K)
    (x : ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A)) :
    Commute (A.galRep ℓ σ) (rationalCompletedEndAction A ℓ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      rw [rationalCompletedEndAction_tmul]
      have hc := (galT_commute_completed A ℓ σ x).map
        (_root_.Module.End.baseChangeHom ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ)).toRingHom
      change Commute ((A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ])
        ((tateEndCompleted A ℓ x).baseChange ℚ_[ℓ]) at hc
      change (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ] *
          (a • (tateEndCompleted A ℓ x).baseChange ℚ_[ℓ]) =
        (a • (tateEndCompleted A ℓ x).baseChange ℚ_[ℓ]) *
          (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ]
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hc.eq]
  | add x y hx hy =>
      change A.galRep ℓ σ * rationalCompletedEndAction A ℓ (x + y) =
        rationalCompletedEndAction A ℓ (x + y) * A.galRep ℓ σ
      rw [map_add, mul_add, add_mul, hx.eq, hy.eq]

/-- Whole-image commutation with the direct rational End algebra. -/
theorem galRep_commute_direct {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K)
    (x : ℚ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A) :
    Commute (A.galRep ℓ σ) (directRationalEndAction A ℓ x) := by
  have h := galRep_commute_completed A ℓ σ ((completionCancel A ℓ).symm x)
  simpa only [rationalCompletedEndAction_eq_direct, LinearEquiv.apply_symm_apply] using h

/-- Whole-image commutation with every completed rational End element. -/
theorem galRep_commute_rationalEndCompletion {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K) (x : ℚ_[ℓ] ⊗[ℚ] A.End0) :
    Commute (A.galRep ℓ σ) (rationalEndCompletionAction A ℓ x) := by
  simpa only [rationalEndCompletionAction_eq_direct] using
    galRep_commute_direct A ℓ σ (rationalCancel A ℓ x)

/-- The actual full quadratic tensor algebra action, through the actual
End/order/field identification. No split factor is discarded. -/
def cmTensorAction {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type} [Field k] [NumberField k] (R : Subring k)
    (e : _root_.PkgI3.AbVar.End A ≃+* R) (hR : HDec.CMBranch.IsImagQuadOrder k R) :
    ℚ_[ℓ] ⊗[ℚ] k →ₐ[ℚ_[ℓ]] Module.End ℚ_[ℓ] (A.V ℓ) :=
  (rationalEndCompletionAction A ℓ).comp
    (_root_.Algebra.TensorProduct.congr (AlgEquiv.refl : ℚ_[ℓ] ≃ₐ[ℚ_[ℓ]] ℚ_[ℓ])
      (end0OrderEquiv A R e hR).symm).toAlgHom

/-- Faithfulness of the whole quadratic tensor action, including at
split primes, derived from the original completed Hom injection. -/
theorem cmTensorAction_injective {K : Type} [Field K] [NumberField K]
    (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0)
    {k : Type} [Field k] [NumberField k] (R : Subring k)
    (e : _root_.PkgI3.AbVar.End A ≃+* R) (hR : HDec.CMBranch.IsImagQuadOrder k R) :
    Function.Injective (cmTensorAction A ℓ R e hR) :=
  (rationalEndCompletionAction_injective A ℓ hℓ).comp
    (_root_.Algebra.TensorProduct.congr (AlgEquiv.refl : ℚ_[ℓ] ≃ₐ[ℚ_[ℓ]] ℚ_[ℓ])
      (end0OrderEquiv A R e hR).symm).injective

/-- The original whole Galois image commutes with the entire full
quadratic tensor algebra, not merely with inertia or one field embedding. -/
theorem galRep_commute_cmTensor {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type} [Field k] [NumberField k] (R : Subring k)
    (e : _root_.PkgI3.AbVar.End A ≃+* R) (hR : HDec.CMBranch.IsImagQuadOrder k R)
    (σ : Field.absoluteGaloisGroup K) (x : ℚ_[ℓ] ⊗[ℚ] k) :
    Commute (A.galRep ℓ σ) (cmTensorAction A ℓ R e hR x) :=
  galRep_commute_rationalEndCompletion A ℓ σ
    ((_root_.Algebra.TensorProduct.congr (AlgEquiv.refl : ℚ_[ℓ] ≃ₐ[ℚ_[ℓ]] ℚ_[ℓ])
      (end0OrderEquiv A R e hR).symm) x)

end HDec.CMSerreTate.P1

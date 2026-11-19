import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.OriginalTateGeometry
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.TateRationalComparison
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# The faithful completed action of original endomorphisms

The unital multiplicative action is the original Hom action on the
original Tate module. Its completion agrees on every tensor with the
original completed Hom map. Rational faithfulness is proved on the whole
localization, not only on simple tensors or one scalar-field embedding.
-/

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj TensorProduct

open CategoryTheory

namespace HDec.CMSerreTate.P1

/-- The original action of base-field endomorphisms, with its actual
composition order, as a unital ring homomorphism. -/
def tateEndRingHom {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] : _root_.PkgI3.AbVar.End A →+* Module.End ℤ_[ℓ] (A.T ℓ) :=
  { _root_.PkgI3.AbVar.tateHom ℓ A A with
    map_one' := by
      apply LinearMap.ext
      intro t
      apply Subtype.ext
      funext n
      change Additive.ofMul (Additive.toMul (t.1 n) ≫ (𝟙 A.X)) = t.1 n
      exact congrArg Additive.ofMul (Category.comp_id (Additive.toMul (t.1 n)))
    map_mul' := by
      intro f g
      apply LinearMap.ext
      intro t
      apply Subtype.ext
      funext n
      change Additive.ofMul (Additive.toMul (t.1 n) ≫ (g.hom ≫ f.hom)) =
        Additive.ofMul ((Additive.toMul (t.1 n) ≫ g.hom) ≫ f.hom)
      exact congrArg Additive.ofMul (Category.assoc _ _ _).symm }

/-- The same ring homomorphism respects the canonical integer algebra. -/
def tateEndIntAlgHom {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] : _root_.PkgI3.AbVar.End A →ₐ[ℤ] Module.End ℤ_[ℓ] (A.T ℓ) :=
  { tateEndRingHom A ℓ with
    commutes' := fun n => by
      change tateEndRingHom A ℓ (n : _root_.PkgI3.AbVar.End A) =
        (n : Module.End ℤ_[ℓ] (A.T ℓ))
      exact map_intCast (tateEndRingHom A ℓ) n }

/-- The completed integral endomorphism algebra acts on the original
Tate module, with no replacement action. -/
def tateEndCompleted {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] : ℤ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A →ₐ[ℤ_[ℓ]]
      Module.End ℤ_[ℓ] (A.T ℓ) :=
  (AlgHom.liftEquiv ℤ ℤ_[ℓ] (_root_.PkgI3.AbVar.End A) (Module.End ℤ_[ℓ] (A.T ℓ)))
    (tateEndIntAlgHom A ℓ)

theorem tateEndCompleted_tmul {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (a : ℤ_[ℓ]) (f : _root_.PkgI3.AbVar.End A) :
    tateEndCompleted A ℓ (a ⊗ₜ[ℤ] f) = a • _root_.PkgI3.AbVar.homT (ℓ := ℓ) f := rfl

/-- Equality with the original completed Hom map on the entire tensor
module, not just on individual endomorphisms. -/
theorem tateEndCompleted_eq_tateHomZl {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (x : ℤ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A) :
    tateEndCompleted A ℓ x = _root_.PkgI3.AbVar.tateHomZl ℓ A A x := by
  induction x using TensorProduct.inductionOn with
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The full completed integral action is faithful by the actual
geometric Hom theorem. -/
theorem tateEndCompleted_injective {K : Type} [Field K] [NumberField K]
    (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    Function.Injective (tateEndCompleted A ℓ) := by
  intro x y hxy
  apply original_tateHomZl_injective A A ℓ hℓ
  simpa only [tateEndCompleted_eq_tateHomZl] using hxy

/-- Rationalization of the whole completed endomorphism algebra, acting
on the same original rational Tate module. -/
def rationalCompletedEndAction {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ℚ_[ℓ] ⊗[ℤ_[ℓ]] (ℤ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A) →ₐ[ℚ_[ℓ]]
      Module.End ℚ_[ℓ] (A.V ℓ) :=
  (AlgHom.liftEquiv ℤ_[ℓ] ℚ_[ℓ] (ℤ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A)
    (Module.End ℚ_[ℓ] (A.V ℓ)))
    ((_root_.Module.End.baseChangeHom ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ)).comp (tateEndCompleted A ℓ))

theorem rationalCompletedEndAction_tmul {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (a : ℚ_[ℓ]) (x : ℤ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A) :
    rationalCompletedEndAction A ℓ (a ⊗ₜ[ℤ_[ℓ]] x) =
      a • (tateEndCompleted A ℓ x).baseChange ℚ_[ℓ] := rfl

/-- Faithfulness survives on the whole rationalized completion by the
actual localization universal property and the actual operator injection.
No claim about one split embedding is substituted for this injection. -/
theorem rationalCompletedEndAction_injective {K : Type} [Field K] [NumberField K]
    (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    Function.Injective (rationalCompletedEndAction A ℓ) := by
  let H := ℤ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A
  let j : H →ₗ[ℤ_[ℓ]] ℚ_[ℓ] ⊗[ℤ_[ℓ]] H := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] H 1
  haveI : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) j := by
    change IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] H 1)
    infer_instance
  apply IsLocalizedModule.injective_of_map_zero (S := nonZeroDivisors ℤ_[ℓ]) j
    (g := (rationalCompletedEndAction A ℓ).toLinearMap.restrictScalars ℤ_[ℓ])
  intro x hx
  have hx' : (tateEndCompleted A ℓ x).baseChange ℚ_[ℓ] = 0 := by
    change rationalCompletedEndAction A ℓ (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] H 1 x) = 0 at hx
    rw [TensorProduct.mk_apply, rationalCompletedEndAction_tmul, one_smul] at hx
    exact hx
  have htx : tateEndCompleted A ℓ x = 0 :=
    baseChangeTate_injective A ℓ (by simpa only [LinearMap.baseChange_zero] using hx')
  have hx0 : x = 0 := tateEndCompleted_injective A ℓ hℓ
    (htx.trans (map_zero (tateEndCompleted A ℓ)).symm)
  simp only [hx0, map_zero]

/-- Every original Galois operator commutes with every base-defined
endomorphism, not merely with inertia operators. -/
theorem galT_commute_end {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K) (f : _root_.PkgI3.AbVar.End A) :
    Commute (A.galT (ℓ := ℓ) σ) (_root_.PkgI3.AbVar.homT (ℓ := ℓ) f) := by
  change A.galT (ℓ := ℓ) σ * _root_.PkgI3.AbVar.homT (ℓ := ℓ) f =
    _root_.PkgI3.AbVar.homT (ℓ := ℓ) f * A.galT (ℓ := ℓ) σ
  apply LinearMap.ext
  intro x
  exact (_root_.PkgI3.homT_galT f σ x).symm

/-- The original whole Galois image commutes with the entire completed
integral endomorphism algebra. -/
theorem galT_commute_completed {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K)
    (x : ℤ_[ℓ] ⊗[ℤ] _root_.PkgI3.AbVar.End A) :
    Commute (A.galT (ℓ := ℓ) σ) (tateEndCompleted A ℓ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a f =>
      rw [tateEndCompleted_tmul]
      change A.galT (ℓ := ℓ) σ * (a • _root_.PkgI3.AbVar.homT (ℓ := ℓ) f) =
        (a • _root_.PkgI3.AbVar.homT (ℓ := ℓ) f) * A.galT (ℓ := ℓ) σ
      rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, (galT_commute_end A ℓ σ f).eq]
  | add x y hx hy =>
      change A.galT (ℓ := ℓ) σ * tateEndCompleted A ℓ (x + y) =
        tateEndCompleted A ℓ (x + y) * A.galT (ℓ := ℓ) σ
      rw [map_add, mul_add, add_mul, hx.eq, hy.eq]

end HDec.CMSerreTate.P1

import ZInQKernel.Contrib.AdelicNormalizer.Objects

/-!
# The adelic quaternion algebra is the scalar extension of the rational algebra

Let `B = GlueRepo.A1.B = ℍ[ℚ, 2, 0, -3]` and `Af = FiniteAdeleRing ℤ ℚ`. This module builds
the actual tensor-product algebra map

`toBA : Af ⊗[ℚ] B →ₐ[Af] BA`,  `a ⊗ q ↦ a · q`,

from Mathlib's `Algebra.TensorProduct.lift`. It uses the canonical scalar map
`Algebra.ofId Af BA` and the coefficientwise rational embedding `rationalToAdelic`. It then
proves that `toBA` is bijective: it sends the base-changed basis `1 ⊗ (1, i, j, k)` to the
basis `(1, i, j, k)` of `BA`. This gives `scalarExtensionEquiv : Af ⊗[ℚ] B ≃ₐ[Af] BA`.

The factors can also be taken in the order `B ⊗[ℚ] Af`. `scalarExtensionEquiv'` composes with
the tensor commutation `Algebra.TensorProduct.comm`.

The module also records the inverse on coordinates, the images of the ordered order basis
`GlueRepo.A1.e`, the unit-group equivalence, and compatibility with evaluation at every finite
place (`quaternionEval v ∘ rationalToAdelic = rationalToLocal`).

This is a contribution, not an acceptance record.
-/

open Quaternion
open scoped TensorProduct

namespace G1.ScalarExtension

noncomputable section

local notation "B" => GlueRepo.A1.B

/-- The coefficientwise embedding `B → BA` induced by `ℚ → Af`, as a `ℚ`-algebra map. -/
def rationalToAdelic : B →ₐ[ℚ] BA :=
  (quaternionMap (algebraMap ℚ Af)).toRatAlgHom

@[simp] theorem rationalToAdelic_apply (q : B) :
    rationalToAdelic q = ⟨algebraMap ℚ Af q.re, algebraMap ℚ Af q.imI,
      algebraMap ℚ Af q.imJ, algebraMap ℚ Af q.imK⟩ :=
  rfl

/-- The actual scalar-extension algebra map `Af ⊗[ℚ] B →ₐ[Af] BA`. -/
def toBA : Af ⊗[ℚ] B →ₐ[Af] BA :=
  Algebra.TensorProduct.lift (Algebra.ofId Af BA) rationalToAdelic
    (fun a _ => Algebra.commutes a _)

@[simp] theorem toBA_tmul (a : Af) (q : B) :
    toBA (a ⊗ₜ[ℚ] q) = algebraMap Af BA a * rationalToAdelic q :=
  Algebra.TensorProduct.lift_tmul _ _ _ a q

theorem toBA_tmul_eq_smul (a : Af) (q : B) :
    toBA (a ⊗ₜ[ℚ] q) = a • rationalToAdelic q := by
  rw [toBA_tmul, Algebra.smul_def]

/-- The `Af`-basis `1 ⊗ (1, i, j, k)` of the tensor product. -/
def tensorBasis : Module.Basis (Fin 4) Af (Af ⊗[ℚ] B) :=
  Algebra.TensorProduct.basis Af (QuaternionAlgebra.basisOneIJK (2 : ℚ) 0 (-3))

/-- The `Af`-basis `(1, i, j, k)` of `BA`. -/
def basBA : Module.Basis (Fin 4) Af BA :=
  QuaternionAlgebra.basisOneIJK (2 : Af) 0 (-3)

theorem rationalToAdelic_basis (k : Fin 4) :
    rationalToAdelic (QuaternionAlgebra.basisOneIJK (2 : ℚ) 0 (-3) k) = basBA k := by
  apply (QuaternionAlgebra.basisOneIJK (2 : Af) 0 (-3)).repr.injective
  rw [basBA, Module.Basis.repr_self]
  ext l
  fin_cases k <;> fin_cases l <;>
    simp [QuaternionAlgebra.basisOneIJK]

theorem toBA_tensorBasis (k : Fin 4) : toBA (tensorBasis k) = basBA k := by
  rw [tensorBasis, Algebra.TensorProduct.basis_apply, toBA_tmul, map_one, one_mul,
    rationalToAdelic_basis]

theorem toBA_linearMap :
    toBA.toLinearMap = (tensorBasis.equiv basBA (Equiv.refl _)).toLinearMap :=
  tensorBasis.ext fun k => by
    rw [AlgHom.toLinearMap_apply, toBA_tensorBasis, LinearEquiv.coe_coe,
      Module.Basis.equiv_apply, Equiv.refl_apply]

theorem toBA_bijective : Function.Bijective toBA := by
  have h : ⇑toBA = ⇑(tensorBasis.equiv basBA (Equiv.refl _)) :=
    funext fun x => LinearMap.congr_fun toBA_linearMap x
  rw [h]
  exact (tensorBasis.equiv basBA (Equiv.refl _)).bijective

/-- **Object identity.** `Af ⊗[ℚ] B ≃ₐ[Af] BA`, given by the tensor algebra map `toBA`. -/
def scalarExtensionEquiv : Af ⊗[ℚ] B ≃ₐ[Af] BA :=
  AlgEquiv.ofBijective toBA toBA_bijective

@[simp] theorem scalarExtensionEquiv_apply (x : Af ⊗[ℚ] B) :
    scalarExtensionEquiv x = toBA x :=
  rfl

theorem scalarExtensionEquiv_tmul (a : Af) (q : B) :
    scalarExtensionEquiv (a ⊗ₜ[ℚ] q) = algebraMap Af BA a * rationalToAdelic q :=
  toBA_tmul a q

theorem scalarExtensionEquiv_one_tmul (q : B) :
    scalarExtensionEquiv (1 ⊗ₜ[ℚ] q) = rationalToAdelic q := by
  rw [scalarExtensionEquiv_tmul, map_one, one_mul]

theorem scalarExtensionEquiv_tmul_one (a : Af) :
    scalarExtensionEquiv (a ⊗ₜ[ℚ] (1 : B)) = algebraMap Af BA a := by
  rw [scalarExtensionEquiv_tmul, map_one, mul_one]

/-- The inverse in coordinates: `x ↦ x.re ⊗ 1 + x.imI ⊗ i + x.imJ ⊗ j + x.imK ⊗ k`. -/
theorem scalarExtensionEquiv_symm_apply (x : BA) :
    scalarExtensionEquiv.symm x =
      x.re ⊗ₜ[ℚ] (⟨1, 0, 0, 0⟩ : B) + x.imI ⊗ₜ[ℚ] (⟨0, 1, 0, 0⟩ : B) +
        x.imJ ⊗ₜ[ℚ] (⟨0, 0, 1, 0⟩ : B) + x.imK ⊗ₜ[ℚ] (⟨0, 0, 0, 1⟩ : B) := by
  apply scalarExtensionEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  simp only [map_add, scalarExtensionEquiv_tmul]
  ext <;> simp

/-- The same identity with the factors in the order `B ⊗[ℚ] Af`, via tensor commutation. -/
def scalarExtensionEquiv' : B ⊗[ℚ] Af ≃+* BA :=
  (Algebra.TensorProduct.comm ℚ B Af).toRingEquiv.trans scalarExtensionEquiv.toRingEquiv

theorem scalarExtensionEquiv'_tmul (q : B) (a : Af) :
    scalarExtensionEquiv' (q ⊗ₜ[ℚ] a) = algebraMap Af BA a * rationalToAdelic q := by
  change scalarExtensionEquiv (Algebra.TensorProduct.comm ℚ B Af (q ⊗ₜ[ℚ] a)) = _
  rw [Algebra.TensorProduct.comm_tmul, scalarExtensionEquiv_tmul]

/-- Unit groups: `(Af ⊗[ℚ] B)ˣ ≃* BAˣ`. -/
def unitsEquiv : (Af ⊗[ℚ] B)ˣ ≃* BAˣ :=
  Units.mapEquiv scalarExtensionEquiv.toMulEquiv

@[simp] theorem coe_unitsEquiv (u : (Af ⊗[ℚ] B)ˣ) :
    ((unitsEquiv u : BAˣ) : BA) = scalarExtensionEquiv (u : Af ⊗[ℚ] B) :=
  rfl

/-! ### The ordered order basis and evaluation at finite places -/

theorem rationalToAdelic_e (k : Fin 4) :
    rationalToAdelic (GlueRepo.A1.e k) =
      ⟨algebraMap ℚ Af (GlueRepo.A1.e k).re, algebraMap ℚ Af (GlueRepo.A1.e k).imI,
        algebraMap ℚ Af (GlueRepo.A1.e k).imJ, algebraMap ℚ Af (GlueRepo.A1.e k).imK⟩ :=
  rfl

/-- The tensor `1 ⊗ e k` of the ordered order basis maps to the embedded basis vector. -/
theorem scalarExtensionEquiv_one_tmul_e (k : Fin 4) :
    scalarExtensionEquiv (1 ⊗ₜ[ℚ] GlueRepo.A1.e k) = rationalToAdelic (GlueRepo.A1.e k) :=
  scalarExtensionEquiv_one_tmul _

/-- Integral combinations of the order basis: `1 ⊗ comb n = Σ n k • (1 ⊗ e k)` maps to
`Σ n k • rationalToAdelic (e k)`. -/
theorem scalarExtensionEquiv_one_tmul_comb (n : Fin 4 → ℤ) :
    scalarExtensionEquiv (1 ⊗ₜ[ℚ] GlueRepo.A1.comb n) =
      ∑ k, (n k : Af) • rationalToAdelic (GlueRepo.A1.e k) := by
  rw [scalarExtensionEquiv_one_tmul, GlueRepo.A1.comb_eq, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_rat_smul]
  simp only [Int.cast_smul_eq_zsmul]

/-- At each finite place, evaluation of the embedded rational algebra is the local scalar
extension `rationalToLocal`. -/
theorem quaternionEval_rationalToAdelic (v : Place) (q : B) :
    quaternionEval v (rationalToAdelic q) = rationalToLocal (primeAt v).1 q := by
  ext <;> simp [quaternionEval, quaternionMap, rationalToLocal]

theorem quaternionEval_scalarExtensionEquiv_tmul (v : Place) (a : Af) (q : B) :
    quaternionEval v (scalarExtensionEquiv (a ⊗ₜ[ℚ] q)) =
      algebraMap (Qv v) (Bv v) (scalarEval v a) * rationalToLocal (primeAt v).1 q := by
  rw [scalarExtensionEquiv_tmul, map_mul, quaternionEval_rationalToAdelic]
  congr 1
  ext <;> simp [quaternionEval, quaternionMap, QuaternionAlgebra.algebraMap_eq]

end

end G1.ScalarExtension

/-
DRAFT — not compiled or kernel-checked in this session.

Pinned source inputs: diophantine-z-q Objects.lean at 8799c581;
StacksFrontier.Algebra.Group.TateModule at Stacks c496df0;
Lean 4.35.0 / Mathlib 56a00585.

This is the parent-owned additive/Tate transport, not the separately owned
scheme-point pullback equivalence. No registered T26, dimension/base-change,
semisimplicity, Frobenius, C10 or H closure is claimed by this draft.
-/
import ZInQKernel.HDecomp.Objects
import StacksFrontier.Algebra.Group.TateModule
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

noncomputable section

namespace AxiomBridge.TateComparison

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (M : Type*) [AddCommGroup M]

/-- The two pinned definitions have the same inverse-limit coordinates and
transition law. This map is the identity on every coordinate, not a chosen iso. -/
def sameGroup : PkgI3.Tate.T ℓ M ≃ₗ[ℤ_[ℓ]]
    Stacks.AbelianGroup.tateModule M ℓ where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := by
    apply Subtype.ext
    funext n
    rfl
  map_smul' a x := by
    apply Subtype.ext
    funext n
    rfl

@[simp] theorem sameGroup_apply (x : PkgI3.Tate.T ℓ M) (n : ℕ) :
    (sameGroup ℓ M x).1 n = x.1 n := rfl

@[simp] theorem sameGroup_symm_apply
    (x : Stacks.AbelianGroup.tateModule M ℓ) (n : ℕ) :
    ((sameGroup ℓ M).symm x).1 n = x.1 n := rfl

variable {M}
variable {N : Type*} [AddCommGroup N]

/-- The pinned Tate functors agree on the actual additive map, coordinatewise. -/
theorem sameGroup_natural (f : M →+ N) (x : PkgI3.Tate.T ℓ M) :
    sameGroup ℓ N (PkgI3.Tate.map f x) =
      Stacks.AbelianGroup.tateModuleMap ℓ f (sameGroup ℓ M x) := by
  apply Subtype.ext
  funext n
  rfl

/-- Lift a genuine additive point equivalence to a linear inverse-limit
comparison. Downstream geometry must construct the point equivalence via the
actual pullback adjunction; this definition does not discharge that obligation. -/
def ofPointEquiv (e : M ≃+ N) : PkgI3.Tate.T ℓ M ≃ₗ[ℤ_[ℓ]]
    Stacks.AbelianGroup.tateModule N ℓ where
  toFun x := Stacks.AbelianGroup.tateModuleMap ℓ e.toAddMonoidHom
    (sameGroup ℓ M x)
  invFun y := PkgI3.Tate.map e.symm.toAddMonoidHom
    ((sameGroup ℓ N).symm y)
  left_inv x := by
    apply Subtype.ext
    funext n
    exact e.symm_apply_apply (x.1 n)
  right_inv y := by
    apply Subtype.ext
    funext n
    exact e.apply_symm_apply (y.1 n)
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact e.map_add (x.1 n) (y.1 n)
  map_smul' a x := by
    apply Subtype.ext
    funext n
    exact map_nsmul e.toAddMonoidHom _ _

@[simp] theorem ofPointEquiv_apply (e : M ≃+ N)
    (x : PkgI3.Tate.T ℓ M) (n : ℕ) :
    (ofPointEquiv ℓ e x).1 n = e (x.1 n) := rfl

/-- A commuting square of the same geometric point maps gives the corresponding
commuting square on Tate modules; no endomorphism or reduction is substituted. -/
theorem ofPointEquiv_natural {M' N' : Type*}
    [AddCommGroup M'] [AddCommGroup N']
    (e : M ≃+ N) (e' : M' ≃+ N')
    (f : M →+ M') (g : N →+ N')
    (h : ∀ x, e' (f x) = g (e x)) (x : PkgI3.Tate.T ℓ M) :
    ofPointEquiv ℓ e' (PkgI3.Tate.map f x) =
      Stacks.AbelianGroup.tateModuleMap ℓ g (ofPointEquiv ℓ e x) := by
  apply Subtype.ext
  funext n
  exact h (x.1 n)

/-- Transfer the actual Stacks freeness result back along the proved point/Tate
comparison. The geometric application must supply that result from its real
base-changed abelian variety, not from a desired `Fact`. -/
theorem free_ofPointEquiv (e : M ≃+ N)
    (h : Module.Free ℤ_[ℓ] (Stacks.AbelianGroup.tateModule N ℓ)) :
    Module.Free ℤ_[ℓ] (PkgI3.Tate.T ℓ M) :=
  Module.Free.of_equiv' h (ofPointEquiv ℓ e).symm

/-- Transfer finite generation for the same actual point/Tate comparison. -/
theorem finite_ofPointEquiv (e : M ≃+ N)
    (h : Module.Finite ℤ_[ℓ] (Stacks.AbelianGroup.tateModule N ℓ)) :
    Module.Finite ℤ_[ℓ] (PkgI3.Tate.T ℓ M) := by
  letI := h
  exact Module.Finite.equiv (ofPointEquiv ℓ e).symm

/-- The corresponding rational Tate module is finite dimensional once the
actual Stacks finite/free conclusions have been instantiated. This is a finite
space input to C10, NOT its representations, traces or semisimplicity. -/
theorem rational_finite_ofPointEquiv (e : M ≃+ N)
    (hf : Module.Free ℤ_[ℓ] (Stacks.AbelianGroup.tateModule N ℓ))
    (hfin : Module.Finite ℤ_[ℓ] (Stacks.AbelianGroup.tateModule N ℓ)) :
    FiniteDimensional ℚ_[ℓ] (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ M)) := by
  letI := free_ofPointEquiv ℓ e hf
  letI := finite_ofPointEquiv ℓ e hfin
  exact Module.Finite.of_basis
    ((Module.Free.chooseBasis ℤ_[ℓ] (PkgI3.Tate.T ℓ M)).baseChange ℚ_[ℓ])

end AxiomBridge.TateComparison

#print axioms AxiomBridge.TateComparison.sameGroup
#print axioms AxiomBridge.TateComparison.sameGroup_natural
#print axioms AxiomBridge.TateComparison.ofPointEquiv
#print axioms AxiomBridge.TateComparison.ofPointEquiv_natural
#print axioms AxiomBridge.TateComparison.free_ofPointEquiv
#print axioms AxiomBridge.TateComparison.finite_ofPointEquiv
#print axioms AxiomBridge.TateComparison.rational_finite_ofPointEquiv

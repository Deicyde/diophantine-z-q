import ZInQKernel.Contrib.OneProof.TateImageSaturation
import ZInQKernel.Contrib.OneProof.HomFreeFiniteAlgClosed
import ZInQKernel.Contrib.OneProof.UniformizationLeafAll
import ZInQKernel.Contrib.OneProof.MumfordTorsionAlgClosed
import ZInQKernel.Contrib.OneProof.DeRhamPrint
import Mathlib.RingTheory.Filtration

/-!
# Finite-level algebraic approximation for the Tate homomorphism theorem

The integral comparison image is closed for the ℓ-adic filtration. Thus a
Galois-equivariant map of Tate modules is algebraic over ℤ_ℓ if at each
torsion level some genuine morphism realizes its action at that level.
The morphisms at different levels may be chosen independently.
-/

noncomputable section
open PkgI3.AbVar
open scoped TensorProduct CategoryTheory.MonObj

namespace ZInQ.Contrib.TateFiniteApproximation

variable {K : Type} [Field K] {A B : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime]

private theorem tateHomZl_smul (r : ℤ_[ℓ]) (ξ : ℤ_[ℓ] ⊗[ℤ] Hom A B) :
    tateHomZl ℓ A B (r • ξ) = r • tateHomZl ℓ A B ξ := by
  induction ξ using TensorProduct.inductionOn with
  | tmul a f =>
    rw [TensorProduct.smul_tmul']
    change (r*a) • homT (ℓ := ℓ) f = r • a • homT (ℓ := ℓ) f
    rw [mul_smul]
  | add x y hx hy => simp [smul_add, map_add, hx, hy]

/-- The image of integral homomorphisms after extending scalars to ℤ_ℓ. -/
def comparisonImage (ℓ : ℕ) [Fact ℓ.Prime] (A B : PkgI3.AbVar K) :
    Submodule ℤ_[ℓ] (A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) where
  carrier := Set.range (tateHomZl ℓ A B)
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩; exact ⟨x+y, map_add _ _ _⟩
  smul_mem' := by rintro r _ ⟨x,rfl⟩; exact ⟨r • x, tateHomZl_smul r x⟩

/-- A submodule of a finite ℤ_ℓ-module contains every element approximated
by its elements modulo all powers of ℓ. -/
theorem mem_of_approx {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M] [Module.Finite ℤ_[ℓ] M]
    (U : Submodule ℤ_[ℓ] M) (x : M)
    (hx : ∀ n : ℕ, ∃ y ∈ U, ∃ z : M, x - y = (ℓ : ℤ_[ℓ])^n • z) : x ∈ U := by
  let I := IsLocalRing.maximalIdeal ℤ_[ℓ]
  have hinf : U.mkQ x ∈ ⨅ n : ℕ, I^n • (⊤ : Submodule ℤ_[ℓ] (M ⧸ U)) := by
    refine (Submodule.mem_iInf _).mpr fun n => ?_
    obtain ⟨y, hy, z, h⟩ := hx n
    have he := congrArg U.mkQ h
    have hz : U.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hy
    rw [map_sub, hz, sub_zero, map_smul] at he
    rw [he]
    apply Submodule.smul_mem_smul _ (Submodule.mem_top : U.mkQ z ∈ ⊤)
    apply Ideal.pow_mem_pow
    rw [show I = IsLocalRing.maximalIdeal ℤ_[ℓ] from rfl, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (by simp)
  rw [I.iInf_pow_smul_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal.isMaximal ℤ_[ℓ]).ne_top] at hinf
  exact (Submodule.Quotient.mk_eq_zero U).mp hinf

/-- Equality of the n-th coordinates for every argument forces the difference
of two maps to be divisible by ℓ^n as an integral linear map. -/
theorem map_sub_eq_pow_smul_of_coord_eq [Module.Free ℤ_[ℓ] (A.T ℓ)]
    (φ ψ : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) (n : ℕ) (h : ∀ x, (φ x).1 n = (ψ x).1 n) :
    ∃ z : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ, φ-ψ = (ℓ : ℤ_[ℓ])^n • z := by
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  have hc (i) : ((φ-ψ) (b i)).1 n = 0 := by
    change (φ (b i)).1 n - (ψ (b i)).1 n = 0
    exact sub_eq_zero.mpr (h _)
  choose z hz using fun i => (PkgI3.Tate.coord_eq_zero_iff ((φ-ψ) (b i)) n).mp (hc i)
  refine ⟨b.constr ℤ_[ℓ] z, b.ext fun i => ?_⟩
  simpa using hz i

/-- Membership in the integral comparison image is equivalent to realization
by an abelian-variety morphism at each finite torsion level. -/
theorem mem_range_iff_approx [NumberField K] (φ : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) :
    φ ∈ Set.range (tateHomZl ℓ A B) ↔
    ∀ n : ℕ, ∃ f : Hom A B, ∀ x : A.T ℓ, (φ x).1 n = ((homT f) x).1 n := by
  have hℓ : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  have hf := DeRhamPrint.tateModuleFree_of_mumford CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  let := (hf K A ℓ hℓ).1
  let := (hf K A ℓ hℓ).2.1
  let := (hf K B ℓ hℓ).2.1
  have one (f : Hom A B) : tateHomZl ℓ A B ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] f) = homT f := by
    change (1 : ℤ_[ℓ]) • homT (ℓ := ℓ) f = homT (ℓ := ℓ) f
    exact one_smul _ _
  constructor
  · rintro ⟨ξ, rfl⟩ n
    obtain ⟨f, ζ, rfl⟩ := TateImageSaturation.tensor_exists_one_tmul_add_nsmul n ξ
    refine ⟨f, fun x => ?_⟩
    rw [map_add, map_nsmul, one]
    have hz := (PkgI3.Tate.coord_eq_zero_iff ((ℓ^n : ℕ) • (tateHomZl ℓ A B ζ x)) n).mpr
      ⟨_, by rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], Nat.cast_pow]⟩
    change ((homT f) x).1 n + ((ℓ^n : ℕ) • (tateHomZl ℓ A B ζ x)).1 n = _
    rw [hz, add_zero]
  · intro h
    apply mem_of_approx (comparisonImage ℓ A B) φ
    intro n
    obtain ⟨f, h⟩ := h n
    exact ⟨homT f, ⟨(1 : ℤ_[ℓ]) ⊗ₜ[ℤ] f, one f⟩, map_sub_eq_pow_smul_of_coord_eq φ (homT f) n h⟩

/-- The full number-field Tate homomorphism theorem reduces to finite-level
algebraic approximation of equivariant maps; injectivity is already proved. -/
theorem faltingsTate_iff_approx : PkgI3.FaltingsTate ↔
    ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
      (φ : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ), IsGalEquivariant φ →
      ∀ n : ℕ, ∃ f : Hom A B, ∀ x : A.T ℓ, (φ x).1 n = ((homT f) x).1 n := by
  constructor
  · intro h K _ _ A B ℓ _ φ hφ
    exact (mem_range_iff_approx φ).mp (by rwa [(h K A B ℓ).2])
  · intro h K _ _ A B ℓ hℓ
    have hi := OneProof.HomFreeC.homFreeFiniteNF uniformizationLeafAll_proof
      CloudB3W16Torsion.mumfordTorsionAlgClosed_proof K A B
    refine ⟨hi.2.2.2 ℓ (Nat.cast_ne_zero.mpr hℓ.out.ne_zero),
      Set.Subset.antisymm (PkgI3.range_tateHomZl_subset A B ℓ) (fun φ hφ => ?_)⟩
    exact (mem_range_iff_approx φ).mpr (h K A B ℓ φ hφ)

end ZInQ.Contrib.TateFiniteApproximation

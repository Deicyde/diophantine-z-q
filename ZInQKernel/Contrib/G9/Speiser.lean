import Mathlib

/-!
# G9: Galois descent for semilinear actions (Speiser's lemma)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Let `L/K` be a finite Galois extension with group `Γ`, and `M` an `L`-vector space with a
semilinear action of `Γ` (`τ(c • m) = τ(c) • τ(m)`). Then `L ⊗_K M^Γ → M` is an isomorphism
(Speiser's lemma; STANDARD: Serre, *Local fields*, X §1, Lemma; Bourbaki *Algèbre* V §10).
We need only the dimension count `dim_K M = [L:K] · dim_K M^Γ`, `speiser_finrank`.

The proof: for a `K`-basis `b` of `L` indexed by `Γ`, the matrix `A = (τ(b_j))_{τ,j}` is
invertible by Dedekind's independence of characters; this gives both surjectivity (each `m` is an
`L`-combination of the traces `Σ_σ σ(b_j m)`) and injectivity.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open Module
open scoped TensorProduct Classical

section Speiser

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- A `K`-basis of `L` indexed by `Gal(L/K)`. -/
noncomputable def galBasis : Basis (L ≃ₐ[K] L) K L :=
  (Module.finBasisOfFinrankEq K L
    (by rw [← IsGalois.card_aut_eq_finrank K L, Nat.card_eq_fintype_card])).reindex
    (Fintype.equivFin (L ≃ₐ[K] L)).symm

/-- The matrix `(τ(b_j))_{τ, j}`. -/
noncomputable def galMatrix : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L :=
  Matrix.of fun τ j => τ (galBasis (K := K) (L := L) j)

/-- Dedekind: `(τ(b_j))` is invertible. -/
theorem isUnit_galMatrix : IsUnit (galMatrix (K := K) (L := L)) := by
  rw [← Matrix.vecMul_injective_iff_isUnit]
  have hli : LinearIndependent L
      (fun τ : L ≃ₐ[K] L => ((τ : L →ₐ[K] L)).toLinearMap) :=
    (linearIndependent_toLinearMap K L L).comp (fun τ : L ≃ₐ[K] L => (τ : L →ₐ[K] L))
      (fun _ _ h => AlgEquiv.coe_toAlgHom_injective h)
  have key : ∀ c : (L ≃ₐ[K] L) → L, Matrix.vecMul c galMatrix = 0 → c = 0 := by
    intro c hc
    have hsum : (∑ τ, c τ • ((τ : L →ₐ[K] L)).toLinearMap) = 0 := by
      refine (galBasis (K := K) (L := L)).ext fun j => ?_
      have := congrFun hc j
      simp only [Matrix.vecMul, dotProduct, galMatrix, Matrix.of_apply, Pi.zero_apply] at this
      simpa [LinearMap.sum_apply] using this
    funext τ
    exact (Fintype.linearIndependent_iff.mp hli) c hsum τ
  intro c d h
  have h' : Matrix.vecMul (c - d) galMatrix = 0 := by
    have h0 : Matrix.vecMul c galMatrix = Matrix.vecMul d (galMatrix (K := K) (L := L)) := h
    rw [Matrix.sub_vecMul, h0, sub_self]
  exact sub_eq_zero.mp (key _ h')

variable {M : Type*} [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]

variable (T : (L ≃ₐ[K] L) → M →+ M)
  (hsmul : ∀ τ (c : L) (m : M), T τ (c • m) = τ c • T τ m)
  (hone : ∀ m, T 1 m = m)
  (hmul : ∀ τ σ m, T (τ * σ) m = T τ (T σ m))

include hsmul in
theorem semilin_smulK (τ : L ≃ₐ[K] L) (k : K) (m : M) : T τ (k • m) = k • T τ m := by
  rw [← algebraMap_smul L k m, hsmul, AlgEquiv.commutes, algebraMap_smul]

/-- The fixed points `M^Γ`, a `K`-subspace. -/
def fixedK : Submodule K M where
  carrier := {m | ∀ τ, T τ m = m}
  zero_mem' := by intro τ; simp
  add_mem' := by
    intro x y hx hy τ
    simp only [Set.mem_ofPred_eq] at hx hy
    rw [map_add, hx, hy]
  smul_mem' := by
    intro k x hx τ
    simp only [Set.mem_ofPred_eq] at hx
    rw [semilin_smulK T hsmul, hx]

/-- `L ⊗_K M^Γ → M`. -/
noncomputable def speiserMap : L ⊗[K] (fixedK T hsmul) →ₗ[K] M :=
  TensorProduct.lift (LinearMap.mk₂ K (fun (x : L) (n : fixedK T hsmul) => x • (n : M))
    (fun x y n => add_smul x y _)
    (fun k x n => by simp only [smul_assoc])
    (fun x n n' => by simp only [Submodule.coe_add, smul_add])
    (fun k x n => by simp only [SetLike.val_smul, smul_comm x k (n : M)]))

theorem speiserMap_tmul (x : L) (n : fixedK T hsmul) :
    speiserMap T hsmul (x ⊗ₜ n) = x • (n : M) := by
  simp [speiserMap]

include hone hmul in
theorem speiserMap_surjective : Function.Surjective (speiserMap T hsmul) := by
  intro m
  set b := galBasis (K := K) (L := L)
  set A := galMatrix (K := K) (L := L)
  have hA := isUnit_galMatrix (K := K) (L := L)
  -- the traces `y j = Σ_σ σ(b j • m)`
  let y : (L ≃ₐ[K] L) → M := fun j => ∑ σ, T σ (b j • m)
  have hy : ∀ j, y j ∈ fixedK T hsmul := by
    intro j τ
    simp only [y, map_sum, ← hmul]
    exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  have hy' : ∀ j, y j = ∑ σ, A σ j • T σ m := by
    intro j
    simp only [y, hsmul, A, galMatrix, Matrix.of_apply, b]
  refine ⟨∑ j, (A⁻¹ j (1 : L ≃ₐ[K] L)) ⊗ₜ ⟨y j, hy j⟩, ?_⟩
  rw [map_sum]
  simp only [speiserMap_tmul, hy', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hmul1 : ∀ σ, (∑ j, A⁻¹ j (1 : L ≃ₐ[K] L) * A σ j) =
      (1 : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) σ (1 : L ≃ₐ[K] L) := by
    intro σ
    rw [← Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA), Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  simp_rw [hmul1, Matrix.one_apply]
  simp [hone]

include hone hmul in
theorem speiserMap_injective : Function.Injective (speiserMap T hsmul) := by
  set b := galBasis (K := K) (L := L)
  set A := galMatrix (K := K) (L := L)
  have hA := isUnit_galMatrix (K := K) (L := L)
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  set n := TensorProduct.equivFinsuppOfBasisLeft b x
  have hxn : x = ∑ j, b j ⊗ₜ n j := by
    have h1 := LinearMap.congr_fun (TensorProduct.equivFinsuppOfBasisLeft_symm b) n
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, n] at h1
    rw [h1, Finsupp.lsum_apply, Finsupp.sum_fintype _ _ (by simp)]
    rfl
  rw [hxn, map_sum] at hx
  simp only [speiserMap_tmul] at hx
  -- apply every `τ`
  have hτ : ∀ τ, ∑ j, A τ j • (n j : M) = 0 := by
    intro τ
    have := congrArg (T τ) hx
    rw [map_sum, map_zero] at this
    simpa only [hsmul, (n _).2 τ, A, galMatrix, Matrix.of_apply, b] using this
  have hn : ∀ k, (n k : M) = 0 := by
    intro k
    have hinv : A⁻¹ * A = 1 :=
      Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
    have : (n k : M) = ∑ τ, A⁻¹ k τ • ∑ j, A τ j • (n j : M) := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      have h2 : ∀ j, (∑ τ, A⁻¹ k τ * A τ j) = (1 : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L) k j := by
        intro j; rw [← hinv, Matrix.mul_apply]
      simp_rw [h2, Matrix.one_apply]
      simp
    rw [this]
    simp [hτ]
  rw [hxn]
  simp [show ∀ k, n k = 0 from fun k => Subtype.ext (hn k)]

include hone hmul in
/-- **Speiser's lemma, dimension form.** `dim_K M = [L:K] · dim_K M^Γ`. -/
theorem speiser_finrank :
    finrank K M = finrank K L * finrank K (fixedK T hsmul) := by
  have e := LinearEquiv.ofBijective (speiserMap T hsmul)
    ⟨speiserMap_injective T hsmul hone hmul, speiserMap_surjective T hsmul hone hmul⟩
  rw [← e.finrank_eq, Module.finrank_tensorProduct]

end Speiser

end ZInQ.Contrib.G9

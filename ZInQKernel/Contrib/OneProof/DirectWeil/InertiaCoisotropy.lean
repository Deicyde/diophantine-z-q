import ZInQKernel.Contrib.OneProof.DirectWeil.AmbientWeilPairing
import ZInQKernel.Contrib.CMSerreTateSupport.NativeTateCongruenceMatrices
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.RepresentationTheory.Invariants

noncomputable section

open PkgI3 PkgI3.AbVar
open scoped CategoryTheory.MonObj

namespace SZRaynaud

open LinearMap Module

/-- The fixed subspace of a group of isometries is coisotropic exactly when
all displacements lie in the fixed subspace. -/
theorem coisotropic_iff_fixed_displacements
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (hρ : ∀ g x y, B (ρ g x) (ρ g y) = B x y) :
    B.orthogonal ρ.invariants ≤ ρ.invariants ↔ ∀ g h x, ρ h (ρ g x - x) = ρ g x - x := by
  constructor
  · intro hc g h x
    have hd : ρ g x - x ∈ B.orthogonal ρ.invariants := by
      apply (B.mem_orthogonal_iff).mpr
      intro y hy
      have h := hρ g y x
      rwa [Representation.mem_invariants ρ y |>.mp hy g, ← sub_eq_zero, ← map_sub] at h
    exact (Representation.mem_invariants ρ _).mp (hc hd) h
  · intro h y hy
    apply (Representation.mem_invariants ρ y).mpr
    intro g
    apply sub_eq_zero.mp
    apply hB.2 (ρ g y - y)
    intro x
    have hx : ρ g (ρ g⁻¹ x) = x := by
      change ((ρ g * ρ g⁻¹) : V →ₗ[k] V) x = x
      rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have hp := hρ g (ρ g⁻¹ x) y
    rw [hx] at hp
    have hu : ρ g⁻¹ x - x ∈ ρ.invariants := (Representation.mem_invariants ρ _).mpr fun j => h g⁻¹ j x
    have hq := (B.mem_orthogonal_iff.mp hy) _ hu
    rw [map_sub₂, sub_eq_zero] at hq
    rw [map_sub, hp, hq, sub_self]

section Inertia

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (A : AbVar K) (w : ValuationSubring Ω) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The rational Tate representation restricted to the inertia subgroup of the chosen valuation. -/
def inertiaTateRep : Representation ℚ_[ℓ] (w.inertiaSubgroup K) (VΩ A Ω ℓ) :=
  ((Module.End.baseChangeHom ℤ_[ℓ] ℚ_[ℓ] _).toMonoidHom.comp
    (NativeTateCongruence.originalTateRep A ℓ)).comp
    ((w.decompositionSubgroup K).subtype.comp (w.inertiaSubgroup K).subtype)

theorem inertiaTateRep_apply (σ : w.inertiaSubgroup K) :
    inertiaTateRep A w ℓ σ = galVΩ A ℓ σ.1.1 := rfl

/-- Inertia invariants in the exact rational Tate module from `SilverbergZarhinThm33`. -/
abbrev inertiaFixedSpace : Submodule ℚ_[ℓ] (VΩ A Ω ℓ) := (inertiaTateRep A w ℓ).invariants

theorem mem_inertiaFixedSpace (x : VΩ A Ω ℓ) : x ∈ inertiaFixedSpace A w ℓ ↔
    ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → galVΩ A ℓ σ x = x := by
  constructor
  · intro hx σ hσ
    obtain ⟨hd, hi⟩ := hσ
    exact (Representation.mem_invariants _ x).mp hx ⟨⟨σ, hd⟩, hi⟩
  · intro hx
    exact (Representation.mem_invariants _ x).mpr fun σ => hx σ.1.1 ⟨σ.1.2, σ.2⟩

/-- The action condition in `SilverbergZarhinThm33` is coisotropy for any
inertia-invariant nondegenerate form on the same rational Tate space. -/
theorem coisotropic_iff_levelTwo (B : LinearMap.BilinForm ℚ_[ℓ] (VΩ A Ω ℓ)) (hB : B.Nondegenerate)
    (hρ : ∀ (σ : Ω ≃ₐ[K] Ω), PkgI2.IsInertia w σ → ∀ x y : VΩ A Ω ℓ,
      B (galVΩ A ℓ σ x) (galVΩ A ℓ σ y) = B x y) :
    B.orthogonal (inertiaFixedSpace A w ℓ) ≤ inertiaFixedSpace A w ℓ ↔
      ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
        ∀ x : VΩ A Ω ℓ, galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x := by
  have h := coisotropic_iff_fixed_displacements (inertiaTateRep A w ℓ) B hB
    (fun σ => hρ σ.1.1 ⟨σ.1.2, σ.2⟩)
  constructor
  · intro hc σ hσ τ hτ x
    obtain ⟨hd, hi⟩ := hσ
    obtain ⟨hd', hi'⟩ := hτ
    exact h.mp hc ⟨⟨σ, hd⟩, hi⟩ ⟨⟨τ, hd'⟩, hi'⟩ x
  · intro hc
    exact h.mpr fun σ τ => hc σ.1.1 ⟨σ.1.2, σ.2⟩ τ.1.1 ⟨τ.1.2, τ.2⟩

end Inertia

section Rank

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- An orthogonal toric subspace of the expected dimension makes the fixed space coisotropic. -/
theorem coisotropic_of_toric_rank (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (U W : Submodule k V) (hWU : W ≤ U) (hWB : W ≤ B.orthogonal U)
    (h_rank : finrank k V ≤ finrank k U + finrank k W) : B.orthogonal U ≤ U := by
  have hdim : finrank k (B.orthogonal U) ≤ finrank k W := by
    rw [B.finrank_orthogonal hB]
    omega
  rwa [← Submodule.eq_of_le_of_finrank_le hWB hdim]

/-- Given the fixed-part rank and toric radical formula, the unipotent rank
is zero exactly when the fixed part is coisotropic. -/
theorem coisotropic_iff_unipotentRank_eq_zero
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (U W : Submodule k V) (hW : W = U ⊓ B.orthogonal U)
    (a t u : ℕ) (hV : finrank k V = 2 * (a + t + u))
    (hU : finrank k U = 2 * a + t) (hT : finrank k W = t) :
    B.orthogonal U ≤ U ↔ u = 0 := by
  constructor
  · intro h
    have he : W = B.orthogonal U := hW.trans (inf_eq_right.mpr h)
    rw [he, B.finrank_orthogonal hB, hV, hU] at hT
    omega
  · intro hu
    apply coisotropic_of_toric_rank B hB U W (hW.trans_le inf_le_left) (hW.trans_le inf_le_right)
    rw [hV, hU, hT, hu]
    omega

end Rank

end SZRaynaud

import InertiaFixedPointFieldV003
import InertiaRestrictConcreteV002

/-!
# Inertia-fixed points of an abelian variety are defined over finite inertia fields

For the kernel's abelian variety `A` over a field `K` of characteristic zero, an algebraic closure
`Ω`, a discrete valuation subring `O` of `K` and a valuation subring `w` of `Ω` above it: an
`Ω`-point fixed by every element of the inertia subgroup of `w` comes from a point over a finite
intermediate field `M` (its coordinate field), and for every finite Galois subextension `N ⊇ M`,
`M` is fixed by the inertia group, in `Gal(N/K)`, of the prime of the integral closure of `O` in
`N` below `w`. That is, `M` lies in the inertia field of that prime.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace InertiaPointDescent

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem exists_point_field_in_inertia_fields [CharZero K] [IsAlgClosure K Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (x : A.Pt Ω)
    (hx : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → A.galAct σ x = x) :
    ∃ M : IntermediateField K Ω, FiniteDimensional K M ∧
      M ≤ IntermediateField.fixedField (inertiaGroup (K := K) w) ∧
      (∃ y : A.Pt M, Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ y.left = x.left) ∧
      ∀ (N : IntermediateField K Ω), FiniteDimensional K N → Normal K N →
        ∀ hMN : M ≤ N, ∀ (m : Ω) (hm : m ∈ M) (τ : N ≃ₐ[K] N),
          τ ∈ (centerIdealN O w hw N).inertia (N ≃ₐ[K] N) →
            τ ⟨m, hMN hm⟩ = ⟨m, hMN hm⟩ := by
  obtain ⟨M, hfd, hfix, y, hy, -⟩ := exists_inertia_fixed_point_field w A x hx
  refine ⟨M, hfd, hfix, ⟨y, hy⟩, ?_⟩
  intro N hN hNn hMN m hm τ hτ
  refine inertia_fixes_of_fixedField O w hw N (hMN hm) (fun σ hσ => ?_) τ hτ
  have hmf := hfix hm
  rw [IntermediateField.mem_fixedField_iff] at hmf
  exact hmf σ ((mem_inertiaGroup_iff w σ).2 hσ)

end InertiaPointDescent

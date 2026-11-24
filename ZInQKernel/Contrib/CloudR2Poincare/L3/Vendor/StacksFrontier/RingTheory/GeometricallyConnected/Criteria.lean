import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksCore.RingTheory.Spectrum.Prime.Topology
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.RingTheory.TensorProduct.Connected
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.RingTheory.GeometricallyConnected.Criteria`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory




universe u v

/-!
# Geometric connectedness is detected by the finite separable extensions

Let `k` be a field and let `R` be a `k`-algebra. Then `R` is geometrically connected over `k`,
that is, `Spec (K ⊗[k] R)` is connected for every field extension `K/k`, if and only if
`Spec (K ⊗[k] R)` is connected for every finite separable field extension `K/k`.

## Main results

* `Stacks.GeometricallyConnectedCriterion.solution`: a `k`-algebra `R` over a field `k` is
  geometrically connected over `k` if and only if `Spec (K ⊗[k] R)` is connected for every finite
  separable field extension `K/k`.
* `Algebra.isGeometricallyConnected_iff_forall_finite_separable`: the same statement, in the
  namespace `Algebra`.

## References

* [Stacks 037S](https://stacks.math.columbia.edu/tag/037S)
-/


open scoped TensorProduct

namespace Stacks.GeometricallyConnectedCriterion
#cloudR2LocalInstances

/-! ### Idempotents of the base change to the separable closure -/
#cloudR2Vendor eq_zero_or_one_of_separableClosure in

/-- If the spectrum of `K ⊗[k] R` is connected for every finite separable extension `K/k`, then
`k^sep ⊗[k] R` has no nontrivial idempotent. -/
private theorem eq_zero_or_one_of_separableClosure (k : Type u) (R : Type v) [Field k] [CommRing R]
    [Algebra k R]
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K],
      ConnectedSpace (PrimeSpectrum (K ⊗[k] R)))
    (e : SeparableClosure k ⊗[k] R) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  classical
  obtain ⟨G, hG⟩ := TensorProduct.exists_finset e
  set F : Finset (SeparableClosure k) := G.image Prod.fst with hF
  set K : IntermediateField k (SeparableClosure k) :=
    IntermediateField.adjoin k (F : Set (SeparableClosure k))
  have : FiniteDimensional k K :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have : Algebra.IsSeparable k K :=
    Algebra.isSeparable_tower_bot_of_isSeparable k K (SeparableClosure k)
  set Φ := Algebra.TensorProduct.map K.val (AlgHom.id k R) with hΦ
  have hinj : Function.Injective Φ :=
    Stacks.TensorProduct.IdempotentBijection.tensorProduct_map_injective K.val (AlgHom.id k R)
      (by simp [IntermediateField.coe_val]) fun _ _ hab ↦ hab
  have hmem : e ∈ Φ.range := by
    rw [hG]
    refine Subalgebra.sum_mem _ fun p hp ↦ ?_
    refine ⟨(⟨p.1, IntermediateField.subset_adjoin k _ (by
      simp only [hF, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨p, hp, rfl⟩)⟩ : K) ⊗ₜ[k] p.2, ?_⟩
    simp [hΦ]
  obtain ⟨e', he'⟩ := hmem
  have he'e : Φ e' = e := he'
  have he'i : IsIdempotentElem e' := hinj (by rw [map_mul, he'e, he])
  have hpc : PreconnectedSpace (PrimeSpectrum (K ⊗[k] R)) := (h K).toPreconnectedSpace
  rcases PrimeSpectrum.preconnectedSpace_iff_isIdempotentElem.mp hpc e' he'i with h1 | h1
  · exact Or.inl (by rw [← he'e, h1, map_zero])
  · exact Or.inr (by rw [← he'e, h1, map_one])

/-! ### From the separable closure to an arbitrary field extension -/
#cloudR2Vendor connectedSpace_primeSpectrum_of_separableClosure in

/-- If the spectrum of `k^sep ⊗[k] R` is connected for a separable closure `k^sep/k`, then the
spectrum of `K ⊗[k] R` is connected for every field extension `K/k`. -/
private theorem connectedSpace_primeSpectrum_of_separableClosure (k : Type u) (R : Type v) [Field k]
    [CommRing R] [Algebra k R] [Nontrivial R]
    [ConnectedSpace (PrimeSpectrum (SeparableClosure k ⊗[k] R))] (K : Type u) [Field K]
    [Algebra k K] : ConnectedSpace (PrimeSpectrum (K ⊗[k] R)) := by
  set φ : SeparableClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let _ : Algebra (SeparableClosure k) (AlgebraicClosure K) := φ.toRingHom.toAlgebra
  have : IsScalarTower k (SeparableClosure k) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  set η := Algebra.TensorProduct.cancelBaseChange k (SeparableClosure k) (AlgebraicClosure K)
    (AlgebraicClosure K) R
  have hL : ∀ e : AlgebraicClosure K ⊗[k] R, IsIdempotentElem e → e = 0 ∨ e = 1 :=
    fun e he ↦ Stacks.TensorProduct.ConnectedSpectrum.eq_zero_or_one_of_injective
      (f := η.symm.toRingHom) η.symm.injective
      (fun x hx ↦ PrimeSpectrum.preconnectedSpace_iff_isIdempotentElem.mp inferInstance x hx) he
  refine PrimeSpectrum.connectedSpace_iff_isIdempotentElem.mpr fun e he ↦ ?_
  refine Stacks.TensorProduct.ConnectedSpectrum.eq_zero_or_one_of_injective
    (f := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k K (AlgebraicClosure K))
      (AlgHom.id k R)).toRingHom)
    (Stacks.TensorProduct.IdempotentBijection.tensorProduct_map_injective _ _ ?_
      fun _ _ hab ↦ hab) hL he
  exact (algebraMap K (AlgebraicClosure K)).injective

/-! ### The lemma -/
#cloudR2Vendor solution in

/-- A `k`-algebra `R` over a field `k` is geometrically connected over `k` if and only if the
spectrum of `K ⊗[k] R` is connected for every finite separable field extension `K/k`. -/
theorem solution (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] :
    Algebra.IsGeometricallyConnected k R ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K],
        ConnectedSpace (PrimeSpectrum (K ⊗[k] R)) := by
  refine ⟨fun hR K _ _ _ _ ↦ hR.connectedSpace_primeSpectrum_tensorProduct K, fun h ↦ ?_⟩
  have hR : Nontrivial R :=
    have : Nontrivial (k ⊗[k] R) := PrimeSpectrum.nonempty_iff_nontrivial.mp (h k).toNonempty
    (Algebra.TensorProduct.lid k R).symm.toRingHom.domain_nontrivial
  have : ConnectedSpace (PrimeSpectrum (SeparableClosure k ⊗[k] R)) :=
    (PrimeSpectrum.connectedSpace_iff_isIdempotentElem
      (R := SeparableClosure k ⊗[k] R)).mpr
      (eq_zero_or_one_of_separableClosure k R h)
  exact ⟨fun K _ _ ↦ connectedSpace_primeSpectrum_of_separableClosure k R K⟩

end Stacks.GeometricallyConnectedCriterion



open scoped TensorProduct

namespace Algebra
#cloudR2LocalInstances
#cloudR2Vendor isGeometricallyConnected_iff_forall_finite_separable in

/-- **Geometric connectedness is detected by the finite separable extensions.** Let `k` be a
field and let `R` be a `k`-algebra. Then `R` is geometrically connected over `k`, that is,
`Spec (K ⊗[k] R)` is connected for every field extension `K/k`, if and only if `Spec (K ⊗[k] R)`
is connected for every finite separable field extension `K/k`. -/

theorem isGeometricallyConnected_iff_forall_finite_separable (k : Type u) (R : Type v)
    [Field k] [CommRing R] [Algebra k R] :
    IsGeometricallyConnected k R ↔
      ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K],
        ConnectedSpace (PrimeSpectrum (K ⊗[k] R)) :=
  Stacks.GeometricallyConnectedCriterion.solution k R

end Algebra


end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort

/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdeleRing_secondCountableTopology (git blob b1cf8561eed2aa133b42ae59ce6c2480ba2a8e7e, sha256 90a56c8aed3f4815540aa156fc1b290e68fa31556966f8e3222e46fee07d8858).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Mathlib_LinearAlgebra_Countable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdeleRing_secondCountableTopology

set_option autoImplicit false

section

open scoped NumberField

open IsDedekindDomain NumberField

private scoped instance scAdele_CountableIdeal (R : Type*) [CommRing R] [Countable R] [IsNoetherianRing R] :
    Countable (Ideal R) := by
  have hsurj : Function.Surjective (fun s : Finset R => Ideal.span (s : Set R)) := by
    intro I
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
    exact ⟨s, hs⟩
  exact hsurj.countable

private scoped instance scAdele_CountableHeightOneSpectrum (R : Type*) [CommRing R] [IsDedekindDomain R] [Countable R] :
    Countable (HeightOneSpectrum R) := by
  have hinj : Function.Injective (fun v : HeightOneSpectrum R => v.asIdeal) := fun v w h => HeightOneSpectrum.ext h
  exact hinj.countable

private scoped instance scAdele_CountableRingOfIntegers (K : Type*) [Field K] [NumberField K] : Countable (𝓞 K) :=
  Function.Injective.countable (RingOfIntegers.coe_injective (K := K))

open scoped RestrictedProduct in
private scoped instance scAdele_SecondCountableFiniteAdeleRing (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), SecondCountableTopology (v.adicCompletion K) := fun v => by
    haveI : TopologicalSpace.SeparableSpace (v.adicCompletion K) :=
      ⟨_, Set.countable_range _, HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v)⟩
    exact UniformSpace.secondCountable_of_separable _
  haveI : SecondCountableTopology
      (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    RestrictedProduct.secondCountableTopology fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]

private scoped instance scAdele_SecondCountableInfiniteAdeleRing (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : NumberField.InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    haveI : SecondCountableTopology v.1.Completion := UniformSpace.secondCountable_of_separable _
    exact (NumberField.InfinitePlace.Completion.isometryEquivCompletion v).toHomeomorph.secondCountableTopology
  exact inferInstanceAs <| SecondCountableTopology <| (v : NumberField.InfinitePlace K) → v.Completion

private scoped instance scAdele_SecondCountableAdeleRing (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

end

theorem solution (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (NumberField.AdeleRing (NumberField.RingOfIntegers K) K) :=
  inferInstance

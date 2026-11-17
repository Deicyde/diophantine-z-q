/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_NumberField_Completion_Finite (git blob afd04b26caad84cd996d1ae6ab6a0514f58892ec, sha256 e5376cf29f62c90b40dd452ff8504c351cd5c304f98e3a1bbfb5fde8f44531b4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Mathlib_LinearAlgebra_Countable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

section

variable (K : Type*) [Field K] [NumberField K]

open NumberField

example (I : Ideal (𝓞 K)) (hI : I ≠ 0) : Finite ((𝓞 K) ⧸ I) :=
  Ideal.finiteQuotientOfFreeOfNeBot I hI

open IsDedekindDomain

variable (v : HeightOneSpectrum (𝓞 K))

open IsLocalRing

instance NumberField.instFiniteResidueFieldAdicCompletionIntegers :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  apply (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv.finite_iff.mp
  exact Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot

open scoped Valued in
instance : Finite (𝓀[v.adicCompletion K]) :=
  inferInstanceAs (Finite (ResidueField (v.adicCompletionIntegers K)))

instance NumberField.instCompactSpaceAdicCompletionIntegers :
    CompactSpace (v.adicCompletionIntegers K) :=
  Valued.WithZeroMulInt.integer_compactSpace (v.adicCompletion K) inferInstance
    (v.valuedAdicCompletion_surjective K)

lemma NumberField.isCompactAdicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  rw [isCompact_iff_compactSpace]
  exact instCompactSpaceAdicCompletionIntegers K v

lemma NumberField.isOpenAdicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

instance Rat.adicCompletion.locallyCompactSpace (v : HeightOneSpectrum (𝓞 ℚ)) :
    LocallyCompactSpace (v.adicCompletion ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isClosedEmbedding
  |>.locallyCompactSpace

instance (v : HeightOneSpectrum (𝓞 K)) :
    WeaklyLocallyCompactSpace (v.adicCompletion K) where
  exists_compact_mem_nhds x :=
    open Pointwise in
    ⟨x +ᵥ ((v.adicCompletionIntegers K) : Set (v.adicCompletion K)),
      (isCompact_iff_compactSpace.mpr <| instCompactSpaceAdicCompletionIntegers K v).vadd x,
      ((isOpenAdicCompletionIntegers K v).vadd x).mem_nhds (Set.mem_vadd_set.mpr ⟨0, by simp⟩)⟩

instance (v : HeightOneSpectrum (𝓞 K)) :
    LocallyCompactSpace (v.adicCompletion K) := inferInstance

example (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (v.adicCompletion K) :=
  inferInstance

end

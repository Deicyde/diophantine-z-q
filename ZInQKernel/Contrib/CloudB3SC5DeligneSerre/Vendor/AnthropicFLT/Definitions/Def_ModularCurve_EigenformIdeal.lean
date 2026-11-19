/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_EigenformIdeal (git blob 0d68eeadc152ccfecf07111127a8ca1b0f617c06, sha256 10dfeb4ffd24ecfd0d0b96702fc7aa085ef6a185592abfb5614110e32bb903a0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_HeckeGalois_EichlerShimura
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def IsEigenformIdeal (N : ℕ) (𝔪 : Ideal HeckeAlg) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
    (k : Type) (_ : Field k) (_ : Finite k) (𝒪 : Subring ℂ)
    (h𝒪 : ∀ ℓ : Nat.Primes, ModularFormClass.qCoeff f ℓ ∈ 𝒪) (φ : 𝒪 →+* k),
      𝔪 = eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩)

abbrev EigenformSupportAt (N p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J] : Prop :=
  EigenformSupport p J (IsEigenformIdeal N)

abbrev EichlerShimuraDataAt {K L : Type*} [Field K] [Field L] [Algebra K L] (N p : ℕ)
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction (L ≃ₐ[K] L) J] :
    Prop :=
  EichlerShimuraDataReduced (K := K) (L := L) N p J (IsEigenformIdeal N)

end ModularCurve

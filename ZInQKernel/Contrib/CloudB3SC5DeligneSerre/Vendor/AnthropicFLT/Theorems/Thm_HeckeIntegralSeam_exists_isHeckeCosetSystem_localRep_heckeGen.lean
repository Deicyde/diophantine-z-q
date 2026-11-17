/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen (git blob f1a4603482a12e2388f6965022196ba3c3fbb5ba, sha256 55e0c774bd2bb2427ea35b22a764efb5853ef3b1d07909c5a2e1a90b32e6ec5f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalLanglands_HeckeCosetSystem
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalLanglands_HeckeCosetLocal
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm LocalGL2 AdelicDock NumberField.AdelicLevel

theorem HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletionIntegers F,
      ∃ hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0,
        Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1 : ℤ) ∧
        finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) = heckeGen (𝓞 F) F v ∧
        ∃ sec : 𝓞 F ⧸ v.asIdeal → 𝓞 F,
          (∀ c : 𝓞 F ⧸ v.asIdeal, Ideal.Quotient.mk v.asIdeal (sec c) = c) ∧
          ∀ M : Ideal (𝓞 F), ¬ v.asIdeal ∣ M →
            HeckeIntegralSeam.IsHeckeCosetSystem
              (levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)
              (fun i : Option (𝓞 F ⧸ v.asIdeal) =>
                finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
                  (i.elim (localRepInf ϖ hϖ0)
                    (fun c => localRepSome ϖ hϖ0
                      (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec c)))))) := by
  revert F v
  exact @_root_.P2MW.S_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen.solution

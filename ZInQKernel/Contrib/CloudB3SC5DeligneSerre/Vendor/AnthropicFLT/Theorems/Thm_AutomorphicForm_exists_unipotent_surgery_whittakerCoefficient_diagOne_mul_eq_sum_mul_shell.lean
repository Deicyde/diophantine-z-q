/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_shell (git blob 4c86ff4b66a9aaedd3fff4ce605903f9059e9859, sha256 a2401dfad8a0d9ed0417891b6c7097529f6ebcb43f0469eec49ebd21411732de).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_shell

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm IsDedekindDomain
open scoped Classical

theorem AutomorphicForm.exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_shell
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (G : AdelicGL2 (𝓞 K) K → ℂ)
    (hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K),
      G (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * h) = G (unipotentGL2 u * h))
    (hint : ∀ (α : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) G α g)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (a : HeightOneSpectrum (𝓞 K) → ℤ) :
    ∃ (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ),
      (∀ i, (y i).1 = 0 ∧ ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → (y i).2 w = 0) ∧
      (∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
        unipotentGL2 (y i) * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * unipotentGL2 (y i)) ∧
      (∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (y i) = unipotentGL2 (y i) * g') →
        whittakerCoefficient K
            (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
            (fun g => ∑ i, cs i * G (g * unipotentGL2 (y i))) 1 (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) *
            whittakerCoefficient K
              (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) G 1 (diagOne t * g')) ∧
      (∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
              ((Multiplicative.ofAdd (a v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0) := by
  revert K D G hper hint S m a
  exact @_root_.P2MW.S_AutomorphicForm_exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_shell.solution

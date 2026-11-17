/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy (git blob fa418bfa6be36ec60f0bcf7f220056951e3d1552, sha256 fd7d852c1aeb0bc6fedadca9d92d515fbd423a0d73466708eef71f1204d4cea3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

theorem AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy
    (K : Type) [Field K] [NumberField K]
    (h1 : ∀ v v' : InfinitePlace K, v.IsComplex → v'.IsComplex → v = v')
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x)
    (hxG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x g)
    (nw : ∀ v : InfinitePlace K, v.IsReal → ℤ) (lam : ∀ v : InfinitePlace K, v.IsReal → ℝ)
    (hxn : ∀ (v : InfinitePlace K) (hv : v.IsReal), HasArchCharacterAt₀ K v (archWeightCharAt hv (nw v hv)) x)
    (hreg : ∀ (v : InfinitePlace K) (hv : v.IsReal) (l : List ArchDir),
      IsArchSmoothAt hv (l.foldr (archDerivAt hv) x) ∧ Continuous (l.foldr (archDerivAt hv) x))
    (hgr : ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              g‖ ≤
        C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (hcas : ∀ (v : InfinitePlace K) (hv : v.IsReal), archCasimirAt hv x = ((lam v hv : ℝ) : ℂ) • x)
    (harch : ∀ (v : InfinitePlace K) (hv : v.IsReal),
      0 < lam v hv ∨
      (∃ (ε : ℝ) (k₀ M : ℕ), (ε = 1 ∨ ε = -1) ∧ 2 ≤ k₀ ∧ lam v hv = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
        ((nw v hv : ℤ) : ℝ) = ε * (k₀ + 2 * M) ∧ (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M + 1] x = 0 ∧
        ∃ Mgr : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
          ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M] x) 1
              g‖ ≤
            Mgr * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) ∨
      (lam v hv = 0 ∧ ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ),
        Matrix.GeneralLinearGroup.det h = 1 → x (g * archRealGLAt hv h) = x g))
    (hcx : ∀ (v : InfinitePlace K), v.IsComplex → ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ v → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (diagOne a)‖ ≤
            C * ‖((a : AdeleRing (𝓞 K) K)).1 v‖ ^ ((v.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 v‖) ^ δ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (diagOne a)‖ ≤
          C * ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := by
  revert K h1 D ξ w₀ hξ x hxc hxG hxZ nw lam hxn hreg hgr hcas harch hcx
  exact @_root_.P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy.solution

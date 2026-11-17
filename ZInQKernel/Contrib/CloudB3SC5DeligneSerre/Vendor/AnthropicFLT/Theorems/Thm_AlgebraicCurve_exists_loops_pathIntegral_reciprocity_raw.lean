/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw (git blob 03f561bc86f86b869a4cd54881086a4bc58f96ab, sha256 6c69db8defa68110bd86964d113e018cae127c38b81fd88af41fdd5850e0d2e3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.exists_loops_pathIntegral_reciprocity_raw
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (S : Finset (Place ℂ F)) :
    ∃ (Pz : Fin n ⊕ Fin n → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
      (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ),
      (∀ k t, Z k t ∉ S ∧ Z k t ≠ P₀) ∧ Q.transpose = -Q ∧ IsUnit Q.det ∧
      (∀ (P : Place ℂ F) (δ : Path P P), ∃ κ : Fin n ⊕ Fin n → ℤ,
        ∀ ξ ∈ regularDifferentials ℂ F,
          pathIntegral ξ δ = ∑ k, ((κ k : ℂ) * pathIntegral ξ (Z k))) ∧
      (∀ (P : Place ℂ F) (δ : Path P P), (∀ t, δ t ∉ S) →
        ∃ (κ : Fin n ⊕ Fin n → ℤ) (w : Place ℂ F → ℤ), ∀ θ : Ω[F⁄ℂ],
          (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
          (∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ) →
          pathIntegral θ δ =
            ∑ k, ((κ k : ℂ) * pathIntegral θ (Z k)) +
              2 * Real.pi * Complex.I *
                ∑ v ∈ S, (w v : ℂ) * Place.evalAt v (v.dCoordFn * v.differentialCoeff θ)) ∧
      (∀ ξ ∈ regularDifferentials ℂ F, ∀ ξ' ∈ regularDifferentials ℂ F,
        ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral ξ (Z k) * pathIntegral ξ' (Z l) = 0) ∧
      (∀ (E : Divisor ℂ F) (θ : Ω[F⁄ℂ]),
        (∀ v : Place ℂ F, -1 ≤ v.ordDifferential θ) →
        (∀ v : Place ℂ F, Place.evalAt v (v.dCoordFn * v.differentialCoeff θ) = (E v : ℂ)) →
        (∀ v : Place ℂ F, E v ≠ 0 → v ∈ S) →
        ∃ κ : Fin n ⊕ Fin n → ℤ, ∀ i : Fin n,
          ∑ k, ∑ l, (Q k l : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (Z k) * pathIntegral θ (Z l) =
            2 * Real.pi * Complex.I *
              (abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ E i +
                ∑ k, ((κ k : ℂ) * pathIntegral (b i : Ω[F⁄ℂ]) (Z k)))) := by
  revert F hfg hF n b P₀ S
  exact @_root_.P2MW.S_AlgebraicCurve_exists_loops_pathIntegral_reciprocity_raw.solution

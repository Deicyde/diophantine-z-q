/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_pairedCellFamily (git blob 8cb8b8fbcb0f04a1926d1590cb2e2436e343e752, sha256 7a30ff97c7b8a8f372112acae37caa15b891994608f5f78142b08cabbb5995cb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CellDissection
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_pairedCellFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Manifold ContDiff Topology Real
open Set AlgebraicCurve Complex

theorem AlgebraicCurve.exists_pairedCellFamily
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
    (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ (m : ℕ) (cell : Fin m → Cell F)
      (pair : (Σ C : Fin m, Fin (cell C).R.N) → (Σ C : Fin m, Fin (cell C).R.N))
      (orient : (Σ C : Fin m, Fin (cell C).R.N) → Bool),
      (∀ a, pair (pair a) = a) ∧
      (∀ a, orient (pair a) = !orient a) ∧
      (∀ (C : Fin m) (k : Fin (cell C).R.N) (C' : Fin m)
        (k' : Fin (cell C').R.N),
        pair ⟨C, k⟩ = ⟨C', k'⟩ → orient ⟨C, k⟩ = true →
        ∃ ψ : ℝ → ℝ,
          StrictAntiOn ψ ((cell C').R.arcIcc k') ∧
          ContDiffOn ℝ 1 ψ ((cell C').R.arcIcc k') ∧
          ψ ((cell C').R.φs k'.castSucc) = (cell C).R.φs k.succ ∧
          ψ ((cell C').R.φs k'.succ) = (cell C).R.φs k.castSucc ∧
          ∀ t ∈ (cell C').R.arcIcc k', (cell C').bdry t = (cell C).bdry (ψ t)) ∧
      (∀ w : Place ℂ F, ∃ C : Fin m, w ∈ (cell C).carrier) ∧
      (∀ (C C' : Fin m) (x : Place ℂ F), x ∈ (cell C).carrier →
        x ∈ (cell C').carrier → Relation.ReflTransGen
          (fun X Y : Fin m => ∃ (k : Fin (cell X).R.N) (k' : Fin (cell Y).R.N),
            pair ⟨X, k⟩ = ⟨Y, k'⟩ ∧ x ∈ (cell X).arc k) C C') ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∃ C : Fin m, v ∈ (cell C).interior') ∧
      (∀ C : Fin m, ((cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) ∧
      (2 * ({v : Place ℂ F | ∃ (C : Fin m) (k : Fin (cell C).R.N),
        v = (cell C).bdry ((cell C).R.φs k.castSucc) ∨
          v = (cell C).bdry ((cell C).R.φs k.succ)}.ncard : ℤ)
        - (∑ C : Fin m, ((cell C).R.N : ℤ)) + 2 * (m : ℤ)
        = 2 * (2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ))) ∧
      (∀ v ∈ (S : Set (Place ℂ F)), ∃ C : Fin m,
        v ∈ (cell C).interior' ∧ (cell C).ζ v = (cell C).R.q) := by
  revert F hfg hF P₀ S
  exact @_root_.P2MW.S_AlgebraicCurve_exists_pairedCellFamily.solution

/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_dissectionScaleData (git blob 4cc3ebe8fc1b82214fa5c73c178a9a5a1dff22aa, sha256 170dc840d84a52781e39c572695b9ff8e5dbb68177bde85ba83ed88432efae20).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_dissectionScaleData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open scoped Manifold ContDiff Topology Real
open Set AlgebraicCurve Complex

theorem AlgebraicCurve.exists_dissectionScaleData
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
    ∃ (x : F) (n : ℕ) (Bad : Finset ℂ) (o : ℝ) (hm : ℝ) (jlo : ℤ) (jhi : ℤ) (klo : ℤ) (khi : ℤ)
      (Rw : ℝ) (capAt : ℤ × ℤ → Option ℂ) (margin : ℤ × ℤ → Set ℂ)
      (sheet : ℤ × ℤ → Fin n → OpenPartialHomeomorph (Place ℂ F) ℂ)
      (capζ : ℂ → Place ℂ F → OpenPartialHomeomorph (Place ℂ F) ℂ) (capρ : ℂ → Place ℂ F → ℝ)
      (cape : ℂ → Place ℂ F → ℕ) (cs : ℂ → ℝ)
      (infζ : Place ℂ F → OpenPartialHomeomorph (Place ℂ F) ℂ) (infρ : Place ℂ F → ℝ)
      (infe : Place ℂ F → ℕ) (centre : ℤ × ℤ → ℂ),
      (Transcendental ℂ x) ∧
      (FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F) ∧
      (0 < n) ∧
      (n = Module.finrank (IntermediateField.adjoin ℂ ({x} : Set F)) F) ∧
      (∀ b : ℂ, {w : Place ℂ F | x ∈ w.toValuationSubring ∧ Place.evalAt w x = b}.Finite) ∧
      (∀ t : ℂ, t ∉ Bad →
        {w : Place ℂ F | x ∈ w.toValuationSubring ∧ Place.evalAt w x = t}.ncard = n) ∧
      ({w : Place ℂ F | x ∉ w.toValuationSubring}.Finite) ∧
      (0 < hm) ∧
      (jlo + 1 < jhi) ∧
      (klo + 1 < khi) ∧
      (1 < Rw) ∧
      (∀ z : ℂ, ‖z‖ ≤ Rw →
        (o + jlo * hm < z.re ∧ z.re < o + (jhi + 1) * hm) ∧ (o + klo * hm < z.im ∧ z.im < o + (khi + 1) * hm)) ∧
      (∀ z : ℂ, ‖z‖ < Rw - 1 →
        (o + (jlo + 1) * hm < z.re ∧ z.re < o + jhi * hm) ∧ (o + (klo + 1) * hm < z.im ∧ z.im < o + khi * hm)) ∧
      (∀ b ∈ Bad, ‖b‖ < Rw - 1) ∧
      (∀ b ∈ Bad, ∀ j : ℤ, b.re - o ≠ j * hm ∧ b.im - o ≠ j * hm) ∧
      (∀ b ∈ Bad, ∀ b' ∈ Bad, b ≠ b' →
        2 ≤ |⌊(b.re - o) / hm⌋ - ⌊(b'.re - o) / hm⌋| ∨ 2 ≤ |⌊(b.im - o) / hm⌋ - ⌊(b'.im - o) / hm⌋|) ∧
      (∀ (p : ℤ × ℤ) (b : ℂ), capAt p = some b ↔
        b ∈ Bad ∧ ⌊(b.re - o) / hm⌋ = p.1 ∧ ⌊(b.im - o) / hm⌋ = p.2) ∧
      (∀ p : ℤ × ℤ, p.1 = jlo ∨ p.1 = jhi ∨ p.2 = klo ∨ p.2 = khi → capAt p = none) ∧
      (∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none → IsOpen (margin p)) ∧
      (∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none →
        {z : ℂ | z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
          z.im ∈ Icc (o + p.2 * hm) (o + (p.2 + 1) * hm)} ⊆ margin p) ∧
      (∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none → ∀ b ∈ Bad, b ∉ margin p) ∧
      (∀ p : ℤ × ℤ, p ∈ Icc jlo jhi ×ˢ Icc klo khi → capAt p = none →
        ((∀ i, (sheet p i).target = margin p) ∧
            (∀ i, ∀ P ∈ (sheet p i).source, x ∈ P.toValuationSubring ∧ sheet p i P = Place.evalAt P x) ∧
            (Pairwise fun i j => Disjoint (sheet p i).source (sheet p j).source) ∧
            (∀ P : Place ℂ F, x ∈ P.toValuationSubring → Place.evalAt P x ∈ margin p →
              ∃ i, P ∈ (sheet p i).source))) ∧
      (∀ b ∈ Bad, 4 * hm < cs b) ∧
      (∀ b ∈ Bad, ∀ b' ∈ Bad, b' ≠ b → 2 * cs b ≤ dist b b') ∧
      (∀ b ∈ Bad, ∀ w : Place ℂ F, x ∈ w.toValuationSubring → Place.evalAt w x = b →
        (0 < capρ b w ∧ 0 < cape b w ∧ w ∈ (capζ b w).source ∧ capζ b w w = 0 ∧
            (capζ b w).target = Metric.ball 0 (capρ b w) ∧
            (capζ b w).source ⊆ (extChartAt 𝓘(ℂ, ℂ) w).source ∧
            AnalyticOnNhd ℂ (capζ b w ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) (extChartAt 𝓘(ℂ, ℂ) w '' (capζ b w).source) ∧
            (∀ z ∈ extChartAt 𝓘(ℂ, ℂ) w '' (capζ b w).source, deriv (capζ b w ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) z ≠ 0) ∧
            (∀ P ∈ (capζ b w).source, (x - algebraMap ℂ F b) ∈ P.toValuationSubring ∧ Place.evalAt P (x - algebraMap ℂ F b) = (capζ b w P) ^ cape b w) ∧
            cape b w = (w.ord (x - algebraMap ℂ F b)).toNat)) ∧
      (∀ b ∈ Bad, ∀ w : Place ℂ F, x ∈ w.toValuationSubring → Place.evalAt w x = b →
        2 * cs b < capρ b w ^ cape b w) ∧
      (∀ b ∈ Bad, ∀ w w' : Place ℂ F,
        x ∈ w.toValuationSubring → Place.evalAt w x = b →
        x ∈ w'.toValuationSubring → Place.evalAt w' x = b → w ≠ w' →
        Disjoint (capζ b w).source (capζ b w').source) ∧
      (∀ b ∈ Bad, ∀ P : Place ℂ F, x ∈ P.toValuationSubring →
        ‖Place.evalAt P x - b‖ < 2 * cs b →
        ∃ w : Place ℂ F, x ∈ w.toValuationSubring ∧ Place.evalAt w x = b ∧ P ∈ (capζ b w).source) ∧
      (∀ w : Place ℂ F, x ∉ w.toValuationSubring → (0 < infρ w ∧ 0 < infe w ∧ w ∈ (infζ w).source ∧ infζ w w = 0 ∧
        (infζ w).target = Metric.ball 0 (infρ w) ∧
        (infζ w).source ⊆ (extChartAt 𝓘(ℂ, ℂ) w).source ∧
        AnalyticOnNhd ℂ (infζ w ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) (extChartAt 𝓘(ℂ, ℂ) w '' (infζ w).source) ∧
        (∀ z ∈ extChartAt 𝓘(ℂ, ℂ) w '' (infζ w).source, deriv (infζ w ∘ (extChartAt 𝓘(ℂ, ℂ) w).symm) z ≠ 0) ∧
        (∀ P ∈ (infζ w).source, x⁻¹ ∈ P.toValuationSubring ∧ Place.evalAt P x⁻¹ = (infζ w P) ^ infe w) ∧
        infe w = (w.ord x⁻¹).toNat)) ∧
      (∀ w : Place ℂ F, x ∉ w.toValuationSubring → 1 / Rw < infρ w ^ infe w) ∧
      (∀ w w' : Place ℂ F, x ∉ w.toValuationSubring → x ∉ w'.toValuationSubring → w ≠ w' →
        Disjoint (infζ w).source (infζ w').source) ∧
      (∀ P : Place ℂ F, x ∈ P.toValuationSubring → Rw ≤ ‖Place.evalAt P x‖ →
        ∃ w : Place ℂ F, x ∉ w.toValuationSubring ∧ P ∈ (infζ w).source) ∧
      (∀ p : ℤ × ℤ, (o + p.1 * hm < (centre p).re ∧ (centre p).re < o + (p.1 + 1) * hm) ∧
        (o + p.2 * hm < (centre p).im ∧ (centre p).im < o + (p.2 + 1) * hm)) ∧
      (∀ p : ℤ × ℤ, p.1 = jhi → o + p.2 * hm < 0 → 0 < o + (p.2 + 1) * hm → (centre p).im = 0) ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), x ∈ v.toValuationSubring → Place.evalAt v x ∉ Bad →
        ‖Place.evalAt v x‖ < Rw - 1 ∧
        (∀ j : ℤ, (Place.evalAt v x).re - o ≠ j * hm ∧ (Place.evalAt v x).im - o ≠ j * hm) ∧
        capAt (⌊((Place.evalAt v x).re - o) / hm⌋, ⌊((Place.evalAt v x).im - o) / hm⌋) = none ∧
        centre (⌊((Place.evalAt v x).re - o) / hm⌋, ⌊((Place.evalAt v x).im - o) / hm⌋) = Place.evalAt v x) ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), ∀ v' ∈ insert P₀ (S : Set (Place ℂ F)), x ∈ v.toValuationSubring → x ∈ v'.toValuationSubring →
        Place.evalAt v x ∉ Bad → Place.evalAt v' x ∉ Bad → Place.evalAt v x ≠ Place.evalAt v' x →
        (⌊((Place.evalAt v x).re - o) / hm⌋, ⌊((Place.evalAt v x).im - o) / hm⌋) ≠
          (⌊((Place.evalAt v' x).re - o) / hm⌋, ⌊((Place.evalAt v' x).im - o) / hm⌋)) ∧
      (∀ v ∈ insert P₀ (S : Set (Place ℂ F)), x ∈ v.toValuationSubring → ‖Place.evalAt v x‖ < Rw - 1) := by
  revert F hfg hF P₀ S
  exact @_root_.P2MW.S_AlgebraicCurve_exists_dissectionScaleData.solution

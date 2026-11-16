/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_WeierstrassCurve_OddOrderSummingSet
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

namespace WeierstrassCurve

namespace Affine.Point

variable {R : Type*} [CommRing R] {W : Affine R}

def coordsOrZero : W.Point → R × R
  | .zero => (0, 0)
  | .some x y _ => (x, y)

@[simp] lemma coordsOrZero_zero : ((.zero : W.Point)).coordsOrZero = (0, 0) := rfl

@[simp] lemma coordsOrZero_some {x y : R} (h : W.Nonsingular x y) :
    (Point.some x y h).coordsOrZero = (x, y) := rfl

end Affine.Point

section SummingSet

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

def oddOrderSummingSet (Q : W.toAffine.Point) (n : ℕ) : Finset (F × F) :=
  (Finset.Icc 1 n).image fun k => (k • Q).coordsOrZero

lemma mem_oddOrderSummingSet {Q : W.toAffine.Point} {n : ℕ} {P : F × F} :
    P ∈ W.oddOrderSummingSet Q n ↔ ∃ k, 1 ≤ k ∧ k ≤ n ∧ (k • Q).coordsOrZero = P := by
  simp only [oddOrderSummingSet, Finset.mem_image, Finset.mem_Icc]
  exact ⟨fun ⟨k, ⟨h1, h2⟩, h3⟩ => ⟨k, h1, h2, h3⟩, fun ⟨k, h1, h2, h3⟩ => ⟨k, ⟨h1, h2⟩, h3⟩⟩

end SummingSet

end WeierstrassCurve

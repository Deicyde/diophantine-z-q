/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 4d91513e4d30, module
-- TauCeti.NumberTheory.ModularForms.Petersson.Trace), Apache-2.0: declarations added to that module
-- after commit 5a01f5fe, whose version is vendored as
-- `ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Petersson.Trace`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Petersson.Trace
public import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ModularForms.Basic
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# Orthogonality across two levels (backport)

* `CuspForm.peterssonInnerCosets_restrict_restrict_eq_zero`: for `L = A ⊓ B` inside a group `D`
  that factors as `A · B`, a form for `B` orthogonal to the forms for `D` is, on `L`, orthogonal
  to the forms for `A`.
-/

public section

open UpperHalfPlane ModularGroup Matrix.SpecialLinearGroup

open scoped MatrixGroups ModularForm ComplexConjugate Pointwise

namespace CuspForm

variable {k : ℤ}

/-! ### Orthogonality across two levels -/

/-- The case `A ≤ D` of `peterssonInnerCosets_restrict_restrict_eq_zero`. -/
private theorem peterssonInnerCosets_restrict_restrict_eq_zero_of_le {A B D L : Subgroup SL(2, ℤ)}
    [A.FiniteIndex] [B.FiniteIndex] [D.FiniteIndex] [L.FiniteIndex] (hAD : A ≤ D) (hBD : B ≤ D)
    (hL : L = A ⊓ B) (hmul : ∀ d ∈ D, ∃ a ∈ A, ∃ b ∈ B, a * b = d)
    {F : CuspForm (B.map (mapGL ℝ)) k}
    (hF : ∀ ψ : CuspForm (D.map (mapGL ℝ)) k,
      peterssonInnerCosets (CuspForm.restrict (Subgroup.map_mono hBD) ψ) F = 0)
    (φ : CuspForm (A.map (mapGL ℝ)) k) :
    peterssonInnerCosets (CuspForm.restrict (Subgroup.map_mono (hL.trans_le inf_le_left)) φ)
      (CuspForm.restrict (Subgroup.map_mono (hL.trans_le inf_le_right)) F) = 0 := by
  have hLAB : L.map (mapGL ℝ) = A.map (mapGL ℝ) ⊓ B.map (mapGL ℝ) := by
    rw [hL, Subgroup.map_inf_eq _ _ _ mapGL_injective]
  -- factorizations in `SL(2, ℤ)` give factorizations of the images in `GL(2, ℝ)`
  have hmap : ∀ {X Y : Subgroup SL(2, ℤ)}, (∀ d ∈ D, ∃ x ∈ X, ∃ y ∈ Y, x * y = d) →
      ∀ h ∈ D.map (mapGL ℝ), ∃ x ∈ X.map (mapGL ℝ), ∃ y ∈ Y.map (mapGL ℝ), x * y = h := by
    rintro X Y hXY _ ⟨d, hd, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hXY d hd
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, (map_mul _ x y).symm⟩
  by_cases hneg : (-1 : SL(2, ℤ)) ∈ B → (-1 : SL(2, ℤ)) ∈ L
  · -- pair at level `B`: the trace of `φ` from `L` to `B` is the restriction of its trace to `D`
    have hmul' : ∀ d ∈ D, ∃ b ∈ B, ∃ a ∈ A, b * a = d := fun d hd ↦ by
      obtain ⟨a, ha, b, hb, hab⟩ := hmul d⁻¹ (inv_mem hd)
      exact ⟨b⁻¹, inv_mem hb, a⁻¹, inv_mem ha, by rw [← mul_inv_rev, hab, inv_inv]⟩
    rw [← peterssonInnerCosets_trace_left hLAB hneg φ F,
      ← CuspForm.restrict_trace (Subgroup.map_mono hBD) (hmap hmul')]
    exact hF _
  · -- otherwise `-I ∈ B` but `-I ∉ A`: pair at level `A`, where the trace of `F` from `L` is
    -- the restriction of its trace to `D`, and that trace vanishes because it is orthogonal to
    -- itself
    obtain ⟨hB1, hL1⟩ := not_imp.mp hneg
    have hA1 : (-1 : SL(2, ℤ)) ∉ A := fun hA1 ↦ hL1 (hL ▸ ⟨hA1, hB1⟩)
    have hB : B.map (mapGL ℝ) = B.map (mapGL ℝ) ⊓ D.map (mapGL ℝ) :=
      (inf_eq_left.mpr (Subgroup.map_mono hBD)).symm
    have htr : CuspForm.trace (D.map (mapGL ℝ)) F = 0 := by
      refine peterssonInnerCosets_definite _ ?_
      rw [peterssonInnerCosets_trace_left hB (fun _ ↦ hB1), ← peterssonInnerCosets_conj_symm]
      exact (congrArg conj (hF _)).trans (map_zero _)
    rw [← peterssonInnerCosets_conj_symm,
      ← peterssonInnerCosets_trace_left (hLAB.trans (inf_comm _ _)) (fun h ↦ absurd h hA1) F φ,
      ← CuspForm.restrict_trace (Subgroup.map_mono hAD) (hmap hmul), htr,
      (CuspForm.restrict_eq_zero_iff _).mpr rfl, peterssonInnerCosets_zero_left, map_zero]

/-- **Orthogonality to the lower level survives restriction to the intersection.** Let
`L = A ⊓ B`, with `B ≤ D` and every element of `D` a product of one of `A` and one of `B`. If a
cusp form `F` for `B` is Petersson-orthogonal to (the restriction of) every cusp form for `D`,
then on `L` its restriction is orthogonal to the restriction of every cusp form for `A`.

For `A = Γ₁(N)`, `B = Γ₁(M)`, `D = Γ₁(gcd N M)` and `L = Γ₁(lcm N M)` this compares forms of two
levels neither of which divides the other: a form of level `M` orthogonal to the forms of level
`gcd N M` stays orthogonal, at level `lcm N M`, to all forms of level `N`. -/
theorem peterssonInnerCosets_restrict_restrict_eq_zero {A B D L : Subgroup SL(2, ℤ)}
    [A.FiniteIndex] [B.FiniteIndex] [D.FiniteIndex] [L.FiniteIndex] (hBD : B ≤ D)
    (hL : L = A ⊓ B) (hmul : ∀ d ∈ D, ∃ a ∈ A, ∃ b ∈ B, a * b = d)
    {F : CuspForm (B.map (mapGL ℝ)) k}
    (hF : ∀ ψ : CuspForm (D.map (mapGL ℝ)) k,
      peterssonInnerCosets (CuspForm.restrict (Subgroup.map_mono hBD) ψ) F = 0)
    (φ : CuspForm (A.map (mapGL ℝ)) k) :
    peterssonInnerCosets (CuspForm.restrict (Subgroup.map_mono (hL.trans_le inf_le_left)) φ)
      (CuspForm.restrict (Subgroup.map_mono (hL.trans_le inf_le_right)) F) = 0 := by
  -- replace `A` by `A ⊓ D`, which lies in `D`
  have hL' : L = (A ⊓ D) ⊓ B := by rw [hL, inf_assoc, inf_eq_right.mpr hBD]
  have hmul' : ∀ d ∈ D, ∃ a ∈ A ⊓ D, ∃ b ∈ B, a * b = d := fun d hd ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := hmul d hd
    exact ⟨a, ⟨ha, by simpa using mul_mem_cancel_right (hBD hb) |>.mp hd⟩, b, hb, rfl⟩
  have key := peterssonInnerCosets_restrict_restrict_eq_zero_of_le inf_le_right hBD hL' hmul' hF
    (CuspForm.restrict (Subgroup.map_mono inf_le_left) φ)
  convert key using 2
  ext
  simp

end CuspForm

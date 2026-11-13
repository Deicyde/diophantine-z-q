import ZInQKernel.Contrib.DifferentBound.UnramifiedFactor
import Mathlib.RingTheory.Nakayama

/-!
# The uniformizer-generation property needed by the Serre proof

This is the residue-surjective DVR case, not a port of general monogenic
existence. The proof constructs truncated residue digits at every power of the
actual upper uniformizer, then applies Nakayama at the actual lower maximal
ideal. It uses the proved identity `m_A B = m_B ^ e`.

The comparison with the more general generation criterion was read in
TauCeti/RingTheory/LocalRing/Monogenic.lean, revision
`a6027b1d24fcb935c53bd5b50d11b40991cda418` (Apache-2.0; Tau Ceti contributors,
Bianca Viray, Bryan Boehnke, Grant Yang, George Peykanu, Tianshuo Wang).
No generator, power basis, or bound is asserted without proof.
-/

namespace ZInQ.Contrib.DifferentBound

open IsLocalRing

/-- In a finite faithful residue-surjective DVR extension, every upper uniformizer generates
the upper ring. The residue digits and all required powers are constructed explicitly. -/
theorem adjoin_eq_top_of_residue_surjective_uniformizer
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [(maximalIdeal B).LiesOver (maximalIdeal A)]
    (hres : Function.Surjective ((residue B).comp (algebraMap A B)))
    {π : B} (hπ : Irreducible π) : Algebra.adjoin A {π} = ⊤ := by
  let S := Algebra.adjoin A {π}
  have hπmem : π ∈ S := Algebra.subset_adjoin (Set.mem_singleton π)
  have hdigits : ∀ (n : ℕ) (b : B), ∃ y ∈ S, ∃ z : B, b = y + π ^ n * z := by
    intro n
    induction n with
    | zero =>
      intro b
      exact ⟨0, S.zero_mem, b, by simp⟩
    | succ n ih =>
      intro b
      obtain ⟨a, ha⟩ := hres (residue B b)
      simp only [RingHom.comp_apply] at ha
      have hdiff : b - algebraMap A B a ∈ maximalIdeal B := by
        rw [← residue_eq_zero_iff, map_sub]
        exact sub_eq_zero.mpr ha.symm
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hdiff
      obtain ⟨z, hz⟩ := hdiff
      obtain ⟨y, hy, w, hw⟩ := ih z
      refine ⟨algebraMap A B a + π * y,
        S.add_mem (S.algebraMap_mem a) (S.mul_mem hπmem hy), w, ?_⟩
      rw [show b = algebraMap A B a + π * z by linear_combination hz, hw, pow_succ]
      ring
  have hsup : S.toSubmodule ⊔
      ((maximalIdeal A).map (algebraMap A B)).restrictScalars A = ⊤ := by
    rw [UnramifiedFactor.map_maximalIdeal_eq_pow_ramificationIdx]
    refine eq_top_iff.mpr fun b _ ↦ ?_
    obtain ⟨y, hy, z, hb⟩ := hdigits ((maximalIdeal B).ramificationIdx A) b
    refine Submodule.mem_sup.mpr ⟨y, hy, π ^ (maximalIdeal B).ramificationIdx A * z, ?_, hb.symm⟩
    rw [Submodule.restrictScalars_mem, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  rw [← Algebra.toSubmodule_eq_top]
  change S.toSubmodule = ⊤
  refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot
    (I := maximalIdeal A) (Module.finite_def.mp inferInstance)
    (maximalIdeal_le_jacobson (⊥ : Ideal A)) ?_)
  rw [Ideal.smul_top_eq_map]
  exact hsup.ge

end ZInQ.Contrib.DifferentBound

/-
H5 lane3 Step 2, B2.c `TrivialLineSectionDichotomy` (Step2B2/Plan.lean 09cbbfbe) PROVED.
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

Proof: transport `s` along `e : L ≅ O_C` to the endomorphism `c := s ≫ e.hom` of the unit.
* If `c = 0`, then `s = 0`.
* Otherwise `c` is an isomorphism by Step1 `isIso_of_ne_zero_endo_unit` (SectionsBothWays.lean
  fc6ff9b8): a nonzero global function on a proper integral scheme over a field is a unit,
  by PMGF. So `s = c ≫ e.inv` is an isomorphism.
Neither algebraic closure nor a rational point is needed.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.Plan
import ZInQKernel.Contrib.CloudR2NOS.Step1.SectionsBothWays

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step2B2

theorem trivialLineSectionDichotomy : TrivialLineSectionDichotomy.{u} := by
  intro K _ _ C fC _ _ L _ he s
  obtain ⟨e⟩ := he
  have hs : s = (s ≫ e.hom) ≫ e.inv := by simp
  by_cases h : s ≫ e.hom = 0
  · left
    rw [hs, h, Limits.zero_comp]
  · right
    haveI := ZInQ.Contrib.CloudR2NOS.Step1.isIso_of_ne_zero_endo_unit fC (s ≫ e.hom) h
    rw [hs]
    infer_instance

end ZInQ.Contrib.CloudR2NOS.Step2B2

import Mathlib.RingTheory.Flat.EquationalCriterion

set_option autoImplicit false

open scoped BigOperators

namespace RC53.EllAdic

universe u v w

variable {R : Type u} [CommRing R]
variable (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
variable {L : Type w} [AddCommGroup L] [Module R L]

/-- Flatness passes to a countable directed colimit, stated using explicit
representatives and eventual equality to zero. All linear maps are over the
same base ring; no injectivity assumption on the transition maps is needed. -/
theorem flat_of_sequence_representatives
    (step : ∀ {i j : ℕ}, i ≤ j → M i →ₗ[R] M j) (ι : ∀ i, M i →ₗ[R] L)
    (hcomm : ∀ {i j : ℕ} (h : i ≤ j) (z : M i), ι j (step h z) = ι i z)
    (rep : ∀ x : L, ∃ (i : ℕ) (z : M i), ι i z = x)
    (dies : ∀ (i : ℕ) (z : M i), ι i z = 0 → ∃ (j : ℕ) (h : i ≤ j), step h z = 0)
    (stageFlat : ∀ i, Module.Flat R (M i)) : Module.Flat R L := by
  classical
  apply Module.Flat.iff_forall_isTrivialRelation.mpr
  intro l f x hx
  choose i y hy using fun j : Fin l => rep (x j)
  let N := (Finset.univ : Finset (Fin l)).sup i
  have hN (j : Fin l) : i j ≤ N := Finset.le_sup (f := i) (Finset.mem_univ j)
  let z (j : Fin l) := step (hN j) (y j)
  have hz (j : Fin l) : ι N (z j) = x j := (hcomm (hN j) (y j)).trans (hy j)
  have zeroInLimit : ι N (∑ j, f j • z j) = 0 := by
    simpa only [map_sum, map_smul, hz] using (show ∑ j, f j • x j = 0 from hx)
  obtain ⟨P, hNP, hP⟩ := dies N (∑ j, f j • z j) zeroInLimit
  have relationAtP : ∑ j, f j • step hNP (z j) = 0 := by
    simpa only [map_sum, map_smul] using hP
  obtain ⟨k, a, b, hgen, hcoeff⟩ :=
    (Module.Flat.iff_forall_isTrivialRelation.mp (stageFlat P)) relationAtP
  refine ⟨k, a, fun j => ι P (b j), ?_, hcoeff⟩
  intro j
  calc
    x j = ι P (step hNP (z j)) := (hcomm hNP (z j) |>.trans (hz j)).symm
    _ = ∑ s, a j s • ι P (b s) := by
      simpa only [map_sum, map_smul] using congrArg (fun m : M P => ι P m) (hgen j)

end RC53.EllAdic

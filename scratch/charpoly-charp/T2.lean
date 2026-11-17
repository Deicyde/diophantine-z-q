import Mathlib
open Polynomial Module
example {K E W : Type*} [Field K] [Field E] [Algebra K E] [AddCommGroup W]
    [Module K W] {d : Type*} [Fintype d]
    {f : d → Module.End K W}  :
    LinearIndependent E (fun i => (f i).baseChange E) := by
  refine Fintype.linearIndependent_iffₛ.mpr fun c c' hc => ?_
  sorry
example {K E W : Type*} [Field K] [Field E] [Algebra K E] [AddCommGroup W]
    [Module K W] {d : Type*} [Fintype d]
    {f : d → Module.End K W}  :
    LinearIndependent E (fun i => (f i).baseChange E) := by
  rw [Fintype.linearIndependent_iff]
  sorry

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# bp-qmmoduli: `|(𝒪/3𝒪)^×| = 72` by kernel computation

`𝒪/3𝒪` modelled on `(Fin 4 → ZMod 3)` with the structure constants `mulCoord` of `QMOrder.lean`
reduced mod 3 (N5's basis `1, i, (1+j)/2, (i+k)/2`; unit `e₀ = (1,0,0,0)`). The count of
two-sided units is 72 (h-trust A3; h-b1 M3 uses it for `|Γ'| = 144`). No `sorry`, no `axiom`,
no `native_decide`.
-/

namespace BPQM.Mod3

abbrev R3 := Fin 4 → ZMod 3

def mul3 (n m : R3) : R3 :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

def e0 : R3 := ![1, 0, 0, 0]

/-- Two-sided units of `𝒪/3𝒪`. -/
def IsUnit3 (n : R3) : Prop := ∃ m : R3, mul3 n m = e0 ∧ mul3 m n = e0

instance : DecidablePred IsUnit3 := fun n => by unfold IsUnit3; infer_instance

theorem card_units : (Finset.univ.filter IsUnit3).card = 72 := by decide +kernel

end BPQM.Mod3

#print axioms BPQM.Mod3.card_units

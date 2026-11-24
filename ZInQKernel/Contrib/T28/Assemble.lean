import ZInQKernel.Contrib.T28.Mestre
import ZInQKernel.Contrib.T28.Special

/-!
# T28 proved: Igusa invariants separate binary sextics (tasks igusa-generic + igusa-special)

Textbook leaf T28 (`PkgI1.IgusaClebschSeparation`, Clebsch 1872, Bolza 1888, Igusa 1960): over an
algebraically closed field of characteristic `0`, two binary sextics with nonzero discriminant
are `GL₂ × 𝔾_m`-equivalent iff their Igusa invariants `[J₂ : J₄ : J₆ : J₁₀]` agree in weighted
projective space `P(1,2,3,5)`.

* `⇒`: `PkgI1.igusa_forward` (task t28-igusa);
* `⇐` reduced to `PkgI1.IgusaSeparationEq` (`PkgI1.igusaClebschSeparation_iff`, task t28-igusa),
  split on Clebsch's determinant `det (yv f)` (`ZInQKernel/Contrib/T28/Generic.lean`):
  - generic locus `det (yv f) ≠ 0`: `T28.separationGeneric` (Mestre's method, task
    igusa-generic, `ZInQKernel/Contrib/T28/Mestre.lean`);
  - both sextics special: `T28Special.separationBothSpecial` (Bolza's involutions, task
    igusa-special, `ZInQKernel/Contrib/T28/Special.lean`).
No `sorry`, no `axiom`.
-/

namespace T28

/-- **T28, the exact-equality form of `⇐`.** -/
theorem igusaSeparationEq_proved : PkgI1.IgusaSeparationEq :=
  igusaSeparationEq_of_generic_bothSpecial separationGeneric T28Special.separationBothSpecial

/-- **Textbook leaf T28 (`PkgI1.IgusaClebschSeparation`), proved.** -/
theorem igusaClebschSeparation_proved : PkgI1.IgusaClebschSeparation :=
  igusaClebschSeparation_of_bothSpecial T28Special.separationBothSpecial

/-- The special case of task t28-igusa (`PkgI1.SeparationSpecial`), proved. -/
theorem separationSpecial_proved : PkgI1.SeparationSpecial := fun L _ _ _ f g hf hg _ h2 h4 h6 h10 =>
  igusaSeparationEq_proved L f g hf hg h2 h4 h6 h10

end T28

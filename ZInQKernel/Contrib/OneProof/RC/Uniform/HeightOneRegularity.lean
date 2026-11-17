import Mathlib

/-!
# Lane RC16: height-one regularity by switches (the descent at `R = Λ_𝔭`)

Manuscript (11/5), Proposition `ex:limits-uniform-lower-bound`, paragraph "Height-one regularity,
including quadratic specializations", tex lines 4976–5200.

At a height-one prime `𝔭 ≠ (2)` of `Λ`, with `R = Λ_𝔭` (a DVR) and `k = Frac(Λ/𝔭)` (characteristic
zero), Elliot runs the switches on the fiber dimension `s = dim_k H¹(C ⊗_R k)`:

* "We will only make switches whose finite localization is nonzero on `v̄`" (tex 4993–4996);
* nonquadratic specialization: rank-two detection, `U = F`, `s` drops by two (tex 4997–5003);
* quadratic specialization (`𝔭 = (t)` or `(t+2)`): if both signs occur, `s` drops by two
  (tex 5116–5122); if only one sign occurs and `s > 1`, "the first switch introduces the other sign
  and preserves total dimension", and "the next switch uses the preceding mixed-sign case and lowers
  the total dimension by two" (tex 5123–5136);
* "At each step the new class is the actual derivative `P_{I∪{ℓ}}` [...] Lemma
  `ex:limits-derivative-switch` therefore makes this class span the new generic kernel and preserves
  the valuation of its class-functional determinant coordinate" (tex 5137–5153);
* "Each new generic kernel has rank one and has a primitive integral vector, so its fiber dimension
  is at least one. [...] Whenever the dimension exceeds one, one or two switches give a strict drop by
  two. Thus finitely many switches leave dimension one" (tex 5154–5159);
* at dimension one the terminal coordinate "is the product of the two integral coefficients, up to a
  determinant-basis unit, so belongs to `R`. Valuation preservation transports this conclusion
  through every switch" (tex 5160–5193).

What is formalized here (`PROVED`): the descent itself — the termination of the switching (one or two
switches per drop of two, never below one) and the transport of membership in `R` back through every
switch — for an abstract switching process whose steps are the inputs above (`ELLIOT`), collected as
the fields of `RegularitySwitchProcess` with their tex lines. The algebra behind the steps is proved in
`QuadraticCase.lean` (sign planes, (5.5a) bookkeeping, (5.5b), polarization), `Switch.lean` (the
relaxed image and the equal valuations) and `KernelDetection.lean` (rank-two detection).

`DEPARTURE` (form only): membership in `R = Λ_𝔭` is an abstract predicate `Reg` on the coordinate field,
closed under products (for `Λ_𝔭` inside `Frac Λ` this is `RegularAt` of `UniformLowerBound.lean`).
-/

namespace ZInQ.Manuscript.RC.Uniform

variable {K : Type*} [Mul K]

/-- The switching process at one height-one prime (tex 4976–5193). Every field is one of Elliot's
steps, taken as an input (`ELLIOT`):

* `fiberDim S` is `s = dim_k H¹(C ⊗_R k)` of the configuration `S`, `coord S` its actual-class
  class-functional coordinate, and `mixed S` says that both cohomology signs occur (in the
  nonquadratic case take `mixed := True`; the sign decomposition exists only at `(t)` and `(t+2)`).
* `pos`: tex 4986–4992 and 5154–5157 — a primitive vector of the saturated kernel has nonzero
  reduction, so `s ≥ 1` (a drop from two to zero cannot occur).
* `switch_mixed`: tex 4997–5003, 5116–5122 — when both signs occur (or the specialization is
  nonquadratic) and `s > 1`, detection puts both finite axes in `U`, so `U = F`, `U ∩ S = 0` and by (5.5a)
  the new dimension is `s − 2`.
* `switch_single`: tex 5123–5136 — when only one sign occurs and `s > 1`, the first switch makes the
  configuration mixed and preserves `s`.
* In both switch fields, the old coordinate is a regular multiple `w · u'` of the new one: the switch
  lemma "preserves the valuation of its class-functional determinant coordinate" (tex 5145–5153;
  algebraic core `Switch.lean`), so `w` is a unit of `R` (only `Reg w` is used).
* `terminal`: tex 5157–5193 — at `s = 1` the terminal complex is `[R --0--> R]`, the actual class and
  the paired functional (orthogonal comparison is the identity at derivative primes; unit `−2` at
  active primes; `t` or the central Frobenius determinants at the moving prime) are integral, so the
  coordinate lies in `R`. -/
structure RegularitySwitchProcess (Reg : K → Prop) where
  /-- The configurations reached by successive switches. -/
  Stage : Type
  /-- The fiber dimension `s`. -/
  fiberDim : Stage → ℕ
  /-- Both cohomology signs occur (or the specialization is nonquadratic). -/
  mixed : Stage → Prop
  /-- The class-functional coordinate of the actual class. -/
  coord : Stage → K
  /-- tex 4986–4992, 5154–5157: `s ≥ 1`. -/
  pos : ∀ S, 1 ≤ fiberDim S
  /-- tex 4997–5003, 5116–5122: mixed signs, one switch lowers `s` by two. -/
  switch_mixed : ∀ S, mixed S → 1 < fiberDim S →
    ∃ S', fiberDim S' + 2 = fiberDim S ∧ ∃ w, Reg w ∧ coord S = w * coord S'
  /-- tex 5123–5136: one sign only, the first switch introduces the other sign, same `s`. -/
  switch_single : ∀ S, ¬ mixed S → 1 < fiberDim S →
    ∃ S', fiberDim S' = fiberDim S ∧ mixed S' ∧ ∃ w, Reg w ∧ coord S = w * coord S'
  /-- tex 5157–5193: the terminal coordinate lies in `R`. -/
  terminal : ∀ S, fiberDim S = 1 → Reg (coord S)

/-- The height-one descent (tex 5154–5193): "Whenever the dimension exceeds one, one or two switches
give a strict drop by two. Thus finitely many switches leave dimension one. [...] Valuation
preservation transports this conclusion through every switch." Every configuration of a switching
process has a coordinate in `R`; in particular the primitive coordinate (the starting configuration)
does. Kind: PROVED (strong induction on `s`, with one extra step in the single-sign case). -/
theorem regular_of_switchProcess {Reg : K → Prop} (hmul : ∀ x y, Reg x → Reg y → Reg (x * y))
    (P : RegularitySwitchProcess Reg) : ∀ S : P.Stage, Reg (P.coord S) := by
  -- first the statement for mixed configurations, by strong induction on `s`
  have key : ∀ m : ℕ, ∀ S : P.Stage, P.fiberDim S = m → Reg (P.coord S) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro S hS
      rcases lt_trichotomy (P.fiberDim S) 1 with h | h | h
      · exact absurd (P.pos S) (by omega)
      · exact P.terminal S h
      · by_cases hmix : P.mixed S
        · obtain ⟨S', hS', w, hw, hc⟩ := P.switch_mixed S hmix h
          rw [hc]
          exact hmul w _ hw (ih (P.fiberDim S') (by omega) S' rfl)
        · obtain ⟨S₁, hS₁, hmix₁, w₁, hw₁, hc₁⟩ := P.switch_single S hmix h
          obtain ⟨S₂, hS₂, w₂, hw₂, hc₂⟩ := P.switch_mixed S₁ hmix₁ (by omega)
          rw [hc₁, hc₂]
          exact hmul w₁ _ hw₁ (hmul w₂ _ hw₂ (ih (P.fiberDim S₂) (by omega) S₂ rfl))
  exact fun S => key _ S rfl

/-- Non-vacuity of `RegularitySwitchProcess`: a process with a single-sign start of dimension three,
then a mixed configuration of dimension three, then one of dimension one, all coordinates `1`, over
`ℚ` with `Reg x := ∃ n : ℤ, x = n` (membership in `ℤ`). Kind: PROVED. -/
def exampleRegularityProcess : RegularitySwitchProcess (fun x : ℚ => ∃ n : ℤ, x = n) where
  Stage := Fin 3
  fiberDim := fun i => if i = 2 then 1 else 3
  mixed := fun i => i ≠ 0
  coord := fun _ => 1
  pos := fun i => by split_ifs <;> omega
  switch_mixed := fun i hmix h => by
    refine ⟨2, ?_, 1, ⟨1, by norm_num⟩, by norm_num⟩
    fin_cases i
    · exact absurd rfl hmix
    · simp
    · simp at h
  switch_single := fun i hmix h => by
    refine ⟨1, ?_, by decide, 1, ⟨1, by norm_num⟩, by norm_num⟩
    fin_cases i
    · simp
    · exact absurd (by decide) hmix
    · exact absurd (by decide) hmix
  terminal := fun _ _ => ⟨1, by norm_num⟩

end ZInQ.Manuscript.RC.Uniform

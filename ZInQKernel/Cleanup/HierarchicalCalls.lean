import ZInQKernel.Compiler.Circuits.Hierarchical
import ZInQKernel.Compiler.Circuits.MacroSemantics

/-!
# Circuits of hierarchical constructions, item 3 in general

Blueprint: `compiler/natural/formulas/hierarchical-calls.md`, item 3.

The relation "the conjunction of the macro relations of the construction, quantified over the
remaining fresh variables" is what the macro semantics produce compositionally: every gadget and
macro has a private-witness specification `MSpec τ m U R` (`lt_spec`, …, `bitAnd_spec`,
`powerSpec_hierarchical`), and `fresh`, `note`, expression steps, `andM` and `orM` compose them
(`MSpec.fresh_bind`, `MSpec.note_bind`, `MSpec.expr_bind`, `seqM_map_specL`, …). A construction
whose final formula has such a specification `R` over the inputs `{i | i < k}` has
`Z_𝒞(c) ⟺ R(c)` (`toCircuit_natRel_iff_of_spec`, `toCircuit_natRel_iff_of_mspec`). This is the
step that `Packed.compiled_natRel_iff` performs inline for the packed construction.
-/

noncomputable section

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

/-- The variable count of the circuit of a construction is the final counter. -/
theorem toCircuit_varCount_eq (k : ℕ) (m : NM NForm) :
    (m.toCircuit k).varCount = (m (State.init k)).2.next := by
  rw [NM.toCircuit_varCount, (counts_encode ExPoly.empty _ _).1]
  rfl

/-- **Item 3.** If the node encoding of the construction is valid and its final formula `φ`
has the private-witness specification `R` over the inputs (for every `x`, some natural values
of the fresh variables and blocks `[k, V)` make `φ` hold iff `R x`), then for every `c ∈ ℕ^k`,
`Z_𝒞(c)` holds iff `R x` for any (equivalently, every) `x` equal to `c` on the inputs. -/
theorem toCircuit_natRel_iff_of_spec {k : ℕ} {m : NM NForm} {T : ExPoly} {P : State → Prop}
    (hP : P (State.init k)) (hm : Triple P m fun φ s => φ.Valid T s) {R : (ℕ → ℕ) → Prop}
    (hspec : Spec (m.formula T k) {i | i < k} k (m (State.init k)).2.next R)
    (c : Fin k → ℕ) (x : ℕ → ℕ) (hx : ∀ i : Fin k, x i = c i) :
    (m.toCircuit k).NatRel T c ↔ R x := by
  have hV := toCircuit_varCount_eq k m
  have hk : (m.toCircuit k).inputCount = k := rfl
  refine (Packed.natRel_iff_agree (m.toCircuit k) T (by rw [hV]; exact hspec.le) c).trans ?_
  generalize hx' : NatCircuit.natPoint (m.toCircuit k).inputCount
    ((m.toCircuit k).varCount - (m.toCircuit k).inputCount) c (fun _ => 0) = x'
  have hxc : ∀ i : Fin k, x' i = c i := fun i => by
    rw [← hx']; simp only [NatCircuit.natPoint, hk]; simp [i.isLt]; rfl
  rw [hk, hV, toCircuit_poly hP hm]
  simp only [compile_zv_eq_zero_iff]
  rw [← hspec.sem x]
  have hlt : VarsLT (m.formula T k).compile (m (State.init k)).2.next := fun i hi => by
    rcases hspec.loc i hi with h | h
    · have : i < k := h
      have := hspec.le
      omega
    · exact h.2
  refine exists_agree_congr hlt fun i hi => ?_
  rw [show i = (⟨i, hi⟩ : Fin k) from rfl, hxc, hx]

/-- **Item 3, macro form.** If the construction has the macro specification `R` over the inputs
(`MSpec`, the composition of the macro semantics), then `Z_𝒞(c)` holds iff `R x` for any `x`
equal to `c` on the inputs. -/
theorem toCircuit_natRel_iff_of_mspec {k : ℕ} {m : NM NForm} {T : ExPoly} {P : State → Prop}
    (hP : P (State.init k)) (hm : Triple P m fun φ s => φ.Valid T s) {R : (ℕ → ℕ) → Prop}
    (hspec : MSpec T m {i | i < k} R) (c : Fin k → ℕ) (x : ℕ → ℕ) (hx : ∀ i : Fin k, x i = c i) :
    (m.toCircuit k).NatRel T c ↔ R x :=
  toCircuit_natRel_iff_of_spec hP hm (hspec (State.init k) fun _ hi => hi) c x hx

/-- **Item 3, conjunction of macros.** For a construction that is the conjunction of
constructions `ms` with macro specifications `Rs` over the inputs (for instance macro calls on
input polynomials), `Z_𝒞(c)` holds iff all the relations `Rs` hold at `c`. -/
theorem toCircuit_andM_natRel_iff {k : ℕ} {ms : List (NM NForm)} {T : ExPoly} {P : State → Prop}
    (hP : P (State.init k)) (hm : Triple P (andM ms) fun φ s => φ.Valid T s)
    {Rs : List ((ℕ → ℕ) → Prop)} (h : List.Forall₂ (fun m R => MSpec T m {i | i < k} R) ms Rs)
    (c : Fin k → ℕ) (x : ℕ → ℕ) (hx : ∀ i : Fin k, x i = c i) :
    ((andM ms).toCircuit k).NatRel T c ↔ ∀ R ∈ Rs, R x :=
  toCircuit_natRel_iff_of_mspec hP hm (MSpec.andM h) c x hx

end ZInQ.Compiler.Natural

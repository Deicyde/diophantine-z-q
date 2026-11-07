import ZInQKernel.Compiler.Circuits.Builder
import ZInQKernel.Compiler.Circuits.MacroSemantics
import ZInQKernel.Compiler.Circuits.Counts

/-!
# The power template and its semantics

The power template `𝒫` is the template of the natural construction with `3` inputs
`P = X_0, Q = X_1, R = X_2` consisting of the single flat macro `power(P, Q, R)`: parameter
count `3`, variable count `82` (witnesses `X_3, …, X_81`, all explicit), polynomial
`κ(power(P, Q, R))` (the product of the three branch polynomials, not squared again). Its node
list is the hash-consed node encoding of the construction.

Its natural zeros are exactly the triples with `P = Q^R` (`0^0 = 1`), so a power call on a
private block means `P = Q^R` (`powerSpec_hierarchical_powerTemplate`).

(Blueprint: `compiler/natural/formulas/power-template.md`,
`compiler/natural/formulas/power-template-semantics.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

/-- The construction of the power template: three inputs and the flat power macro. -/
def powerTemplateConstruction : NM NForm := power .flat ⟨0, X 0⟩ ⟨1, X 1⟩ ⟨2, X 2⟩

/-- The power template as a natural circuit (no call nodes). -/
def powerTemplateCircuit : NatCircuit := powerTemplateConstruction.toCircuit 3

/-- The polynomial of the power template: the denotation of the root of its node list. It is
irreducible so that elaboration never evaluates the node list. -/
@[irreducible] def powerTemplatePoly : Poly := powerTemplateCircuit.poly ExPoly.empty

/-- **The power template** `𝒫`: parameter count `3`, witness count `79` (its variable count
is `82`, `powerTemplateCircuit_varCount`), polynomial the denotation of the root of its node
list. -/
def powerTemplate : ExPoly := ⟨3, 79, powerTemplatePoly⟩

/-- The formula of the power template, `power(P, Q, R)` in flat mode. -/
def powerTemplateFormula : Formula := powerTemplateConstruction.formula ExPoly.empty 3

theorem powerTemplateConstruction_next :
    (powerTemplateConstruction (State.init 3)).2.next = 82 := by
  have := (Counts.power_flat (⟨0, X 0⟩ : Ex) ⟨1, X 1⟩ ⟨2, X 2⟩ (State.init 3)).1
  simpa [powerTemplateConstruction, State.init, powerWitnesses] using this

theorem powerTemplateCircuit_varCount : powerTemplateCircuit.varCount = 82 := by
  rw [powerTemplateCircuit, NM.toCircuit_varCount]
  have := (counts_encode ExPoly.empty (powerTemplateConstruction (State.init 3)).1
    (powerTemplateConstruction (State.init 3)).2).1
  rw [this, powerTemplateConstruction_next]; rfl

@[simp] theorem powerTemplate_params : powerTemplate.params = 3 := rfl

@[simp] theorem powerTemplate_witnesses : powerTemplate.witnesses = 79 := rfl

/-- The witness count is the variable count of the circuit minus the three parameters. -/
theorem powerTemplate_witnesses_circuit :
    powerTemplate.witnesses = powerTemplateCircuit.varCount - 3 := by
  rw [powerTemplateCircuit_varCount]; rfl

theorem powerTemplate_varCount : powerTemplate.varCount = 82 := by
  simp [ExPoly.varCount]

theorem powerTemplate_witnesses_eq : powerTemplate.witnesses = powerWitnesses := by
  simp [powerWitnesses]

theorem powerTemplate_poly_def :
    powerTemplate.poly = (powerTemplateConstruction.toCircuit 3).poly ExPoly.empty := by
  show powerTemplatePoly = _
  unfold powerTemplatePoly powerTemplateCircuit
  rfl

/-- The polynomial of the power template is `κ(power(P, Q, R))`. -/
theorem powerTemplate_poly : powerTemplate.poly = powerTemplateFormula.compile := by
  rw [powerTemplate_poly_def, powerTemplateFormula]
  have hm : Triple
      (fun s => (⟨0, X 0⟩ : Ex).Valid ExPoly.empty s ∧ (⟨1, X 1⟩ : Ex).Valid ExPoly.empty s ∧
        (⟨2, X 2⟩ : Ex).Valid ExPoly.empty s) powerTemplateConstruction
      fun φ s => φ.Valid ExPoly.empty s :=
    Triple.power ((Mono.valid _ _).and ((Mono.valid _ _).and (Mono.valid _ _))) fun _ h => h
  exact toCircuit_poly (P := fun s => (⟨0, X 0⟩ : Ex).Valid ExPoly.empty s ∧
    (⟨1, X 1⟩ : Ex).Valid ExPoly.empty s ∧ (⟨2, X 2⟩ : Ex).Valid ExPoly.empty s)
    ⟨input_valid (by norm_num), input_valid (by norm_num), input_valid (by norm_num)⟩ hm

/-- The flat power macro at the initial state of three inputs. -/
theorem powerTemplate_spec :
    Spec powerTemplateFormula {i | i < 3} 3 82 fun x => x 0 = x 1 ^ x 2 := by
  have h := powerSpec_flat' (τ := ExPoly.empty) {i | i < 3} (X 0) (X 1) (X 2)
    (VarsIn.X (by simp)) (VarsIn.X (by simp)) (VarsIn.X (by simp)) (IsNat.X 0) (IsNat.X 1)
    (IsNat.X 2) ⟨0, X 0⟩ ⟨1, X 1⟩ ⟨2, X 2⟩ rfl rfl rfl (State.init 3)
    (fun i hi => by simpa [State.init] using hi)
  rw [show (power .flat ⟨0, X 0⟩ ⟨1, X 1⟩ ⟨2, X 2⟩ (State.init 3)).2.next = 82 from
    powerTemplateConstruction_next] at h
  exact h.congr fun x => by simp only [nv_X]

theorem powerTemplate_wf : powerTemplate.WF := by
  intro i hi
  rw [powerTemplate_poly] at hi
  rcases powerTemplate_spec.loc i hi with h | h
  · simp only [Set.mem_ofPred_eq] at h; rw [powerTemplate_varCount]; omega
  · rw [powerTemplate_varCount]; omega

/-- **Semantics of the power template.** For all natural `P, Q, R`, some natural witnesses
`w ∈ ℕ^79` make `𝒫(P, Q, R, w)` vanish exactly when `P = Q^R` (with `0^0 = 1`). -/
theorem powerTemplate_natRel (P Q R : ℕ) :
    (∃ w : Fin 79 → ℕ, MvPolynomial.eval
        (fun i => (NatCircuit.natPoint 3 79 ![P, Q, R] w i : ℤ)) powerTemplate.poly = 0) ↔
      P = Q ^ R := by
  let x : ℕ → ℕ := NatCircuit.natPoint 3 79 ![P, Q, R] fun _ => 0
  have hsem := powerTemplate_spec.sem x
  have hx : x 0 = P ∧ x 1 = Q ∧ x 2 = R := by simp [x, NatCircuit.natPoint]
  rw [hx.1, hx.2.1, hx.2.2] at hsem
  rw [← hsem, powerTemplate_poly]
  simp only [show ∀ (f : ℕ → ℕ) (p : Poly), MvPolynomial.eval (fun i => (f i : ℤ)) p = zv f p
    from fun _ _ => rfl, compile_zv_eq_zero_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨_, fun i hi => ?_, hw⟩
    simp only [x, NatCircuit.natPoint]
    split_ifs with h1 h2 <;> first | rfl | omega
  · rintro ⟨y, hy, hφ⟩
    refine ⟨fun j => y (3 + j), ?_⟩
    convert hφ using 2
    funext i
    simp only [NatCircuit.natPoint]
    split_ifs with h1 h2
    · rw [hy i (by omega)]; simp [x, NatCircuit.natPoint, h1]
    · congr 1; omega
    · rw [hy i (by omega)]; simp [x, NatCircuit.natPoint, h1, h2]

theorem exNatRel_iff_eval {τ : ExPoly} (hp : τ.params = 3) (hw : τ.witnesses = 79) (P Q R : ℕ) :
    ExNatRel τ (natArgs P Q R τ.params) ↔ ∃ w : Fin 79 → ℕ,
      MvPolynomial.eval (fun i => (NatCircuit.natPoint 3 79 ![P, Q, R] w i : ℤ)) τ.poly = 0 := by
  rcases τ with ⟨p, m, f⟩
  simp only at hp hw
  subst hp hw
  unfold ExNatRel
  refine exists_congr fun w => ?_
  have : (assign 3 79 (fun i => (natArgs P Q R 3 i : ℚ)) fun j => (w j : ℚ)) =
      qa (NatCircuit.natPoint 3 79 ![P, Q, R] w) := by
    funext i
    simp only [assign, qa, NatCircuit.natPoint]
    split_ifs with h1 h2
    · rcases i with _ | _ | _ | i
      · rfl
      · rfl
      · rfl
      · omega
    · rfl
    · rfl
  simp only [this, ev_qa, Int.cast_eq_zero]
  rfl

/-- The power template has the power semantics in the form of the call specification. -/
theorem powerTemplateSem : PowerTemplateSem powerTemplate := fun P Q R =>
  (exNatRel_iff_eval powerTemplate_params powerTemplate_witnesses P Q R).trans
    (powerTemplate_natRel P Q R)

/-- **Hierarchical power calls** on the power template mean `P = Q^R`. -/
theorem powerSpec_hierarchical_powerTemplate : PowerSpec powerTemplate .hierarchical :=
  powerSpec_hierarchical powerTemplate_wf powerTemplate_witnesses_eq powerTemplateSem

end ZInQ.Compiler.Natural

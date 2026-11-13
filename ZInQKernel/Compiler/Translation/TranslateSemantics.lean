import ZInQKernel.Compiler.Translation.Library
import ZInQKernel.Compiler.Translation.ModelSemantics

/-!
# Relational form and semantics of the translated recipes

For the translation `ρ = translate consts 𝒩 mode natIn power` of a well-formed natural circuit,
read with the template library:

* `translate_rel_iff` (relational form): `Rel_ρ(a)` holds exactly when some assignment extending
  `a` satisfies the generator equations, the natural calls, the constant definitions, the
  operations and the root equality;
* `translate_rel_iff_zero`, `translate_rel_iff_value` (semantics of the model-evaluation
  translation), under M and (PV) for the power recipe.

The constant table `consts` must be a prefix of the library's integer constants
`(4, 2, 3, c_3, 1399)` containing every nontrivial constant of `𝒩`; the power recipe
`power = (index, witness count)` must be present when `𝒩` has call nodes, with the witness count
of the recipe at that index.

(Blueprint: `compiler/translation/model-recipe-relation.md`,
`compiler/translation/model-evaluation-semantics.md`.)
-/

namespace ZInQ.Translation

open Compiler.Natural Syntax

variable {E : Type}

/-- The hypotheses on the power recipe of a translation: the power recipe is well formed, the
recorded witness count is the recipe's, a power recipe is present when the circuit has call
nodes, and it satisfies (PV). -/
structure PowerSetup (recipes : List ExPoly) (power : Option (ℕ × ℕ)) (P N : NatCircuit) :
    Prop where
  wf : ∀ i w, power = some (i, w) → (getEx recipes i).WF
  witnesses : ∀ i w, power = some (i, w) → (getEx recipes i).witnesses = w
  present : HasCall N → power.isSome
  spec : ∀ i w, power = some (i, w) → HasCall N → PowerValueSpec (getEx recipes i) P

/-- No power recipe, for a circuit without call nodes. -/
theorem PowerSetup.none {recipes : List ExPoly} {P N : NatCircuit} (hN : ¬ HasCall N) :
    PowerSetup recipes none P N :=
  ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h), fun h => absurd h hN,
    fun _ _ h => (by cases h)⟩

section

variable (I : Constructors E) (cstar ell T c3 : ℤ) {consts : List ℤ} {N P : NatCircuit} {V : ℕ}
  {mode : OutputMode} {natIn : Bool} {power : Option (ℕ × ℕ)} {recipes : List ExPoly}

theorem powerSetup_callee (hpow : PowerSetup recipes power P N) :
    HasCall N → PowerValueSpec (powerCallee recipes (translate consts N mode natIn power)) P := by
  intro hc
  obtain ⟨⟨i, w⟩, hp⟩ := Option.isSome_iff_exists.1 (hpow.present hc)
  have : powerCallee recipes (translate consts N mode natIn power) = getEx recipes i := by
    simp [powerCallee, Syntax.translate, hp]
  rw [this]
  exact hpow.spec i w hp hc

/-- The translation of a well-formed circuit with the library has the witness-scope facts. -/
theorem translate_scopedIn_library (hwf : WellFormed P N V) (hcons : consts <+: integerConstants c3)
    (hcmem : ∀ c, NatNode.const c ∈ N.nodes → Nontrivial c → c ∈ consts)
    (hpow : PowerSetup recipes power P N) :
    ScopedIn ((translate consts N mode natIn power).formula (templateLibrary I cstar ell T c3)
      recipes) (translate consts N mode natIn power).parameterCount
      (translate consts N mode natIn power).variableCount := by
  obtain ⟨h1, h2, h3⟩ := library_witnesses I cstar ell T c3
  refine translate_scopedIn hwf (Syntax.templateLibrary_wf I cstar ell T c3) hpow.wf h1 h2 h3
    (fun c hc hn => ?_) hpow.witnesses
  rw [getEx_library_scalar I cstar ell T c3 hcons (hcmem c hc hn), scalarTemplate_witnesses]

/-- The shape of the translation with the library. -/
noncomputable def translateShapeLibrary (hwf : WellFormed P N V) (hcons : consts <+: integerConstants c3)
    (hcmem : ∀ c, NatNode.const c ∈ N.nodes → Nontrivial c → c ∈ consts)
    (hpow : PowerSetup recipes power P N) :
    TranslationShape (templateLibrary I cstar ell T c3) recipes (scalarTemplate I)
      (translate consts N mode natIn power) P N (decide (mode = .value)) natIn :=
  translateShape consts P N V mode natIn power _ recipes _ hwf
    (fun c hc hn => getEx_library_scalar I cstar ell T c3 hcons (hcmem c hc hn)) hpow.present

/-- **Relational form of a model-evaluation recipe** (the translation of a well-formed circuit,
read with the template library). -/
theorem translate_rel_iff (hwf : WellFormed P N V) (hcons : consts <+: integerConstants c3)
    (hcmem : ∀ c, NatNode.const c ∈ N.nodes → Nontrivial c → c ∈ consts)
    (hpow : PowerSetup recipes power P N)
    (a : Fin (translate consts N mode natIn power).parameterCount → ℚ) :
    ((Recipe.model (translate consts N mode natIn power)).denote
        (templateLibrary I cstar ell T c3) recipes).Rel a ↔
      ∃ x : ℕ → ℚ, (∀ i (hi : i < (translate consts N mode natIn power).parameterCount),
        x i = a ⟨i, hi⟩) ∧
        ModelHolds (templateLibrary I cstar ell T c3) recipes (translate consts N mode natIn power) x :=
  modelRecipe_rel_iff _ _ _ (translate_scopedIn_library I cstar ell T c3 hwf hcons hcmem hpow) a

/-- **Semantics of the model-evaluation translation, zero mode with natural inputs**: for all
rational parameter points (not assumed to be codes), `Rel_ρ(E₀, …, E_{k-1})` holds exactly when
`E_i = ι(θ_i)` with `θ_i ∈ ℕ` and `𝒩(θ) = 0` for some admissible `θ`. -/
theorem translate_rel_iff_zero (hI : I.psi = psiComponent) (hM : MultiplicationExact I cstar ell T)
    (hwf : WellFormed P N V) (hcons : consts <+: integerConstants c3)
    (hcmem : ∀ c, NatNode.const c ∈ N.nodes → Nontrivial c → c ∈ consts)
    (hpow : PowerSetup recipes power P N)
    (a : Fin (translate consts N .zero true power).parameterCount → ℚ) :
    ((Recipe.model (translate consts N .zero true power)).denote
        (templateLibrary I cstar ell T c3) recipes).Rel a ↔
      ∃ θ : ℕ → ℤ, Admissible P N θ ∧
        (∀ i < N.inputCount, 0 ≤ θ i ∧ paramCode a i = iota (θ i)) ∧ circuitValue P N θ = 0 :=
  TranslationShape.rel_iff_zero
    (translateShapeLibrary I cstar ell T c3 (mode := .zero) (natIn := true) hwf hcons hcmem hpow)
    hwf (calleeSemantics_library I cstar ell T c3 hI hM) (powerSetup_callee hpow)
    (translate_scopedIn_library I cstar ell T c3 hwf hcons hcmem hpow) a

/-- **Semantics of the model-evaluation translation, value mode with unconstrained inputs**: for
integers `c_i` and `r ∈ ℚ⁵`, `Rel_ρ(ι(c₀), …, ι(c_{k-1}), r)` holds exactly when
`r = ι(𝒩(θ))` for some admissible `θ` with `θ_i = c_i`. -/
theorem translate_rel_iff_value (hI : I.psi = psiComponent) (hM : MultiplicationExact I cstar ell T)
    (hwf : WellFormed P N V) (hcons : consts <+: integerConstants c3)
    (hcmem : ∀ c, NatNode.const c ∈ N.nodes → Nontrivial c → c ∈ consts)
    (hpow : PowerSetup recipes power P N)
    (c : ℕ → ℤ) (R : Fin 5 → ℚ) (a : Fin (translate consts N .value false power).parameterCount → ℚ)
    (ha : ∀ i < N.inputCount, paramCode a i = iota (c i)) (hR : paramCode a N.inputCount = R) :
    ((Recipe.model (translate consts N .value false power)).denote
        (templateLibrary I cstar ell T c3) recipes).Rel a ↔
      ∃ θ : ℕ → ℤ, Admissible P N θ ∧ (∀ i < N.inputCount, θ i = c i) ∧
        R = iota (circuitValue P N θ) :=
  TranslationShape.rel_iff_value
    (translateShapeLibrary I cstar ell T c3 (mode := .value) (natIn := false) hwf hcons hcmem hpow)
    hwf (calleeSemantics_library I cstar ell T c3 hI hM) (powerSetup_callee hpow)
    (translate_scopedIn_library I cstar ell T c3 hwf hcons hcmem hpow) c R a ha hR

end

end ZInQ.Translation

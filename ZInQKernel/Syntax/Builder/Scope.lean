import ZInQKernel.Syntax.Builder.Construction
import ZInQKernel.Syntax.Templates.Library
import ZInQKernel.Compiler.Translation.RecipeRelation

/-!
# Witness scope of constructed templates

Blueprint: `syntax/language/builder-well-formed.md` (templates).

The witness scope of an existential polynomial `τ` with `p` parameters and `v` variables
(`ExPoly.WitnessScope`) is a formula `φ` with `[[τ]] = κ(φ)` whose call blocks `[w, w + m)`

1. lie in `[p, v)` and are pairwise disjoint,
2. avoid every parameter polynomial of a call and every atom `a ≐ b`, `⟨f⟩` of `φ`,

whose callees are well formed, and all of whose variables lie below `v`
(`Formula.InScope φ p v`, the facts `Translation.ScopedIn` of the compiler chapter together
with the upper end of the blocks). Under the witness scope the relation of `τ` is the formula
with every call replaced by the callee relation (`ExPoly.WitnessScope.rel_iff`), and `τ` is
well formed (`ExPoly.WitnessScope.wf`).

The witness scope of a constructed template is checked per template: `Build.Facts` (proved for
the templates with calls in `ZInQKernel/Syntax/Templates/`) gives it
(`Build.Facts.witnessScope`), and a template whose final formula has no call is in scope as soon
as it is well formed (`Build.template_witnessScope_of_blocks_eq_nil`). Every template of the
library is in scope (`templateLibrary_witnessScope`).

A construction may use a call atom twice in its final formula (the language does not forbid it);
the list of blocks would then not be pairwise disjoint. This is why disjointness is a property
of each template (checked by `decide` on its concrete list of blocks) rather than of all
constructions.
-/

namespace ZInQ.Syntax

open MvPolynomial

/-- **Witness scope of a formula** compiled with `p` parameters and `v` variables: callees well
formed, call blocks pairwise disjoint, at or above `p`, ending at or below `v` and avoided by the
free polynomials, and every variable below `v`. -/
structure Formula.InScope (φ : Formula) (p v : ℕ) : Prop where
  /-- The scope facts of the compiler chapter. -/
  scopedIn : Translation.ScopedIn φ p v
  /-- The blocks end at or below the variable count. -/
  inside : ∀ b ∈ φ.blocks, b.1 + b.2 ≤ v

/-- **Witness scope of an existential polynomial**: its polynomial is the compilation of a
formula in scope for its parameter and variable counts. -/
def ExPoly.WitnessScope (τ : ExPoly) : Prop :=
  ∃ φ : Formula, τ.poly = φ.compile ∧ φ.InScope τ.params τ.varCount

namespace ExPoly.WitnessScope

/-- Every variable of a polynomial in scope lies below its variable count. -/
theorem wf {τ : ExPoly} (h : τ.WitnessScope) : τ.WF := by
  obtain ⟨φ, hφ, hs⟩ := h
  unfold ExPoly.WF
  rw [hφ]
  exact hs.scopedIn.varsLT

/-- **Relations through private blocks.** If `[[τ]] = κ(φ)` with `φ` in scope, then `Rel_τ(a)`
holds exactly when `φ^*` (every call replaced by the callee relation) holds at some assignment
extending `a`. -/
theorem rel_iff {τ : ExPoly} {φ : Formula} (hφ : τ.poly = φ.compile)
    (hs : φ.InScope τ.params τ.varCount) (a : Fin τ.params → ℚ) :
    τ.Rel a ↔ ∃ x : ℕ → ℚ, (∀ i : Fin τ.params, x i = a i) ∧ φ.Lift x :=
  ExPoly.rel_iff_exists_lift (wf ⟨φ, hφ, hs⟩) hφ hs.scopedIn.scope hs.scopedIn.above a

end ExPoly.WitnessScope

/-! ### Formulas without calls -/

theorem Formula.callees_eq_nil_of_blocks_eq_nil {φ : Formula} (h : φ.blocks = []) :
    φ.callees = [] := by
  induction φ using Formula.induct' with
  | eq a b => simp [Formula.callees]
  | atom f => simp [Formula.callees]
  | call τ g w => simp [Formula.blocks] at h
  | and fs ih =>
    rw [Formula.blocks_and, List.flatMap_eq_nil_iff] at h
    rw [Formula.callees_and, List.flatMap_eq_nil_iff]
    exact fun φ hφ => ih φ hφ (h φ hφ)
  | or fs ih =>
    rw [Formula.blocks_or, List.flatMap_eq_nil_iff] at h
    rw [Formula.callees_or, List.flatMap_eq_nil_iff]
    exact fun φ hφ => ih φ hφ (h φ hφ)

/-- A formula without call blocks is in scope as soon as its variables lie below `v`. -/
theorem Formula.inScope_of_blocks_eq_nil {φ : Formula} {p v : ℕ} (h : φ.blocks = [])
    (hv : VarsLT φ.compile v) (hp : p ≤ v) : φ.InScope p v where
  scopedIn :=
    { scope :=
        { wf := fun τ hτ => by
            rw [callees_eq_nil_of_blocks_eq_nil h] at hτ
            exact absurd hτ List.not_mem_nil
          disjoint := by rw [h]; exact List.Pairwise.nil
          free := fun _ _ _ _ ⟨b, hb, _⟩ => by rw [h] at hb; exact absurd hb List.not_mem_nil }
      above := fun b hb => by rw [h] at hb; exact absurd hb List.not_mem_nil
      varsLT := hv
      le := hp }
  inside := fun b hb => by rw [h] at hb; exact absurd hb List.not_mem_nil

/-! ### Constructed templates -/

theorem Build.blocks_fullFormula (p : ℕ) (b : Build Formula) :
    (Build.fullFormula p b).blocks = (b ⟨p, []⟩).1.blocks := by
  have hg : ((b ⟨p, []⟩).2.globals.map globalEq).flatMap Formula.blocks = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro φ hφ
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hφ
    simp [globalEq, Formula.blocks]
  rw [Build.fullFormula, Formula.blocks_and, List.flatMap_append, hg, List.nil_append,
    List.flatMap_singleton]

theorem Build.template_params (p : ℕ) (b : Build Formula) : (Build.template p b).params = p := rfl

/-- A template whose final formula has no call is in scope as soon as it is well formed. -/
theorem Build.template_witnessScope_of_blocks_eq_nil (p : ℕ) (b : Build Formula)
    (hp : p ≤ (b ⟨p, []⟩).2.next) (hb : (b ⟨p, []⟩).1.blocks = [])
    (hwf : (Build.template p b).WF) : (Build.template p b).WitnessScope := by
  refine ⟨Build.fullFormula p b, Build.template_poly p b, ?_⟩
  rw [Build.template_params, Build.template_varCount p b hp]
  have hwf' := hwf
  unfold ExPoly.WF at hwf'
  rw [Build.template_varCount p b hp, Build.template_poly] at hwf'
  exact Formula.inScope_of_blocks_eq_nil (by rw [Build.blocks_fullFormula, hb]) hwf' hp

namespace Build.Facts

variable {p : ℕ} {b : Build Formula} {N : ℕ} {B : List (ℕ × ℕ)} {GE : List (ℕ × ℤ × ℤ)}

/-- The variable count of a template with the facts is the final counter `N`. -/
theorem varCount (h : Build.Facts p b N B GE) : (Build.template p b).varCount = N := by
  rw [Build.template_varCount p b (h.next ▸ h.le), h.next]

/-- The formula `⋀(E_1, …, E_r, φ)` of a template with the facts is in scope. -/
theorem inScope (h : Build.Facts p b N B GE) : (Build.fullFormula p b).InScope p N := by
  have hglobals : ∀ e ∈ (b ⟨p, []⟩).2.globals, FOk (Avail N B) N (globalEq e) := fun e he => by
    rw [h.globalsEq] at he
    exact FOk.eq ((VarsIn.C _ _).mul (VarsIn.X (h.globals e he).1)) (VarsIn.C _ _)
  have hψ : FOk (Avail N B) N (Build.fullFormula p b) :=
    FOk.and_iff.2 fun ψ hψ => by
      rcases List.mem_append.1 hψ with h' | h'
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h'
        exact hglobals e he
      · rw [List.mem_singleton] at h'
        exact h' ▸ h.fok
  have hblocks : (Build.fullFormula p b).blocks = B := by
    rw [Build.blocks_fullFormula, h.blocks]
  exact
    { scopedIn :=
        { scope :=
            { wf := hψ.1
              disjoint := hblocks ▸ pairwise_blockDisjoint_of_sep h.sep
              free := fun f hf i hi => by
                rw [hblocks, ← blockFree_iff]
                exact (hψ.2.1 f hf i hi).2 }
          above := fun bl hbl => h.above bl (hblocks ▸ hbl)
          varsLT := varsLT_compile_of_fok hψ fun i hi => hi.1
          le := h.le }
      inside := hψ.2.2 }

/-- **Witness scope of a constructed template** with the facts. -/
theorem witnessScope (h : Build.Facts p b N B GE) : (Build.template p b).WitnessScope := by
  refine ⟨Build.fullFormula p b, Build.template_poly p b, ?_⟩
  rw [Build.template_params, h.varCount]
  exact h.inScope

end Build.Facts

/-! ### The templates of the library -/

section Library

variable {E : Type}

theorem memberTemplate_witnessScope : memberTemplate.WitnessScope :=
  Build.template_witnessScope_of_blocks_eq_nil 5 _ (by rw [memberBuild_run]; decide)
    (by simp [memberBuild_run, memberFormula]) memberTemplate_wf

theorem rawAddTemplate_witnessScope : rawAddTemplate.WitnessScope :=
  Build.template_witnessScope_of_blocks_eq_nil 15 _ (by rw [rawAddBuild_run]; decide)
    (by simp [rawAddBuild_run, rawAddFormula, addOut]) rawAddTemplate_wf

theorem rawZTemplate_witnessScope : rawZTemplate.WitnessScope :=
  Build.template_witnessScope_of_blocks_eq_nil 7 _ (by rw [rawZBuild_run]; decide)
    (by rw [rawZBuild_run]; exact blocks_zFormula _ _ _) rawZTemplate_wf

theorem rawInverseXTemplate_witnessScope : rawInverseXTemplate.WitnessScope :=
  Build.template_witnessScope_of_blocks_eq_nil 7 _ (by rw [rawInverseXBuild_run])
    (by rw [rawInverseXBuild_run]; exact blocks_ixFormula _ _) rawInverseXTemplate_wf

theorem log25Template_witnessScope : log25Template.WitnessScope :=
  Build.template_witnessScope_of_blocks_eq_nil 4 _ (by rw [log25Build_run])
    (by rw [log25Build_run]; exact blocks_feq _ _) log25Template_wf

theorem poleTemplate_witnessScope : poleTemplate.WitnessScope :=
  Build.template_witnessScope_of_blocks_eq_nil 1 _ (by rw [poleBuild_run]; decide)
    (by rw [poleBuild_run]; simp [Formula.blocks]) poleTemplate_wf

/-- **Witness scope of the templates.** Every template of the library is in scope. -/
theorem templateLibrary_witnessScope (I : Constructors E) (cstar ell T c3 : ℤ) :
    ∀ τ ∈ templateLibrary I cstar ell T c3, τ.WitnessScope := by
  simp only [templateLibrary, integerConstants, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨memberTemplate_witnessScope, rawAddTemplate_witnessScope, rawZTemplate_witnessScope,
    rawInverseXTemplate_witnessScope, log25Template_witnessScope, poleTemplate_witnessScope,
    testGroup_facts.witnessScope, slope_facts.witnessScope, height_facts.witnessScope,
    (scalar_facts I cstar).witnessScope, (guard_facts I T).witnessScope,
    (multiply_facts I cstar ell T).witnessScope, (natural_facts I cstar ell T).witnessScope,
    (signedEncode_facts I cstar ell T).witnessScope, abs_facts.witnessScope,
    close_facts.witnessScope, (valueTest_facts I cstar ell T).witnessScope,
    exceptions_facts.witnessScope, (scalar_facts I 4).witnessScope,
    (scalar_facts I 2).witnessScope, (scalar_facts I 3).witnessScope,
    (scalar_facts I c3).witnessScope, (scalar_facts I 1399).witnessScope⟩

theorem templateLibrary_getEx_witnessScope (I : Constructors E) (cstar ell T c3 : ℤ) (j : ℕ)
    (hj : j < 23) : (getEx (templateLibrary I cstar ell T c3) j).WitnessScope := by
  unfold getEx
  rw [List.getD_eq_getElem _ _ (by rw [length_templateLibrary]; exact hj)]
  exact templateLibrary_witnessScope I cstar ell T c3 _ (List.getElem_mem _)

end Library

end ZInQ.Syntax

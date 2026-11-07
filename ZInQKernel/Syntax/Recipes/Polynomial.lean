import ZInQKernel.Syntax.Recipes.Accounting
import ZInQKernel.Syntax.Recipes.FixedScalar
import ZInQKernel.Syntax.Constants

/-!
# The specified polynomial and its rational zero projection

Blueprints: `syntax/literal-polynomial.md`, `syntax/recipes/fin-variable-form.md`.

`P_*` is the polynomial `[[integers]]` of the root recipe (`PstarNatOf`), read in the variables
`X_0, …, X_{292890231904}` with every variable of larger index replaced by `0`
(`PstarOf = killCompl`). By the witness accounting no such variable occurs
(`rename_PstarOf`), so `P_*` has the same coefficients as `[[integers]]` and no larger total
degree, and `[[integers]] = value[X_1, …, X_5, X_0; 6]²` (`PstarNatOf_eq`).

The constructors are read by `specConstructors` (the value map of the fixed expressions, the
component polynomials `Ψ_{n,c}` and the guard polynomials `G_T`), and the fixed constants
`c_*`, `ℓ`, `T` are the symbolic values of the named constants (`Pstar`). The natural precision
circuit `N` and the program literal `c₃` are parameters, supplied by the compiler chapter; the
variable bound needs their shape (`PrecisionShape N c₃`).

The rational zero projection (`Pstar_zero_projection`): for `q ∈ ℚ` the following are
equivalent: some `w ∈ ℚ^{292890231904}` has `P_*(q, w) = 0`; `Rel_integers(q)`; some
`x : ℕ → ℚ` with `x₀ = q` has `[[integers]](x) = 0`; some `N ∈ ℚ⁵` has `Rel_value(N, q)`.
-/

namespace ZInQ.Syntax

open MvPolynomial
open ZInQ.Compiler.Natural (NatCircuit)

/-- The meaning of the constructor symbols in the specification: fixed expressions are
evaluated with the values of the named constants, psi nodes are the component polynomials
`Ψ_{n,c}` and guard nodes the guard polynomials `G_T`. -/
noncomputable def specConstructors : Constructors (FixedExpr FixedConst) :=
  ⟨FixedConst.fixedVal, psiComponent, guardPoly⟩

theorem specConstructors_psi : specConstructors.psi = psiComponent := rfl

section General

variable {E : Type} (I : Constructors E) (cstar ell T c3 : ℤ) (N : NatCircuit)

/-- `[[integers]]` over the template library with constructors `I` and constants
`c_*, ℓ, T, c₃`. -/
noncomputable def PstarNatOf : Poly := (getEx (specLib I cstar ell T c3 N) 6).poly

/-- `P_*`: `[[integers]]` in the variables `X_0, …, X_{292890231904}`, variables of larger index
replaced by `0`. -/
noncomputable def PstarOf : MvPolynomial (Fin 292890231905) ℤ :=
  killCompl Fin.val_injective (PstarNatOf I cstar ell T c3 N)

/-- The denotation of `value` (recipe `5`). -/
noncomputable def valueExPoly : ExPoly := getEx (specLib I cstar ell T c3 N) 5

/-- The denotation of `integers` (recipe `6`). -/
noncomputable def integersExPoly : ExPoly := getEx (specLib I cstar ell T c3 N) 6

theorem valueExPoly_params : (valueExPoly I cstar ell T c3 N).params = 6 := by
  rw [valueExPoly, getEx_specLib I cstar ell T c3 N (by decide)]
  rfl

theorem integersExPoly_params : (integersExPoly I cstar ell T c3 N).params = 1 := by
  rw [integersExPoly, getEx_specLib I cstar ell T c3 N (by decide)]
  rfl

/-- The parameter polynomials `X_1, …, X_5, X_0` of the call of `value` in `integers`. -/
noncomputable def integersArgs : List Poly := (point 1 ++ [0]).map X

/-- **Unfolding the root**: `[[integers]] = value[X_1, …, X_5, X_0; 6]²`. -/
theorem PstarNatOf_eq : PstarNatOf I cstar ell T c3 N =
    ((valueExPoly I cstar ell T c3 N).callList integersArgs 6) ^ 2 := by
  rw [PstarNatOf, getEx_specLib_six]
  show Recipe.poly _ _ (specIntegers N c3) = _
  simp only [specIntegers, Recipe.poly, integersRecipe_connective, CompositionRecipe.constraints,
    integersRecipe_calls, List.map_cons, List.map_nil, RecipeCall.constraint_eq,
    CallTarget.resolve, Connective.apply, List.sum_cons, List.sum_nil, add_zero]
  rw [getEx_specLib_take I cstar ell T c3 N (by decide) (by decide)]
  rfl

theorem getPoly_integersArgs (x : ℕ → ℚ) (i : Fin 6) :
    ev x (getPoly integersArgs i) = if (i : ℕ) < 5 then x (1 + i) else x 0 := by
  fin_cases i <;> simp [integersArgs, getPoly, point, List.range']

/-- `Rel_integers(q)` is the existence of a zero of `[[integers]]` with `x₀ = q`. -/
theorem integers_rel_iff (q : ℚ) :
    (integersExPoly I cstar ell T c3 N).Rel (fun _ => q) ↔
      ∃ x : ℕ → ℚ, x 0 = q ∧ ev x (PstarNatOf I cstar ell T c3 N) = 0 := by
  have hwf := specLib_wf_6 I cstar ell T c3 N
  rw [← integersExPoly] at hwf
  rw [ExPoly.rel_iff_exists_assignment hwf]
  have hp := integersExPoly_params I cstar ell T c3 N
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy ⟨0, by omega⟩, h⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨x, fun i => ?_, h⟩
    have : (i : ℕ) = 0 := by have := i.isLt; omega
    rw [this, hx]

theorem append_snoc_apply (M : Fin 5 → ℚ) (q : ℚ) (i : ℕ) (hi : i < 6) :
    Fin.append M ![q] ⟨i, hi⟩ = if h : i < 5 then M ⟨i, h⟩ else q := by
  by_cases h : i < 5
  · simp only [h, dite_true]
    exact Fin.append_left M ![q] ⟨i, h⟩
  · simp only [h, dite_false]
    have : i = 5 := by omega
    subst this
    exact Fin.append_right M ![q] 0

/-- A zero of `[[integers]]` with `x₀ = q` is a code `M` with `Rel_value(M, q)`. -/
theorem exists_zero_integers_iff (q : ℚ) :
    (∃ x : ℕ → ℚ, x 0 = q ∧ ev x (PstarNatOf I cstar ell T c3 N) = 0) ↔
      ∃ M : Fin 5 → ℚ, (valueExPoly I cstar ell T c3 N).Rel
        (fun i => Fin.append M ![q] (Fin.cast (valueExPoly_params I cstar ell T c3 N) i)) := by
  have hwf := specLib_wf_5 I cstar ell T c3 N
  rw [← valueExPoly] at hwf
  have hp := valueExPoly_params I cstar ell T c3 N
  simp only [ExPoly.rel_iff_exists_assignment hwf]
  have key : ∀ x : ℕ → ℚ, ev x (PstarNatOf I cstar ell T c3 N) = 0 ↔
      ev (fun i => if h : i < (valueExPoly I cstar ell T c3 N).params then
        ev x (getPoly integersArgs i) else x (6 + (i - (valueExPoly I cstar ell T c3 N).params)))
        (valueExPoly I cstar ell T c3 N).poly = 0 := by
    intro x
    rw [PstarNatOf_eq, map_pow, pow_eq_zero_iff two_ne_zero, ExPoly.callList, ExPoly.call,
      ev_callPoly]
  simp only [key]
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨fun i => x (1 + i), _, fun i => ?_, h⟩
    rcases i with ⟨i, hi⟩
    have hi6 : i < 6 := hp ▸ hi
    simp only [Fin.cast_mk, hi, dite_true, append_snoc_apply _ _ i hi6]
    rw [getPoly_integersArgs x ⟨i, hi6⟩]
    by_cases h5 : i < 5
    · simp [h5]
    · simp [h5, hx]
  · rintro ⟨M, y, hy, h⟩
    refine ⟨fun i => if i = 0 then q else if h : i < 6 then M ⟨i - 1, by omega⟩ else y i,
      by simp, ?_⟩
    rw [← h]
    refine congrArg (fun z => ev z (valueExPoly I cstar ell T c3 N).poly) ?_
    funext i
    by_cases hi : i < 6
    · have hi' : i < (valueExPoly I cstar ell T c3 N).params := hp ▸ hi
      have hyi := hy ⟨i, hi'⟩
      simp only [Fin.cast_mk, append_snoc_apply _ _ i hi] at hyi
      simp only [hi', dite_true, hyi]
      rw [getPoly_integersArgs _ ⟨i, hi⟩]
      by_cases h5 : i < 5
      · have h1 : 1 + i ≠ 0 := by omega
        have h2 : 1 + i < 6 := by omega
        simp only [h5, ite_true, dite_true, h1, ite_false, h2]
        congr 1
        ext
        simp only
        omega
      · simp [h5]
    · have hi' : ¬ i < (valueExPoly I cstar ell T c3 N).params := hp ▸ hi
      simp only [hi', dite_false]
      have : 6 + (i - 6) = i := by omega
      rw [hp, this]
      have h0 : i ≠ 0 := by omega
      simp [h0, hi]

/-- **The Fin form of `P_*`.** Given the shape of the natural precision circuit, `P_*` renamed
into `ℕ`-indexed variables is `[[integers]]`; it has the coefficients of `[[integers]]`, no larger
total degree, and its value at `v` is the value of `[[integers]]` at `v` extended by zeros. -/
theorem PstarOf_spec (hN : PrecisionShape N c3) :
    rename Fin.val (PstarOf I cstar ell T c3 N) = PstarNatOf I cstar ell T c3 N ∧
      (∀ d, (PstarOf I cstar ell T c3 N).coeff d =
        (PstarNatOf I cstar ell T c3 N).coeff (d.mapDomain Fin.val)) ∧
      (PstarOf I cstar ell T c3 N).totalDegree ≤ (PstarNatOf I cstar ell T c3 N).totalDegree ∧
      ∀ v : Fin 292890231905 → ℚ, eval₂ (Int.castRingHom ℚ) v (PstarOf I cstar ell T c3 N) =
        ev (extendFin v) (PstarNatOf I cstar ell T c3 N) := by
  obtain ⟨Q, hQ, h1, h2, h3⟩ := exists_fin_rename (vars_integers_lt I cstar ell T hN)
  have hP : PstarOf I cstar ell T c3 N = Q := by
    rw [PstarOf, PstarNatOf, ← hQ]
    exact killCompl_rename_app _ _
  rw [hP]
  exact ⟨hQ, h1, h2, h3⟩

/-- Zeros of `P_*` with first coordinate `q` are zeros of `[[integers]]` with `x₀ = q`. -/
theorem exists_zero_PstarOf_iff (hN : PrecisionShape N c3) (q : ℚ) :
    (∃ w : Fin 292890231904 → ℚ,
        eval₂ (Int.castRingHom ℚ) (Fin.cons q w) (PstarOf I cstar ell T c3 N) = 0) ↔
      ∃ x : ℕ → ℚ, x 0 = q ∧ ev x (PstarNatOf I cstar ell T c3 N) = 0 := by
  have hev := (PstarOf_spec I cstar ell T c3 N hN).2.2.2
  have hvars := vars_integers_lt I cstar ell T hN
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨extendFin (Fin.cons q w), ?_, by rw [← hev]; exact hw⟩
    simp [extendFin]
  · rintro ⟨x, hx, h⟩
    refine ⟨fun j => x (j + 1), ?_⟩
    rw [hev, ← h]
    refine ev_congr fun i hi => ?_
    have hi' : i < 292890231905 := hvars i hi
    simp only [extendFin, hi', dite_true]
    cases i with
    | zero => simp [hx]
    | succ i => exact Fin.cons_succ (α := fun _ => ℚ) q (fun j => x (j + 1)) ⟨i, by omega⟩

/-- **The rational zero projection of the specified polynomial.** For every `q ∈ ℚ` the
following are equivalent: (1) some `w ∈ ℚ^{292890231904}` has `P_*(q, w) = 0`;
(2) `Rel_integers(q)`; (3) some `x : ℕ → ℚ` with `x₀ = q` has `[[integers]](x) = 0`; (4) some
`M ∈ ℚ⁵` has `Rel_value(M, q)`. -/
theorem PstarOf_zero_projection (hN : PrecisionShape N c3) (q : ℚ) :
    ((∃ w : Fin 292890231904 → ℚ,
        eval₂ (Int.castRingHom ℚ) (Fin.cons q w) (PstarOf I cstar ell T c3 N) = 0) ↔
      (integersExPoly I cstar ell T c3 N).Rel (fun _ => q)) ∧
    ((integersExPoly I cstar ell T c3 N).Rel (fun _ => q) ↔
      ∃ x : ℕ → ℚ, x 0 = q ∧ ev x (PstarNatOf I cstar ell T c3 N) = 0) ∧
    ((∃ x : ℕ → ℚ, x 0 = q ∧ ev x (PstarNatOf I cstar ell T c3 N) = 0) ↔
      ∃ M : Fin 5 → ℚ, (valueExPoly I cstar ell T c3 N).Rel
        (fun i => Fin.append M ![q] (Fin.cast (valueExPoly_params I cstar ell T c3 N) i))) :=
  ⟨(exists_zero_PstarOf_iff I cstar ell T c3 N hN q).trans
      (integers_rel_iff I cstar ell T c3 N q).symm,
    integers_rel_iff I cstar ell T c3 N q, exists_zero_integers_iff I cstar ell T c3 N q⟩

end General

/-! ### The specified polynomial -/

section Spec

variable (N : NatCircuit) (c3 : ℤ)

/-- **The specified polynomial** `P_* ∈ ℤ[X_0, …, X_{292890231904}]`, for the natural precision
circuit `N` and the program literal `c₃`: `[[integers]]` over the template library with the
constructors of the specification and the fixed constants `c_*`, `ℓ`, `T`, every variable of
index above `292890231904` replaced by `0`. -/
noncomputable def Pstar : MvPolynomial (Fin 292890231905) ℤ :=
  PstarOf specConstructors FixedConst.cstar.value FixedConst.ell.value FixedConst.T.value c3 N

/-- `[[integers]]` of the specification. -/
noncomputable def PstarNat : Poly :=
  PstarNatOf specConstructors FixedConst.cstar.value FixedConst.ell.value FixedConst.T.value c3 N

/-- `P_*` is `[[integers]]` read in `Fin 292890231905`, with the same coefficients and no larger
total degree. -/
theorem Pstar_spec (hN : PrecisionShape N c3) :
    rename Fin.val (Pstar N c3) = PstarNat N c3 ∧
      (∀ d, (Pstar N c3).coeff d = (PstarNat N c3).coeff (d.mapDomain Fin.val)) ∧
      (Pstar N c3).totalDegree ≤ (PstarNat N c3).totalDegree ∧
      ∀ v : Fin 292890231905 → ℚ, eval₂ (Int.castRingHom ℚ) v (Pstar N c3) =
        ev (extendFin v) (PstarNat N c3) :=
  PstarOf_spec _ _ _ _ _ _ hN

/-- **The rational zero projection of `P_*`**: `P_*(q, w) = 0` for some rational `w` exactly when
`Rel_value(M, q)` for some `M ∈ ℚ⁵`. -/
theorem Pstar_zero_projection (hN : PrecisionShape N c3) (q : ℚ) :
    (∃ w : Fin 292890231904 → ℚ, eval₂ (Int.castRingHom ℚ) (Fin.cons q w) (Pstar N c3) = 0) ↔
      ∃ M : Fin 5 → ℚ, (valueExPoly specConstructors FixedConst.cstar.value FixedConst.ell.value
        FixedConst.T.value c3 N).Rel (fun i => Fin.append M ![q] (Fin.cast
          (valueExPoly_params specConstructors FixedConst.cstar.value FixedConst.ell.value
            FixedConst.T.value c3 N) i)) :=
  let h := PstarOf_zero_projection specConstructors FixedConst.cstar.value FixedConst.ell.value
    FixedConst.T.value c3 N hN q
  h.1.trans (h.2.1.trans h.2.2)

end Spec

end ZInQ.Syntax

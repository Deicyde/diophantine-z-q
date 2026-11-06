import ZInQKernel.Syntax.Templates.Certificate
import ZInQKernel.Model.Field.Codes

/-!
# Fixed scalars, the guard, multiplication and natural codes

Templates `9` (`multiply.scalar = S_{c_*}`), `10` (`multiply.guard`), `11` (`multiply`), `12`
(`natural`) and the scalar templates `18`–`22`: `finiteScalarFormula`, `buildFiniteModel` of
`construction/finite-polynomial-expressions.js` and `addNaturalModel` of
`construction/rational-model-assembly.js`.

The constructors stay symbolic: the templates take the meaning `I : Constructors E` of the
constructor symbols and the integer values `val(e)` of the fixed expressions they name (`c_*`,
`ℓ`, `T`, or an integer constant) as parameters, and no proof evaluates them. The psi node
`psi e (a₀, …, a₃) c` denotes `Ψ_{val(e),c}` at the argument polynomials and the guard node
`G_{val(e)}` at its fifteen arguments, as in `Node.denote`; the index expressions
`e + 1`, `e + (-1)` and `2·e` of the scalar template have the values `n + 1`, `n + (-1)`, `2n`.
-/

namespace ZInQ.Syntax

open MvPolynomial

variable {E : Type}

/-! ### The fixed-scalar templates -/

/-- The pair of psi nodes `ψ_n(p) = (Ψ_{n,0}, Ψ_{n,1})(p₁, p₂, p₃, p₄)` at `x(p), y(p)`. -/
noncomputable def psiPair (I : Constructors E) (n : ℤ) (p : Code) : Pair :=
  (bind₁ ![p 1, p 2, p 3, p 4] (I.psi n 0), bind₁ ![p 1, p 2, p 3, p 4] (I.psi n 1))

/-- The formula of `S_e` (`val(e) = n`) with points `p`, `r` and inverse witness `X_u`:
`⋁(⋀(isO(p), isO(r)), ⋀(fin(p), fin(r), N(g) u ≐ 1, g²·x(r) ≐ x(p)·g² - g₊·g₋,
(2(g²)²)·y(r) ≐ g₂))` with `g = ψ_n`, `g₊ = ψ_{n+1}`, `g₋ = ψ_{n+(-1)}`, `g₂ = ψ_{2n}`. -/
noncomputable def scalarFormula (I : Constructors E) (n : ℤ) (p r : Code) (u : ℕ) : Formula :=
  let g := psiPair I n p
  let g2 := g.sq
  let gp := psiPair I (n + 1) p
  let gm := psiPair I (n + -1) p
  let gd := psiPair I (2 * n) p
  .or [.and [isO p, isO r],
    .and [fin p, fin r, nzFormula g.norm u, feq (g2.mul r.x) ((p.x.mul g2).sub (gp.mul gm)),
      feq ((Pair.smul 2 g2.sq).mul r.y) gd]]

/-- The construction of `S_e` on the points `p`, `r`: the inverse witness of `NZ_K(ψ_n)`. -/
noncomputable def scalarBuild (I : Constructors E) (n : ℤ) (p r : Code) : Build Formula := do
  let u ← Build.freshIdx
  pure (scalarFormula I n p r u)

/-- **The fixed-scalar template** `S_e` for a fixed expression `e` with value `val(e) = n`
(10 parameters, 1 witness): `multiply.scalar = S_{c_*}` (template index `9`) and
`scalar.integer_constant_k` (template indices `18`–`22`). -/
noncomputable def scalarTemplate (I : Constructors E) (n : ℤ) : ExPoly :=
  Build.template 10 (scalarBuild I n (varPoint 0) (varPoint 5))

theorem scalarBuild_run (I : Constructors E) (n : ℤ) :
    scalarBuild I n (varPoint 0) (varPoint 5) ⟨10, []⟩ =
      (scalarFormula I n (varPoint 0) (varPoint 5) 10, ⟨11, []⟩) := rfl

theorem scalarTemplate_params (I : Constructors E) (n : ℤ) : (scalarTemplate I n).params = 10 :=
  rfl

theorem scalarTemplate_witnesses (I : Constructors E) (n : ℤ) :
    (scalarTemplate I n).witnesses = 1 := rfl

theorem scalar_facts (I : Constructors E) (n : ℤ) :
    Build.Facts 10 (scalarBuild I n (varPoint 0) (varPoint 5)) 11 [] [] := by
  refine Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)
  wp_run (Avail 11 []) 11
  unfold scalarFormula
  facts_close

theorem scalarTemplate_wf (I : Constructors E) (n : ℤ) : (scalarTemplate I n).WF :=
  (scalar_facts I n).wf

/-- The polynomial of `S_e` is `κ(φ)²` for the formula of the article. -/
theorem scalarTemplate_poly (I : Constructors E) (n : ℤ) :
    (scalarTemplate I n).poly = (scalarFormula I n (varPoint 0) (varPoint 5) 10).compile ^ 2 := by
  rw [scalarTemplate, Build.template_poly, Build.fullFormula, scalarBuild_run]
  exact compile_globals_nil _

theorem scalarTemplate_rel_iff (I : Constructors E) (n : ℤ) (a : Fin 10 → ℚ) :
    (scalarTemplate I n).Rel a ↔ ∃ y : Fin 1 → ℚ,
      (scalarFormula I n (varPoint 0) (varPoint 5) 10).Holds (assign 10 1 a y) := by
  unfold scalarTemplate
  rw [Build.template_rel_iff 10 _ (by rw [scalarBuild_run]; simp)]
  simp only [scalarBuild_run, List.not_mem_nil, false_imp_iff, imp_true_iff, true_and]

/-! ### The guard template -/

/-- The construction of `multiply.guard` on the fifteen coordinates `g`: `NZ(G_T(g))`. -/
noncomputable def guardBuild (I : Constructors E) (T : ℤ) (g : Fin 15 → Poly) : Build Formula :=
  Build.nz (bind₁ g (I.guard T))

/-- **The guard template** `multiply.guard` (template index `10`) at the cutoff `T = val(T)`:
the atom `G_T(X₀, …, X₁₄) · X₁₅ ≐ 1`. -/
noncomputable def guardTemplate (I : Constructors E) (T : ℤ) : ExPoly :=
  Build.template 15 (guardBuild I T (varArgs 0 15))

theorem guardBuild_run (I : Constructors E) (T : ℤ) :
    guardBuild I T (varArgs 0 15) ⟨15, []⟩ =
      (nzFormula (bind₁ (varArgs 0 15) (I.guard T)) 15, ⟨16, []⟩) := rfl

theorem guardTemplate_params (I : Constructors E) (T : ℤ) : (guardTemplate I T).params = 15 :=
  rfl

theorem guardTemplate_witnesses (I : Constructors E) (T : ℤ) :
    (guardTemplate I T).witnesses = 1 := rfl

theorem guard_facts (I : Constructors E) (T : ℤ) :
    Build.Facts 15 (guardBuild I T (varArgs 0 15)) 16 [] [] := by
  refine Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)
  wp_run (Avail 16 []) 16
  facts_close

theorem guardTemplate_wf (I : Constructors E) (T : ℤ) : (guardTemplate I T).WF :=
  (guard_facts I T).wf

/-- The polynomial of `multiply.guard` is `(G_T(X₀, …, X₁₄) X₁₅ - 1)²`. -/
theorem guardTemplate_poly (I : Constructors E) (T : ℤ) :
    (guardTemplate I T).poly = (bind₁ (varArgs 0 15) (I.guard T) * X 15 - 1) ^ 2 := by
  rw [guardTemplate, Build.template_poly, Build.fullFormula, guardBuild_run, compile_globals_nil]
  simp only [nzFormula, Formula.compile_eq]

/-- The relation of `multiply.guard`: the guard polynomial does not vanish at the parameters. -/
theorem guardTemplate_rel_iff (I : Constructors E) (T : ℤ) (a : Fin 15 → ℚ) :
    (guardTemplate I T).Rel a ↔ eval₂ (Int.castRingHom ℚ) a (I.guard T) ≠ 0 := by
  unfold guardTemplate
  rw [Build.template_rel_iff 15 _ (by rw [guardBuild_run]; simp)]
  simp only [guardBuild_run, List.not_mem_nil, false_imp_iff, imp_true_iff, true_and,
    holds_nzFormula]
  have hg : ∀ y : Fin 1 → ℚ, ev (assign 15 1 a y) (bind₁ (varArgs 0 15) (I.guard T)) =
      eval₂ (Int.castRingHom ℚ) a (I.guard T) := fun y => by
    show eval₂Hom (Int.castRingHom ℚ) (assign 15 1 a y) (bind₁ (varArgs 0 15) (I.guard T)) = _
    rw [eval₂Hom_bind₁]
    refine congrArg (fun f => eval₂Hom (Int.castRingHom ℚ) f (I.guard T)) (funext fun i => ?_)
    simp only [varArgs, zero_add, coe_eval₂Hom, eval₂_X]
    exact assign_of_lt a y i.isLt
  simp only [hg]
  constructor
  · rintro ⟨y, hy⟩ h
    rw [h, zero_mul] at hy
    exact zero_ne_one hy
  · intro h
    refine ⟨![(eval₂ (Int.castRingHom ℚ) a (I.guard T))⁻¹], ?_⟩
    have : assign 15 1 a ![(eval₂ (Int.castRingHom ℚ) a (I.guard T))⁻¹] 15 =
        (eval₂ (Int.castRingHom ℚ) a (I.guard T))⁻¹ := assign_add 15 1 a _ 0
    rw [this, mul_inv_cancel₀ h]

/-- The fifteen coordinates of three codes, in point-major order. -/
def codes3 (P Q R : Fin 5 → ℚ) : Fin 15 → ℚ := Fin.append (Fin.append P Q) R

/-- A false triple of codes in the box `[-T, T]³`. -/
def FalseTripleCodes (T : ℤ) (P : Fin 15 → ℚ) : Prop :=
  ∃ a b c : ℤ, |a| ≤ T ∧ |b| ≤ T ∧ |c| ≤ T ∧ a * b ≠ c ∧ P = codes3 (iota a) (iota b) (iota c)

/-- **Semantics of the guard template.** If the zero set of `G_T` over `ℚ` is the set of false
triples of codes in the box (the defining property of the false-triple product), the guard
holds exactly off that set. -/
theorem guardTemplate_rel_iff_not_falseTriple (I : Constructors E) (T : ℤ)
    (hG : ∀ P : Fin 15 → ℚ, eval₂ (Int.castRingHom ℚ) P (I.guard T) = 0 ↔ FalseTripleCodes T P)
    (a : Fin 15 → ℚ) : (guardTemplate I T).Rel a ↔ ¬ FalseTripleCodes T a := by
  rw [guardTemplate_rel_iff, Ne, hG]

/-- The zero set of a product of denominator-cleared squared distances. Each factor
`Σ_j (D_t X_j - c_{t,j})²` with `D_t ≠ 0` vanishes at a rational point `X` exactly when
`X_j = c_{t,j}/D_t` for all `j`, so the product vanishes exactly at the target points. This is
the step of the guard semantics that does not depend on the false triples. -/
theorem eval₂_distanceProduct_eq_zero_iff {n : ℕ} (L : List (ℤ × (Fin n → ℤ)))
    (hD : ∀ t ∈ L, t.1 ≠ 0) (P : Fin n → ℚ) :
    eval₂ (Int.castRingHom ℚ) P
        (L.map fun t => ∑ j, (C t.1 * X j - C (t.2 j)) ^ 2 : List (MvPolynomial (Fin n) ℤ)).prod
          = 0 ↔ ∃ t ∈ L, ∀ j, P j = (t.2 j : ℚ) / t.1 := by
  rw [← coe_eval₂Hom, map_list_prod, List.prod_eq_zero_iff, List.map_map, List.mem_map]
  refine exists_congr fun t => and_congr_right fun ht => ?_
  simp only [Function.comp_apply, coe_eval₂Hom, eval₂_sum, eval₂_pow, eval₂_sub, eval₂_mul,
    eval₂_C, eval₂_X]
  simp only [eq_intCast]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)]
  have hD' : (t.1 : ℚ) ≠ 0 := by exact_mod_cast hD t ht
  refine forall_congr' fun j => ?_
  simp only [Finset.mem_univ, true_implies, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
  rw [eq_div_iff hD', mul_comm]

/-! ### The multiplication template -/

/-- The construction of `multiply` on the roots `P₀, P₁, P₂`, with `c_* = cstar`, `ℓ = ell`,
`T = T`: the generator point `G` (constants `1641/8`, `-15465/4`, `87483/32`), for each of
`G, P₀, P₁, P₂` a shift point `S_i` and the call `S_{c_*}[·, S_i]`, then
`height_certificate[P₀, P₁, P₂, ℓ, S₀, …, S₃]` and `multiply.guard[P₀, P₁, P₂]`. -/
noncomputable def multiplyBuild (I : Constructors E) (cstar ell T : ℤ) (P0 P1 P2 : Code) :
    Build Formula := do
  let G ← Build.gen
  let S0 ← Build.point
  let c0 ← Build.call (scalarTemplate I cstar) (Fin.append G S0)
  let S1 ← Build.point
  let c1 ← Build.call (scalarTemplate I cstar) (Fin.append P0 S1)
  let S2 ← Build.point
  let c2 ← Build.call (scalarTemplate I cstar) (Fin.append P1 S2)
  let S3 ← Build.point
  let c3 ← Build.call (scalarTemplate I cstar) (Fin.append P2 S3)
  let h ← Build.call heightTemplate (Fin.append (Fin.append (Fin.append (Fin.append
    (Fin.append P0 P1) P2) ![C ell]) (Fin.append (Fin.append S0 S1) S2)) S3)
  let g ← Build.call (guardTemplate I T) (Fin.append (Fin.append P0 P1) P2)
  pure (.and [c0, c1, c2, c3, h, g])

/-- **The multiplication template** (template index `11`) for the fixed constants with values
`c_*`, `ℓ` and `T`. -/
noncomputable def multiplyTemplate (I : Constructors E) (cstar ell T : ℤ) : ExPoly :=
  Build.template 15 (multiplyBuild I cstar ell T (varPoint 0) (varPoint 5) (varPoint 10))

/-- The call blocks of `multiply`, in order. -/
def multiplyBlocks : List (ℕ × ℕ) :=
  [(23, 1), (29, 1), (35, 1), (41, 1), (42, 35106), (35148, 1)]

/-- The rational constants of `multiply`: `8 X₁₅ ≐ 1641`, `4 X₁₆ ≐ -15465`, `32 X₁₇ ≐ 87483`. -/
def multiplyGlobals : List (ℕ × ℤ × ℤ) := [(15, 1641, 8), (16, -15465, 4), (17, 87483, 32)]

set_option maxRecDepth 20000 in
theorem multiply_facts (I : Constructors E) (cstar ell T : ℤ) :
    Build.Facts 15 (multiplyBuild I cstar ell T (varPoint 0) (varPoint 5) (varPoint 10)) 35149
      multiplyBlocks multiplyGlobals := by
  refine Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)
  have := scalarTemplate_wf I cstar
  have := scalarTemplate_witnesses I cstar
  have := heightTemplate_wf
  have := heightTemplate_witnesses
  have := guardTemplate_wf I T
  have := guardTemplate_witnesses I T
  wp_run (Avail 35149 multiplyBlocks) 35149
  facts_close

/-- The generator point `(0, X_c, -145, X_{c+1}, X_{c+2})` with constant variables at `c`. -/
noncomputable def genPoint (c : ℕ) : Code := ![0, X c, -145, X (c + 1), X (c + 2)]

/-- The formula `φ_mul` of `multiply` with the variables of the article: the roots `P_i` at
`X_{5i}`, the generator point at `X₁₅, X₁₆, X₁₇`, the shift points `S_i` at `X_{18+6i}` with
scalar blocks at `23 + 6i`, the height block at `42` and the guard block at `35148`. -/
noncomputable def multiplyFormula (I : Constructors E) (cstar ell T : ℤ) : Formula :=
  .and [.call (scalarTemplate I cstar) (Fin.append (genPoint 15) (varPoint 18)) 23,
    .call (scalarTemplate I cstar) (Fin.append (varPoint 0) (varPoint 24)) 29,
    .call (scalarTemplate I cstar) (Fin.append (varPoint 5) (varPoint 30)) 35,
    .call (scalarTemplate I cstar) (Fin.append (varPoint 10) (varPoint 36)) 41,
    .call heightTemplate (Fin.append (Fin.append (Fin.append (Fin.append
      (Fin.append (varPoint 0) (varPoint 5)) (varPoint 10)) ![C ell])
      (Fin.append (Fin.append (varPoint 18) (varPoint 24)) (varPoint 30))) (varPoint 36)) 42,
    .call (guardTemplate I T) (Fin.append (Fin.append (varPoint 0) (varPoint 5)) (varPoint 10))
      35148]

theorem multiplyBuild_formula (I : Constructors E) (cstar ell T : ℤ) :
    (multiplyBuild I cstar ell T (varPoint 0) (varPoint 5) (varPoint 10) ⟨15, []⟩).1 =
      multiplyFormula I cstar ell T := by
  dsimp only [multiplyBuild, Build.bind_apply, Build.pure_apply, Build.call, Build.point, Build.gen,
    Build.rational, Build.normalize]
  simp only [scalarTemplate_witnesses, heightTemplate_witnesses]
  rfl

theorem multiplyTemplate_params (I : Constructors E) (cstar ell T : ℤ) :
    (multiplyTemplate I cstar ell T).params = 15 := rfl

theorem multiplyTemplate_witnesses (I : Constructors E) (cstar ell T : ℤ) :
    (multiplyTemplate I cstar ell T).witnesses = 35134 := (multiply_facts I cstar ell T).witnesses

theorem multiplyTemplate_wf (I : Constructors E) (cstar ell T : ℤ) :
    (multiplyTemplate I cstar ell T).WF := (multiply_facts I cstar ell T).wf

/-- The relation of `multiply` through its private blocks: the generator constants take their
values and the conjunction of the six calls holds with every call replaced by the callee
relation. -/
theorem multiplyTemplate_rel_iff (I : Constructors E) (cstar ell T : ℤ) (a : Fin 15 → ℚ) :
    (multiplyTemplate I cstar ell T).Rel a ↔ ∃ y : ℕ → ℚ, (∀ i : Fin 15, y i = a i) ∧
      (y 15 = 1641 / 8 ∧ y 16 = -15465 / 4 ∧ y 17 = 87483 / 32) ∧
      (multiplyFormula I cstar ell T).Lift y := by
  unfold multiplyTemplate
  rw [(multiply_facts I cstar ell T).rel_iff, multiplyBuild_formula]
  simp [multiplyGlobals]

/-! ### The natural-code template -/

/-- The construction of `natural` on the point `A`: the points `σ₀, …, σ₃` and `Σ₀, …, Σ₃`,
the calls `multiply[σ_i, σ_i, Σ_i]`, then `π₁` with `raw_add[Σ₀, Σ₁, π₁]`, `π₂` with
`raw_add[π₁, Σ₂, π₂]`, and `raw_add[π₂, Σ₃, A]`. -/
noncomputable def naturalBuild (I : Constructors E) (cstar ell T : ℤ) (A : Code) :
    Build Formula := do
  let σ ← Build.freshPoints 4
  let Sq ← Build.freshPoints 4
  let m0 ← Build.call (multiplyTemplate I cstar ell T) (Fin.append (Fin.append (σ 0) (σ 0)) (Sq 0))
  let m1 ← Build.call (multiplyTemplate I cstar ell T) (Fin.append (Fin.append (σ 1) (σ 1)) (Sq 1))
  let m2 ← Build.call (multiplyTemplate I cstar ell T) (Fin.append (Fin.append (σ 2) (σ 2)) (Sq 2))
  let m3 ← Build.call (multiplyTemplate I cstar ell T) (Fin.append (Fin.append (σ 3) (σ 3)) (Sq 3))
  let π1 ← Build.point
  let a1 ← Build.call rawAddTemplate (Fin.append (Fin.append (Sq 0) (Sq 1)) π1)
  let π2 ← Build.point
  let a2 ← Build.call rawAddTemplate (Fin.append (Fin.append π1 (Sq 2)) π2)
  let a3 ← Build.call rawAddTemplate (Fin.append (Fin.append π2 (Sq 3)) A)
  pure (.and [m0, m1, m2, m3, a1, a2, a3])

/-- **The natural-code template** (template index `12`). -/
noncomputable def naturalTemplate (I : Constructors E) (cstar ell T : ℤ) : ExPoly :=
  Build.template 5 (naturalBuild I cstar ell T (varPoint 0))

/-- The call blocks of `natural`, in order. -/
def naturalBlocks : List (ℕ × ℕ) :=
  [(45, 35134), (35179, 35134), (70313, 35134), (105447, 35134), (140586, 6), (140597, 6),
    (140603, 6)]

set_option maxRecDepth 20000 in
theorem natural_facts (I : Constructors E) (cstar ell T : ℤ) :
    Build.Facts 5 (naturalBuild I cstar ell T (varPoint 0)) 140609 naturalBlocks [] := by
  refine Build.Facts.of_wp ?_ (by decide) (by decide) (by decide) (by decide)
  have := multiplyTemplate_wf I cstar ell T
  have := multiplyTemplate_witnesses I cstar ell T
  have := rawAddTemplate_wf
  have := rawAddTemplate_witnesses
  wp_run (Avail 140609 naturalBlocks) 140609
  facts_close

/-- The formula of `natural` with the variables of the article: `σ_i` at `X_{5+5i}`, `Σ_i` at
`X_{25+5i}`, the multiplication blocks at `45 + 35134 i`, `π₁` at `X_{140581}`, `π₂` at
`X_{140592}` and the raw addition blocks at `140586`, `140597`, `140603`. -/
noncomputable def naturalFormula (I : Constructors E) (cstar ell T : ℤ) : Formula :=
  .and [.call (multiplyTemplate I cstar ell T)
      (Fin.append (Fin.append (varPoint 5) (varPoint 5)) (varPoint 25)) 45,
    .call (multiplyTemplate I cstar ell T)
      (Fin.append (Fin.append (varPoint 10) (varPoint 10)) (varPoint 30)) 35179,
    .call (multiplyTemplate I cstar ell T)
      (Fin.append (Fin.append (varPoint 15) (varPoint 15)) (varPoint 35)) 70313,
    .call (multiplyTemplate I cstar ell T)
      (Fin.append (Fin.append (varPoint 20) (varPoint 20)) (varPoint 40)) 105447,
    .call rawAddTemplate (Fin.append (Fin.append (varPoint 25) (varPoint 30)) (varPoint 140581))
      140586,
    .call rawAddTemplate (Fin.append (Fin.append (varPoint 140581) (varPoint 35))
      (varPoint 140592)) 140597,
    .call rawAddTemplate (Fin.append (Fin.append (varPoint 140592) (varPoint 40)) (varPoint 0))
      140603]

theorem naturalBuild_formula (I : Constructors E) (cstar ell T : ℤ) :
    (naturalBuild I cstar ell T (varPoint 0) ⟨5, []⟩).1 = naturalFormula I cstar ell T := by
  dsimp only [naturalBuild, Build.bind_apply, Build.pure_apply, Build.call, Build.point,
    Build.freshPoints]
  simp only [multiplyTemplate_witnesses, rawAddTemplate_witnesses]
  rfl

theorem naturalTemplate_params (I : Constructors E) (cstar ell T : ℤ) :
    (naturalTemplate I cstar ell T).params = 5 := rfl

theorem naturalTemplate_witnesses (I : Constructors E) (cstar ell T : ℤ) :
    (naturalTemplate I cstar ell T).witnesses = 140604 := (natural_facts I cstar ell T).witnesses

theorem naturalTemplate_wf (I : Constructors E) (cstar ell T : ℤ) :
    (naturalTemplate I cstar ell T).WF := (natural_facts I cstar ell T).wf

/-- The relation of `natural` through its private blocks. -/
theorem naturalTemplate_rel_iff (I : Constructors E) (cstar ell T : ℤ) (a : Fin 5 → ℚ) :
    (naturalTemplate I cstar ell T).Rel a ↔ ∃ y : ℕ → ℚ, (∀ i : Fin 5, y i = a i) ∧
      (naturalFormula I cstar ell T).Lift y := by
  unfold naturalTemplate
  rw [← naturalBuild_formula]
  exact (natural_facts I cstar ell T).rel_iff_nil a

end ZInQ.Syntax

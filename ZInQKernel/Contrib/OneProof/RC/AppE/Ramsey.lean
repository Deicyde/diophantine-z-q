import ZInQKernel.Contrib.OneProof.RC.AppE.Linear

/-!
# Appendix E: Ramsey's algebraic model, as Elliot uses it, and an algebraic reference vector

The 11/5 manuscript, Appendix E, tex 8041–8083 ("An algebraic vector and the Galois
comparison") and 8090–8098 (the conjugation assertion).

**The print.** N. Ramsey, *Geometric and `p`-adic modular forms of half-integral weight*,
Ann. Inst. Fourier 56 (2006), Definition 3.1, Theorem 4.2, Remark 4.4 (as cited at tex 8042, 8064;
locators UNVERIFIED: no copy was available, no network). Ramsey defines weight-`k/2` forms of level
`4N` over a `ℤ[1/4N]`-algebra as sections of a divisor sheaf on `X₁(4N)` (Def. 3.1), and identifies
them over `ℂ` with the classical forms (Thm. 4.2). Elliot uses two consequences:

* **(R-span)** (tex 8043–8076): sections over characteristic-zero fields commute with flat field
  extension (Elliot checks this himself by a finite affine cover, tex 8064–8076, so that
  Rem. 4.4's restriction on arbitrary base change in weight `3/2` does not matter), so the complex
  space `S_{3/2}(N, ψ)` is spanned by forms with algebraic Fourier coefficients;
* **(R-conj)** (tex 8090–8098): coefficientwise conjugation `g ↦ g^τ` by `τ ∈ Aut(ℚ̄/ℚ)` maps an
  algebraic form of character `ψ` to a form of character `ψ^τ`. Elliot reduces this to integral
  weight by multiplying by `θ` ("The algebraic divisibility condition at the cusps is precisely the
  one in Ramsey's section model, so division after conjugation is again a half-integral-weight
  form"); equivalently it is the `ℚ`-rationality of Ramsey's model and of its `q`-expansion and
  diamond operators.

`RamseyAlgebraicModel` states exactly these two clauses over lane RC8's genuine definitions
(PRINT, printed form as Elliot uses it; the conjugation clause includes the integral-weight
Galois action that Elliot's `θ`-reduction invokes, which the manuscript does not cite separately).

**Proved here.** `exists_algebraic_normalized` (tex 8053–8063, 8076–8083): a nonzero reference
functional on the complex good-Hecke eigenspace `V` is nonzero on its algebraic vectors, so `V`
contains a form `g'` with algebraic coefficients and `a_{g'}(D₀) = 1`. The manuscript argues with
a finite basis of the defining linear equations; the proof here writes a complex eigenvector as
`Σ_j b_j h_j` with `b_j ∈ ℂ` linearly independent over `ℚ̄` and `h_j` algebraic forms, and reads the
`ℚ̄`-rational Hecke equations off each `h_j` (same content, linear algebra over `ℚ̄`; provenance
(c) for the route). The orthogonality of `V` to unary theta series (tex 8053–8059) is not needed
in this form: lane RC8's eigenspace is defined inside the whole cusp space (see
`unary_eigenvalue_ne` for Elliot's eigenvalue inequality).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppE

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.PrintsAnalytic UpperHalfPlane

/-- `ℚ̄`, the algebraic numbers inside `ℂ`. -/
abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

/-- All Fourier coefficients of `g` are algebraic numbers. -/
def HasAlgebraicCoeffs (g : ℍ → ℂ) : Prop := ∀ n : ℕ, hiwCoeff g n ∈ Qbar

/-- **Ramsey's algebraic model of the weight-`3/2` spaces, as Appendix E uses it** (PRINT;
Ramsey, Ann. Inst. Fourier 56 (2006), Def. 3.1 and Thm. 4.2, with Elliot's flat-base-change check,
tex 8064–8076, and Rem. 4.4 for the base-change restriction that is avoided; locators
UNVERIFIED). For a level `N > 0` with `4 ∣ N` and a character `ψ` modulo `N`:
* (R-span) every cusp form of weight `3/2`, level `N`, character `ψ` is a finite complex linear
  combination of such forms with algebraic Fourier coefficients;
* (R-conj) for every `τ ∈ Aut(ℚ̄/ℚ)` and every such form `g` with algebraic coefficients there is
  a cusp form of weight `3/2`, level `N` and character `ψ^τ` (`ψ^τ(n) = τ(ψ(n))`) whose Fourier
  coefficients are `τ(a_g(n))` (tex 8090–8098). -/
def RamseyAlgebraicModel : Prop :=
  ∀ N : ℕ, 0 < N → 4 ∣ N → ∀ ψ : DirichletCharacter ℂ N,
    (∀ g : ℍ → ℂ, IsHalfIntegralWeightCuspForm 3 N ψ g →
      ∃ (s : Finset ℕ) (c : ℕ → ℂ) (f : ℕ → ℍ → ℂ),
        (∀ i ∈ s, IsHalfIntegralWeightCuspForm 3 N ψ (f i) ∧ HasAlgebraicCoeffs (f i)) ∧
        g = ∑ i ∈ s, c i • f i) ∧
    (∀ τ : Qbar ≃ₐ[ℚ] Qbar, ∀ ψ' : DirichletCharacter ℂ N,
      (∀ (n : ZMod N) (x : Qbar), ψ n = (x : ℂ) → ψ' n = ((τ x : Qbar) : ℂ)) →
      ∀ g : ℍ → ℂ, IsHalfIntegralWeightCuspForm 3 N ψ g → HasAlgebraicCoeffs g →
        ∃ g' : ℍ → ℂ, IsHalfIntegralWeightCuspForm 3 N ψ' g' ∧
          ∀ (n : ℕ) (x : Qbar), hiwCoeff g n = (x : ℂ) → hiwCoeff g' n = ((τ x : Qbar) : ℂ))

/-! ## Algebraic numbers -/

theorem mem_Qbar_iff {x : ℂ} : x ∈ Qbar ↔ IsAlgebraic ℚ x := mem_algebraicClosure_iff

/-- A complex number with `x^m = 1`, `m > 0`, is algebraic (PROVED). -/
theorem mem_Qbar_of_pow_eq_one {x : ℂ} {m : ℕ} (hm : 0 < m) (h : x ^ m = 1) : x ∈ Qbar := by
  rw [mem_Qbar_iff]
  have : IsIntegral ℚ (x ^ m) := by rw [h]; exact isIntegral_one
  exact (IsIntegral.of_pow hm this).isAlgebraic

/-- The values of a Dirichlet character are algebraic (PROVED): roots of unity at units, `0`
elsewhere. -/
theorem dirichlet_mem_Qbar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n : ZMod N) :
    χ n ∈ Qbar := by
  by_cases hn : IsUnit n
  · obtain ⟨u, rfl⟩ := hn
    have hpos : 0 < orderOf u := orderOf_pos u
    refine mem_Qbar_of_pow_eq_one hpos ?_
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  · rw [χ.map_nonunit hn]
    exact zero_mem _

theorem intCast_mem_Qbar (z : ℤ) : (z : ℂ) ∈ Qbar := intCast_mem _ z

theorem natCast_mem_Qbar (z : ℕ) : (z : ℂ) ∈ Qbar := natCast_mem _ z

/-- The Hecke defect `T(p²)a − η(p)a_p(E) a` at `n` of an algebraic coefficient sequence is
algebraic (PROVED). -/
theorem heckeDefect_mem_Qbar {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N]
    (ψ η : DirichletCharacter ℂ N) (p : ℕ) {a : ℕ → ℂ} (ha : ∀ m, a m ∈ Qbar) (n : ℕ) :
    heckeT3 N ψ p a n - η p * lcoeff E p * a n ∈ Qbar := by
  unfold heckeT3 lcoeff
  refine sub_mem (add_mem (add_mem (ha _) (mul_mem (mul_mem (dirichlet_mem_Qbar ψ _)
    (intCast_mem_Qbar _)) (ha _))) (mul_mem (mul_mem (pow_mem (dirichlet_mem_Qbar ψ _) _)
    (natCast_mem_Qbar _)) ?_)) (mul_mem (mul_mem (dirichlet_mem_Qbar η _) (intCast_mem_Qbar _))
    (ha _))
  split_ifs
  · exact ha _
  · exact zero_mem _

/-- `heckeT3` commutes with finite linear combinations of coefficient sequences (PROVED). -/
theorem heckeT3_sum {N : ℕ} (χ : DirichletCharacter ℂ N) (p : ℕ) {ι : Type*} (s : Finset ι)
    (b : ι → ℂ) (a : ι → ℕ → ℂ) (n : ℕ) :
    heckeT3 N χ p (fun m => ∑ j ∈ s, b j * a j m) n = ∑ j ∈ s, b j * heckeT3 N χ p (a j) n := by
  unfold heckeT3
  split_ifs
  · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_zero, add_zero]
    exact Finset.sum_congr rfl fun j _ => by ring

/-! ## An algebraic reference vector (tex 8053–8083) -/

/-- **An algebraic vector with `a(D₀) = 1` in the complex eigenspace** (tex 8053–8083; PROVED from
the PRINT `RamseyAlgebraicModel`, clause (R-span)): if `g` lies in the full good-Hecke eigenspace of
`E` and `η` at the level `N` and `a_g(D₀) ≠ 0`, then the same eigenspace contains a form `g'` with
algebraic Fourier coefficients and `a_{g'}(D₀) = 1`. -/
theorem exists_algebraic_normalized (hR : RamseyAlgebraicModel) {E : WeierstrassCurve ℚ} {N : ℕ}
    (hN0 : 0 < N) (hN : 4 ∣ N) {ψ η : DirichletCharacter ℂ N} {g : ℍ → ℂ}
    (hg : IsInWaldspurgerEigenspace E N ψ η g) {D₀ : ℕ} (ha₀ : hiwCoeff g D₀ ≠ 0) :
    ∃ g' : ℍ → ℂ, IsInWaldspurgerEigenspace E N ψ η g' ∧ HasAlgebraicCoeffs g' ∧
      hiwCoeff g' D₀ = 1 := by
  classical
  have : NeZero N := ⟨hN0.ne'⟩
  obtain ⟨s, c, f, hf, hgsum⟩ := (hR N hN0 hN ψ).1 g hg.1
  -- the `ℚ̄`-span of the coefficients `c i`, with a basis `b`
  let W : Submodule Qbar ℂ := Submodule.span Qbar ((s.image c : Finset ℂ) : Set ℂ)
  let b := Module.finBasis Qbar W
  have hcW : ∀ i ∈ s, c i ∈ W := fun i hi =>
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem c hi))
  let q : ℕ → Fin (Module.finrank Qbar W) → Qbar := fun i j =>
    if h : c i ∈ W then b.repr ⟨c i, h⟩ j else 0
  have hcq : ∀ i ∈ s, c i = ∑ j, ((q i j : Qbar) : ℂ) * ((b j : W) : ℂ) := by
    intro i hi
    have h := b.sum_repr ⟨c i, hcW i hi⟩
    have h' := congrArg (fun w : W => (w : ℂ)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    rw [← h']
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [q, hcW i hi, ↓reduceDIte, Algebra.smul_def]
    rfl
  -- the algebraic forms `h_j = Σ_i q_{ij} f_i`
  let h : Fin (Module.finrank Qbar W) → ℍ → ℂ := fun j => ∑ i ∈ s, ((q i j : Qbar) : ℂ) • f i
  have hS : ∀ j, IsHalfIntegralWeightCuspForm 3 N ψ (h j) := fun j =>
    hiwForm_sum s _ f fun i hi => (hf i hi).1
  have hcoef : ∀ j n, hiwCoeff (h j) n = ∑ i ∈ s, ((q i j : Qbar) : ℂ) * hiwCoeff (f i) n :=
    fun j n => hiwCoeff_sum s _ f (fun i hi => (hf i hi).1) n
  have halg : ∀ j, HasAlgebraicCoeffs (h j) := by
    intro j n
    rw [hcoef]
    exact sum_mem fun i hi => mul_mem (q i j).2 ((hf i hi).2 n)
  -- the coefficients of `g` are `Σ_j b_j a_{h_j}(n)`
  have hgcoef : ∀ n, hiwCoeff g n = ∑ j, ((b j : W) : ℂ) * hiwCoeff (h j) n := by
    intro n
    rw [hgsum, hiwCoeff_sum s c f (fun i hi => (hf i hi).1) n]
    simp only [hcoef, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hcq i hi, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- the `ℚ̄`-rational Hecke equations hold for every `h_j`
  have hli := b.linearIndependent
  have hV : ∀ j, IsInWaldspurgerEigenspace E N ψ η (h j) := by
    intro j
    refine ⟨hS j, fun p hp hpN n => ?_⟩
    let Λ : Fin (Module.finrank Qbar W) → Qbar := fun j' =>
      ⟨heckeT3 N ψ p (hiwCoeff (h j')) n - η p * lcoeff E p * hiwCoeff (h j') n,
        heckeDefect_mem_Qbar (E := E) ψ η p (halg j') n⟩
    have hsum : ∑ j', Λ j' • b j' = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def, Submodule.coe_zero]
      have hT := hg.2 p hp hpN n
      have hfun : hiwCoeff g = fun m => ∑ j', ((b j' : W) : ℂ) * hiwCoeff (h j') m :=
        funext hgcoef
      rw [hfun, heckeT3_sum] at hT
      have : ∑ j', ((b j' : W) : ℂ) * (heckeT3 N ψ p (hiwCoeff (h j')) n -
          η p * lcoeff E p * hiwCoeff (h j') n) = 0 := by
        rw [Finset.sum_congr rfl fun j' _ => mul_sub _ _ _, Finset.sum_sub_distrib, hT,
          Finset.mul_sum]
        rw [sub_eq_zero]
        exact Finset.sum_congr rfl fun j' _ => by ring
      rw [← this]
      exact Finset.sum_congr rfl fun j' _ => by
        simp only [Λ]
        rw [mul_comm]
        rfl
    have hΛ := Fintype.linearIndependent_iff.mp hli Λ hsum j
    have := congrArg (fun x : Qbar => (x : ℂ)) hΛ
    simp only [Λ, IntermediateField.coe_zero] at this
    exact sub_eq_zero.mp this
  -- some `h_j` has nonzero reference coefficient
  rw [hgcoef D₀] at ha₀
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha₀
  have hj0 : hiwCoeff (h j) D₀ ≠ 0 := right_ne_zero_of_mul hj
  refine ⟨(hiwCoeff (h j) D₀)⁻¹ • h j, eigen_smul _ (hV j), fun n => ?_, ?_⟩
  · rw [hiwCoeff_smul (hS j)]
    exact mul_mem (inv_mem (halg j D₀)) (halg j n)
  · rw [hiwCoeff_smul (hS j), inv_mul_cancel₀ hj0]

/-! ## Elliot's eigenvalue inequality (tex 8053–8059) -/

/-- **The unary eigenvalues differ from the elliptic ones** (tex 8053–8059; PROVED as the
inequality the manuscript states): at a good prime `p`, a unary theta series has `T(p²)`
eigenvalue of absolute value `p + 1`, whereas `|η(p) a_p(E)| ≤ 2√p < p + 1` (Hasse's bound, with
`|η(p)| = 1`). Only the strict inequality `2√p < p + 1` is proved here; it is the arithmetic content
of "their elliptic eigenspaces are disjoint". -/
theorem unary_eigenvalue_ne {p : ℕ} (hp : p.Prime) {lamE : ℝ}
    (hlam : |lamE| ≤ 2 * Real.sqrt p) : |lamE| < p + 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hs : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (by positivity)
  have hne : Real.sqrt p ≠ 1 := by
    intro h
    rw [h] at hsq
    linarith
  have : 2 * Real.sqrt p < p + 1 := by
    have h1 : 0 < (Real.sqrt p - 1) ^ 2 := by
      have : Real.sqrt p - 1 ≠ 0 := sub_ne_zero.mpr hne
      positivity
    nlinarith
  linarith

end ZInQ.Manuscript.RC.AppE

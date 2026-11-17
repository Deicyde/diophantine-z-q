import ZInQKernel.Contrib.OneProof.Gamma0QExp.Reduce

/-!
# gamma0-qexp, part 6: `ℂ(X₀(N)) = ℂ(j, j_N)` for meromorphic modular functions

For `g` invariant under `Γ₀(N)`, meromorphic on `ℍ` and of moderate growth at every cusp, and the
cosets `c ∈ SL₂(ℤ)/Γ₀(N)` with representatives `γ_c`, put `g_c = g ∘ γ_c⁻¹`, `J_c = j_N ∘ γ_c⁻¹`.
The coefficients of `R(Y) = Σ_c g_c ∏_{c' ≠ c} (Y − J_{c'})` and of
`S(Y) = Σ_c ∏_{c' ≠ c} (Y − J_{c'})` are `SL₂(ℤ)`-invariant meromorphic functions of moderate
growth, hence rational in `j` (`levelOne_mero`); evaluating at `Y = j_N = J_1` gives
`g · S(j_N) = R(j_N)`, and `S(j_N) = ∏_{c ≠ 1} (j_N − J_c) ≠ 0` for `Im τ` large (separation).
Result (`analytic_core`): `B(j, j_N)·g = A(j, j_N)` on punctured neighbourhoods of every point,
with `B(j, j_N)` not identically zero.

No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane ModularCurve Filter Topology Asymptotics
open scoped MatrixGroups

namespace ZInQ.Gamma0QExp

/-! ### The symmetric polynomials -/

section SymPoly

open Polynomial

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Σ_i f_i ∏_{j ≠ i} (X − J_j)`. -/
def symPoly (f J : ι → R) : R[X] :=
  ∑ i, C (f i) * ∏ j, (if j = i then 1 else (X - C (J j)))

theorem symPoly_comp_equiv (f J : ι → R) (e : ι ≃ ι) :
    symPoly (f ∘ e) (J ∘ e) = symPoly f J := by
  unfold symPoly
  refine Eq.trans ?_ (Equiv.sum_comp e
    (fun i => C (f i) * ∏ j, (if j = i then 1 else (X - C (J j)))))
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  congr 1
  refine Eq.trans ?_ (Equiv.prod_comp e (fun j => if j = e i then (1 : R[X]) else (X - C (J j))))
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [e.injective.eq_iff]

theorem symPoly_eval_self (f J : ι → R) (i₀ : ι) :
    (symPoly f J).eval (J i₀) = f i₀ * ∏ j, (if j = i₀ then 1 else J i₀ - J j) := by
  simp only [symPoly, eval_finset_sum, eval_mul, eval_C, eval_prod, apply_ite (eval (J i₀)),
    eval_one, eval_sub, eval_X]
  rw [Finset.sum_eq_single i₀]
  · intro i _ hi
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ i₀)
    simp [Ne.symm hi]
  · simp

theorem symPoly_map {S : Type*} [CommRing S] (φ : R →+* S) (f J : ι → R) :
    (symPoly f J).map φ = symPoly (φ ∘ f) (φ ∘ J) := by
  simp [symPoly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_prod, apply_ite]

theorem natDegree_symPoly_le (f J : ι → R) : (symPoly f J).natDegree ≤ Fintype.card ι := by
  unfold symPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans (natDegree_C_mul_le _ _) (le_trans (natDegree_prod_le _ _) ?_)
  calc ∑ j, (if j = i then (1 : R[X]) else (X - C (J j))).natDegree ≤ ∑ _j : ι, 1 :=
        Finset.sum_le_sum fun j _ => by
          split_ifs
          · simp
          · exact le_trans (natDegree_sub_le _ _) (max_le natDegree_X_le (by simp))
    _ = Fintype.card ι := by simp

/-- The universal coefficient. -/
theorem symPoly_coeff_eval (f J : ι → ℂ) (k : ℕ) :
    (symPoly f J).coeff k = MvPolynomial.eval (Sum.elim f J)
      ((symPoly (fun i => MvPolynomial.X (Sum.inl i)) (fun i => MvPolynomial.X (Sum.inr i)) :
        (MvPolynomial (ι ⊕ ι) ℂ)[X]).coeff k) := by
  rw [← Polynomial.coeff_map, symPoly_map]
  have h1 : (MvPolynomial.eval (Sum.elim f J)) ∘ (fun i => MvPolynomial.X (Sum.inl i)) = f := by
    funext i; simp
  have h2 : (MvPolynomial.eval (Sum.elim f J)) ∘ (fun i => MvPolynomial.X (Sum.inr i)) = J := by
    funext i; simp
  rw [h1, h2]

end SymPoly

/-! ### Meromorphy and analyticity -/

theorem mero_mvEval {σ : Type*} (F : σ → ℍ → ℂ)
    (h : ∀ i (τ : ℍ), MeromorphicAt (F i ∘ ofComplex) (τ : ℂ)) (p : MvPolynomial σ ℂ) (τ : ℍ) :
    MeromorphicAt ((fun τ => MvPolynomial.eval (fun i => F i τ) p) ∘ ofComplex) (τ : ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa [Function.comp_def] using MeromorphicAt.const a (τ : ℂ)
  | add p q hp hq =>
    convert hp.add hq using 1
    funext z; simp
  | mul_X p i hp =>
    convert hp.mul (h i τ) using 1
    funext z; simp

theorem jf_analyticAt {z : ℂ} (hz : 0 < z.im) : AnalyticAt ℂ (jf ∘ ofComplex) z :=
  DifferentiableOn.analyticAt (fun u hu => (jf_differentiableAt ⟨u, hu⟩).differentiableWithinAt)
    (isOpen_UH.mem_nhds hz)

theorem jN_analyticAt (N : ℕ) [NeZero N] {z : ℂ} (hz : 0 < z.im) :
    AnalyticAt ℂ (jN N ∘ ofComplex) z := by
  have hNz : 0 < ((N : ℂ) * z).im := natCast_mul_im_pos N ⟨z, hz⟩
  have h1 : AnalyticAt ℂ ((jf ∘ ofComplex) ∘ fun u : ℂ => (N : ℂ) * u) z :=
    (jf_analyticAt hNz).comp (analyticAt_const.mul analyticAt_id)
  refine h1.congr ?_
  filter_upwards [isOpen_UH.mem_nhds hz] with u hu
  have hNu : 0 < ((N : ℂ) * u).im := natCast_mul_im_pos N ⟨u, hu⟩
  simp only [Function.comp_apply, jN]
  congr 1
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos hNu, coe_scaleN, ofComplex_apply_of_im_pos hu]

theorem mob_analyticAt (γ : SL(2, ℤ)) (τ : ℍ) : AnalyticAt ℂ (mob γ) (τ : ℂ) := by
  have hden := denom_SL_ne_zero γ τ
  have h1 : AnalyticAt ℂ (fun z : ℂ => ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1))
      (τ : ℂ) :=
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
      ((analyticAt_const.mul analyticAt_id).add analyticAt_const) hden
  refine h1.congr ?_
  filter_upwards [isOpen_UH.mem_nhds (coe_mem_UH τ)] with z hz
  simp only [mob, coe_SL_smul, ofComplex_apply_of_im_pos hz]

theorem comp_mob (F : ℍ → ℂ) (γ : SL(2, ℤ)) :
    (fun τ => F (γ • τ)) ∘ ofComplex = (F ∘ ofComplex) ∘ mob γ := by
  funext z; simp [mob]

theorem mero_comp_smul {F : ℍ → ℂ} (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (γ : SL(2, ℤ)) (τ : ℍ) : MeromorphicAt ((fun τ => F (γ • τ)) ∘ ofComplex) (τ : ℂ) := by
  rw [comp_mob]
  refine MeromorphicAt.comp_analyticAt ?_ (mob_analyticAt γ τ)
  rw [mob_coe]
  exact hF _

/-! ### Polynomials are nonzero far out -/

theorem exists_eval_ne_zero_of_norm_gt (p : Polynomial ℂ) (hp : p ≠ 0) :
    ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → p.eval z ≠ 0 := by
  classical
  refine ⟨∑ x ∈ p.roots.toFinset, ‖x‖, fun z hz h0 => ?_⟩
  have hz' : z ∈ p.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]; exact h0
  have := Finset.single_le_sum (f := fun x : ℂ => ‖x‖) (fun _ _ => norm_nonneg _) hz'
  linarith

/-! ### Cosets of `Γ₀(N)` -/

section Cosets

variable (N : ℕ) [NeZero N]

/-- `SL₂(ℤ)/Γ₀(N)`. -/
abbrev Cos := SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N

noncomputable instance : Fintype (Cos N) := Fintype.ofFinite _

noncomputable instance : DecidableEq (Cos N) := Classical.decEq _

/-- `g_c = g ∘ γ_c⁻¹`. -/
def conjF (g : ℍ → ℂ) (c : Cos N) (τ : ℍ) : ℂ := g ((Quotient.out c)⁻¹ • τ)

/-- `J_c = j_N ∘ γ_c⁻¹`. -/
def conjJ (c : Cos N) (τ : ℍ) : ℂ := jN N ((Quotient.out c)⁻¹ • τ)

theorem out_smul (σ : SL(2, ℤ)) (c : Cos N) :
    ∃ h ∈ CongruenceSubgroup.Gamma0 N, Quotient.out (σ • c) = σ * Quotient.out c * h := by
  have hc : σ • c = (QuotientGroup.mk (σ * Quotient.out c) : Cos N) := by
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) (σ * Quotient.out c)
  exact ⟨h, h.2, by rw [hc]; exact hh⟩

theorem out_inv_smul (σ : SL(2, ℤ)) (c : Cos N) (τ : ℍ) :
    ∃ h ∈ CongruenceSubgroup.Gamma0 N,
      (Quotient.out (σ • c))⁻¹ • σ • τ = h • ((Quotient.out c)⁻¹ • τ) := by
  obtain ⟨h, hh, he⟩ := out_smul N σ c
  refine ⟨h⁻¹, inv_mem hh, ?_⟩
  rw [he, mul_inv_rev, mul_inv_rev, mul_smul, mul_smul, inv_smul_smul]

theorem conjF_smul {g : ℍ → ℂ}
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ, g (γ • τ) = g τ)
    (σ : SL(2, ℤ)) (c : Cos N) (τ : ℍ) : conjF N g (σ • c) (σ • τ) = conjF N g c τ := by
  obtain ⟨h, hh, he⟩ := out_inv_smul N σ c τ
  simp only [conjF, he, hinv h hh]

theorem conjJ_smul (σ : SL(2, ℤ)) (c : Cos N) (τ : ℍ) :
    conjJ N (σ • c) (σ • τ) = conjJ N c τ := by
  obtain ⟨h, hh, he⟩ := out_inv_smul N σ c τ
  simp only [conjJ, he, jN_smul_of_mem N hh]

/-- The identity coset. -/
def c₀ : Cos N := QuotientGroup.mk 1

theorem out_c₀_mem : Quotient.out (c₀ N) ∈ CongruenceSubgroup.Gamma0 N := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) (1 : SL(2, ℤ))
  rw [c₀, hh, one_mul]
  exact h.2

theorem conjF_c₀ {g : ℍ → ℂ}
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ, g (γ • τ) = g τ) (τ : ℍ) :
    conjF N g (c₀ N) τ = g τ :=
  hinv _ (inv_mem (out_c₀_mem N)) τ

theorem conjJ_c₀ (τ : ℍ) : conjJ N (c₀ N) τ = jN N τ :=
  jN_smul_of_mem N (inv_mem (out_c₀_mem N)) τ

theorem out_inv_not_mem {c : Cos N} (hc : c ≠ c₀ N) :
    (Quotient.out c)⁻¹ ∉ CongruenceSubgroup.Gamma0 N := by
  intro h
  apply hc
  rw [← QuotientGroup.out_eq' c, c₀, QuotientGroup.eq]
  simpa using h

end Cosets

/-! ### The coefficients are level-one functions -/

section Core

variable (N : ℕ) [NeZero N]

theorem coeff_levelOne (F J : Cos N → ℍ → ℂ)
    (hFs : ∀ (σ : SL(2, ℤ)) c τ, F (σ • c) (σ • τ) = F c τ)
    (hJs : ∀ (σ : SL(2, ℤ)) c τ, J (σ • c) (σ • τ) = J c τ)
    (hFm : ∀ c (τ : ℍ), MeromorphicAt (F c ∘ ofComplex) (τ : ℂ))
    (hJm : ∀ c (τ : ℍ), MeromorphicAt (J c ∘ ofComplex) (τ : ℂ))
    (hFg : ∀ c, ModGrowth (F c)) (hJg : ∀ c, ModGrowth (J c)) (k : ℕ) :
    ∃ A B : Polynomial ℂ, B ≠ 0 ∧
      EvNe (fun τ => B.eval (jf τ) * (symPoly (F · τ) (J · τ)).coeff k = A.eval (jf τ)) := by
  classical
  set U := ((symPoly (fun i => MvPolynomial.X (Sum.inl i)) (fun i => MvPolynomial.X (Sum.inr i)) :
        Polynomial (MvPolynomial (Cos N ⊕ Cos N) ℂ)).coeff k)
  set H : Cos N ⊕ Cos N → ℍ → ℂ := fun i τ => Sum.elim (F · τ) (J · τ) i
  have hrep : ∀ τ, (symPoly (F · τ) (J · τ)).coeff k = MvPolynomial.eval (fun i => H i τ) U :=
    fun τ => by
      rw [symPoly_coeff_eval]
  apply levelOne_mero
  · intro σ τ
    have hF' : (F · (σ • τ)) = (F · τ) ∘ (MulAction.toPerm σ⁻¹ : Equiv.Perm (Cos N)) := by
      funext c
      simp only [Function.comp_apply, MulAction.toPerm_apply]
      conv_lhs => rw [← smul_inv_smul σ c]
      exact hFs σ _ τ
    have hJ' : (J · (σ • τ)) = (J · τ) ∘ (MulAction.toPerm σ⁻¹ : Equiv.Perm (Cos N)) := by
      funext c
      simp only [Function.comp_apply, MulAction.toPerm_apply]
      conv_lhs => rw [← smul_inv_smul σ c]
      exact hJs σ _ τ
    rw [hF', hJ', symPoly_comp_equiv]
  · intro τ
    have := mero_mvEval H (fun i τ => by cases i <;> simp [H, hFm, hJm]) U τ
    convert this using 1
    funext z
    simp only [Function.comp_apply, hrep]
  · have := ModGrowth.mvEval H (fun i => by cases i <;> simp [H, hFg, hJg]) U
    convert this using 1
    funext τ
    exact hrep τ

theorem evalX0 (p : Polynomial ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) p) =
      p.eval (v 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

/-- **`ℂ(X₀(N)) = ℂ(j, j_N)`, analytic form.** -/
theorem analytic_core (g : ℍ → ℂ)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ, g (γ • τ) = g τ)
    (hmer : ∀ τ : ℍ, MeromorphicAt (g ∘ ofComplex) (τ : ℂ))
    (hgr : ∀ γ : SL(2, ℤ), ModGrowth (fun τ => g (γ • τ))) :
    ∃ A B : MvPolynomial (Fin 2) ℂ, (∃ τ₀ : ℍ, MvPolynomial.eval ![jf τ₀, jN N τ₀] B ≠ 0) ∧
      EvNe (fun τ => MvPolynomial.eval ![jf τ, jN N τ] B * g τ =
        MvPolynomial.eval ![jf τ, jN N τ] A) := by
  classical
  set F : Cos N → ℍ → ℂ := conjF N g
  set F1 : Cos N → ℍ → ℂ := fun _ _ => 1
  set J : Cos N → ℍ → ℂ := conjJ N
  have hJs : ∀ (σ : SL(2, ℤ)) c τ, J (σ • c) (σ • τ) = J c τ := conjJ_smul N
  have hJm : ∀ c (τ : ℍ), MeromorphicAt (J c ∘ ofComplex) (τ : ℂ) := fun c τ =>
    mero_comp_smul (fun τ => (jN_analyticAt N τ.im_pos).meromorphicAt) _ τ
  have hJg : ∀ c, ModGrowth (J c) := fun c => modGrowth_jN_smul N _
  have hr := coeff_levelOne N F J (conjF_smul N hinv) hJs
    (fun c τ => mero_comp_smul hmer _ τ) hJm (fun c => hgr _) hJg
  have hs := coeff_levelOne N F1 J (fun _ _ _ => rfl) hJs
    (fun c τ => MeromorphicAt.const 1 _) hJm (fun c => ModGrowth.const 1) hJg
  choose Ar Br hBr hr using hr
  choose As Bs hBs hs using hs
  set n := Fintype.card (Cos N) + 1
  set D0 : Polynomial ℂ := (∏ k ∈ Finset.range n, Br k) * ∏ k ∈ Finset.range n, Bs k
  have hD0 : D0 ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => hBr k)
    (Finset.prod_ne_zero_iff.2 fun k _ => hBs k)
  set Atr : ℕ → Polynomial ℂ := fun k =>
    Ar k * ((∏ k' ∈ (Finset.range n).erase k, Br k') * ∏ k' ∈ Finset.range n, Bs k')
  set Ats : ℕ → Polynomial ℂ := fun k =>
    As k * ((∏ k' ∈ Finset.range n, Br k') * ∏ k' ∈ (Finset.range n).erase k, Bs k')
  set B : MvPolynomial (Fin 2) ℂ := ∑ k ∈ Finset.range n,
    Polynomial.aeval (MvPolynomial.X 0) (Ats k) * MvPolynomial.X 1 ^ k
  set A : MvPolynomial (Fin 2) ℂ := ∑ k ∈ Finset.range n,
    Polynomial.aeval (MvPolynomial.X 0) (Atr k) * MvPolynomial.X 1 ^ k
  have hevB : ∀ x y : ℂ, MvPolynomial.eval ![x, y] B = ∑ k ∈ Finset.range n, (Ats k).eval x * y ^ k :=
    fun x y => by simp [B, evalX0]
  have hevA : ∀ x y : ℂ, MvPolynomial.eval ![x, y] A = ∑ k ∈ Finset.range n, (Atr k).eval x * y ^ k :=
    fun x y => by simp [A, evalX0]
  -- all level-one identities at once
  have hall := EvNe.finset (Finset.range n) (P := fun k τ =>
      (Br k).eval (jf τ) * (symPoly (F · τ) (J · τ)).coeff k = (Ar k).eval (jf τ) ∧
      (Bs k).eval (jf τ) * (symPoly (F1 · τ) (J · τ)).coeff k = (As k).eval (jf τ))
    (fun k _ => (hr k).and (hs k))
  -- at a point where they hold
  have hpt : ∀ τ : ℍ, (∀ k ∈ Finset.range n,
      (Br k).eval (jf τ) * (symPoly (F · τ) (J · τ)).coeff k = (Ar k).eval (jf τ) ∧
      (Bs k).eval (jf τ) * (symPoly (F1 · τ) (J · τ)).coeff k = (As k).eval (jf τ)) →
      MvPolynomial.eval ![jf τ, jN N τ] B =
        D0.eval (jf τ) * (symPoly (F1 · τ) (J · τ)).eval (jN N τ) ∧
      MvPolynomial.eval ![jf τ, jN N τ] A =
        D0.eval (jf τ) * (symPoly (F · τ) (J · τ)).eval (jN N τ) := by
    intro τ hτ
    have hdeg : ∀ (f' : Cos N → ℂ), (symPoly f' (J · τ)).natDegree < n := fun f' =>
      Nat.lt_succ_of_le (natDegree_symPoly_le _ _)
    constructor
    · rw [hevB, Polynomial.eval_eq_sum_range' (hdeg _), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have h1 := (hτ k hk).2
      simp only [Ats, D0, Polynomial.eval_mul, Polynomial.eval_prod]
      rw [← Finset.mul_prod_erase _ _ hk]
      rw [← Finset.mul_prod_erase (Finset.range n) (fun k' => (Bs k').eval (jf τ)) hk] at *
      rw [← h1]
      ring
    · rw [hevA, Polynomial.eval_eq_sum_range' (hdeg _), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have h1 := (hτ k hk).1
      simp only [Atr, D0, Polynomial.eval_mul, Polynomial.eval_prod]
      rw [← Finset.mul_prod_erase (Finset.range n) (fun k' => (Br k').eval (jf τ)) hk]
      rw [← h1]
      ring
  -- the evaluation identity `g · S(j_N) = R(j_N)`
  have hSR : ∀ τ : ℍ, (symPoly (F · τ) (J · τ)).eval (jN N τ) =
      g τ * (symPoly (F1 · τ) (J · τ)).eval (jN N τ) := by
    intro τ
    have e1 := symPoly_eval_self (fun c => F c τ) (fun c => J c τ) (c₀ N)
    have e2 := symPoly_eval_self (fun c => F1 c τ) (fun c => J c τ) (c₀ N)
    simp only [J, F, F1, conjJ_c₀ N, conjF_c₀ N hinv, one_mul] at e1 e2
    simp only [J, F, F1]
    rw [e1, e2]
  refine ⟨A, B, ?_, ?_⟩
  · -- nonvanishing at a point with large imaginary part
    obtain ⟨R0, hR0⟩ := exists_eval_ne_zero_of_norm_gt D0 hD0
    obtain ⟨T₁, hT₁⟩ := jf_bounds
    obtain ⟨Ts, hTs⟩ := jN_separation N
    obtain ⟨τ₀, hτ₀, hτ₀P⟩ := hall.exists_im_gt (max (max T₁ Ts) (max |R0| 1))
    have hy1 : 1 ≤ τ₀.im := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hτ₀.le
    refine ⟨τ₀, ?_⟩
    rw [(hpt τ₀ hτ₀P).1]
    refine mul_ne_zero (hR0 _ ?_) ?_
    · have h1 := (hT₁ τ₀ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hτ₀.le)).1
      have h2 := Real.add_one_le_exp (2 * Real.pi * τ₀.im)
      have h3 : |R0| < τ₀.im := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hτ₀
      have hpi := Real.two_le_pi
      have h4 : 2 * τ₀.im ≤ Real.pi * τ₀.im := mul_le_mul_of_nonneg_right hpi (by linarith)
      nlinarith [le_abs_self R0]
    · have e2 := symPoly_eval_self (fun c => F1 c τ₀) (fun c => J c τ₀) (c₀ N)
      simp only [J, F1, conjJ_c₀ N, one_mul] at e2
      simp only [J, F1]
      rw [e2]
      refine Finset.prod_ne_zero_iff.2 fun c _ => ?_
      split_ifs with hc
      · exact one_ne_zero
      · rw [sub_ne_zero]
        intro heq
        exact hTs _ τ₀ (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hτ₀.le)
          (out_inv_not_mem N hc) heq.symm
  · refine hall.mono fun τ hτ => ?_
    rw [(hpt τ hτ).1, (hpt τ hτ).2, hSR]
    ring

end Core

end ZInQ.Gamma0QExp

import ZInQKernel.Contrib.OneProof.PanBergerPrinted
import ZInQKernel.Contrib.OneProof.DSThm965Weak

/-!
# Berger's `B_st = B_max[log [p̃]] ⊆ B_dR` and the leaves of `r11r12` over it (task bst-construct)

pb-fix2's `BergerPrintedU` (Berger 2002, Théorème 0.7) used pb-bypass's abstract `B_st = B_cris[X]` and a
`ℚ_p`-dimension normalization with an abstract `K_0`. This file builds the period rings the way Berger prints
them (Berger 2002 §1.2; wording UNVERIFIED here), as subrings of Mathlib's `B_dR = BDeRham 𝓞_ℂ_p p`:

* `Amax`: `A_max = {Σ a_n (ω/p)^n : a_n ∈ A_inf = W(𝓞_ℂ_p♭), a_n → 0 p-adically}` inside `B_dR^+`, the
  series evaluated `ker θ`-adically (`psEval`), `ω = ξ = p − [p̃]` (bdr-kertheta's generator;
  `amaxOf_eq_amax`: every generator of `ker θ` gives the same ring);
* `logPlus`, `logTeich` (`log [ε]`, `ε^♯ = 1`), `logPTilde` (`log [p̃] := log([p̃]/p)`), all in `B_dR^+`;
* `BmaxPlus = A_max[1/p]`, `Bmax = B_max^+[1/t]` (inverting every `log [ε]`, `ε ≠ 1`),
  `Bst = B_max[log [p̃]]`;
* Fontaine's admissibility `IsAdmissible B H ρ :⇔ dim_{B^H} (B ⊗_{ℚ_p} V)^H = dim_{ℚ_p} V`;
  `IsSemistableB`, `IsPstB`, `LocalIsPstB`.

Proved (standard axioms): `B_max^+`, `B_max` and `B_st` are `G_{ℚ_p}`-stable (`bmaxPlus_stable`,
`bmax_stable`, `bst_stable`), with `σ(log [p̃]) = log [p̃] + log [u_σ]` (`bdrAct_logPTilde`), from the
additivity of `log` on `1 + ker θ` (`logPlus_add`) and `log [ε] ∈ A_max` (`logTeich_mem_amax`); the trivial
representation is admissible for every `B` (`isAdmissible_trivial`); `B_dR^+ → B_dR` is injective;
`log [ε] ≠ 0` for every `ε ≠ 1` with `ε^♯ = 1`, and such `ε` exist, so `t ≠ 0` (`logTeich_ne_zero`,
`exists_t_ne_zero`); given
Fontaine's transcendence of `log [p̃]` (`LogPTildeTranscendental`), `B_st ≅ B_max[X]`
(`bstEquivPolynomial`); given Fontaine's `B_st^{G_K} = K_0` in dimension form (`FontaineBstInvariants`),
admissibility is pb-fix2's normalization `dim_{ℚ_p} D_st,K = [K_0 : ℚ_p] · dim V` (`isSemistableB_iff_K0`).

The leaves `BergerPrintedB` and `PanPrintedB` are pb-fix2's `BergerPrintedU` and `PanPrintedU` with potential
semistability computed over Berger's `B_st` (`LocalIsPstB`); `panBerger_of_printedB` discharges `r11r12`
from them and Diamond–Shurman 9.6.5/9.6.6 (pb-fix2's proof verbatim). Neither named input above is used by
it.
-/


noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace BergerBst

open Module PowerSeries
open scoped TensorProduct

/-! ## §1. Evaluating a power series at an element of `I` in the `I`-adic completion -/

section PSEval

variable {A : Type*} [CommRing A] (I : Ideal A) {x : A}

theorem eval_mem_pow_of_coeff (hx : x ∈ I) (n : ℕ) (Q : Polynomial A)
    (hQ : ∀ k < n, Q.coeff k = 0) : Q.eval x ∈ I ^ n := by
  have hdvd : (Polynomial.X : Polynomial A) ^ n ∣ Q := by
    rw [Polynomial.X_pow_dvd_iff]
    exact hQ
  obtain ⟨R, rfl⟩ := hdvd
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hx n)

/-- `P(x) ≡ (P mod X^n)(x) mod I^n`. -/
theorem eval_sub_trunc_mem (hx : x ∈ I) (n : ℕ) (P : Polynomial A) :
    P.eval x - (trunc n (P : A⟦X⟧)).eval x ∈ I ^ n := by
  rw [← Polynomial.eval_sub]
  refine eval_mem_pow_of_coeff I hx n _ fun k hk => ?_
  rw [Polynomial.coeff_sub, coeff_trunc, ite_eq_left hk, Polynomial.coeff_coe, sub_self]

theorem trunc_cauchy (hx : x ∈ I) (f : A⟦X⟧) (n : ℕ) :
    (trunc n f).eval x ≡ (trunc (n + 1) f).eval x [SMOD (I ^ n • ⊤ : Submodule A A)] := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Polynomial.eval_sub]
  refine eval_mem_pow_of_coeff I hx n _ fun k hk => ?_
  rw [Polynomial.coeff_sub, coeff_trunc, coeff_trunc, ite_eq_left hk, ite_eq_left (by omega), sub_self]

/-- The `I`-adic limit of the truncations `Σ_{k<n} a_k x^k`. -/
def psEvalFun (hx : x ∈ I) (f : A⟦X⟧) : AdicCompletion I A :=
  AdicCompletion.mk I A (AdicCompletion.AdicCauchySequence.mk I A
    (fun n => (trunc n f).eval x) (trunc_cauchy I hx f))

theorem evalₐ_psEvalFun (hx : x ∈ I) (f : A⟦X⟧) (n : ℕ) :
    AdicCompletion.evalₐ I n (psEvalFun I hx f) = Ideal.Quotient.mk (I ^ n) ((trunc n f).eval x) := by
  unfold psEvalFun
  rw [AdicCompletion.evalₐ_mk]
  rfl

theorem mk_eval_trunc (hx : x ∈ I) (n : ℕ) (P : Polynomial A) :
    Ideal.Quotient.mk (I ^ n) ((trunc n (P : A⟦X⟧)).eval x) = Ideal.Quotient.mk (I ^ n) (P.eval x) := by
  rw [Ideal.Quotient.eq]
  have := eval_sub_trunc_mem I hx n P
  rw [← neg_sub]
  exact Submodule.neg_mem _ this

/-- **Evaluation at `x ∈ I`**, `A⟦X⟧ → Â_I`, `Σ a_k X^k ↦ Σ a_k x^k` (an `I`-adic limit). -/
def psEval (hx : x ∈ I) : A⟦X⟧ →+* AdicCompletion I A where
  toFun := psEvalFun I hx
  map_one' := AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEvalFun, map_one (AdicCompletion.evalₐ I n), ← Polynomial.coe_one, mk_eval_trunc I hx,
      Polynomial.eval_one, map_one]
  map_mul' f g := AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEvalFun, map_mul (AdicCompletion.evalₐ I n), evalₐ_psEvalFun, evalₐ_psEvalFun,
      ← trunc_trunc_mul_trunc,
      ← Polynomial.coe_mul, mk_eval_trunc I hx, Polynomial.eval_mul, map_mul]
  map_zero' := AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEvalFun, map_zero (AdicCompletion.evalₐ I n), map_zero (trunc n),
      Polynomial.eval_zero, map_zero]
  map_add' f g := AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEvalFun, map_add (AdicCompletion.evalₐ I n), evalₐ_psEvalFun, evalₐ_psEvalFun,
      map_add (trunc n), Polynomial.eval_add, map_add]

theorem evalₐ_psEval (hx : x ∈ I) (f : A⟦X⟧) (n : ℕ) :
    AdicCompletion.evalₐ I n (psEval I hx f) = Ideal.Quotient.mk (I ^ n) ((trunc n f).eval x) :=
  evalₐ_psEvalFun I hx f n

/-- Two evaluations agree if the terms agree: `a_k x^k = b_k y^k` for all `k`. -/
theorem psEval_eq_of_terms {y : A} (hx : x ∈ I) (hy : y ∈ I) (f g : A⟦X⟧)
    (h : ∀ k, PowerSeries.coeff k f * x ^ k = PowerSeries.coeff k g * y ^ k) :
    psEval I hx f = psEval I hy g :=
  AdicCompletion.ext_evalₐ fun n => by
    rw [evalₐ_psEval, evalₐ_psEval, Polynomial.eval, Polynomial.eval, eval₂_trunc_eq_sum_range,
      eval₂_trunc_eq_sum_range]
    simp only [RingHom.id_apply, h]

theorem psEval_C (hx : x ∈ I) (a : A) :
    psEval I hx (C a) = algebraMap A (AdicCompletion I A) a := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_psEval, ← Polynomial.coe_C, mk_eval_trunc I hx, Polynomial.eval_C]
  simp

end PSEval

/-! ## §2. `A_max`, `B_max^+`, `log`, `t`, `log [p̃]`, `B_max` and `B_st` inside `B_dR` -/

section Rings

variable (p : ℕ) [Fact p.Prime]

open PanBergerSplit (Ainf AinfP)

/-- `ker θ ⊆ W(𝓞_ℂ_p♭)[1/p]` (`θ` with `p` inverted), the ideal Mathlib's `B_dR^+` completes at. -/
abbrev Ith : Ideal (AinfP p) := RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p)

/-- `B_dR^+ → B_dR`. -/
abbrev toBdR : BDeRhamPlus 𝓞_ℂ_[p] p →+* BdR p := algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)

/-- Evaluation of a power series over `W(𝓞_ℂ_p♭)[1/p]` at `x ∈ ker θ`, as an element of `B_dR^+`
(Mathlib's `BDeRhamPlus` is by definition the `ker θ`-adic completion). -/
def evalB {x : AinfP p} (hx : x ∈ Ith p) : (AinfP p)⟦X⟧ →+* BDeRhamPlus 𝓞_ℂ_[p] p :=
  psEval (Ith p) hx

theorem xi'_mem : ZInQ.Contrib.G9.BdrKer.Cp.xi' p ∈ Ith p := by
  rw [Ith, ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineThetaInvertP_Cp]
  exact Ideal.mem_span_singleton_self _

/-- `ω/p` with `ω = ξ = p − [p̃]`, the generator of `ker θ ⊆ A_inf` of bdr-kertheta. -/
def omegaP : AinfP p := ZInQ.Contrib.G9.BdrKer.Cp.xi' p * qpToLoc p ((p : ℚ_[p])⁻¹)

theorem omegaP_mem : omegaP p ∈ Ith p := Ideal.mul_mem_right _ _ (xi'_mem p)

/-- `a_n → 0` `p`-adically in `A_inf = W(𝓞_ℂ_p♭)`. -/
def PAdicNull (a : ℕ → Ainf p) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, (p : Ainf p) ^ k ∣ a n

/-- Power series over `A_inf` whose coefficients tend to `0` `p`-adically. -/
def restricted : Subring (Ainf p)⟦X⟧ where
  carrier := {f | PAdicNull p fun n => PowerSeries.coeff n f}
  one_mem' k := ⟨1, fun n hn => by
    beta_reduce
    rw [PowerSeries.coeff_one, ite_eq_right (by omega)]
    exact dvd_zero _⟩
  zero_mem' k := ⟨0, fun n _ => by beta_reduce; rw [map_zero]; exact dvd_zero _⟩
  add_mem' {f g} hf hg k := by
    obtain ⟨N, hN⟩ := hf k
    obtain ⟨M, hM⟩ := hg k
    exact ⟨max N M, fun n hn => by
      beta_reduce
      rw [map_add]
      exact dvd_add (hN n (le_of_max_le_left hn)) (hM n (le_of_max_le_right hn))⟩
  neg_mem' {f} hf k := by
    obtain ⟨N, hN⟩ := hf k
    exact ⟨N, fun n hn => by beta_reduce; rw [map_neg]; exact (dvd_neg).mpr (hN n hn)⟩
  mul_mem' {f g} hf hg k := by
    obtain ⟨N, hN⟩ := hf k
    obtain ⟨M, hM⟩ := hg k
    refine ⟨N + M, fun n hn => ?_⟩
    beta_reduce
    rw [PowerSeries.coeff_mul]
    refine Finset.dvd_sum fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    by_cases hi : N ≤ ij.1
    · exact Dvd.dvd.mul_right (hN _ hi) _
    · exact Dvd.dvd.mul_left (hM _ (by omega)) _

/-- **`A_max`** (Berger 2002 §1.2 / Colmez, UNVERIFIED wording): the series `Σ a_n (ω/p)^n`,
`a_n ∈ Ã^+ = A_inf` tending to `0` `p`-adically, `ω` a generator of `ker(θ : A_inf → 𝓞_ℂ_p)`,
as a subring of `B_dR^+`. -/
def Amax : Subring (BDeRhamPlus 𝓞_ℂ_[p] p) :=
  (restricted p).map ((evalB p (omegaP_mem p)).comp
    (PowerSeries.map (algebraMap (Ainf p) (AinfP p))))

/-- The logarithm series `log(1 + X) = Σ_{n ≥ 1} (−1)^{n+1} X^n / n` over `W(𝓞_ℂ_p♭)[1/p]`. -/
def logSeries : (AinfP p)⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (-1) ^ (n + 1) * qpToLoc p ((n : ℚ_[p])⁻¹)

/-- **`log(1 + y) ∈ B_dR^+`** for `y ∈ ker θ`, the `ker θ`-adically convergent series. -/
def logPlus {y : AinfP p} (hy : y ∈ Ith p) : BDeRhamPlus 𝓞_ℂ_[p] p := evalB p hy (logSeries p)

theorem teich_sub_one_mem {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) :
    algebraMap (Ainf p) (AinfP p) (WittVector.teichmuller p ε - 1) ∈ Ith p := by
  have hk : WittVector.teichmuller p ε - 1 ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) :=
    PanBergerSplit.theta_teich_sub_one p h
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  rw [← hc, map_mul, mul_comm]
  exact Ideal.mul_mem_right _ _ (xi'_mem p)

/-- **`log [ε] ∈ B_dR^+`** for `ε ∈ 𝓞_ℂ_p♭` with `ε^♯ = 1`: `log(1 + ([ε] − 1))`. -/
def logTeich {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) : BDeRhamPlus 𝓞_ℂ_[p] p :=
  logPlus p (teich_sub_one_mem p h)

/-- The inverses in `B_dR` of `log [ε]`, `ε^♯ = 1`, `ε ≠ 1`. Each is `a·t` with `a ∈ ℤ_p ∖ 0`
(`t = log [ε₀]` for a generator `ε₀` of `ℤ_p(1)`), so adjoining them to a `ℚ_p`-algebra
containing `t` is adjoining `1/t`. `Ring.inverse` is the inverse in the field `B_dR`. -/
def tInvSet : Set (BdR p) :=
  {z | ∃ (ε : PreTilt 𝓞_ℂ_[p] p) (h : PreTilt.untilt ε = 1), ε ≠ 1 ∧
    z = Ring.inverse (toBdR p (logTeich p h))}

/-- `[p̃]/p − 1 = −ω/p` (`ω = p − [p̃]`). -/
def pTildeArg : AinfP p := -omegaP p

theorem pTildeArg_mem : pTildeArg p ∈ Ith p := Submodule.neg_mem _ (omegaP_mem p)

/-- **`log [p̃] := log([p̃]/p) ∈ B_dR^+`**, `p̃ = (p, p^{1/p}, …) ∈ 𝓞_ℂ_p♭` (bdr-kertheta's `pFlat`):
`Σ_{n ≥ 1} (−1)^{n+1} ([p̃]/p − 1)^n / n`. -/
def logPTilde : BDeRhamPlus 𝓞_ℂ_[p] p := logPlus p (pTildeArg_mem p)

/-- **`B_max^+ = A_max[1/p]`**, inside `B_dR`. -/
def BmaxPlus : Subalgebra ℚ_[p] (BdR p) := Algebra.adjoin ℚ_[p] (toBdR p '' Amax p)

/-- **`B_max = B_max^+[1/t]`**, inside `B_dR`. -/
def Bmax : Subalgebra ℚ_[p] (BdR p) := Algebra.adjoin ℚ_[p] (toBdR p '' Amax p ∪ tInvSet p)

/-- **`B_st = B_max[log [p̃]]`**, inside `B_dR` (Berger 2002 §1.2, UNVERIFIED wording). -/
def Bst : Subalgebra ℚ_[p] (BdR p) :=
  Algebra.adjoin ℚ_[p] (toBdR p '' Amax p ∪ tInvSet p ∪ {toBdR p (logPTilde p)})

theorem bmaxPlus_le_bmax : BmaxPlus p ≤ Bmax p :=
  Algebra.adjoin_mono Set.subset_union_left

theorem bmax_le_bst : Bmax p ≤ Bst p :=
  Algebra.adjoin_mono Set.subset_union_left

theorem logPTilde_mem_bst : toBdR p (logPTilde p) ∈ Bst p :=
  Algebra.subset_adjoin (Set.mem_union_right _ rfl)

/-- `B_st` is the `B_max`-algebra generated by `log [p̃]`. -/
theorem bst_eq_adjoin :
    Bst p = (Algebra.adjoin (Bmax p) {toBdR p (logPTilde p)}).restrictScalars ℚ_[p] := by
  rw [Bst, Algebra.adjoin_union_eq_adjoin_adjoin]
  rfl

end Rings

/-! ## §3. Fontaine's admissibility for a `G_{ℚ_p}`-stable subring `B ⊆ B_dR` -/

section Admissible

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- **`B^H`**: the elements of `B` fixed by every `σ ∈ H` (a `ℚ_p`-subalgebra of `B`). -/
def fixedSub (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) : Subalgebra ℚ_[p] B where
  carrier := {b | ∀ σ ∈ H, bdrAct p σ (b : BdR p) = b}
  mul_mem' {a b} ha hb σ hσ := by
    simp only [Set.mem_ofPred_eq, Subalgebra.coe_mul, map_mul] at *
    rw [ha σ hσ, hb σ hσ]
  add_mem' {a b} ha hb σ hσ := by
    simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, map_add] at *
    rw [ha σ hσ, hb σ hσ]
  algebraMap_mem' c σ _ := by
    change bdrAct p σ (algebraMap ℚ_[p] (BdR p) c) = algebraMap ℚ_[p] (BdR p) c
    exact bdrAct_qpToBdR p σ c

/-- `B ⊗_{ℚ_p} V → B_dR ⊗_{ℚ_p} V`. -/
def inclT (B : Subalgebra ℚ_[p] (BdR p)) :
    (B ⊗[ℚ_[p]] (Fin n → E)) →ₗ[ℚ_[p]] (BdR p ⊗[ℚ_[p]] (Fin n → E)) :=
  TensorProduct.map B.val.toLinearMap LinearMap.id

theorem inclT_smul (B : Subalgebra ℚ_[p] (BdR p)) (b : B) (x : B ⊗[ℚ_[p]] (Fin n → E)) :
    inclT p B (b • x) = (b : BdR p) • inclT p B x := by
  induction x using TensorProduct.inductionOn with
  | tmul c v =>
    rw [TensorProduct.smul_tmul', inclT, TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul']
    rfl
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem tensorAct_smul (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (b : BdR p)
    (y : BdR p ⊗[ℚ_[p]] (Fin n → E)) :
    TensorProduct.map (PanBergerSplit.bdrLin p σ) (PanBergerSplit.vAct p ρ σ) (b • y) =
      bdrAct p σ b • TensorProduct.map (PanBergerSplit.bdrLin p σ) (PanBergerSplit.vAct p ρ σ) y := by
  induction y using TensorProduct.inductionOn with
  | tmul c v =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul']
    change bdrAct p σ (b * c) ⊗ₜ _ = (bdrAct p σ b * bdrAct p σ c) ⊗ₜ _
    rw [map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **`D_B,H(V) = (B ⊗_{ℚ_p} V)^H`**, Fontaine's functor (Fontaine, Astérisque 223, Exp. III
§1; UNVERIFIED numbering), for `V = E^n` with the action `ρ`: the elements of `B ⊗ V` fixed by
`H`, the action computed in `B_dR ⊗ V`. A module over `B^H` (multiplication on `B`). -/
def dB (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule (fixedSub p B H) (B ⊗[ℚ_[p]] (Fin n → E)) where
  carrier := {x | inclT p B x ∈ PanBergerSplit.tensorInv p (PanBergerSplit.bdrLin p) H ρ}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact Submodule.zero_mem _
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact Submodule.add_mem _ hx hy
  smul_mem' e x hx := by
    simp only [Set.mem_ofPred_eq] at *
    intro σ hσ
    have h1 : inclT p B (e • x) = ((e : B) : BdR p) • inclT p B x := inclT_smul p B (e : B) x
    rw [h1, tensorAct_smul, hx σ hσ, e.2 σ hσ]

instance (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Module (fixedSub p B H) (dB p B H ρ) := Submodule.module _

instance isScalarTower_fixedSub (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) :
    IsScalarTower ℚ_[p] (fixedSub p B H) (B ⊗[ℚ_[p]] (Fin n → E)) :=
  ⟨fun c e x => by
    change ((c • e : fixedSub p B H) : B) • x = c • ((e : B) • x)
    rw [Subalgebra.coe_smul, smul_assoc]⟩

set_option synthInstance.maxHeartbeats 400000 in
instance (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Module ℚ_[p] (dB p B H ρ) := Submodule.module' _

set_option synthInstance.maxHeartbeats 400000 in
instance (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    IsScalarTower ℚ_[p] (fixedSub p B H) (dB p B H ρ) := Submodule.isScalarTower _

/-- **`V` is `B`-admissible as a representation of `H`** (Fontaine's definition):
`dim_{B^H} (B ⊗_{ℚ_p} V)^H = dim_{ℚ_p} V`. -/
def IsAdmissible (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p))
    (ρ : GQp p →* GL (Fin n) E) : Prop :=
  finrank (fixedSub p B H) (dB p B H ρ) = finrank ℚ_[p] (Fin n → E)

end Admissible

/-! ## §4. Semistable and potentially semistable over Berger's `B_st`; the two leaves -/

section Predicates

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- **`V|_{G_K}` is semistable** (Fontaine; Berger 2002 §1.2): `B_st`-admissible as a
representation of `G_K`, i.e. `dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`, with
`B_st = B_max[log [p̃]] ⊆ B_dR` (`Bst`). -/
def IsSemistableB (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (ρ : GQp p →* GL (Fin n) E) :
    Prop :=
  IsAdmissible p (Bst p) K.fixingSubgroup ρ

/-- **`V` is potentially semistable**: semistable over some finite `K/ℚ_p` inside `ℚ̄_p`. -/
def IsPstB (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ IsSemistableB p K ρ

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` is potentially semistable: it has a model over a
finite `E ⊆ ℚ̄_p` whose underlying `ℚ_p`-representation `E^n` is potentially semistable. -/
def LocalIsPstB (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsPstB p ρE

end Predicates

open PanBergerSplit in
/-- **Berger, Théorème 0.7** (L. Berger, *Représentations p-adiques et équations
différentielles*, Invent. Math. 148 (2002), 219-284; Théorème 0.7 = Corollaire 5.22 of the
published version (locator audit row R11) = Théorème 0.6 = Théorème 5.19 of
arXiv:math/0102179v3), at `K = ℚ_p`: every de Rham representation of `G_{ℚ_p}` is potentially
semistable. Applied to the `ℚ_p`-representation `V = E^n` underlying a continuous `ρ` with
values in `GL_n(E)`, `E/ℚ_p` finite inside `ℚ̄_p`, both conditions computed on `V`:

* de Rham: `dim_{ℚ_p} (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}} = dim_{ℚ_p} V` (`LocalIsDeRhamU`; `K = ℚ_p`);
* potentially semistable: for some finite `K/ℚ_p` in `ℚ̄_p`,
  `dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V` (`LocalIsPstB`), with Berger's
  `B_st = B_max[log [p̃]] ⊆ B_dR`, `B_max = B_max^+[1/t]`, `B_max^+ = A_max[1/p]`,
  `A_max = {Σ a_n (ω/p)^n : a_n ∈ A_inf, a_n → 0}` (`Bst`, `Bmax`, `BmaxPlus`, `Amax`). -/
def BergerPrintedB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
    Continuous ρ → LocalIsDeRhamU p n ρ → LocalIsPstB p n ρ

open PanBergerSplit in
/-- **Pan, Theorem 1.0.4**, as pb-fix2's `PanPrintedU` with potential semistability computed
over Berger's `B_st ⊆ B_dR` (`LocalIsPstB`) instead of pb-bypass's abstract `B_cris[X]`.
Everything else is `PanPrintedU` verbatim (eigenform reading flagged there). -/
def PanPrintedB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    ρ.IsIrreducible → ρ.FinitelyRamified → LocalIsPstB p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTU p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (S : Finset ℕ), ∀ q : ℕ, q.Prime → q ∉ S →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v q → IsArithFrob σ v q →
          (ρ.mat σ⁻¹).trace = (ψ.toHom σ⁻¹ : PadicAlgCl p) * ιp.symm (coeff g q)

open PanBergerSplit in
/-- **`PanBerger` (the research field `r11r12`) from Pan's and Berger's theorems, potential
semistability over Berger's `B_st ⊆ B_dR`**: pb-fix2's proof verbatim. -/
theorem panBerger_of_printedB (hP : PanPrintedB) (hB : BergerPrintedB)
    (hD : ZInQ.Contrib.HodgeSplit.DSThm965) (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) :
    PanBerger := by
  intro p _ hp ρ hirr hfr hdr hodd hdist
  have hdr' : LocalIsDeRhamU p 2 ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localIsDeRhamU_dualHom p _ hdr
  have hpst' := hB p 2 _ ((dualRep ρ).continuous_toHom.comp
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous) hdr'
  have hht' : LocalDistinctHTU p ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localDistinctHTU_dualHom p ρ hdist
  obtain ⟨Φ⟩ := exists_complex_equiv p
  obtain ⟨N, k, χ, g, hN, hk, hg, ψ, S, htr⟩ := hP p hp Φ.symm (dualRep ρ)
    (dualRep_isIrreducible ρ hirr) (dualRep_finitelyRamified ρ hfr) hpst'
    (dualRep_isOdd ρ hodd) hht'
  obtain ⟨Sr, hSr⟩ := hfr
  let ιC : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ιL : Qbar →ₐ[ℚ] PadicAlgCl p := (Φ : ℂ →+* PadicAlgCl p).toRatAlgHom.comp ιC
  refine ⟨N, k, χ, g, hN, hk, hg, charInv ψ, ιC, ιL, S ∪ Sr ∪ Finset.range (N * p + 1), ?_⟩
  intro q hq hqS
  simp only [Finset.mem_union, Finset.mem_range, not_or, not_lt] at hqS
  obtain ⟨⟨hqS, hqSr⟩, hqNp⟩ := hqS
  have hNp : 0 < N * p := Nat.mul_pos hN (Fact.out : p.Prime).pos
  have hqdvd : ¬ q ∣ N * p := fun h => by
    have := Nat.le_of_dvd hNp h
    omega
  refine ⟨hSr q hq hqSr, ?_⟩
  obtain ⟨α, hα⟩ := coeff_mem_range hD hDS p ιC ιL hN hk hg hq hqdvd
  refine ⟨α, hα, fun v σ hv hσ => ?_⟩
  have h1 := htr q hq hqS v σ hv hσ
  rw [trace_dualRep_inv] at h1
  rw [h1, charInv_apply]
  congr 1
  change Φ.symm.symm (coeff g q) = Φ (ιC α)
  rw [hα]
  rfl

/-- **`r11r12` from the current bundle's fields**: as `panBerger_of_printedB`, with Diamond–Shurman 9.6.5
in ds965-weak's weakest printed reading (`DS965Weak.DSThm965Weak`, the field of `OpenResearchLeaves26`). -/
theorem panBerger_of_printedB_weak (hP : PanPrintedB) (hB : BergerPrintedB)
    (hW : DS965Weak.DSThm965Weak) (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) : PanBerger :=
  panBerger_of_printedB hP hB (DS965Weak.dsThm965_of_weak hW) hDS

/-! ## §5. Sanity: the trivial representation is admissible for every `B` and `H` -/

section Trivial

variable (p : ℕ) [Fact p.Prime]

/-- `M ⊗_{ℚ_p} ℚ_p^1 ≅ M`, `m ⊗ v ↦ v₀ m`. -/
def ev1 (M : Type*) [AddCommGroup M] [Module ℚ_[p] M] : (M ⊗[ℚ_[p]] (Fin 1 → ℚ_[p])) ≃ₗ[ℚ_[p]] M :=
  (TensorProduct.congr (LinearEquiv.refl ℚ_[p] M)
    (LinearEquiv.funUnique (Fin 1) ℚ_[p] ℚ_[p])).trans (TensorProduct.rid ℚ_[p] M)

theorem ev1_tmul (M : Type*) [AddCommGroup M] [Module ℚ_[p] M] (m : M) (v : Fin 1 → ℚ_[p]) :
    ev1 p M (m ⊗ₜ v) = v 0 • m := rfl

theorem ev1_inclT (B : Subalgebra ℚ_[p] (BdR p)) (x : B ⊗[ℚ_[p]] (Fin 1 → ℚ_[p])) :
    ((ev1 p B x : B) : BdR p) = ev1 p (BdR p) (inclT p B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    rw [ev1_tmul, inclT, TensorProduct.map_tmul, ev1_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, Subalgebra.coe_add, hx, hy]

theorem ev1_act (σ : GQp p) (y : BdR p ⊗[ℚ_[p]] (Fin 1 → ℚ_[p])) :
    ev1 p (BdR p) (TensorProduct.map (PanBergerSplit.bdrLin p σ)
      (PanBergerSplit.vAct p (1 : GQp p →* GL (Fin 1) ℚ_[p]) σ) y) =
      bdrAct p σ (ev1 p (BdR p) y) := by
  induction y using TensorProduct.inductionOn with
  | tmul b v =>
    rw [TensorProduct.map_tmul, ev1_tmul, ev1_tmul, PanBergerSplit.vAct_apply]
    simp only [MonoidHom.one_apply, Units.val_one, Matrix.one_mulVec]
    rw [bdrAct_smul]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

theorem ev1_smul (B : Subalgebra ℚ_[p] (BdR p)) (c : B) (x : B ⊗[ℚ_[p]] (Fin 1 → ℚ_[p])) :
    ev1 p B (c • x) = c * ev1 p B x := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    rw [TensorProduct.smul_tmul', ev1_tmul, ev1_tmul, smul_eq_mul, mul_smul_comm]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]

/-- `D_B,H(ℚ_p) → B^H`, `x ↦ ev₁ x`. -/
def dBTrivialMap (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) :
    dB p B H (1 : GQp p →* GL (Fin 1) ℚ_[p]) →ₗ[fixedSub p B H] fixedSub p B H where
  toFun x := ⟨ev1 p B (x : B ⊗[ℚ_[p]] (Fin 1 → ℚ_[p])), fun σ hσ => by
    rw [ev1_inclT, ← ev1_act]
    exact congrArg (ev1 p (BdR p)) (x.2 σ hσ)⟩
  map_add' x y := Subtype.ext (by
    change ev1 p B ((x : B ⊗[ℚ_[p]] (Fin 1 → ℚ_[p])) + y) = ev1 p B x + ev1 p B y
    rw [map_add])
  map_smul' c x := Subtype.ext (by
    change ev1 p B ((c : B) • (x : B ⊗[ℚ_[p]] (Fin 1 → ℚ_[p]))) = (c : B) * ev1 p B x
    rw [ev1_smul])

theorem dBTrivialMap_bijective (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) :
    Function.Bijective (dBTrivialMap p B H) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply (ev1 p B).injective
    exact congrArg (fun z : fixedSub p B H => (z : B)) h
  · intro f
    refine ⟨⟨(ev1 p B).symm f, fun σ hσ => ?_⟩, ?_⟩
    · apply (ev1 p (BdR p)).injective
      rw [ev1_act, ← ev1_inclT, LinearEquiv.apply_symm_apply]
      exact f.2 σ hσ
    · apply Subtype.ext
      change ev1 p B ((ev1 p B).symm f) = f
      rw [LinearEquiv.apply_symm_apply]

/-- **Normalization check (unconditional).** The trivial one-dimensional representation is
`B`-admissible for every `ℚ_p`-subalgebra `B ⊆ B_dR` and every `H`; in particular it is
semistable over every `K` and potentially semistable for Berger's `B_st`. -/
theorem isAdmissible_trivial (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) :
    IsAdmissible p B H (1 : GQp p →* GL (Fin 1) ℚ_[p]) := by
  have : Nontrivial (BdR p) := ZInQ.Contrib.G9.BdrKer.Cp.nontrivial_BDeRham p
  rw [IsAdmissible, LinearEquiv.finrank_eq
    (LinearEquiv.ofBijective _ (dBTrivialMap_bijective p B H)), finrank_self,
    finrank_fin_fun]

theorem isPstB_trivial : IsPstB p (1 : GQp p →* GL (Fin 1) ℚ_[p]) :=
  ⟨⊥, inferInstance, isAdmissible_trivial p _ _⟩

end Trivial

/-! ## §6. The action of `G_{ℚ_p}`: `A_max`, `B_max^+` and `B_max` are stable -/

section Action

theorem adicMap_psEval {A B : Type*} [CommRing A] [CommRing B] (J : Ideal A) (J' : Ideal B)
    (g : A →+* B) (hg : J ≤ J'.comap g) {x : A} (hx : x ∈ J) (f : A⟦X⟧) :
    DR.adicMap J J' g hg (psEval J hx f) =
      psEval J' (show g x ∈ J' from hg hx) (PowerSeries.map g f) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [DR.adicMap_evalₐ, evalₐ_psEval]
  unfold DR.adicMapAux
  rw [RingHom.comp_apply]
  erw [evalₐ_psEval]
  rw [Ideal.quotientMap_mk, PowerSeries.trunc_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]

variable (p : ℕ) [Fact p.Prime]

open PanBergerSplit (Ainf AinfP locAct flatAct)

theorem evalB_congr {x y : AinfP p} (hx : x ∈ Ith p) (hxy : x = y) (f : (AinfP p)⟦X⟧) :
    evalB p hx f = evalB p (hxy ▸ hx) f := by
  subst hxy
  rfl

theorem evalB_congr' {x y : AinfP p} (hx : x ∈ Ith p) (hy : y ∈ Ith p) (hxy : x = y)
    (f : (AinfP p)⟦X⟧) : evalB p hx f = evalB p hy f := by
  subst hxy
  rfl

theorem locAct_mem (σ : GQp p) {x : AinfP p} (hx : x ∈ Ith p) : locAct p σ x ∈ Ith p :=
  DR.ker_le_comap_locMap p (oAct p σ) hx

theorem bdrAct_toBdR (σ : GQp p) (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    bdrAct p σ (toBdR p y) = toBdR p (DR.bdrPlusMap p (oAct p σ) y) := by
  rw [bdrAct, DR.bdrMap, IsLocalization.map_eq]

/-- **`σ(Σ a_k x^k) = Σ σ(a_k) σ(x)^k`** in `B_dR`. -/
theorem bdrAct_evalB (σ : GQp p) {x : AinfP p} (hx : x ∈ Ith p) (f : (AinfP p)⟦X⟧) :
    bdrAct p σ (toBdR p (evalB p hx f)) =
      toBdR p (evalB p (locAct_mem p σ hx) (PowerSeries.map (locAct p σ) f)) := by
  rw [bdrAct_toBdR]
  exact congrArg (toBdR p) (adicMap_psEval _ _ _ _ hx f)

/-- `σ` as a `ℚ_p`-algebra map of `B_dR`. -/
def bdrAlg (σ : GQp p) : BdR p →ₐ[ℚ_[p]] BdR p :=
  { bdrAct p σ with commutes' := bdrAct_qpToBdR p σ }

theorem bdrAlg_apply (σ : GQp p) (x : BdR p) : bdrAlg p σ x = bdrAct p σ x := rfl

theorem wittMap_xi_mem (σ : GQp p) :
    ∃ c : Ainf p, WittVector.map (flatAct p σ) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) =
      ZInQ.Contrib.G9.BdrKer.Cp.xi p * c := by
  have hk : WittVector.map (flatAct p σ) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ∈
      RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := by
    rw [RingHom.mem_ker, PanBergerSplit.theta_wittMap]
    have : ZInQ.Contrib.G9.BdrKer.Cp.xi p ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := by
      rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
      exact Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker.mp this, map_zero]
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  exact ⟨c, by rw [← hc, mul_comm]⟩

theorem restricted_map (g : Ainf p →+* Ainf p) {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) :
    PowerSeries.map g f ∈ restricted p := fun k => by
  obtain ⟨N, hN⟩ := hf k
  refine ⟨N, fun n hn => ?_⟩
  change (p : Ainf p) ^ k ∣ PowerSeries.coeff n (PowerSeries.map g f)
  rw [PowerSeries.coeff_map]
  have := map_dvd g (hN n hn)
  rwa [map_pow, map_natCast] at this

theorem restricted_rescale (c : Ainf p) {f : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) :
    PowerSeries.rescale c f ∈ restricted p := fun k => by
  obtain ⟨N, hN⟩ := hf k
  refine ⟨N, fun n hn => ?_⟩
  change (p : Ainf p) ^ k ∣ PowerSeries.coeff n (PowerSeries.rescale c f)
  rw [PowerSeries.coeff_rescale]
  exact Dvd.dvd.mul_left (hN n hn) _

/-- **`A_max` is `G_{ℚ_p}`-stable**: `σ(Σ a_n (ω/p)^n) = Σ σ(a_n) c^n (ω/p)^n` where
`σ(ω) = ω c`, `c ∈ A_inf` (`σ(ω) ∈ ker θ = ω A_inf`). -/
theorem bdrAct_amax (σ : GQp p) {y : BDeRhamPlus 𝓞_ℂ_[p] p} (hy : y ∈ Amax p) :
    ∃ y' ∈ Amax p, bdrAct p σ (toBdR p y) = toBdR p y' := by
  obtain ⟨f, hf, rfl⟩ := hy
  obtain ⟨c, hc⟩ := wittMap_xi_mem p σ
  refine ⟨_, ⟨PowerSeries.rescale c (PowerSeries.map (WittVector.map (flatAct p σ)) f),
    restricted_rescale p c (restricted_map p _ hf), rfl⟩, ?_⟩
  rw [RingHom.comp_apply, bdrAct_evalB]
  congr 1
  rw [RingHom.comp_apply]
  apply psEval_eq_of_terms
  intro k
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_rescale,
    PowerSeries.coeff_map, PanBergerSplit.locAct_algebraMap, omegaP, map_mul,
    PanBergerSplit.locAct_qpToLoc, ZInQ.Contrib.G9.BdrKer.Cp.xi', PanBergerSplit.locAct_algebraMap,
    hc, map_mul, map_mul, map_pow]
  ring

theorem ringInverse_bdrAct (σ : GQp p) (x : BdR p) :
    bdrAct p σ (Ring.inverse x) = Ring.inverse (bdrAct p σ x) := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    rw [Ring.inverse_unit]
    have h : bdrAct p σ (u : BdR p) = ((Units.map (bdrAct p σ : BdR p →* BdR p) u : (BdR p)ˣ) :
        BdR p) := rfl
    rw [h, Ring.inverse_unit, ← map_inv]
    rfl
  · have h0 : x = 0 := by
      by_contra hne
      obtain ⟨y, hy⟩ : ∃ y : BdR p, x * y = 1 :=
        (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).mul_inv_cancel hne
      exact hx ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
    rw [h0, Ring.inverse_zero, map_zero, Ring.inverse_zero]

theorem map_locAct_logSeries (σ : GQp p) :
    PowerSeries.map (locAct p σ) (logSeries p) = logSeries p := by
  ext n
  rw [PowerSeries.coeff_map, logSeries, PowerSeries.coeff_mk]
  split_ifs
  · exact map_zero _
  · rw [map_mul, map_pow, map_neg, map_one, PanBergerSplit.locAct_qpToLoc]

/-- `σ(log [ε]) = log [σ(ε)]`. -/
theorem bdrAct_logTeich (σ : GQp p) {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) :
    bdrAct p σ (toBdR p (logTeich p h)) =
      toBdR p (logTeich p (show PreTilt.untilt (flatAct p σ ε) = 1 by
        rw [DR.untilt_preTiltMap, h, map_one])) := by
  rw [logTeich, logPlus, bdrAct_evalB, map_locAct_logSeries]
  congr 1
  apply evalB_congr
  rw [PanBergerSplit.locAct_algebraMap, map_sub, map_one, WittVector.map_teichmuller]

theorem tInvSet_stable (σ : GQp p) {z : BdR p} (hz : z ∈ tInvSet p) :
    bdrAct p σ z ∈ tInvSet p := by
  obtain ⟨ε, h, hne, rfl⟩ := hz
  refine ⟨flatAct p σ ε, by rw [DR.untilt_preTiltMap, h, map_one], fun h1 => hne (PanBergerSplit.flatAct_injective p σ
    (by rw [h1, map_one])), ?_⟩
  rw [ringInverse_bdrAct, bdrAct_logTeich]

/-- **`B_max^+` is `G_{ℚ_p}`-stable.** -/
theorem bmaxPlus_stable (σ : GQp p) : BmaxPlus p ≤ (BmaxPlus p).comap (bdrAlg p σ) := by
  rw [BmaxPlus, Algebra.adjoin_le_iff]
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [SetLike.mem_coe, Subalgebra.mem_comap, bdrAlg_apply]
  obtain ⟨y', hy', he⟩ := bdrAct_amax p σ hy
  rw [he]
  exact Algebra.subset_adjoin ⟨y', hy', rfl⟩

/-- **`B_max` is `G_{ℚ_p}`-stable.** -/
theorem bmax_stable (σ : GQp p) : Bmax p ≤ (Bmax p).comap (bdrAlg p σ) := by
  rw [Bmax, Algebra.adjoin_le_iff]
  intro z hz
  rw [SetLike.mem_coe, Subalgebra.mem_comap, bdrAlg_apply]
  rcases hz with ⟨y, hy, rfl⟩ | hz
  · obtain ⟨y', hy', he⟩ := bdrAct_amax p σ hy
    rw [he]
    exact Algebra.subset_adjoin (Or.inl ⟨y', hy', rfl⟩)
  · exact Algebra.subset_adjoin (Or.inr (tInvSet_stable p σ hz))

end Action

/-! ## §7. `t = log [ε]` lies in `A_max` (so `B_max = B_max^+[1/t]` inverts an element of `B_max^+`) -/

section TMem

variable (p : ℕ) [hp : Fact p.Prime]

open PanBergerSplit (Ainf AinfP)

theorem exists_logCoeff (n : ℕ) (hn : n ≠ 0) :
    ∃ (e : ℤ_[p]) (v : ℕ), (e : ℚ_[p]) * n = (p : ℚ_[p]) ^ n ∧ p ^ v ≤ n ∧
      (p : ℤ_[p]) ^ (n - v) ∣ e := by
  obtain ⟨v, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)
  have hu : IsUnit (m : ℤ_[p]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm))
  have hvle : p ^ v ≤ p ^ v * m := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm0)
  have hv : v ≤ p ^ v * m := le_trans (Nat.lt_pow_self hp.out.one_lt).le hvle
  refine ⟨(p : ℤ_[p]) ^ (p ^ v * m - v) * ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), v, ?_, hvle,
    Dvd.intro _ rfl⟩
  have hum : ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (m : ℤ_[p]) = 1 := hu.val_inv_mul
  have hum' : (((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (m : ℚ_[p]) = 1 := by
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hum
    rwa [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_one] at this
  push_cast
  calc ((p : ℚ_[p]) ^ (p ^ v * m - v) * (((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) *
        ((p : ℚ_[p]) ^ v * (m : ℚ_[p]))
      = (p : ℚ_[p]) ^ (p ^ v * m - v) * (p : ℚ_[p]) ^ v *
          ((((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (m : ℚ_[p])) := by ring
    _ = (p : ℚ_[p]) ^ (p ^ v * m) := by rw [hum', mul_one, ← pow_add, Nat.sub_add_cancel hv]

theorem val_bound (k n v : ℕ) (hn : 2 * k ≤ n) (hv : p ^ v ≤ n) : k + v ≤ n := by
  by_contra h
  have h2 : 2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp.out.two_le v
  have hm : n - k + 1 ≤ v := by omega
  have h3 : 2 ^ (n - k + 1) ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hm
  have h4 : n - k < 2 ^ (n - k) := Nat.lt_two_pow_self
  rw [pow_succ] at h3
  omega

/-- `p^n/n ∈ ℤ_p` (`0` at `n = 0`). -/
def logCoeff (n : ℕ) : ℤ_[p] :=
  if hn : n = 0 then 0 else Classical.choose (exists_logCoeff p n hn)

theorem logCoeff_spec {n : ℕ} (hn : n ≠ 0) :
    (logCoeff p n : ℚ_[p]) * n = (p : ℚ_[p]) ^ n ∧ ∀ k, 2 * k ≤ n → (p : ℤ_[p]) ^ k ∣ logCoeff p n := by
  obtain ⟨v, h1, h2, h3⟩ := Classical.choose_spec (exists_logCoeff p n hn)
  rw [logCoeff, dite_eq_right hn]
  refine ⟨h1, fun k hk => dvd_trans (pow_dvd_pow _ ?_) h3⟩
  have := val_bound p k n v hk h2
  omega

/-- **`log [ε] ∈ A_max`** for `ε^♯ = 1`: with `[ε] − 1 = ω c` (`ker θ = ω A_inf`),
`log [ε] = Σ_{n ≥ 1} (−1)^{n+1} (p^n/n) c^n (ω/p)^n` and `p^n/n → 0` in `ℤ_p`. -/
theorem logTeich_mem_amax {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) :
    logTeich p h ∈ Amax p := by
  have hk : WittVector.teichmuller p ε - 1 ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) :=
    PanBergerSplit.theta_teich_sub_one p h
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  let f : (Ainf p)⟦X⟧ := PowerSeries.mk fun n =>
    if n = 0 then 0 else (-1) ^ (n + 1) * zpToW p (logCoeff p n) * c ^ n
  have hf : f ∈ restricted p := fun k => ⟨2 * k + 1, fun n hn => by
    change (p : Ainf p) ^ k ∣ PowerSeries.coeff n f
    rw [PowerSeries.coeff_mk, ite_eq_right (by omega)]
    obtain ⟨d, hd⟩ := (logCoeff_spec p (show n ≠ 0 by omega)).2 k (by omega)
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ⟨zpToW p d, ?_⟩ _) _
    rw [hd, map_mul, map_pow, map_natCast]⟩
  refine ⟨f, hf, ?_⟩
  rw [RingHom.comp_apply, logTeich, logPlus]
  apply psEval_eq_of_terms
  intro n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, logSeries, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · simp [hn]
  · rw [ite_eq_right hn, ite_eq_right hn, ← hc]
    have key : ((n : ℚ_[p]))⁻¹ = (logCoeff p n : ℚ_[p]) * ((p : ℚ_[p])⁻¹) ^ n := by
      have h1 := (logCoeff_spec p hn).1
      have hn' : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hp' : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
      have he : (logCoeff p n : ℚ_[p]) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h1
        exact pow_ne_zero _ hp' h1.symm
      rw [inv_pow, ← h1, mul_inv, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
    have hq : qpToLoc p (logCoeff p n : ℚ_[p]) = algebraMap _ _ (zpToW p (logCoeff p n)) :=
      qpToLoc_algebraMap p _
    rw [key]
    simp only [map_mul, map_pow, map_neg, map_one]
    rw [← hq, omegaP, ZInQ.Contrib.G9.BdrKer.Cp.xi']
    ring

end TMem

/-! ## §8. `log` is additive on `1 + ker θ` (Rees-algebra argument) -/

section LogAdd

variable (p : ℕ) [hp : Fact p.Prime]

open PanBergerSplit (Ainf AinfP)

theorem natCast_mul_qp (k : ℕ) (hk : k ≠ 0) : (k : AinfP p) * qpToLoc p ((k : ℚ_[p])⁻¹) = 1 := by
  rw [← map_natCast (qpToLoc p) k, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk), map_one]

/-- The truncated logarithm `P_N = Σ_{1 ≤ n < N} (−1)^{n+1} X^n/n`. -/
abbrev logPoly (N : ℕ) : Polynomial (AinfP p) := trunc N (logSeries p)

theorem derivative_logPoly (M : ℕ) :
    Polynomial.derivative (logPoly p (M + 1)) =
      ∑ i ∈ Finset.range M, Polynomial.C ((-1 : AinfP p) ^ i) * Polynomial.X ^ i := by
  ext m
  rw [Polynomial.coeff_derivative, coeff_trunc, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range M) m]
  by_cases hm : m < M
  · rw [ite_eq_left (by omega), ite_eq_left (Finset.mem_range.mpr hm), logSeries, PowerSeries.coeff_mk,
      ite_eq_right (by omega)]
    have h := natCast_mul_qp p (m + 1) (by omega)
    rw [← Nat.cast_succ]
    linear_combination (-1 : AinfP p) ^ m * h
  · rw [ite_eq_right (by omega), ite_eq_right (by simpa using hm), zero_mul]

theorem one_add_X_mul_derivative_logPoly (M : ℕ) :
    (1 + Polynomial.X) * Polynomial.derivative (logPoly p (M + 1)) = 1 - (-Polynomial.X) ^ M := by
  rw [derivative_logPoly, ← mul_neg_geom_sum, sub_neg_eq_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, map_neg, map_one, neg_pow (Polynomial.X : Polynomial (AinfP p)) i]

theorem dvd_of_one_add_X_mul {R : Type*} [CommRing R] (M : ℕ) (V F : Polynomial R)
    (h : Polynomial.X ^ M ∣ (1 + Polynomial.X * V) * F) : Polynomial.X ^ M ∣ F := by
  have hg := mul_neg_geom_sum (-(Polynomial.X * V)) M
  rw [sub_neg_eq_add] at hg
  have hF : F = ((1 + Polynomial.X * V) * F) * ∑ i ∈ Finset.range M, (-(Polynomial.X * V)) ^ i +
      F * (-(Polynomial.X * V)) ^ M := by
    linear_combination (-F) * hg
  rw [hF]
  refine dvd_add (Dvd.dvd.mul_right h _) (Dvd.dvd.mul_left ?_ _)
  rw [neg_pow, mul_pow]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right dvd_rfl _) _

theorem coeff_zero_logPoly (N : ℕ) : (logPoly p N).coeff 0 = 0 := by
  rw [coeff_trunc]
  split_ifs
  · rw [logSeries, PowerSeries.coeff_mk, ite_eq_left rfl]
  · rfl

/-- **The key polynomial identity**: with `Y = yT`, `Z = zT`, `W = Y + Z + YZ` in `A[T]`,
`T^N ∣ P_N(W) − P_N(Y) − P_N(Z)` (`A` a `ℚ`-algebra). -/
theorem X_pow_dvd_logPoly (N : ℕ) (y z : AinfP p) :
    Polynomial.X ^ N ∣
      (logPoly p N).comp (Polynomial.C y * Polynomial.X + Polynomial.C z * Polynomial.X +
          Polynomial.C y * Polynomial.X * (Polynomial.C z * Polynomial.X)) -
        (logPoly p N).comp (Polynomial.C y * Polynomial.X) -
        (logPoly p N).comp (Polynomial.C z * Polynomial.X) := by
  rcases N with _ | M
  · simp
  set Y : Polynomial (AinfP p) := Polynomial.C y * Polynomial.X
  set Z : Polynomial (AinfP p) := Polynomial.C z * Polynomial.X
  set W := Y + Z + Y * Z
  set P := logPoly p (M + 1)
  set Q := P.comp W - P.comp Y - P.comp Z
  have hP := one_add_X_mul_derivative_logPoly p M
  have hcomp : ∀ R : Polynomial (AinfP p), (1 + R) * (Polynomial.derivative P).comp R =
      1 - (-R) ^ M := fun R => by
    have := congrArg (fun F => F.comp R) hP
    simpa [Polynomial.mul_comp, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.pow_comp,
      Polynomial.neg_comp] using this
  have hDQ : Polynomial.derivative Q = Polynomial.derivative W * (Polynomial.derivative P).comp W -
      Polynomial.derivative Y * (Polynomial.derivative P).comp Y -
      Polynomial.derivative Z * (Polynomial.derivative P).comp Z := by
    simp only [Q, Polynomial.derivative_sub, Polynomial.derivative_comp]
  have hDW : Polynomial.derivative W = Polynomial.derivative Y * (1 + Z) +
      Polynomial.derivative Z * (1 + Y) := by
    simp only [W, Polynomial.derivative_add, Polynomial.derivative_mul]
    ring
  set V : Polynomial (AinfP p) := Polynomial.C y + Polynomial.C z +
    Polynomial.C y * Polynomial.C z * Polynomial.X
  have hU : (1 + Y) * (1 + Z) = 1 + Polynomial.X * V := by simp only [Y, Z, V]; ring
  have hW : W = Polynomial.X * V := by simp only [W, Y, Z, V]; ring
  have hUDQ : (1 + Polynomial.X * V) * Polynomial.derivative Q =
      -(-W) ^ M * Polynomial.derivative W + (1 + Z) * (-Y) ^ M * Polynomial.derivative Y +
        (1 + Y) * (-Z) ^ M * Polynomial.derivative Z := by
    rw [← hU, hDQ]
    have h1 := hcomp W
    have h2 := hcomp Y
    have h3 := hcomp Z
    have hW1 : 1 + W = (1 + Y) * (1 + Z) := by simp only [W]; ring
    rw [hW1] at h1
    linear_combination (Polynomial.derivative W) * h1 - (1 + Z) * Polynomial.derivative Y * h2 -
      (1 + Y) * Polynomial.derivative Z * h3 + hDW
  have hdvd : Polynomial.X ^ M ∣ Polynomial.derivative Q := by
    apply dvd_of_one_add_X_mul M V
    have hXW : Polynomial.X ∣ -W := by rw [hW]; exact (dvd_mul_right _ _).neg_right
    have hXY : Polynomial.X ∣ -Y := (dvd_mul_left _ _).neg_right
    have hXZ : Polynomial.X ∣ -Z := (dvd_mul_left _ _).neg_right
    rw [hUDQ]
    refine dvd_add (dvd_add ?_ ?_) ?_
    · exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hXW M).neg_right _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hXY M) _) _
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hXZ M) _) _
  rw [Polynomial.X_pow_dvd_iff] at hdvd ⊢
  intro d hd
  rcases d with _ | e
  · rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_comp, W, Y, Z, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero, add_zero,
      ← Polynomial.coeff_zero_eq_eval_zero, P, coeff_zero_logPoly, sub_zero]
  · have h := hdvd e (by omega)
    rw [Polynomial.coeff_derivative] at h
    have hu := natCast_mul_qp p (e + 1) (by omega)
    push_cast at hu
    calc Q.coeff (e + 1) = Q.coeff (e + 1) * (((e : AinfP p) + 1) * qpToLoc p ((e + 1 : ℚ_[p]))⁻¹) := by
          rw [hu, mul_one]
      _ = (Q.coeff (e + 1) * ((e : AinfP p) + 1)) * qpToLoc p ((e + 1 : ℚ_[p]))⁻¹ := by ring
      _ = 0 := by rw [h, zero_mul]

theorem eval_one_mem_of_rees {R : Type*} [CommRing R] (I : Ideal R) (N : ℕ) (Q : Polynomial R)
    (hQ : Q ∈ reesAlgebra I) (hN : Polynomial.X ^ N ∣ Q) : Q.eval 1 ∈ I ^ N := by
  rw [Polynomial.eval_eq_sum_range]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [one_pow, mul_one]
  by_cases hk : k < N
  · rw [(Polynomial.X_pow_dvd_iff.mp hN) k hk]
    exact Ideal.zero_mem _
  · exact Ideal.pow_le_pow_right (by omega) ((mem_reesAlgebra_iff I Q).mp hQ k)

theorem C_mul_X_mem_rees {R : Type*} [CommRing R] (I : Ideal R) {y : R} (hy : y ∈ I) :
    Polynomial.C y * Polynomial.X ∈ reesAlgebra I := by
  rw [mem_reesAlgebra_iff]
  intro i
  rw [Polynomial.coeff_C_mul_X]
  split_ifs with h
  · subst h; rwa [pow_one]
  · exact Ideal.zero_mem _

theorem comp_mem_rees {R : Type*} [CommRing R] (I : Ideal R) (P : Polynomial R) {W : Polynomial R}
    (hW : W ∈ reesAlgebra I) : P.comp W ∈ reesAlgebra I := by
  rw [Polynomial.comp_eq_aeval]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hW)
    (Polynomial.aeval_mem_adjoin_singleton _ _)

/-- **`log((1+y)(1+z)) = log(1+y) + log(1+z)`** in `B_dR^+`, for `y, z ∈ ker θ`. -/
theorem logPlus_add {y z : AinfP p} (hy : y ∈ Ith p) (hz : z ∈ Ith p) :
    logPlus p (show y + z + y * z ∈ Ith p from
      Ideal.add_mem _ (Ideal.add_mem _ hy hz) (Ideal.mul_mem_right _ _ hy)) =
      logPlus p hy + logPlus p hz := by
  show psEval (Ith p) _ (logSeries p) =
    psEval (Ith p) hy (logSeries p) + psEval (Ith p) hz (logSeries p)
  refine AdicCompletion.ext_evalₐ fun N => ?_
  rw [map_add, evalₐ_psEval, evalₐ_psEval, evalₐ_psEval, ← map_add, Ideal.Quotient.eq]
  have hY := C_mul_X_mem_rees (Ith p) hy
  have hZ := C_mul_X_mem_rees (Ith p) hz
  have hW : Polynomial.C y * Polynomial.X + Polynomial.C z * Polynomial.X +
      Polynomial.C y * Polynomial.X * (Polynomial.C z * Polynomial.X) ∈ reesAlgebra (Ith p) :=
    Subalgebra.add_mem _ (Subalgebra.add_mem _ hY hZ) (Subalgebra.mul_mem _ hY hZ)
  have hQ := eval_one_mem_of_rees (Ith p) N _
    (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (comp_mem_rees _ _ hW) (comp_mem_rees _ _ hY))
      (comp_mem_rees _ _ hZ)) (X_pow_dvd_logPoly p N y z)
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, mul_one] at hQ
  convert hQ using 1
  ring

end LogAdd

/-! ## §9. `σ(log [p̃]) = log [p̃] + log [u_σ]`: `B_st` is `G_{ℚ_p}`-stable -/

section BstStable

variable (p : ℕ) [hp : Fact p.Prime]

open PanBergerSplit (Ainf AinfP locAct flatAct)

/-- `σ(p̃) = p̃ · u` with `u^♯ = 1` (`u = σ(p̃)/p̃`, the Kummer cocycle of `p` at `σ`). -/
theorem exists_uSigma (σ : GQp p) :
    ∃ u : PreTilt 𝓞_ℂ_[p] p, flatAct p σ (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) = (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) * u ∧ PreTilt.untilt u = 1 := by
  have hσp : PreTilt.untilt (flatAct p σ (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p)) = (p : 𝓞_ℂ_[p]) := by
    rw [DR.untilt_preTiltMap, ZInQ.Contrib.G9.BdrKer.Cp.untilt_pFlat, map_natCast]
  obtain ⟨u, hu⟩ := ZInQ.Contrib.G9.BdrKer.Cp.dvd_of_coeff_zero p (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p)
    (ZInQ.Contrib.G9.BdrKer.Cp.untilt_pFlat p) (flatAct p σ (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p)) (by
      rw [← PreTilt.mk_untilt_eq_coeff_zero, hσp]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))
  refine ⟨u, hu, ?_⟩
  have h1 : (p : 𝓞_ℂ_[p]) * (PreTilt.untilt u - 1) = 0 := by
    have := congrArg PreTilt.untilt hu
    rw [hσp, map_mul, ZInQ.Contrib.G9.BdrKer.Cp.untilt_pFlat] at this
    linear_combination -this
  exact sub_eq_zero.mp (ZInQ.Contrib.G9.BdrKer.Cp.p_regular p _ h1)

theorem locAct_pTildeArg (σ : GQp p) {u : PreTilt 𝓞_ℂ_[p] p} (hu : flatAct p σ (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) = (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) * u) :
    locAct p σ (pTildeArg p) =
      algebraMap (Ainf p) (AinfP p) (WittVector.teichmuller p u - 1) + pTildeArg p +
        algebraMap (Ainf p) (AinfP p) (WittVector.teichmuller p u - 1) * pTildeArg p := by
  have hq := natCast_mul_qp p p hp.out.ne_zero
  simp only [pTildeArg, omegaP, map_neg, map_mul, PanBergerSplit.locAct_qpToLoc,
    ZInQ.Contrib.G9.BdrKer.Cp.xi', PanBergerSplit.locAct_algebraMap, ZInQ.Contrib.G9.BdrKer.Cp.xi,
    map_sub, map_natCast, WittVector.map_teichmuller, hu, map_one]
  linear_combination
    (algebraMap (Ainf p) (AinfP p) (WittVector.teichmuller p u) - 1) * hq

theorem logPTilde_eq : logPTilde p = evalB p (pTildeArg_mem p) (logSeries p) := rfl

theorem logTeich_eq {u : PreTilt 𝓞_ℂ_[p] p} (hu1 : PreTilt.untilt u = 1) :
    logTeich p hu1 = evalB p (teich_sub_one_mem p hu1) (logSeries p) := rfl

theorem logPTilde_step_B (σ : GQp p) :
    bdrAct p σ (toBdR p (logPTilde p)) =
      toBdR p (evalB p (locAct_mem p σ (pTildeArg_mem p)) (logSeries p)) := by
  have h := bdrAct_evalB p σ (pTildeArg_mem p) (logSeries p)
  rw [map_locAct_logSeries] at h
  rw [logPTilde_eq]
  exact h

theorem logPTilde_step_A (σ : GQp p) {u : PreTilt 𝓞_ℂ_[p] p} (hu : flatAct p σ (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) = (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) * u)
    (hu1 : PreTilt.untilt u = 1) :
    evalB p (locAct_mem p σ (pTildeArg_mem p)) (logSeries p) = logTeich p hu1 + logPTilde p := by
  exact (evalB_congr' p _ _ (locAct_pTildeArg p σ hu) _).trans
    (logPlus_add p (teich_sub_one_mem p hu1) (pTildeArg_mem p))

/-- **`σ(log [p̃]) = log [p̃] + log [u_σ]`** in `B_dR` (`log [u_σ] = c(σ)·t`). -/
theorem bdrAct_logPTilde (σ : GQp p) {u : PreTilt 𝓞_ℂ_[p] p} (hu : flatAct p σ (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) = (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) * u)
    (hu1 : PreTilt.untilt u = 1) :
    bdrAct p σ (toBdR p (logPTilde p)) = toBdR p (logTeich p hu1) + toBdR p (logPTilde p) := by
  rw [logPTilde_step_B, logPTilde_step_A p σ hu hu1, map_add]

/-- **`B_st` is `G_{ℚ_p}`-stable.** -/
theorem bst_stable (σ : GQp p) : Bst p ≤ (Bst p).comap (bdrAlg p σ) := by
  rw [Bst, Algebra.adjoin_le_iff]
  intro z hz
  rw [SetLike.mem_coe, Subalgebra.mem_comap, bdrAlg_apply]
  rcases hz with (⟨y, hy, rfl⟩ | hz) | hz
  · obtain ⟨y', hy', he⟩ := bdrAct_amax p σ hy
    rw [he]
    exact Algebra.subset_adjoin (Or.inl (Or.inl ⟨y', hy', rfl⟩))
  · exact Algebra.subset_adjoin (Or.inl (Or.inr (tInvSet_stable p σ hz)))
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]
    obtain ⟨u, hu, hu1⟩ := exists_uSigma p σ
    rw [bdrAct_logPTilde p σ hu hu1]
    exact Subalgebra.add_mem _ (Algebra.subset_adjoin (Or.inl (Or.inl
      ⟨_, logTeich_mem_amax p hu1, rfl⟩))) (logPTilde_mem_bst p)

end BstStable

/-! ## §10. Transcendence of `log [p̃]` (named input) and `B_st ≅ B_max[X]` -/

section Transcendence

variable (p : ℕ) [Fact p.Prime]

/-- `B_dR^+ → B_dR` is injective (`B_dR` is the fraction field of the domain `B_dR^+`). -/
theorem toBdR_injective : Function.Injective (toBdR p) := by
  have := ZInQ.Contrib.G9.BdrKer.Cp.isFractionRing_BDeRham p
  exact IsFractionRing.injective (BDeRhamPlus 𝓞_ℂ_[p] p) (ZInQ.Contrib.G9.BdrKer.BdR 𝓞_ℂ_[p] p)

/-- **Fontaine: `log [p̃]` is transcendental over `B_max`** (Fontaine, *Le corps des périodes
p-adiques*, Astérisque 223 (1994), Exp. II §3 for `B_cris`; Colmez for `B_max`; Berger 2002 §1.2
uses it to write `B_st = B_max[log [p̃]]`; numbering UNVERIFIED). Stated over this file's genuine
`B_max ⊆ B_dR` and `log [p̃] ∈ B_dR^+`. Not used by `panBerger_of_printedB`. -/
def LogPTildeTranscendental : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Transcendental (Bmax p) (toBdR p (logPTilde p))

/-- Equivalently, `B_max[X] → B_dR`, `X ↦ log [p̃]`, is injective. -/
theorem logPTildeTranscendental_iff :
    LogPTildeTranscendental ↔ ∀ (p : ℕ) [Fact p.Prime],
      Function.Injective (Polynomial.aeval (R := Bmax p) (toBdR p (logPTilde p))) :=
  ⟨fun h p _ => transcendental_iff_injective.mp (h p),
    fun h p _ => transcendental_iff_injective.mpr (h p)⟩

/-- **Given the transcendence, `B_st` is the polynomial ring `B_max[X]`** (`X ↦ log [p̃]`). -/
def bstEquivPolynomial (h : LogPTildeTranscendental) :
    Polynomial (Bmax p) ≃ₐ[Bmax p] Algebra.adjoin (Bmax p) {toBdR p (logPTilde p)} :=
  (AlgEquiv.ofInjective _ (transcendental_iff_injective.mp (h p))).trans
    (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval _ _).symm)

theorem bstEquivPolynomial_X (h : LogPTildeTranscendental) :
    ((bstEquivPolynomial p h Polynomial.X : Algebra.adjoin (Bmax p) {toBdR p (logPTilde p)}) :
      BdR p) = toBdR p (logPTilde p) := by
  simp [bstEquivPolynomial]

end Transcendence

/-! ## §11. Fontaine's `B_st^{G_K} = K_0` (named input) and the `ℚ_p`-dimension normalization -/

section Normalization

variable (p : ℕ) [Fact p.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- **Fontaine: `B_st^{G_K} = K_0`, in dimension form**, for Berger's `B_st ⊆ B_dR`:
`dim_{ℚ_p} B_st^{G_K} = [K_0 : ℚ_p]` with `K_0 = W(k_K)[1/p]` (pb-fix2's `K0W`). (Fontaine,
Astérisque 223 (1994), Exp. II §§4-5 / Exp. III §1, numbering UNVERIFIED.) Used only to compare
the admissibility definition with pb-fix2's normalization; not used by `panBerger_of_printedB`. -/
def FontaineBstInvariants : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K →
    finrank ℚ_[p] (fixedSub p (Bst p) K.fixingSubgroup) = finrank ℚ_[p] (PanBergerSplit.K0W p K)

set_option synthInstance.maxHeartbeats 400000 in
theorem isField_fixedSub (H : Subgroup (GQp p)) (hfin : 0 < finrank ℚ_[p] (fixedSub p (Bst p) H)) :
    IsField (fixedSub p (Bst p) H) := by
  have : IsDomain (BdR p) := (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).isDomain
  have : Module.Free ℚ_[p] (fixedSub p (Bst p) H) := Module.Free.of_divisionRing ℚ_[p] (fixedSub p (Bst p) H)
  have : Module.Finite ℚ_[p] (fixedSub p (Bst p) H) := Module.finite_of_finrank_pos hfin
  have : Algebra.IsIntegral ℚ_[p] (fixedSub p (Bst p) H) := Algebra.IsIntegral.of_finite _ _
  exact isField_of_isIntegral_of_isField' (R := ℚ_[p]) (S := fixedSub p (Bst p) H)
    (Field.toIsField ℚ_[p])

omit [FiniteDimensional ℚ_[p] E] in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The admissibility definition in `ℚ_p`-dimensions.** If `B_st^{G_K}` is finite-dimensional
over `ℚ_p` and nonzero-dimensional, semistability over `K` (`dim_{B_st^{G_K}} D_st,K(V) = dim V`)
is `dim_{ℚ_p} D_st,K(V) = dim_{ℚ_p} B_st^{G_K} · dim_{ℚ_p} V`. -/
theorem isSemistableB_iff_finrank (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (ρ : GQp p →* GL (Fin n) E)
    (hfin : 0 < finrank ℚ_[p] (fixedSub p (Bst p) K.fixingSubgroup)) :
    IsSemistableB p K ρ ↔
      finrank ℚ_[p] (dB p (Bst p) K.fixingSubgroup ρ) =
        finrank ℚ_[p] (fixedSub p (Bst p) K.fixingSubgroup) * finrank ℚ_[p] (Fin n → E) := by
  have : Module.Free ℚ_[p] (fixedSub p (Bst p) K.fixingSubgroup) :=
    Module.Free.of_divisionRing ℚ_[p] (fixedSub p (Bst p) K.fixingSubgroup)
  let hM : Module (fixedSub p (Bst p) K.fixingSubgroup) (dB p (Bst p) K.fixingSubgroup ρ) :=
    inferInstance
  have : Nontrivial (fixedSub p (Bst p) K.fixingSubgroup) :=
    ⟨(isField_fixedSub p _ hfin).exists_pair_ne⟩
  have : StrongRankCondition (fixedSub p (Bst p) K.fixingSubgroup) :=
    by exact commRing_strongRankCondition (fixedSub p (Bst p) K.fixingSubgroup)
  have hT : IsScalarTower ℚ_[p] (fixedSub p (Bst p) K.fixingSubgroup)
      (dB p (Bst p) K.fixingSubgroup ρ) := Submodule.isScalarTower _
  let hA0 : AddCommGroup ((dB p (Bst p) K.fixingSubgroup ρ).restrictScalars ℚ_[p]) :=
    @Submodule.addCommGroup ℚ_[p] (↥(Bst p) ⊗[ℚ_[p]] (Fin n → E)) _ inferInstance _ _
  let hA : AddCommGroup (dB p (Bst p) K.fixingSubgroup ρ) := hA0
  have : Module.Free (fixedSub p (Bst p) K.fixingSubgroup) (dB p (Bst p) K.fixingSubgroup ρ) := by
    let F : Field (fixedSub p (Bst p) K.fixingSubgroup) := (isField_fixedSub p _ hfin).toField
    exact @Module.Free.of_divisionRing _ _ F.toDivisionRing hA hM
  rw [IsSemistableB, IsAdmissible, ← Module.finrank_mul_finrank ℚ_[p]
    (fixedSub p (Bst p) K.fixingSubgroup) (dB p (Bst p) K.fixingSubgroup ρ)]
  exact ⟨fun h => by rw [h], fun h => Nat.eq_of_mul_eq_mul_left hfin h⟩

omit [FiniteDimensional ℚ_[p] E] in
/-- **Given Fontaine's `B_st^{G_K} = K_0`, semistability by admissibility is pb-fix2's
normalization** `dim_{ℚ_p} D_st,K(V) = [K_0 : ℚ_p] · dim_{ℚ_p} V` (now over Berger's `B_st`). -/
theorem isSemistableB_iff_K0 (hF : FontaineBstInvariants) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (ρ : GQp p →* GL (Fin n) E) :
    IsSemistableB p K ρ ↔
      finrank ℚ_[p] (dB p (Bst p) K.fixingSubgroup ρ) =
        finrank ℚ_[p] (PanBergerSplit.K0W p K) * finrank ℚ_[p] (Fin n → E) := by
  have h := hF p K inferInstance
  rw [isSemistableB_iff_finrank p K ρ (by rw [h]; exact PanBergerSplit.finrank_K0W_pos p K), h]

end Normalization

/-! ## §12. `A_max` does not depend on the generator `ω` of `ker θ` -/

section Generator

variable (p : ℕ) [Fact p.Prime]

open PanBergerSplit (Ainf AinfP)

theorem alg_mem_of_theta {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    algebraMap (Ainf p) (AinfP p) w * qpToLoc p ((p : ℚ_[p])⁻¹) ∈ Ith p := by
  have hk : w ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := hw
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, rfl⟩ := hk
  rw [map_mul, mul_comm (algebraMap _ _ c), mul_assoc]
  exact Ideal.mul_mem_right _ _ (xi'_mem p)

/-- `A_max` built with an arbitrary `ω ∈ ker θ`: `{Σ a_n (ω/p)^n : a_n ∈ A_inf, a_n → 0}`. -/
def AmaxOf (w : Ainf p) (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    Subring (BDeRhamPlus 𝓞_ℂ_[p] p) :=
  (restricted p).map ((evalB p (alg_mem_of_theta p hw)).comp
    (PowerSeries.map (algebraMap (Ainf p) (AinfP p))))

theorem amaxOf_le {w w' : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hw' : WittVector.fontaineTheta 𝓞_ℂ_[p] p w' = 0) (c : Ainf p) (hc : w' = w * c) :
    AmaxOf p w' hw' ≤ AmaxOf p w hw := by
  rintro _ ⟨f, hf, rfl⟩
  refine ⟨PowerSeries.rescale c f, restricted_rescale p c hf, ?_⟩
  simp only [RingHom.comp_apply]
  apply psEval_eq_of_terms
  intro k
  rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, PowerSeries.coeff_map, hc, map_mul, map_mul,
    map_pow]
  ring

/-- **`A_max` is the same for every generator `ω` of `ker(θ : A_inf → 𝓞_ℂ_p)`** (e.g. Fontaine's
`[p̃] − p` or `ξ = p − [p̃]`). -/
theorem amaxOf_eq_amax {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w}) :
    AmaxOf p w hw = Amax p := by
  have hxi : WittVector.fontaineTheta 𝓞_ℂ_[p] p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = 0 := by
    have : ZInQ.Contrib.G9.BdrKer.Cp.xi p ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := by
      rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
      exact Ideal.mem_span_singleton_self _
    exact this
  have hA : Amax p = AmaxOf p _ hxi := rfl
  rw [hA]
  apply le_antisymm
  · have : w ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := hw
    rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact amaxOf_le p hxi hw c (by rw [← hc, mul_comm])
  · have : ZInQ.Contrib.G9.BdrKer.Cp.xi p ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := hxi
    rw [hgen, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact amaxOf_le p hw hxi c (by rw [← hc, mul_comm])

end Generator

/-! ## §13. `t ≠ 0`: `log [ε] ≠ 0` in `B_dR` for every `ε ≠ 1`, and such `ε` exist

The separatedness lemmas and the construction of `ε = (1, ζ_p, ζ_{p²}, …)` below are copied from
pb-sanity (`ZInQKernel/Contrib/OneProof/PanBergerSanity.lean`, which cannot be imported next to
`PanBergerPrinted`: both chains define the bdr-kertheta constants). -/

section TNonzero

variable (p : ℕ) [Fact p.Prime]

open Ideal
open PanBergerSplit (Ainf AinfP theta)

/-- `ε ∈ 𝓞_ℂ_p♭` with `ε^♯ = 1`, `ε ≠ 1` (pb-sanity's `TEps`). -/
abbrev TEps := {ε : PreTilt 𝓞_ℂ_[p] p // PreTilt.untilt ε = 1 ∧ ε ≠ 1}

/-- An element of `𝓞_ℂ_p♭` divisible by every power of `p♭` is zero. -/
theorem tilt_eq_zero_of_dvd (ϖ : PreTilt 𝓞_ℂ_[p] p) (hϖ : ϖ.untilt = p) (c : PreTilt 𝓞_ℂ_[p] p)
    (h : ∀ n, ϖ ^ n ∣ c) : c = 0 := by
  have h0 : c.untilt = 0 := by
    apply IsHausdorff.haus' (I := span {(p : 𝓞_ℂ_[p])})
    intro n
    obtain ⟨d, rfl⟩ := h n
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, map_mul, map_pow, hϖ]
    exact dvd_mul_right _ _
  apply Perfection.ext
  intro n
  change PreTilt.coeff n c = PreTilt.coeff n 0
  rw [← ZInQ.Contrib.G9.BdrKer.Cp.mk_root, map_zero]
  have : ZInQ.Contrib.G9.BdrKer.Cp.root c n ^ p ^ n = 0 := by
    rw [ZInQ.Contrib.G9.BdrKer.Cp.root_pow, h0]
  rw [pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at this
  rw [this, map_zero]

/-- `p` is regular modulo `ξ^n` in `A_inf`. -/
theorem mem_xi_pow_of_p_mul (n : ℕ) : ∀ a : Ainf p,
    (p : Ainf p) * a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} → a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} := by
  induction n with
  | zero => intro a _; rw [pow_zero, Ideal.span_singleton_one]; trivial
  | succ n ih =>
    intro a ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    have hθ : theta p a = 0 := by
      apply ZInQ.Contrib.G9.BdrKer.Cp.p_regular p
      have := congrArg (theta p) hc
      rw [map_mul, map_mul, map_pow, map_natCast] at this
      rw [← this]
      have hx : theta p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = 0 := by
        rw [← RingHom.mem_ker]
        change (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p)
        rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
        exact Ideal.mem_span_singleton_self _
      rw [hx, zero_pow (Nat.succ_ne_zero n), mul_zero]
    have ha' : a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p)} := by
      rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
      exact hθ
    obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.mp ha'
    have hξ : (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ≠ 0 := ZInQ.Contrib.G9.BdrKer.Cp.xi_ne_zero p
    have h2 : (p : Ainf p) * a' = c * (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n := by
      apply mul_left_cancel₀ hξ
      linear_combination hc.symm
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (ih a' (Ideal.mem_span_singleton'.mpr ⟨c, h2.symm⟩))
    exact Ideal.mem_span_singleton'.mpr ⟨d, by rw [← hd, pow_succ]; ring⟩

theorem mem_xi_pow_of_p_pow_mul (n e : ℕ) (a : Ainf p)
    (h : (p : Ainf p) ^ e * a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n}) : a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} := by
  induction e generalizing a with
  | zero => simpa using h
  | succ e ih =>
    apply ih
    apply mem_xi_pow_of_p_mul
    rw [pow_succ] at h
    simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- `A_inf` is `ξ`-adically separated on non-zero elements. -/
theorem exists_not_mem_xi_pow (x : Ainf p) (hx : x ≠ 0) : ∃ n, x ∉ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} := by
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x hx
  by_contra hcon
  push Not at hcon
  apply hb
  have hb' : ∀ n, b ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ n} := fun n => mem_xi_pow_of_p_pow_mul p n m b (hcon n)
  have h0 : WittVector.constantCoeff (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = -(ZInQ.Contrib.G9.BdrKer.Cp.pFlat p) := by
    rw [ZInQ.Contrib.G9.BdrKer.Cp.xi, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
    simp
  apply tilt_eq_zero_of_dvd p (ZInQ.Contrib.G9.BdrKer.Cp.pFlat p)
    (ZInQ.Contrib.G9.BdrKer.Cp.untilt_pFlat p)
  intro n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hb' n)
  have := congrArg WittVector.constantCoeff hc
  rw [map_mul, map_pow, h0] at this
  refine ⟨(-1) ^ n * WittVector.constantCoeff c, ?_⟩
  change b.coeff 0 = _
  rw [← WittVector.constantCoeff_apply, ← this, neg_pow]
  ring

/-- Every non-zero `x ∈ A_inf` is `ξ^s · w` with `θ(w) ≠ 0`. -/
theorem eq_xi_pow_mul (x : Ainf p) (hx : x ≠ 0) :
    ∃ (s : ℕ) (w : Ainf p), x = (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ s * w ∧ theta p w ≠ 0 := by
  classical
  have hex := exists_not_mem_xi_pow p x hx
  let N := Nat.find hex
  have hN : x ∉ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ N} := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h0; apply hN; rw [h0, pow_zero, Ideal.span_singleton_one]; trivial
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hxM : x ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ M} := by
    have := Nat.find_min hex (show M < N by omega)
    push Not at this
    exact this
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hxM
  refine ⟨M, w, by rw [← hw, mul_comm], fun hθ => hN ?_⟩
  have : w ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p)} := by
    rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]; exact hθ
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp this
  rw [hM, ← hw]
  exact Ideal.mem_span_singleton'.mpr ⟨c, by rw [Nat.succ_eq_add_one, pow_succ]; ring⟩

theorem teich_sub_one_ne_zero {ε : PreTilt 𝓞_ℂ_[p] p} (hne : ε ≠ 1) :
    WittVector.teichmuller p ε - 1 ≠ 0 := by
  intro h
  apply hne
  have h1 : WittVector.teichmuller p ε = 1 := sub_eq_zero.mp h
  have := congrArg (fun w => WittVector.coeff w 0) h1
  simpa [WittVector.teichmuller_coeff_zero] using this

/-- `ι(a) ∈ ξ^k A_inf[1/p]` implies `a ∈ ξ^k A_inf`. -/
theorem mem_xi_pow_of_algebraMap (k : ℕ) (a : Ainf p)
    (h : algebraMap (Ainf p) (AinfP p) a ∈ span {algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ k}) :
    a ∈ span {(ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ k} := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : Ainf p)) y
  obtain ⟨e, he⟩ := s.2
  apply mem_xi_pow_of_p_pow_mul p k e
  have hinj := IsLocalization.injective (AinfP p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (ZInQ.Contrib.G9.BdrKer.Cp.witt_p_ne_zero p))
  have : (p : Ainf p) ^ e * a = b * (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ k := by
    apply hinj
    have hs := IsLocalization.mk'_spec (AinfP p) b s
    simp only at he
    dsimp only at hy
    rw [map_mul, map_mul, map_pow, ← hy, ← hs, ← he]
    simp only [map_pow]
    ring
  exact Ideal.mem_span_singleton'.mpr ⟨b, this.symm⟩


open ZInQ.Contrib.G9.BdrKer.Cp in
/-- If the components of `x ∈ 𝓞_ℂ_p♭` are the classes of a compatible system `c` of `p`-th
power roots, then `x^♯ = c 0`. -/
theorem untilt_eq_of_coeff (c : ℕ → 𝓞_ℂ_[p]) (hc : ∀ m, c (m + 1) ^ p = c m) (x : PreTilt 𝓞_ℂ_[p] p)
    (hx : ∀ m, PreTilt.coeff m x = Ideal.Quotient.mk _ (c m)) : x.untilt = c 0 := by
  have hpow : ∀ k, c k ^ p ^ k = c 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hc, ih]
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : 𝓞_ℂ_[p])})]
  intro n
  rw [SModEq.sub_mem, ZInQ.Contrib.G9.BdrKer.mem_span_pow_iff']
  have h1 : root x n - c n ∈ span {(p : 𝓞_ℂ_[p])} := by
    rw [← Ideal.Quotient.eq, mk_root, hx]
  have h2 := dvd_sub_pow_of_dvd_sub (Ideal.mem_span_singleton.mp h1) n
  rw [root_pow, hpow] at h2
  obtain ⟨d, hd⟩ := h2
  exact ⟨p * d, by rw [hd]; ring⟩

open ZInQ.Contrib.G9.BdrKer.Cp in
theorem root_eq_of_coeff (c : ℕ → 𝓞_ℂ_[p]) (hc : ∀ m, c (m + 1) ^ p = c m) (x : PreTilt 𝓞_ℂ_[p] p)
    (hx : ∀ m, PreTilt.coeff m x = Ideal.Quotient.mk _ (c m)) (n : ℕ) : root x n = c n := by
  have := untilt_eq_of_coeff p (fun m => c (m + n)) (fun m => by
    simpa [Nat.add_right_comm] using hc (m + n)) (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) x)
    (fun m => by rw [PreTilt.coeff_iterate_frobeniusEquiv_symm, hx])
  simpa [ZInQ.Contrib.G9.BdrKer.Cp.root] using this

/-- A compatible system `1, ζ_p, ζ_{p²}, …` of `p`-power roots of unity in `ℂ_p`. -/
noncomputable def zetaSeq (ζ : ℂ_[p]) : ℕ → ℂ_[p]
  | 0 => 1
  | 1 => ζ
  | n + 2 => Classical.choose (IsAlgClosed.exists_pow_nat_eq (zetaSeq ζ (n + 1))
      (Fact.out : p.Prime).pos)

theorem zetaSeq_succ_pow (ζ : ℂ_[p]) (hζ : ζ ^ p = 1) (n : ℕ) :
    zetaSeq p ζ (n + 1) ^ p = zetaSeq p ζ n := by
  rcases n with _ | n
  · simpa [zetaSeq] using hζ
  · exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (zetaSeq p ζ (n + 1))
      (Fact.out : p.Prime).pos)

theorem zetaSeq_pow (ζ : ℂ_[p]) (hζ : ζ ^ p = 1) (n : ℕ) : zetaSeq p ζ n ^ p ^ n = 1 := by
  induction n with
  | zero => simp [zetaSeq]
  | succ n ih => rw [pow_succ', pow_mul, zetaSeq_succ_pow p ζ hζ, ih]

theorem norm_zetaSeq_le (ζ : ℂ_[p]) (hζ : ζ ^ p = 1) (n : ℕ) : ‖zetaSeq p ζ n‖ ≤ 1 := by
  have h := congrArg norm (zetaSeq_pow p ζ hζ n)
  rw [norm_pow, norm_one] at h
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _
    (Fact.out : p.Prime).ne_zero)).mp h).le

/-- **There is `ε ∈ 𝓞_ℂ_p♭` with `ε^♯ = 1` and `ε ≠ 1`**: `ε = (1, ζ_p, ζ_{p²}, …)`. -/
theorem nonempty_tEps : Nonempty (TEps p) := by
  have hdeg : (Polynomial.cyclotomic p ℂ_[p]).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic, Nat.totient_prime (Fact.out : p.Prime)]
    have := (Fact.out : p.Prime).two_le
    exact_mod_cast (show p - 1 ≠ 0 by omega)
  obtain ⟨ζ, hroot⟩ := IsAlgClosed.exists_root _ hdeg
  have hprim : IsPrimitiveRoot ζ p :=
    (Polynomial.isRoot_cyclotomic_iff_charZero (Fact.out : p.Prime).pos).mp hroot
  have hζ : ζ ^ p = 1 := hprim.pow_eq_one
  have hζ1 : ζ ≠ 1 := hprim.ne_one (Fact.out : p.Prime).one_lt
  let c : ℕ → 𝓞_ℂ_[p] := fun n => ⟨zetaSeq p ζ n,
    (ZInQ.Contrib.G9.PkgI4.Cp.mem_O_iff p _).mpr (norm_zetaSeq_le p ζ hζ n)⟩
  have hc : ∀ m, c (m + 1) ^ p = c m := fun m =>
    Subtype.ext (by simpa [c] using zetaSeq_succ_pow p ζ hζ m)
  let ε : PreTilt 𝓞_ℂ_[p] p := ⟨fun n => Ideal.Quotient.mk _ (c n), fun n => by
    rw [← map_pow, hc]⟩
  have hx : ∀ m, PreTilt.coeff m ε = Ideal.Quotient.mk _ (c m) := fun m => rfl
  refine ⟨⟨ε, ?_, ?_⟩⟩
  · rw [untilt_eq_of_coeff p c hc ε hx]
    exact Subtype.ext (by simp [c, zetaSeq])
  · intro h1
    have h2 := root_eq_of_coeff p c hc ε hx 1
    rw [h1] at h2
    apply hζ1
    have h3 : ZInQ.Contrib.G9.BdrKer.Cp.root (1 : PreTilt 𝓞_ℂ_[p] p) 1 = 1 := by
      simp [ZInQ.Contrib.G9.BdrKer.Cp.root]
    rw [h3] at h2
    have := congrArg Subtype.val h2
    simpa [c, zetaSeq] using this.symm


theorem trunc_logSeries_sub_X (N : ℕ) :
    ∃ R : Polynomial (AinfP p), (trunc (N + 2) (logSeries p)) - Polynomial.X =
      Polynomial.X ^ 2 * R := by
  show (Polynomial.X : Polynomial (AinfP p)) ^ 2 ∣ (trunc (N + 2)) (logSeries p) - Polynomial.X
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub, coeff_trunc, ite_eq_left (by omega), logSeries, PowerSeries.coeff_mk,
    Polynomial.coeff_X]
  rcases d with _ | _ | d
  · simp
  · simp
  · omega

/-- **`log [ε] ≠ 0` for `ε^♯ = 1`, `ε ≠ 1`.** Write `[ε] − 1 = ξ^s w` with `θ(w) ≠ 0` (`s ≥ 1`);
modulo `(ker θ)^{s+1}`, `log [ε] ≡ [ε] − 1 ≢ 0`. -/
theorem logTeich_ne_zero {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) (hne : ε ≠ 1) :
    logTeich p h ≠ 0 := by
  intro h0
  obtain ⟨s, w, hx, hw⟩ := eq_xi_pow_mul p _ (teich_sub_one_ne_zero p hne)
  have hs : s ≠ 0 := by
    rintro rfl
    apply hw
    rw [pow_zero, one_mul] at hx
    rw [← hx]
    exact PanBergerSplit.theta_teich_sub_one p h
  obtain ⟨R, hR⟩ := trunc_logSeries_sub_X p (s - 1)
  have hs2 : s - 1 + 2 = s + 1 := by omega
  rw [hs2] at hR
  have h0' : psEval (Ith p) (teich_sub_one_mem p h) (logSeries p) =
      (0 : AdicCompletion (Ith p) (AinfP p)) := h0
  have hev := congrArg (AdicCompletion.evalₐ (Ith p) (s + 1)) h0'
  rw [evalₐ_psEval, map_zero, Ideal.Quotient.eq_zero_iff_mem] at hev
  have hI : Ith p ^ (s + 1) =
      span {algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ (s + 1)} := by
    rw [Ith, ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineThetaInvertP_Cp, Ideal.span_singleton_pow]
    rfl
  set y := algebraMap (Ainf p) (AinfP p) (WittVector.teichmuller p ε - 1)
  have hy : y = algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ s *
      algebraMap (Ainf p) (AinfP p) w := by
    simp only [y, hx, map_mul, map_pow]
  have hsq : y ^ 2 * R.eval y ∈ Ith p ^ (s + 1) := by
    rw [hI, Ideal.mem_span_singleton]
    refine ⟨algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ (s - 1) *
      algebraMap (Ainf p) (AinfP p) w ^ 2 * R.eval y, ?_⟩
    rw [hy]
    have : 2 * s = (s + 1) + (s - 1) := by omega
    rw [mul_pow, ← pow_mul, mul_comm s 2, this, pow_add]
    ring
  have hyI : y ∈ Ith p ^ (s + 1) := by
    have he : y = (trunc (s + 1) (logSeries p)).eval y - y ^ 2 * R.eval y := by
      have := congrArg (Polynomial.eval y) hR
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X] at this
      linear_combination -this
    rw [he]
    exact Ideal.sub_mem _ hev hsq
  rw [hI] at hyI
  have hmem := mem_xi_pow_of_algebraMap p (s + 1) _ hyI
  rw [hx] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hw' : w = ZInQ.Contrib.G9.BdrKer.Cp.xi p * c := by
    have hξ : (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ s ≠ 0 :=
      pow_ne_zero _ (ZInQ.Contrib.G9.BdrKer.Cp.xi_ne_zero p)
    apply mul_left_cancel₀ hξ
    rw [← hc]
    ring
  apply hw
  rw [hw', map_mul]
  have hxi : theta p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = 0 := by
    change ZInQ.Contrib.G9.BdrKer.Cp.xi p ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p)
    rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
    exact Ideal.mem_span_singleton_self _
  rw [hxi, zero_mul]

/-- **`t ≠ 0` in `B_dR`**: every inverted `log [ε]` is a nonzero element of the field `B_dR`, so
`Ring.inverse` is its inverse, and there is such an `ε`. Hence `B_max` contains `t` and `1/t`. -/
theorem exists_t_ne_zero : ∃ (ε : PreTilt 𝓞_ℂ_[p] p) (h : PreTilt.untilt ε = 1), ε ≠ 1 ∧
    toBdR p (logTeich p h) ≠ 0 ∧
    toBdR p (logTeich p h) * Ring.inverse (toBdR p (logTeich p h)) = 1 := by
  obtain ⟨⟨ε, h, hne⟩⟩ := nonempty_tEps p
  have hne0 : toBdR p (logTeich p h) ≠ 0 := fun h0 =>
    logTeich_ne_zero p h hne ((toBdR_injective p) (h0.trans (map_zero _).symm))
  refine ⟨ε, h, hne, hne0, ?_⟩
  obtain ⟨y, hy⟩ : ∃ y : BdR p, toBdR p (logTeich p h) * y = 1 :=
    (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).mul_inv_cancel hne0
  have hu : IsUnit (toBdR p (logTeich p h)) := ⟨⟨_, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  exact Ring.mul_inverse_cancel _ hu

end TNonzero

end BergerBst
end PkgI4
end HDec

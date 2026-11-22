/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytic.ParametricCircleIntegral
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# The Weierstrass preparation theorem

We state the Weierstrass preparation theorem: a holomorphic function on a neighbourhood of the
origin in `ℂ^{n+1}` which does not vanish identically on the last coordinate axis factors, near
the origin, as a unit times a Weierstrass polynomial.

## Main definitions

- `IsWeierstrassPolynomial`: a monic polynomial whose lower coefficients vanish at the origin.
- `LocalOkaRing.fromPolynomial`: a polynomial over the germs in `n` variables, viewed as a germ
  in `n + 1` variables.
- `Polynomial.toOkaRing`: a polynomial over `OkaRing U` viewed as a holomorphic function on the
  cylinder `U.extend'` over `U`.
- `OkaRing.germ`: the Taylor series of a holomorphic function at a point of its domain.
- `OkaRing.germPoly`: the coefficientwise germ of a polynomial over `OkaRing U` at a point of
  the cylinder over `U`, Taylor expanded in the polynomial variable.

## Main results

Besides the statement of the local Weierstrass division theorem
(`localweierstrass_division`) and the proof of the local Weierstrass preparation theorem
from it (`localweierstrass_preparation`, via division by the generic Weierstrass polynomial
and the analytic implicit function theorem `exists_analyticAt_implicit`), this file develops
the dictionary between functions and germs used to reduce Oka's coherence lemma to them:

- `OkaRing.germ_toOkaRing`: the germ of the function attached to a polynomial is the germ
  polynomial, viewed as a germ via `LocalOkaRing.fromPolynomial`.
- `OkaRing.exists_restrict_eq_of_germ_eq`, `LocalOkaRing.exists_okaRing_germ`,
  `OkaRing.exists_isUnit_restrict`: germs detect local equality, are realized by functions on
  neighbourhoods, and detect local invertibility.
- `LocalOkaRing.exists_isWeierstrassPolynomial_realize` and
  `LocalOkaRing.exists_poly_germPoly`: realizations of germ polynomials by polynomials over
  the holomorphic functions on a neighbourhood.
- `Polynomial.exists_map_restrict_eq_zero`: a polynomial in the last variable whose attached
  function vanishes near a point of the cylinder vanishes coefficientwise near the base point.
- `MvPowerSeries.Represents.homogeneous_eval_eq_zero`, `MvPowerSeries.exists_direction`,
  `lineEquiv`: choice of a linear change of coordinates making finitely many nonzero germs
  general in the last variable.
-/

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Finsupp in
theorem MvPowerSeries.mem_span_X_of_constantCoeff_eq_zero
    {σ : Type*} [Finite σ] [LinearOrder σ] {φ : MvPowerSeries σ ℂ}
    (hφ : MvPowerSeries.constantCoeff φ = 0) :
    φ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ ℂ)) := by
  classical
  haveI := Fintype.ofFinite σ
  rw [Ideal.mem_span_range_iff_exists_fun]
  set g : σ → MvPowerSeries σ ℂ :=
    fun i ↦ (fun e ↦ if ∀ j, j < i → e j = 0 then coeff (e + single i 1) φ else 0) with hg
  refine ⟨g, ?_⟩
  ext d
  rw [map_sum]
  have key : ∀ i : σ, coeff d (g i * X i)
      = if single i 1 ≤ d then (if ∀ j, j < i → d j = 0 then coeff d φ else 0) else 0 := by
    intro i
    rw [X_def, coeff_mul_monomial, mul_one]
    by_cases hle : single i 1 ≤ d
    · rw [if_pos hle, if_pos hle, hg, MvPowerSeries.coeff_apply]
      dsimp only
      rw [tsub_add_cancel_of_le hle]
      refine if_congr (forall_congr' fun j ↦ imp_congr_right fun hj ↦ ?_) rfl rfl
      simp [Finsupp.tsub_apply, ne_of_gt hj]
    · rw [if_neg hle, if_neg hle]
  rw [Finset.sum_congr rfl fun i _ ↦ key i]
  simp_rw [← ite_and]
  by_cases hd : d = 0
  · subst hd
    rw [coeff_zero_eq_constantCoeff, hφ]
    refine Finset.sum_eq_zero fun i _ ↦ if_neg fun h ↦ ?_
    have h1 := Finsupp.single_le_iff.mp h.1
    simp only [Finsupp.coe_zero, Pi.zero_apply] at h1
    omega
  · have hne : d.support.Nonempty := Finsupp.support_nonempty_iff.mpr hd
    have hmem : d.support.min' hne ∈ d.support := Finset.min'_mem _ hne
    have hpos : 1 ≤ d (d.support.min' hne) :=
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hmem)
    rw [Finset.sum_eq_single (d.support.min' hne)]
    · have hcond : single (d.support.min' hne) 1 ≤ d ∧
          (∀ j, j < d.support.min' hne → d j = 0) := by
        refine ⟨Finsupp.single_le_iff.mpr hpos, fun j hj ↦ ?_⟩
        by_contra hdj
        exact absurd (Finset.min'_le _ j (Finsupp.mem_support_iff.mpr hdj)) (not_le.mpr hj)
      rw [if_pos hcond]
    · intro i _ hi
      refine if_neg fun h ↦ ?_
      have hisupp : i ∈ d.support :=
        Finsupp.mem_support_iff.mpr (by have := Finsupp.single_le_iff.mp h.1; omega)
      have hlt : d.support.min' hne < i :=
        lt_of_le_of_ne (Finset.min'_le _ i hisupp) (Ne.symm hi)
      exact absurd (h.2 _ hlt) (Nat.one_le_iff_ne_zero.mp hpos)
    · intro h; exact absurd (Finset.mem_univ _) h

open MvPowerSeries in
theorem MvPowerSeries.maximalIdeal_eq_span_X {σ : Type*} [Finite σ] [LinearOrder σ] :
    IsLocalRing.maximalIdeal (MvPowerSeries σ ℂ)
      = Ideal.span (Set.range (X : σ → MvPowerSeries σ ℂ)) := by
  apply le_antisymm
  · intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    refine mem_span_X_of_constantCoeff_eq_zero ?_
    by_contra hc
    exact hx (isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hc))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 := isUnit_iff_constantCoeff.mp hu
    rw [constantCoeff_X] at h0
    exact not_isUnit_zero h0

/-- **The formal power series ring is complete for its maximal-adic topology.**

No order on `σ` is assumed: `MvPowerSeries.maximalIdeal_eq_span_X` needs one to pick a smallest
variable occurring in a monomial, but its *statement* does not mention the order, so any linear
order will do and a finite type has one. -/
instance instIsAdicCompleteMaximalIdealMvPowerSeries {σ : Type*} [Finite σ] :
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries σ ℂ)) (MvPowerSeries σ ℂ) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  letI : LinearOrder σ := LinearOrder.lift' e e.injective
  rw [MvPowerSeries.maximalIdeal_eq_span_X]
  infer_instance

open Polynomial in
theorem exists_diffQuotient
    {R : Type*} [CommRing R] [Nontrivial R]
    (q : R[X]) (hq : q ≠ 0) (c : R) :
    ∃ Q : R[X], Q.degree < q.degree ∧ q - C (q.eval c) = (X - C c) * Q := by
  refine ⟨q /ₘ (X - C c), ?_, ?_⟩
  · refine degree_divByMonic_lt q (X - C c) hq ?_
    rw [degree_X_sub_C]
    exact_mod_cast Nat.zero_lt_one
  · have h := modByMonic_add_div q (X - C c)
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    exact (eq_sub_of_add_eq' h).symm

open Polynomial in
/-- Divided difference: `p(c) - p(t) = (c - t) * (p /ₘ (X - C c))(t)`. -/
theorem eval_sub_eval_eq_mul_divByMonic {R : Type*} [CommRing R] (p : R[X]) (c t : R) :
    p.eval c - p.eval t = (c - t) * (p /ₘ (X - C c)).eval t := by
  have h := modByMonic_add_div p (X - C c)
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  have h2 := congrArg (Polynomial.eval t) h
  simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X] at h2
  linear_combination h2

open Finset Polynomial in
/-- Divided-difference identity for a finite power sum with leading coefficient one. -/
theorem sum_pow_sub_sum_pow_eq (d : ℕ) (c : ℕ → ℂ) (hcd : c d = 1) (ζ t : ℂ) :
    (∑ j ∈ range (d + 1), c j * ζ ^ j) - (∑ j ∈ range (d + 1), c j * t ^ j)
      = (ζ - t) * ∑ i ∈ range d, t ^ i *
          ∑ j ∈ Icc (i + 1) d, ζ ^ (j - 1 - i) * c j := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0; simp
  set p : ℂ[X] := ∑ j ∈ range (d + 1), C (c j) * X ^ j with hp
  have hcoeff : ∀ k, p.coeff k = if k ≤ d then c k else 0 := by
    intro k
    rw [hp, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (range (d + 1)) k c]
    simp
  have hle : p.natDegree ≤ d :=
    natDegree_le_iff_coeff_eq_zero.mpr (fun k hk ↦ by rw [hcoeff k, if_neg (by omega)])
  have hnd : p.natDegree = d := by
    refine natDegree_eq_of_le_of_coeff_ne_zero hle ?_
    rw [hcoeff d, if_pos le_rfl, hcd]
    exact one_ne_zero
  have heval : ∀ s : ℂ, p.eval s = ∑ j ∈ range (d + 1), c j * s ^ j := by
    intro s
    rw [hp, eval_finsetSum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    simp
  have hdeg : (p /ₘ (X - C ζ)).natDegree < d := by
    rw [natDegree_divByMonic p (monic_X_sub_C ζ), natDegree_X_sub_C, hnd]
    omega
  have hkey := eval_sub_eval_eq_mul_divByMonic p ζ t
  rw [heval, heval] at hkey
  rw [hkey, eval_eq_sum_range' hdeg]
  congr 1
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [coeff_divByMonic_X_sub_C p ζ i, hnd, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj ↦ ?_)
  have hexp : j - 1 - i = j - (i + 1) := by omega
  rw [hcoeff j, if_pos (Finset.mem_Icc.mp hj).2, hexp]
  ring

namespace MvPowerSeries
section Curry

/-! ### Currying a power series in a sum of variables

A formal power series in the variables `σ ⊕ τ` is the same thing as a power series in `σ`
whose coefficients are power series in `τ`: on coefficients this is nothing but
`Finsupp.sumFinsuppEquivProdFinsupp`, which splits an exponent on `σ ⊕ τ` into its `σ`-part
and its `τ`-part. `curry` and `uncurry` are the two directions and `curryEquiv` packages them
as a ring equivalence; `finSuccRingEquiv` specialises it to
`ℂ⟦x₁, …, x_{n+1}⟧ ≃+* (ℂ⟦x₁, …, x_n⟧)⟦X⟧`, singling out the last variable.

Nothing in this section is used elsewhere in the project: the Weierstrass theorems below reach
the same "one distinguished variable" viewpoint through `LocalOkaRing.fromPolynomial` and
`Polynomial` rather than through `PowerSeries`. It is general `MvPowerSeries` API in a Mathlib
namespace and a Mathlib upstreaming candidate, which is why it is documented and kept rather
than made `private`.
-/

variable {σ τ R : Type*} [CommSemiring R]

/-- A power series in the variables `σ ⊕ τ`, read as a power series in `σ` with coefficients
power series in `τ`. Its `(dσ, dτ)`-coefficient is the coefficient of the exponent on `σ ⊕ τ`
assembled from `dσ` and `dτ`. Inverse to `uncurry`; packaged as a ring equivalence in
`curryEquiv`. -/
noncomputable def curry (f : MvPowerSeries (σ ⊕ τ) R) : MvPowerSeries σ (MvPowerSeries τ R) :=
  fun dσ dτ ↦ coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (dσ, dτ)) f

/-- A power series in `σ` with coefficients power series in `τ`, read as a power series in the
variables `σ ⊕ τ`. Inverse to `curry`. -/
noncomputable def uncurry (g : MvPowerSeries σ (MvPowerSeries τ R)) : MvPowerSeries (σ ⊕ τ) R :=
  fun d ↦ coeff (Finsupp.sumFinsuppEquivProdFinsupp d).2
              (coeff (Finsupp.sumFinsuppEquivProdFinsupp d).1 g)

@[simp] lemma coeff_curry (f : MvPowerSeries (σ ⊕ τ) R) (dσ : σ →₀ ℕ) (dτ : τ →₀ ℕ) :
    coeff dτ (coeff dσ (curry f)) =
      coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (dσ, dτ)) f := rfl

@[simp] lemma coeff_uncurry (g : MvPowerSeries σ (MvPowerSeries τ R)) (d : σ ⊕ τ →₀ ℕ) :
    coeff d (uncurry g) =
      coeff (Finsupp.sumFinsuppEquivProdFinsupp d).2
        (coeff (Finsupp.sumFinsuppEquivProdFinsupp d).1 g) := rfl

lemma uncurry_curry (f : MvPowerSeries (σ ⊕ τ) R) : uncurry (curry f) = f := by
  ext d
  rw [coeff_uncurry, coeff_curry, Prod.mk.eta, Equiv.symm_apply_apply]

lemma curry_uncurry (g : MvPowerSeries σ (MvPowerSeries τ R)) : curry (uncurry g) = g := by
  ext dσ dτ
  rw [coeff_curry, coeff_uncurry, Equiv.apply_symm_apply]

@[simp] lemma curry_add (f g : MvPowerSeries (σ ⊕ τ) R) :
    curry (f + g) = curry f + curry g := by
  ext dσ dτ
  simp [map_add]

@[simp] lemma curry_zero : curry (0 : MvPowerSeries (σ ⊕ τ) R) = 0 := by
  ext dσ dτ
  simp

lemma curry_one : curry (1 : MvPowerSeries (σ ⊕ τ) R) = 1 := by
  classical
  have he0 : Finsupp.sumFinsuppEquivProdFinsupp (0 : σ ⊕ τ →₀ ℕ) = (0, 0) := by
    apply Prod.ext <;> ext x <;> simp
  ext dσ dτ
  rw [coeff_curry, coeff_one]
  have key : (Finsupp.sumFinsuppEquivProdFinsupp.symm (dσ, dτ) = (0 : σ ⊕ τ →₀ ℕ))
      ↔ (dσ = 0 ∧ dτ = 0) := by
    rw [Equiv.symm_apply_eq, he0, Prod.mk.injEq]
  simp only [key]
  by_cases h : dσ = 0 ∧ dτ = 0
  · obtain ⟨h1, h2⟩ := h; subst h1; subst h2; simp
  · rw [if_neg h]
    rcases not_and_or.mp h with h' | h'
    · simp [coeff_one, if_neg h']
    · by_cases hσ : dσ = 0
      · subst hσ; simp [coeff_one, if_neg h']
      · simp [coeff_one, if_neg hσ]

lemma symm_prod_eq_sumElim (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    Finsupp.sumFinsuppEquivProdFinsupp.symm (a, b) = Finsupp.sumElim a b := by
  ext x
  cases x with
  | inl x => simp
  | inr x => simp

lemma curry_mul (f g : MvPowerSeries (σ ⊕ τ) R) : curry (f * g) = curry f * curry g := by
  classical
  ext dσ dτ
  have hL : coeff dτ (coeff dσ (curry (f * g)))
      = ∑ q ∈ (Finset.antidiagonal dσ) ×ˢ (Finset.antidiagonal dτ),
          coeff (Finsupp.sumElim q.1.1 q.2.1) f * coeff (Finsupp.sumElim q.1.2 q.2.2) g := by
    rw [coeff_curry, symm_prod_eq_sumElim, coeff_mul,
      ← Finsupp.image_sumElim_product_antidiagonal,
      Finset.sum_image (by
        rintro ⟨⟨x, y⟩, z, w⟩ _ ⟨⟨x', y'⟩, z', w'⟩ _ hEq
        simp only [Prod.mk.injEq] at hEq
        obtain ⟨h1, h2⟩ := hEq
        have hx : x = x' := by ext a; simpa using DFunLike.congr_fun h1 (Sum.inl a)
        have hz : z = z' := by ext a; simpa using DFunLike.congr_fun h1 (Sum.inr a)
        have hy : y = y' := by ext a; simpa using DFunLike.congr_fun h2 (Sum.inl a)
        have hw : w = w' := by ext a; simpa using DFunLike.congr_fun h2 (Sum.inr a)
        subst hx; subst hy; subst hz; subst hw; rfl)]
  have hR : coeff dτ (coeff dσ (curry f * curry g))
      = ∑ q ∈ (Finset.antidiagonal dσ) ×ˢ (Finset.antidiagonal dτ),
          coeff (Finsupp.sumElim q.1.1 q.2.1) f * coeff (Finsupp.sumElim q.1.2 q.2.2) g := by
    rw [coeff_mul, map_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun pσ _ ↦ ?_
    rw [coeff_mul]
    refine Finset.sum_congr rfl fun pτ _ ↦ ?_
    rw [coeff_curry, coeff_curry, symm_prod_eq_sumElim, symm_prod_eq_sumElim]
  rw [hL, hR]

/-- `curry` and `uncurry` as a ring equivalence
`R⟦σ ⊕ τ⟧ ≃+* (R⟦τ⟧)⟦σ⟧`. -/
noncomputable def curryEquiv : MvPowerSeries (σ ⊕ τ) R ≃+* MvPowerSeries σ (MvPowerSeries τ R) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
  map_add' := curry_add
  map_mul' := curry_mul

/-- `Fin (n + 1)` split as its last element and the rest, in the form `Unit ⊕ Fin n` that
`curryEquiv` consumes: `Fin.last n` goes to `Sum.inl ()` and `Fin.castSucc j` to `Sum.inr j`.

This differs from `finSumFinEquiv` and `Fin.consEquiv` in singling out the **last** variable,
which is the one the Weierstrass theorems distinguish. -/
def finLastEquivSum (n : ℕ) : Fin (n + 1) ≃ Unit ⊕ Fin n where
  toFun i := Fin.lastCases (Sum.inl ()) Sum.inr i
  invFun x := Sum.elim (fun _ ↦ Fin.last n) Fin.castSucc x
  left_inv i := by
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp
  right_inv x := by
    cases x with
    | inl u => simp
    | inr j => simp

/-- Power series in `n + 1` variables, read as power series in the last variable with
coefficients power series in the first `n`: `ℂ⟦x₁, …, x_{n+1}⟧ ≃+* (ℂ⟦x₁, …, x_n⟧)⟦X⟧`.

This is `curryEquiv` along `finLastEquivSum`, and it is the change of viewpoint that makes the
Weierstrass division and preparation theorems statements about a polynomial ring in one
variable. -/
noncomputable def finSuccRingEquiv (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) ℂ ≃+* PowerSeries (MvPowerSeries (Fin n) ℂ) :=
  (MvPowerSeries.renameEquiv (R := ℂ) (finLastEquivSum n)).toRingEquiv.trans
    (curryEquiv (σ := Unit) (τ := Fin n) (R := ℂ))

end Curry
end MvPowerSeries

namespace MvPowerSeries

lemma summableAt_X {ι : Type*} (i : ι) (x : ι → ℂ) :
    (X i : MvPowerSeries ι ℂ).SummableAt x := by
  classical
  refine summable_of_ne_finset_zero (s := {Finsupp.single i 1}) fun d hd ↦ ?_
  rw [Finset.mem_singleton] at hd
  rw [term, coeff_X, if_neg hd, zero_mul, norm_zero]

lemma locallyConvergent_X {ι : Type*} (i : ι) :
    (X i : MvPowerSeries ι ℂ).LocallyConvergent :=
  .of_forall fun x ↦ summableAt_X i x

lemma eval_X {ι : Type*} (i : ι) (x : ι → ℂ) :
    (X i : MvPowerSeries ι ℂ).eval x = x i := by
  classical
  rw [eval, tsum_eq_single (Finsupp.single i 1) ?_]
  · rw [term, coeff_X, if_pos rfl, one_mul, evalMonomial, Finsupp.prod_single_index] <;> simp
  · intro d hd
    rw [term, coeff_X, if_neg hd, zero_mul]

lemma eval_add_of_summableAt {ι : Type*} {P Q : MvPowerSeries ι ℂ} {x : ι → ℂ}
    (hP : P.SummableAt x) (hQ : Q.SummableAt x) :
    (P + Q).eval x = P.eval x + Q.eval x := by
  have hfun : (P + Q).term x = fun d ↦ P.term x d + Q.term x d :=
    funext fun d ↦ term_add P Q x d
  refine (hP.add hQ).hasSum.unique ?_
  rw [hfun]
  exact hP.hasSum.add hQ.hasSum

lemma eval_mul_of_summableAt {ι : Type*} {P Q : MvPowerSeries ι ℂ} {x : ι → ℂ}
    (hP : P.SummableAt x) (hQ : Q.SummableAt x) :
    (P * Q).eval x = P.eval x * Q.eval x := by
  classical
  have hFsum : Summable fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ P.term x p.1 * Q.term x p.2 := by
    refine Summable.of_norm ?_
    simpa [norm_mul] using
      Summable.mul_of_nonneg hP hQ (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hF : HasSum (fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦ P.term x p.1 * Q.term x p.2)
      (P.eval x * Q.eval x) := hP.hasSum.mul hQ.hasSum hFsum
  have hσ := (antidiagonalSigmaEquiv ι).hasSum_iff.mpr hF
  have hfib : ∀ d : ι →₀ ℕ,
      HasSum (fun c : {p : (ι →₀ ℕ) × (ι →₀ ℕ) //
          p ∈ Finset.HasAntidiagonal.antidiagonal d} ↦ P.term x c.1.1 * Q.term x c.1.2)
        ((P * Q).term x d) := by
    intro d
    rw [term_mul, ← Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal d)
      (fun p ↦ P.term x p.1 * Q.term x p.2)]
    exact hasSum_fintype _
  exact ((hσ.sigma hfib).unique (hP.mul hQ).hasSum).symm

lemma summableAt_zero {ι : Type*} (x : ι → ℂ) : (0 : MvPowerSeries ι ℂ).SummableAt x := by
  simpa using summableAt_algebraMap 0 x

lemma summableAt_one {ι : Type*} (x : ι → ℂ) : (1 : MvPowerSeries ι ℂ).SummableAt x := by
  simpa using summableAt_algebraMap 1 x

lemma eval_algebraMap {ι : Type*} (c : ℂ) (x : ι → ℂ) :
    (algebraMap ℂ (MvPowerSeries ι ℂ) c).eval x = c := by
  classical
  rw [eval, tsum_eq_single 0 (fun d hd ↦ term_algebraMap_of_ne_zero c x hd),
    term_algebraMap_zero]

lemma eval_of_zero {ι : Type*} (x : ι → ℂ) : (0 : MvPowerSeries ι ℂ).eval x = 0 := by
  simpa using eval_algebraMap 0 x

lemma eval_one {ι : Type*} (x : ι → ℂ) : (1 : MvPowerSeries ι ℂ).eval x = 1 := by
  simpa using eval_algebraMap 1 x

lemma SummableAt.sum {ι κ : Type*} {x : ι → ℂ} {s : Finset κ} {P : κ → MvPowerSeries ι ℂ} :
    (∀ k ∈ s, (P k).SummableAt x) → (∑ k ∈ s, P k).SummableAt x := by
  classical
  induction s using Finset.induction with
  | empty => intro _; simpa using summableAt_zero x
  | insert k s hk ih =>
      intro h
      rw [Finset.sum_insert hk]
      exact (h k (by simp)).add (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

lemma eval_sum_of_summableAt {ι κ : Type*} {x : ι → ℂ} {s : Finset κ}
    {P : κ → MvPowerSeries ι ℂ} :
    (∀ k ∈ s, (P k).SummableAt x) → (∑ k ∈ s, P k).eval x = ∑ k ∈ s, (P k).eval x := by
  classical
  induction s using Finset.induction with
  | empty => intro _; simp [eval_of_zero]
  | insert k s hk ih =>
      intro h
      have hs : ∀ j ∈ s, (P j).SummableAt x := fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hk, Finset.sum_insert hk,
        eval_add_of_summableAt (h k (by simp)) (SummableAt.sum hs), ih hs]

lemma SummableAt.pow {ι : Type*} {P : MvPowerSeries ι ℂ} {x : ι → ℂ} (h : P.SummableAt x) :
    ∀ m : ℕ, (P ^ m).SummableAt x
  | 0 => by simpa using summableAt_one x
  | m + 1 => by rw [pow_succ]; exact (SummableAt.pow h m).mul h

lemma eval_pow_of_summableAt {ι : Type*} {P : MvPowerSeries ι ℂ} {x : ι → ℂ}
    (h : P.SummableAt x) :
    ∀ m : ℕ, (P ^ m).eval x = P.eval x ^ m
  | 0 => by simpa using eval_one x
  | m + 1 => by
      rw [pow_succ, pow_succ, eval_mul_of_summableAt (h.pow m) h, eval_pow_of_summableAt h m]

lemma summableAt_zero_pt {ι : Type*} (P : MvPowerSeries ι ℂ) :
    P.SummableAt (0 : ι → ℂ) := by
  classical
  refine summable_of_ne_finset_zero (s := {0}) fun d hd ↦ ?_
  rw [Finset.mem_singleton] at hd
  rw [term, evalMonomial_eq_zero hd, mul_zero, norm_zero]

end MvPowerSeries

variable {n : ℕ}

/-- The last coordinate `x_{n+1}` as a germ at the origin in `n + 1` variables: the
distinguished variable of the Weierstrass theorems, and the one variable not in the image of
`LocalOkaRing.incl`. Local convergence is `MvPowerSeries.locallyConvergent_X`. -/
noncomputable def LocalOkaRing.lastVar : LocalOkaRing (Fin (n + 1)) :=
  ⟨MvPowerSeries.X (Fin.last n), MvPowerSeries.locallyConvergent_X _⟩

namespace MvPowerSeries
open Filter Topology

variable {σ τ : Type*}

lemma evalMonomial_mapDomain (e : σ ↪ τ) (d : σ →₀ ℕ) (x : τ → ℂ) :
    evalMonomial (Finsupp.mapDomain e d) x = evalMonomial d (x ∘ e) :=
  Finsupp.prod_mapDomain_index_inj e.injective

lemma term_rename (e : σ ↪ τ) [TendstoCofinite (e : σ → τ)]
    (P : MvPowerSeries σ ℂ) (x : τ → ℂ) (d : σ →₀ ℕ) :
    (rename (e : σ → τ) P).term x (Finsupp.mapDomain e d) = P.term (x ∘ e) d := by
  rw [term, term, ← Finsupp.embDomain_eq_mapDomain, coeff_embDomain_rename,
    Finsupp.embDomain_eq_mapDomain, evalMonomial_mapDomain]

lemma eval_rename (e : σ ↪ τ) [TendstoCofinite (e : σ → τ)]
    (P : MvPowerSeries σ ℂ) (x : τ → ℂ) :
    (rename (e : σ → τ) P).eval x = P.eval (x ∘ e) := by
  have hzero : Function.support (fun d' ↦ (rename (e : σ → τ) P).term x d') ⊆
      Set.range (Finsupp.mapDomain (e : σ → τ)) := by
    intro d' hd'
    by_contra h
    apply hd'
    change (rename (e : σ → τ) P).term x d' = 0
    rw [term, coeff_rename_eq_zero _ _ h, zero_mul]
  rw [eval, eval, ← Function.Injective.tsum_eq
    (Finsupp.mapDomain_injective e.injective) hzero]
  exact tsum_congr fun d ↦ term_rename e P x d

lemma SummableAt.rename (e : σ ↪ τ) [TendstoCofinite (e : σ → τ)]
    {P : MvPowerSeries σ ℂ} {x : τ → ℂ} (h : P.SummableAt (x ∘ e)) :
    (rename (e : σ → τ) P).SummableAt x := by
  refine (Function.Injective.summable_iff
    (g := fun d : σ →₀ ℕ ↦ Finsupp.mapDomain (e : σ → τ) d)
    (Finsupp.mapDomain_injective e.injective) ?_).mp ?_
  · intro d' hd'
    rw [term, coeff_rename_eq_zero _ _ hd', zero_mul, norm_zero]
  · simpa [SummableAt, Function.comp_def, term_rename] using h

lemma LocallyConvergent.rename (e : σ ↪ τ) [TendstoCofinite (e : σ → τ)]
    {P : MvPowerSeries σ ℂ} (hP : P.LocallyConvergent) :
    (rename (e : σ → τ) P).LocallyConvergent := by
  have hc : Tendsto (fun x : τ → ℂ ↦ x ∘ (e : σ → τ)) (𝓝 0) (𝓝 0) :=
    (continuous_pi fun i ↦ continuous_apply (e i)).tendsto' 0 0 rfl
  filter_upwards [hc.eventually hP] with x hx using SummableAt.rename e hx

end MvPowerSeries

instance : Filter.TendstoCofinite (Fin.castSuccEmb : Fin n → Fin (n + 1)) :=
  Filter.tendstoCofinite_of_finite _

/-- A germ at the origin in `n` variables, read as a germ in `n + 1` variables not involving
the last one: renaming along `Fin.castSuccEmb`, as a morphism of `ℂ`-algebras.

Together with `LocalOkaRing.lastVar` this presents `LocalOkaRing (Fin (n + 1))` over
`LocalOkaRing (Fin n)`, which is what the induction on the number of variables needs. Local
convergence is preserved because renaming along an embedding only reindexes the variables
(`MvPowerSeries.LocallyConvergent.rename`). -/
noncomputable def LocalOkaRing.incl :
    LocalOkaRing (Fin n) →ₐ[ℂ] LocalOkaRing (Fin (n + 1)) :=
  ((MvPowerSeries.rename (Fin.castSuccEmb : Fin n → Fin (n + 1))).comp
      (localOkaSubring (Fin n)).val).codRestrict _
    (fun P ↦ MvPowerSeries.LocallyConvergent.rename _ P.2)

open Polynomial TopologicalSpace

variable {n : ℕ}

/-- A local Weierstrass polynomial is a monic polynomial whose coefficients below the leading
one vanish at the origin. -/
structure IsLocalWeierstrassPolynomial
  (P : (MvPowerSeries (Fin n) ℂ)[X]) : Prop where
  monic : P.Monic
  apply_zero (i : ℕ) (hi : i < P.degree) :
  MvPowerSeries.constantCoeff (P.coeff i) = 0

section FromPolynomial

namespace MvPowerSeries

/-- A power series in `n` variables representing `F` represents, as a power series in `n + 1`
variables, the pullback of `F` along the projection to the first `n` coordinates. -/
lemma Represents.rename_castSucc {P : MvPowerSeries (Fin n) ℂ} {F : (Fin n → ℂ) → ℂ}
    (hP : P.Represents F) :
    (rename (Fin.castSuccEmb : Fin n → Fin (n + 1)) P).Represents
      (fun x ↦ F (Fin.init x)) := by
  have hcont : Continuous (Fin.init : (Fin (n + 1) → ℂ) → (Fin n → ℂ)) :=
    continuous_pi fun i ↦ continuous_apply i.castSucc
  filter_upwards [(hcont.tendsto 0).eventually hP] with x hx
  have hinj : Function.Injective
      (Finsupp.mapDomain (M := ℕ) (Fin.castSuccEmb : Fin n → Fin (n + 1))) :=
    Finsupp.mapDomain_injective Fin.castSuccEmb.injective
  have hvanish : ∀ d ∉ Set.range
      (Finsupp.mapDomain (M := ℕ) (Fin.castSuccEmb : Fin n → Fin (n + 1))),
      (rename (Fin.castSuccEmb : Fin n → Fin (n + 1)) P).term x d = 0 := fun d hd ↦ by
    rw [term, coeff_rename_eq_zero _ _ hd, zero_mul]
  refine (Function.Injective.hasSum_iff hinj hvanish).mp ?_
  have hfun : (rename (Fin.castSuccEmb : Fin n → Fin (n + 1)) P).term x ∘
      Finsupp.mapDomain (Fin.castSuccEmb : Fin n → Fin (n + 1)) = P.term (Fin.init x) :=
    funext fun d ↦ term_rename Fin.castSuccEmb P x d
  rw [hfun]
  exact hx

variable {ι : Type*}

/-- The power series `X i` represents the `i`-th coordinate function. -/
lemma represents_X (i : ι) : (X i : MvPowerSeries ι ℂ).Represents (fun x ↦ x i) := by
  classical
  refine .of_forall fun x ↦ ?_
  have h : ∀ d ≠ Finsupp.single i 1, (X i : MvPowerSeries ι ℂ).term x d = 0 := fun d hd ↦ by
    rw [term, coeff_X, if_neg hd, zero_mul]
  have h1 : (X i : MvPowerSeries ι ℂ).term x (Finsupp.single i 1) = x i := by
    rw [term, coeff_X, if_pos rfl, one_mul]
    simp [evalMonomial]
  simpa only [h1] using hasSum_single (f := (X i : MvPowerSeries ι ℂ).term x)
    (Finsupp.single i 1) h

end MvPowerSeries

namespace LocalOkaRing

open MvPowerSeries

@[simp]
lemma coe_incl (P : LocalOkaRing (Fin n)) :
    (incl P : MvPowerSeries (Fin (n + 1)) ℂ) =
      MvPowerSeries.rename (Fin.castSuccEmb : Fin n → Fin (n + 1))
        (P : MvPowerSeries (Fin n) ℂ) :=
  rfl

@[simp]
lemma coe_lastVar :
    ((lastVar : LocalOkaRing (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℂ) =
      MvPowerSeries.X (Fin.last n) :=
  rfl

end LocalOkaRing

end FromPolynomial

/-- A polynomial over the germs in `n` variables, viewed as a germ in `n + 1` variables. -/
noncomputable def LocalOkaRing.fromPolynomial :
    (LocalOkaRing (Fin n))[X] →ₐ[ℂ] LocalOkaRing (Fin (n + 1)) :=
  Polynomial.aevalTower LocalOkaRing.incl LocalOkaRing.lastVar

namespace LocalOkaRing

@[simp]
lemma fromPolynomial_C (P : LocalOkaRing (Fin n)) :
    fromPolynomial (Polynomial.C P) = incl P :=
  Polynomial.aevalTower_C _ _ _

@[simp]
lemma fromPolynomial_X :
    fromPolynomial (Polynomial.X : (LocalOkaRing (Fin n))[X]) = lastVar :=
  Polynomial.aevalTower_X _ _

/-- The underlying power series of `LocalOkaRing.fromPolynomial Q` is
`MvPowerSeries.fromPolynomial'` applied to the underlying polynomial of power series. -/
lemma coe_fromPolynomial (Q : (LocalOkaRing (Fin n))[X]) :
    (fromPolynomial Q : MvPowerSeries (Fin (n + 1)) ℂ) =
      MvPowerSeries.fromPolynomial'
        (Q.map (Subring.subtype (localOkaSubring (Fin n)).toSubring)) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, AddMemClass.coe_add, hp, hq, Polynomial.map_add, map_add]
  | monomial k a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    rw [map_mul, map_pow, fromPolynomial_C, fromPolynomial_X]
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
    rw [map_mul, map_pow, MvPowerSeries.fromPolynomial'_C, MvPowerSeries.fromPolynomial'_X]
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_incl, coe_lastVar]
    rfl

lemma fromPolynomial_injective :
    Function.Injective (fromPolynomial (n := n)) := by
  intro Q₁ Q₂ h
  have h2 : (fromPolynomial Q₁ : MvPowerSeries (Fin (n + 1)) ℂ) = fromPolynomial Q₂ :=
    congrArg Subtype.val h
  rw [coe_fromPolynomial, coe_fromPolynomial] at h2
  exact Polynomial.map_injective _ (fun a b hab ↦ Subtype.ext hab)
    (MvPowerSeries.fromPolynomial'_injective h2)

end LocalOkaRing

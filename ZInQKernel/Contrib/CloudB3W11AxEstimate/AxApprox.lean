/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy (AI-assisted)

This module is a port, to this repository's pinned Lean v4.35.0 / Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, of the Ax approximation lemma from

  anthropics/fermats-last-theorem @ 6e837e75, Apache License 2.0,
  P2M/Sol/S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le.lean
  (written against an earlier toolchain, Lean v4.33),

whose statement, proof skeleton and lemma decomposition are reused here under that licence.
Changes made in porting: `import Mathlib` replaced by the specific Mathlib modules used; the
upstream dependency on `P2M.Util` removed (it declares elaborators, which this repository does not
admit in contributed files), together with the `p2m_reactivate` command; the `local notation`
abbreviations `Ω`, `Γ` expanded to `PadicAlgCl p` and `PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p`, since
contributed files may not declare notation; `push Not` replaced by ordinary tactics; the local
`hasseDeriv_map` dropped in favour of Mathlib's; names placed in this repository's namespace.
-/
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ax's uniform algebraic approximation estimate

For a prime `p`, an intermediate field `K` of `ℚ̄_p / ℚ_p` and an algebraic `α ∈ ℚ̄_p` whose
`G_K`-displacement is at most `δ`, there is `a ∈ K` with `‖α - a‖ ≤ p ^ 2 * δ`. The constant
`p ^ 2` depends on `p` only: it is independent of `K`, of `α`, and — this is the whole point, and
what a trace-averaging argument cannot give — of the degree `[K(α) : K]`.

This is the arithmetic half of Ax–Sen–Tate (Ax, *Zeros of polynomials over local fields — the
Galois action*, Invent. Math. 10 (1970) 116-124). The completion/density half is
`ZInQKernel/Contrib/CloudB3W11AxCompletion/`.

The proof is Ax's descent on the degree. Write `f` for the minimal polynomial of `α` over `K`, of
degree `n₀`; all its roots are `G_K`-translates of `α`, hence within `δ` of `α`, so the Taylor
coefficients of `f` at `α` are bounded by powers of `δ` (`key`). The `j`-th Hasse derivative of `f`
is a polynomial over `K` of degree `n₀ - j` and leading coefficient `C(n₀, j)`, so the trivial root
estimate produces a root `β` of it with

  `‖β - α‖ ^ (n₀ - j) ≤ δ ^ (n₀ - j) / ‖C(n₀, j)‖`,

of degree at most `n₀ - j` over `K` and with `G_K`-displacement at most `‖β - α‖`. Choosing
`n₀ - j = p ^ (Nat.log p n₀)` when that is `< n₀` costs nothing (`C(n₀, p^L)` is a unit, by Lucas),
and from a degree that is exactly `p ^ L` one descends to `p ^ (L - 1)` at the cost of
`p ^ (1 / p ^ (L-1))` (Kummer: `C(p^L, p^(L-1))` has `p`-adic valuation exactly one). The costs
form a geometric series bounded by `∑ i, p⁻¹ ^ i ≤ 2`, giving the uniform constant `p ^ 2`.

Main results:

* `AxL.main`: the estimate with the running constant `AxL.B p n` for degrees at most `n`;
* `exists_mem_intermediateField_norm_sub_le_mul`: the uniform estimate with constant `p ^ 2`;
* `uniform_ax_approximation`: the same, packaged with `b : K`, the form the completion bridge
  consumes.
-/

namespace ZInQ.Contrib.CloudB3W11AxEstimate

open Polynomial

namespace AxL

variable (p : ℕ) [hp : Fact p.Prime]

lemma norm_algEquiv (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    ‖σ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv σ x).symm

lemma norm_natCast (N : ℕ) : ‖(N : PadicAlgCl p)‖ = ‖(N : ℚ_[p])‖ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]

lemma norm_natCast_eq_one {N : ℕ} (h : ¬ p ∣ N) : ‖(N : PadicAlgCl p)‖ = 1 := by
  rw [norm_natCast, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr h

lemma inv_p_le_norm_natCast {N : ℕ} (hN : N ≠ 0) (h : ¬ p ^ 2 ∣ N) :
    (p : ℝ)⁻¹ ≤ ‖(N : PadicAlgCl p)‖ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  by_cases hd : p ∣ N
  · obtain ⟨u, rfl⟩ := hd
    have hu : ¬ p ∣ u := by
      rintro ⟨v, rfl⟩
      exact h ⟨v, by ring⟩
    rw [Nat.cast_mul, norm_mul, norm_natCast_eq_one p hu, mul_one, norm_natCast, Padic.norm_p]
  · rw [norm_natCast_eq_one p hd]
    exact inv_le_one_of_one_le₀ hp1

lemma norm_natCast_pos {N : ℕ} (hN : N ≠ 0) : 0 < ‖(N : PadicAlgCl p)‖ := by
  rw [norm_pos_iff]
  exact_mod_cast hN

lemma norm_multiset_sum_le (t : Multiset (PadicAlgCl p)) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ x ∈ t, ‖x‖ ≤ B) : ‖t.sum‖ ≤ B := by
  induction t using Multiset.induction with
  | empty => simpa using hB
  | cons a t ih =>
    rw [Multiset.sum_cons]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact h a (Multiset.mem_cons_self a t)
    · exact ih fun x hx => h x (Multiset.mem_cons_of_mem hx)

lemma norm_multiset_prod_le (t : Multiset (PadicAlgCl p)) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ x ∈ t, ‖x‖ ≤ δ) : ‖t.prod‖ ≤ δ ^ Multiset.card t := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ, mul_comm (δ ^ _)]
    exact mul_le_mul (h a (Multiset.mem_cons_self a t))
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (norm_nonneg _) hδ

lemma norm_multiset_prod_eq (t : Multiset (PadicAlgCl p)) :
    ‖t.prod‖ = (t.map fun x => ‖x‖).prod := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t ih => rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, ih]

lemma norm_esymm_le (s : Multiset (PadicAlgCl p)) (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ x ∈ s, ‖x‖ ≤ δ)
    (m : ℕ) : ‖s.esymm m‖ ≤ δ ^ m := by
  unfold Multiset.esymm
  refine norm_multiset_sum_le p _ _ (pow_nonneg hδ m) ?_
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [Multiset.mem_powersetCard] at hu
  rw [← hu.2]
  exact norm_multiset_prod_le p u δ hδ fun y hy => h y (Multiset.mem_of_le hu.1 hy)

lemma pow_card_le_prod_of_le (t : Multiset ℝ) (a : ℝ) (ha : 0 ≤ a) (h : ∀ x ∈ t, a ≤ x) :
    a ^ Multiset.card t ≤ t.prod := by
  induction t using Multiset.induction with
  | empty => simp
  | cons b t ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
    have hb := h b (Multiset.mem_cons_self b t)
    exact mul_le_mul hb (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (pow_nonneg ha _)
      (ha.trans hb)

lemma taylor_multiset_prod (r : PadicAlgCl p) (t : Multiset (Polynomial (PadicAlgCl p))) :
    taylor r t.prod = (t.map fun q => taylor r q).prod := by
  induction t using Multiset.induction with
  | empty => simp [taylor_one]
  | cons a t ih => rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, taylor_mul, ih]

lemma taylor_prod_X_sub_C (r : PadicAlgCl p) (s : Multiset (PadicAlgCl p)) :
    taylor r ((s.map fun a => X - C a).prod)
      = ((s.map fun a => a - r).map fun a => X - C a).prod := by
  rw [taylor_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp only [Function.comp_apply, map_sub, taylor_X, taylor_C, C_sub]
  ring

/-- **The one-step descent estimate.** For a monic `f` all of whose roots are within `δ` of `α`,
the `j`-th Hasse derivative of `f` has a root `β` with
`‖β - α‖ ^ (deg f - j) ≤ δ ^ (deg f - j) / ‖C(deg f, j)‖`. -/
theorem key (f : Polynomial (PadicAlgCl p)) (hf : f.Monic) (α : PadicAlgCl p) (δ : ℝ)
    (hδ : 0 ≤ δ) (hroots : ∀ β ∈ f.roots, ‖β - α‖ ≤ δ) (j : ℕ) (hj : j < f.natDegree)
    (hN : (f.natDegree.choose j : PadicAlgCl p) ≠ 0) :
    ∃ β ∈ (hasseDeriv j f).roots,
      ‖β - α‖ ^ (f.natDegree - j)
        ≤ δ ^ (f.natDegree - j) / ‖(f.natDegree.choose j : PadicAlgCl p)‖ := by
  classical
  set n := f.natDegree with hn
  set m := n - j with hm
  have hm0 : m ≠ 0 := by omega
  have hmj : m + j = n := by omega

  have hsplit : f = (f.roots.map fun a => X - C a).prod :=
    (IsAlgClosed.splits f).eq_prod_roots_of_monic hf
  have hcard : Multiset.card f.roots = n := ((IsAlgClosed.splits f).natDegree_eq_card_roots).symm
  set s : Multiset (PadicAlgCl p) := f.roots.map fun a => a - α with hs
  have hscard : Multiset.card s = n := by rw [hs, Multiset.card_map, hcard]
  have hsδ : ∀ x ∈ s, ‖x‖ ≤ δ := by
    intro x hx
    rw [hs, Multiset.mem_map] at hx
    obtain ⟨β, hβ, rfl⟩ := hx
    exact hroots β hβ

  have htaylor : taylor α f = (s.map fun a => X - C a).prod := by
    conv_lhs => rw [hsplit]
    rw [taylor_prod_X_sub_C]
  have hcoeff : (taylor α f).coeff j = (-1) ^ (n - j) * s.esymm (n - j) := by
    rw [htaylor, Multiset.prod_X_sub_C_coeff s (by rw [hscard]; omega), hscard]
  set g := hasseDeriv j f with hg
  have heval_le : ‖g.eval α‖ ≤ δ ^ m := by
    rw [hg, ← taylor_coeff, hcoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← hm]
    exact norm_esymm_le p s δ hδ hsδ m

  have hgcoeff : g.coeff m = (n.choose j : PadicAlgCl p) := by
    rw [hg, hasseDeriv_coeff, hmj]
    have hc : f.coeff n = 1 := hf.coeff_natDegree
    rw [hc, mul_one]
  have hgdeg : g.natDegree = m := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [hgcoeff]; exact hN))
    rw [hg, hm, hn]
    exact natDegree_hasseDeriv_le f j
  have hglead : g.leadingCoeff = (n.choose j : PadicAlgCl p) := by
    rw [leadingCoeff, hgdeg, hgcoeff]
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, leadingCoeff_zero] at hglead
    exact hN hglead.symm
  have hgsplit : g = C (n.choose j : PadicAlgCl p) * (g.roots.map fun a => X - C a).prod := by
    rw [← hglead]
    exact (IsAlgClosed.splits g).eq_prod_roots
  have hgcard : Multiset.card g.roots = m := by
    rw [← hgdeg]; exact ((IsAlgClosed.splits g).natDegree_eq_card_roots).symm

  have hevalprod : g.eval α
      = (n.choose j : PadicAlgCl p) * (g.roots.map fun β => α - β).prod := by
    conv_lhs => rw [hgsplit]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun β _ => ?_)
    simp
  have hnormprod : ‖(n.choose j : PadicAlgCl p)‖ * (g.roots.map fun β => ‖α - β‖).prod ≤ δ ^ m := by
    have hle := heval_le
    rw [hevalprod, norm_mul, norm_multiset_prod_eq, Multiset.map_map] at hle
    exact hle

  have hne : g.roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty, ← Multiset.card_pos, hgcard]
    exact Nat.pos_of_ne_zero hm0
  obtain ⟨β₀, hβ₀, hmin⟩ := Finset.exists_min_image g.roots.toFinset (fun β => ‖α - β‖) hne
  rw [Multiset.mem_toFinset] at hβ₀
  refine ⟨β₀, hβ₀, ?_⟩
  have hNpos : 0 < ‖(n.choose j : PadicAlgCl p)‖ := norm_pos_iff.mpr hN
  have hpow : ‖α - β₀‖ ^ m ≤ (g.roots.map fun β => ‖α - β‖).prod := by
    have hprod := pow_card_le_prod_of_le (g.roots.map fun β => ‖α - β‖) ‖α - β₀‖ (norm_nonneg _)
      (by
        intro x hx
        rw [Multiset.mem_map] at hx
        obtain ⟨β, hβ, rfl⟩ := hx
        exact hmin β (Multiset.mem_toFinset.mpr hβ))
    rwa [Multiset.card_map, hgcard] at hprod
  rw [norm_sub_rev, le_div_iff₀ hNpos, mul_comm]
  exact (mul_le_mul_of_nonneg_left hpow hNpos.le).trans hnormprod

section Galois

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

scoped instance isAlgClosureK : IsAlgClosure K (PadicAlgCl p) :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K⟩

scoped instance normalK : Normal K (PadicAlgCl p) := IsAlgClosure.normal K (PadicAlgCl p)

lemma isIntegralK (α : PadicAlgCl p) : IsIntegral K α :=
  (Algebra.IsAlgebraic.isAlgebraic (R := K) α).isIntegral

/-- Every root of the minimal polynomial of `α` over `K` is a `G_K`-translate of `α`, hence within
the displacement bound `δ`. -/
lemma roots_minpoly_norm_sub_le (α : PadicAlgCl p) (δ : ℝ)
    (h : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) :
    ∀ β ∈ ((minpoly K α).map (algebraMap K (PadicAlgCl p))).roots, ‖β - α‖ ≤ δ := by
  intro β hβ
  have hint := isIntegralK p K α
  have hmon : ((minpoly K α).map (algebraMap K (PadicAlgCl p))).Monic := (minpoly.monic hint).map _
  rw [mem_roots hmon.ne_zero, IsRoot.def, eval_map, ← aeval_def] at hβ
  have hmin : minpoly K α = minpoly K β :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hβ (minpoly.monic hint)
  have horb : β ∈ MulAction.orbit (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) α :=
    (Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).mp hmin.symm
  obtain ⟨τ, hτ⟩ := horb
  have hσK : (τ.restrictScalars ℚ_[p]) ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change τ x = x
    exact τ.commutes ⟨x, hx⟩
  have hσα : (τ.restrictScalars ℚ_[p]) α = β := hτ
  rw [← hσα]
  exact h _ hσK

/-- A root of the `j`-th Hasse derivative of the minimal polynomial of `α` has degree at most
`deg (minpoly K α) - j` over `K`. -/
lemma natDegree_minpoly_le_of_mem_roots_hasseDeriv (α : PadicAlgCl p) (j : ℕ)
    (hj : j < (minpoly K α).natDegree) (β : PadicAlgCl p)
    (hβ : β ∈ (hasseDeriv j ((minpoly K α).map (algebraMap K (PadicAlgCl p)))).roots) :
    (minpoly K β).natDegree ≤ (minpoly K α).natDegree - j := by
  set gK := hasseDeriv j (minpoly K α) with hgK
  have hmap : hasseDeriv j ((minpoly K α).map (algebraMap K (PadicAlgCl p)))
      = gK.map (algebraMap K (PadicAlgCl p)) := hasseDeriv_map _ _ _
  have hint := isIntegralK p K α

  have hcoeff : gK.coeff ((minpoly K α).natDegree - j)
      = ((minpoly K α).natDegree.choose j : K) := by
    rw [hgK, hasseDeriv_coeff, Nat.sub_add_cancel hj.le, (minpoly.monic hint).coeff_natDegree,
      mul_one]
  have hgK0 : gK ≠ 0 := by
    intro h0
    have hz := hcoeff
    rw [h0, coeff_zero] at hz
    have hc : ((minpoly K α).natDegree.choose j : K) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hj.le).ne'
    exact hc hz.symm
  have hmap0 : gK.map (algebraMap K (PadicAlgCl p)) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero]
  rw [hmap, mem_roots hmap0, IsRoot.def, eval_map, ← aeval_def] at hβ
  have hdeg := minpoly.degree_le_of_ne_zero K β hgK0 hβ
  refine (natDegree_le_natDegree hdeg).trans ?_
  rw [hgK]
  exact natDegree_hasseDeriv_le _ _

/-- The displacement of a nearby element is controlled by the displacement of `α` and the distance
between them (ultrametric, no factor `2`). -/
lemma norm_conj_sub_le (α β : PadicAlgCl p) (δ ε : ℝ)
    (h : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ)
    (hβ : ‖β - α‖ ≤ ε) (hδε : δ ≤ ε) :
    ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → ‖σ β - β‖ ≤ ε := by
  intro σ hσ
  have hsplit : σ β - β = σ (β - α) + ((σ α - α) + (α - β)) := by
    rw [map_sub]; abel
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_algEquiv]; exact hβ
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((h σ hσ).trans hδε) ?_)
    rw [norm_sub_rev]; exact hβ

end Galois

/-- Lucas' theorem in the form needed: `C(n, p^L) ≡ n / p^L` modulo `p`. -/
lemma choose_prime_pow_modEq (L : ℕ) : ∀ n : ℕ, n.choose (p ^ L) ≡ n / p ^ L [MOD p] := by
  induction L with
  | zero => intro n; rw [pow_zero, Nat.choose_one_right, Nat.div_one]
  | succ L ih =>
    intro n
    have h1 := @Choose.choose_modEq_choose_mod_mul_choose_div_nat n (p ^ (L + 1)) p hp
    have hk : p ^ (L + 1) % p = 0 := by
      rw [pow_succ]; exact Nat.mul_mod_left _ _
    have hk' : p ^ (L + 1) / p = p ^ L := by
      rw [pow_succ, Nat.mul_div_cancel _ hp.out.pos]
    rw [hk, hk', Nat.choose_zero_right, one_mul] at h1
    refine h1.trans ?_
    have h2 := ih (n / p)
    rwa [Nat.div_div_eq_div_mul, mul_comm, ← pow_succ] at h2

/-- If `p ^ L ≤ n < p ^ (L+1)` then `C(n, p^L)` is prime to `p`: the descent to degree `p ^ L`
costs nothing. -/
lemma not_dvd_choose_prime_pow {n L : ℕ} (h1 : p ^ L ≤ n) (h2 : n < p ^ (L + 1)) :
    ¬ p ∣ n.choose (p ^ L) := by
  intro hd
  have hmod := choose_prime_pow_modEq p L n
  have hq1 : 1 ≤ n / p ^ L := (Nat.le_div_iff_mul_le (pow_pos hp.out.pos L)).mpr (by simpa using h1)
  have hq2 : n / p ^ L < p := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp.out.pos L)]
    calc n < p ^ (L + 1) := h2
      _ = p * p ^ L := by rw [pow_succ, mul_comm]
  have h0 : n.choose (p ^ L) % p = 0 := by
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.mul_mod_right]
  have hdiv : (n / p ^ L) % p = 0 := by
    have hm := hmod
    rw [Nat.ModEq, h0] at hm
    exact hm.symm
  rw [Nat.mod_eq_of_lt hq2] at hdiv
  omega

/-- Kummer: `C(p^L, p^(L-1))` has `p`-adic valuation exactly one, so the descent from a degree that
is exactly a power of `p` costs a single factor of `p`. -/
lemma not_sq_dvd_choose_prime_pow_pred {L : ℕ} (hL : 1 ≤ L) :
    ¬ p ^ 2 ∣ (p ^ L).choose (p ^ (L - 1)) := by
  have hprime : Prime p := Nat.prime_iff.mp hp.out
  have hk : p ^ (L - 1) ≤ p ^ L := Nat.pow_le_pow_right hp.out.pos (Nat.sub_le L 1)
  have hk0 : p ^ (L - 1) ≠ 0 := (pow_pos hp.out.pos _).ne'
  have hem := Nat.Prime.emultiplicity_choose_prime_pow hp.out hk hk0
  rw [multiplicity_pow_self_of_prime hprime] at hem
  have hL1 : L - (L - 1) = 1 := by omega
  rw [hL1] at hem
  have hfin := (emultiplicity_eq_coe.mp hem).2
  simpa using hfin

/-- The exponent budget: the geometric sum of the descent costs for degrees up to `n`. -/
noncomputable def E (n : ℕ) : ℝ := ∑ i ∈ Finset.range (Nat.log p n), ((p : ℝ)⁻¹) ^ i

/-- The running constant for degrees up to `n`. -/
noncomputable def B (n : ℕ) : ℝ := (p : ℝ) ^ (E p n)

lemma one_le_p : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos

lemma E_nonneg (n : ℕ) : 0 ≤ E p n :=
  Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (p_pos p).le) i

lemma E_mono {m n : ℕ} (h : m ≤ n) : E p m ≤ E p n := by
  unfold E
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.log_mono_right h)) ?_
  intro i _ _
  exact pow_nonneg (inv_nonneg.mpr (p_pos p).le) i

lemma E_le_two (n : ℕ) : E p n ≤ 2 := by
  unfold E
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_geometric_two_le (Nat.log p n))
  rw [one_div]
  refine pow_le_pow_left₀ (inv_nonneg.mpr (p_pos p).le) ?_ i
  refine inv_anti₀ (by norm_num) ?_
  exact_mod_cast hp.out.two_le

lemma E_pow_succ (L : ℕ) : E p (p ^ (L + 1)) = E p (p ^ L) + ((p : ℝ)⁻¹) ^ L := by
  unfold E
  rw [Nat.log_pow hp.out.one_lt, Nat.log_pow hp.out.one_lt, Finset.sum_range_succ]

lemma one_le_B (n : ℕ) : 1 ≤ B p n := Real.one_le_rpow (one_le_p p) (E_nonneg p n)

lemma B_pos (n : ℕ) : 0 < B p n := lt_of_lt_of_le one_pos (one_le_B p n)

lemma B_mono {m n : ℕ} (h : m ≤ n) : B p m ≤ B p n :=
  Real.rpow_le_rpow_of_exponent_le (one_le_p p) (E_mono p h)

lemma B_le_sq (n : ℕ) : B p n ≤ (p : ℝ) ^ 2 := by
  have hle := Real.rpow_le_rpow_of_exponent_le (one_le_p p) (E_le_two p n)
  rw [B]
  refine hle.trans_eq ?_
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma B_pow_succ (L : ℕ) : B p (p ^ (L + 1)) = B p (p ^ L) * (p : ℝ) ^ (((p : ℝ)⁻¹) ^ L) := by
  rw [B, E_pow_succ, Real.rpow_add (p_pos p), B]

/-- **Ax's estimate, with the running constant.** For every intermediate field `K`, every `α` of
degree at most `n` over `K` and every bound `δ` on the `G_K`-displacement of `α`, there is `a ∈ K`
with `‖α - a‖ ≤ B p n * δ`. -/
theorem main (n : ℕ) : ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (α : PadicAlgCl p) (δ : ℝ),
    (minpoly K α).natDegree ≤ n →
    (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) →
      ∃ a ∈ K, ‖α - a‖ ≤ B p n * δ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K α δ hdeg hconj
    have hδ : 0 ≤ δ := by
      have h1 := hconj 1 (Subgroup.one_mem _)
      simpa using h1
    have hint := isIntegralK p K α
    set n₀ := (minpoly K α).natDegree with hn₀
    have hn₀pos : 0 < n₀ := minpoly.natDegree_pos hint

    by_cases h1 : n₀ = 1
    · have hα : α ∈ (algebraMap K (PadicAlgCl p)).range := minpoly.natDegree_eq_one_iff.mp h1
      obtain ⟨a, ha⟩ := hα
      refine ⟨(a : PadicAlgCl p), a.2, ?_⟩
      have hae : (a : PadicAlgCl p) = α := ha
      rw [hae, sub_self, norm_zero]
      exact mul_nonneg (B_pos p n).le hδ
    have hn₀2 : 2 ≤ n₀ := by omega

    set L := Nat.log p n₀ with hL
    have hpL : p ^ L ≤ n₀ := Nat.pow_log_le_self p (by omega)
    have hn₀lt : n₀ < p ^ (L + 1) := Nat.lt_pow_succ_log_self hp.out.one_lt n₀

    set f : Polynomial (PadicAlgCl p) := (minpoly K α).map (algebraMap K (PadicAlgCl p)) with hf
    have hfmon : f.Monic := (minpoly.monic hint).map _
    have hfdeg : f.natDegree = n₀ := (minpoly.monic hint).natDegree_map _
    have hroots : ∀ β ∈ f.roots, ‖β - α‖ ≤ δ := roots_minpoly_norm_sub_le p K α δ hconj

    have cont : ∀ (m : ℕ) (Λ : ℝ), 0 < m → m < n₀ → 1 ≤ Λ →
        (n₀.choose (n₀ - m) : PadicAlgCl p) ≠ 0 →
        (‖(n₀.choose (n₀ - m) : PadicAlgCl p)‖)⁻¹ ≤ Λ ^ m →
        B p m * Λ ≤ B p n₀ →
        ∃ a ∈ K, ‖α - a‖ ≤ B p n * δ := by
      intro m Λ hm0 hmn hΛ1 hN hNΛ hBΛ
      set j := n₀ - m with hj
      have hjlt : j < f.natDegree := by rw [hfdeg]; omega
      have hmj : f.natDegree - j = m := by rw [hfdeg]; omega
      have hNf : (f.natDegree.choose j : PadicAlgCl p) ≠ 0 := by rw [hfdeg]; exact hN
      obtain ⟨β, hβ, hβle⟩ := key p f hfmon α δ hδ hroots j hjlt hNf
      rw [hmj, hfdeg] at hβle

      have hβΛ : ‖β - α‖ ≤ Λ * δ := by
        have hΛδ : 0 ≤ Λ * δ := mul_nonneg (zero_le_one.trans hΛ1) hδ
        refine le_of_pow_le_pow_left₀ hm0.ne' hΛδ ?_
        refine hβle.trans ?_
        rw [div_eq_mul_inv, mul_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right hNΛ (pow_nonneg hδ m)

      have hβdeg : (minpoly K β).natDegree ≤ m := by
        have hd := natDegree_minpoly_le_of_mem_roots_hasseDeriv p K α j (by omega) β
          (by rw [← hf]; exact hβ)
        omega

      have hβconj := norm_conj_sub_le p K α β δ (Λ * δ) hconj hβΛ
        (by nlinarith [hδ, hΛ1])

      have hmn' : m < n := lt_of_lt_of_le hmn hdeg
      obtain ⟨a, haK, ha⟩ := ih m hmn' K β (Λ * δ) hβdeg hβconj
      refine ⟨a, haK, ?_⟩
      have hsplit : α - a = (α - β) + (β - a) := by abel
      rw [hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_sub_rev]
        refine hβΛ.trans ?_
        have hΛB : Λ ≤ B p n := by
          have hle1 : Λ ≤ B p m * Λ := le_mul_of_one_le_left (zero_le_one.trans hΛ1) (one_le_B p m)
          exact hle1.trans (hBΛ.trans (B_mono p hdeg))
        exact mul_le_mul_of_nonneg_right hΛB hδ
      · refine ha.trans ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hBΛ.trans (B_mono p hdeg)) hδ
    by_cases hcase : p ^ L < n₀
    · -- the degree is not a power of `p`: descend to `p ^ L` for free
      refine cont (p ^ L) 1 (pow_pos hp.out.pos L) hcase le_rfl ?_ ?_ ?_
      · rw [Nat.choose_symm hpL]
        have h := not_dvd_choose_prime_pow p hpL hn₀lt
        intro h0
        have hone : ‖((n₀.choose (p ^ L) : ℕ) : PadicAlgCl p)‖ = 1 := norm_natCast_eq_one p h
        rw [h0, norm_zero] at hone
        exact zero_ne_one hone
      · rw [Nat.choose_symm hpL, norm_natCast_eq_one p (not_dvd_choose_prime_pow p hpL hn₀lt),
          inv_one, one_pow]
      · rw [mul_one]; exact B_mono p hpL
    · -- the degree is exactly `p ^ L`: descend to `p ^ (L-1)` at cost `p ^ (1 / p ^ (L-1))`
      have hn₀eq : n₀ = p ^ L := le_antisymm (not_lt.mp hcase) hpL
      have hL1 : 1 ≤ L := by
        rcases Nat.eq_zero_or_pos L with hL0 | hLpos
        · rw [hL0, pow_zero] at hn₀eq; omega
        · exact hLpos
      set m := p ^ (L - 1) with hm
      have hm0 : 0 < m := pow_pos hp.out.pos _
      have hmn : m < n₀ := by
        rw [hn₀eq, hm]
        exact Nat.pow_lt_pow_right hp.out.one_lt (by omega)
      have hmle : m ≤ n₀ := hmn.le
      have hNnat : ¬ p ^ 2 ∣ n₀.choose m := by
        rw [hn₀eq, hm]; exact not_sq_dvd_choose_prime_pow_pred p hL1
      have hNne : n₀.choose m ≠ 0 := (Nat.choose_pos hmle).ne'
      set Λ : ℝ := (p : ℝ) ^ ((m : ℝ)⁻¹) with hΛ
      have hΛ1 : 1 ≤ Λ := Real.one_le_rpow (one_le_p p) (by positivity)
      refine cont m Λ hm0 hmn hΛ1 ?_ ?_ ?_
      · rw [Nat.choose_symm hmle]
        exact_mod_cast hNne
      · rw [Nat.choose_symm hmle]
        have hle := inv_p_le_norm_natCast p hNne hNnat
        have hΛm : Λ ^ m = p := by
          rw [hΛ]; exact Real.rpow_inv_natCast_pow (p_pos p).le hm0.ne'
        rw [hΛm, inv_le_comm₀ (norm_natCast_pos p hNne) (p_pos p)]
        exact hle
      · have hL' : L = (L - 1) + 1 := by omega
        have hΛ' : Λ = (p : ℝ) ^ (((p : ℝ)⁻¹) ^ (L - 1)) := by
          rw [hΛ, hm]
          congr 1
          rw [Nat.cast_pow, ← inv_pow]
        rw [hn₀eq, hL', B_pow_succ, hΛ']

end AxL

variable (p : ℕ) [Fact p.Prime]

/-- **Ax's uniform algebraic approximation estimate.** For every intermediate field `K` of
`ℚ̄_p / ℚ_p`, every `α ∈ ℚ̄_p` and every `δ` bounding the `G_K`-displacement of `α`, there is
`a ∈ K` with `‖α - a‖ ≤ p ^ 2 * δ`. The constant depends on `p` alone — in particular not on the
degree of `α` over `K`, which is what makes this, and not the trace-averaging bound, the arithmetic
input to Ax–Sen–Tate. -/
theorem exists_mem_intermediateField_norm_sub_le_mul
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (α : PadicAlgCl p) (δ : ℝ)
    (h : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) :
    ∃ a ∈ K, ‖α - a‖ ≤ (p : ℝ) ^ 2 * δ := by
  have hδ : 0 ≤ δ := by
    have h1 := h 1 (Subgroup.one_mem _)
    simpa using h1
  obtain ⟨a, haK, ha⟩ := AxL.main p ((minpoly K α).natDegree) K α δ le_rfl h
  exact ⟨a, haK, ha.trans (mul_le_mul_of_nonneg_right (AxL.B_le_sq p _) hδ)⟩

/-- The same estimate, with the approximant packaged as an element of `K`: this is the exact shape
`ZInQ.Contrib.CloudB3W11AxCompletion.UniformAxApproximation p K ((p : ℝ) ^ 2)` consumed by the
completion bridge. -/
theorem uniform_ax_approximation (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (a : PadicAlgCl p) (δ : ℝ) (hδ : 0 < δ)
    (h : ∀ σ ∈ K.fixingSubgroup, ‖σ a - a‖ ≤ δ) :
    ∃ b : K, ‖a - (b : PadicAlgCl p)‖ ≤ (p : ℝ) ^ 2 * δ := by
  obtain ⟨c, hcK, hc⟩ := exists_mem_intermediateField_norm_sub_le_mul p K a δ h
  exact ⟨⟨c, hcK⟩, hc⟩

/-- The estimate in its existential form, as stated upstream: some positive constant, depending on
`p` alone, works for every intermediate field, every algebraic element and every radius. -/
theorem exists_const_forall_exists_mem_intermediateField_norm_sub_le_mul :
    ∃ c : ℝ, 0 < c ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (α : PadicAlgCl p) (δ : ℝ),
        (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) →
          ∃ a ∈ K, ‖α - a‖ ≤ c * δ :=
  ⟨(p : ℝ) ^ 2, pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) 2,
    exists_mem_intermediateField_norm_sub_le_mul p⟩

end ZInQ.Contrib.CloudB3W11AxEstimate

/-- **Root-namespace export of Ax's uniform approximation estimate**, under the name the upstream
source gives it, for consumers that expect the root API. It is an ordinary theorem: this
repository admits no macros, wrappers or build-time code in contributed files. -/
theorem PadicAlgCl.exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (α : PadicAlgCl p) (δ : ℝ)
    (h : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) :
    ∃ a ∈ K, ‖α - a‖ ≤ (p : ℝ) ^ 2 * δ :=
  ZInQ.Contrib.CloudB3W11AxEstimate.exists_mem_intermediateField_norm_sub_le_mul p K α δ h

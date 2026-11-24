import ZInQKernel.Contrib.OneProof.PanBergerDict
import ZInQKernel.Contrib.OneProof.AxSenTate

/-!
# pb-pst: Pan's and Berger's leaves of `r11r12`: one `t`, Fontaine's admissibility, Hodge–Tate finiteness

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task pb-pst, 2026-11-17). Report
`docs/research/pb-pst.md`; generated from `scratch/pb-pst/BmaxOne.lean` and `scratch/pb-pst/HTFinite.lean` by
`scratch/pb-pst/mkcontrib.py`.

* **One `t`** (`BmaxOne.bmaxOf_eq`, `BmaxOne.bstOf_eq`): bst-construct's `Bmax`, `Bst` (which invert `log [ε]` for every
  `ε^♯ = 1`, `ε ≠ 1`) are `B_max^+[1/t]` and `B_max^+[1/t][log [p̃]]` for `t = log [ε₀]`, `ε₀` any generator of
  `ℤ_p(1)`: `log [ε] = a t` with `a ∈ ℤ_p` (`logTeich_eq_mul`, from the `p`-adic separatedness of `A_max ⊆ B_dR^+`,
  `amax_sep`).
* **Fontaine's admissibility, basis form** (`BmaxOne.IsAdmissibleT`): `B ⊗_{ℚ_p} V` has a `B`-basis of invariant
  vectors; it implies bst-construct's dimension form (`isAdmissible_of_T`) for every `G_{ℚ_p}`-stable `B ⊆ B_dR`.
* **Restated leaves**: `PanDict.BergerPrintedVT` (Berger 2002 Thm 0.7, one `t`, basis form) with
  `bergerPrintedV_of_T : BergerPrintedVT → BergerPrintedV`; `PanDict.PanPrintedPt` (Pan 2022 Thm 1.0.4 over
  `B_max^+[1/t][log [p̃]]`) with `panPrintedP_of_t : PanPrintedPt → PanPrintedP`.
* **Hodge–Tate finiteness** (`HTFinite.finiteDimensional_htSpaceE`, `HTFinite.htMultE_le`): `(V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}`
  is finite-dimensional over `E`, of dimension `≤ n` (Galois descent with Ax–Sen–Tate, `axSenTate_proof`).
-/



noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace BmaxOne

open Module PowerSeries Ideal
open scoped TensorProduct
open BergerBst
open PanBergerSplit (Ainf AinfP theta)

variable (p : ℕ) [Fact p.Prime]

/-! ## §1. `A_inf / ξ^m` is `p`-adically separated -/

theorem theta_xi : theta p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = 0 := by
  change ZInQ.Contrib.G9.BdrKer.Cp.xi p ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p)
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
  exact Ideal.mem_span_singleton_self _

theorem mem_xi_of_forall (w : Ainf p)
    (h : ∀ k : ℕ, ∃ a b : Ainf p, w = (p : Ainf p) ^ k * a + ZInQ.Contrib.G9.BdrKer.Cp.xi p * b) :
    w ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p} := by
  rw [← ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
  change theta p w = 0
  apply IsHausdorff.haus' (I := span {(p : 𝓞_ℂ_[p])})
  intro k
  obtain ⟨a, b, rfl⟩ := h k
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, map_add, map_mul, map_mul, map_pow, map_natCast, theta_xi, zero_mul,
    add_zero]
  exact dvd_mul_right _ _

/-- `⋂_k (p^k A_inf + ξ^m A_inf) = ξ^m A_inf`. -/
theorem mem_xi_pow_of_forall (m : ℕ) : ∀ w : Ainf p,
    (∀ k : ℕ, ∃ a b : Ainf p, w = (p : Ainf p) ^ k * a + ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m * b) →
    w ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m} := by
  induction m with
  | zero => intro w _; rw [pow_zero, Ideal.span_singleton_one]; trivial
  | succ m ih =>
    intro w h
    have h1 : w ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m} := ih w fun k => by
      obtain ⟨a, b, hab⟩ := h k
      exact ⟨a, ZInQ.Contrib.G9.BdrKer.Cp.xi p * b, by rw [hab, pow_succ]; ring⟩
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp h1
    have h2 : z ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p} := mem_xi_of_forall p z fun k => by
      obtain ⟨a, b, hab⟩ := h k
      rw [pow_succ] at hab
      have ha : (p : Ainf p) ^ k * a ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m} :=
        Ideal.mem_span_singleton'.mpr ⟨z - ZInQ.Contrib.G9.BdrKer.Cp.xi p * b, by
          linear_combination hab⟩
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (mem_xi_pow_of_p_pow_mul p m k a ha)
      refine ⟨c, b, ?_⟩
      apply mul_left_cancel₀ (pow_ne_zero m (ZInQ.Contrib.G9.BdrKer.Cp.xi_ne_zero p))
      rw [← hc] at hab
      linear_combination hab
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp h2
    exact Ideal.mem_span_singleton'.mpr ⟨d, by rw [pow_succ]; ring⟩

/-! ## §2. `A_max` is `p`-adically separated inside `B_dR^+` -/

theorem ith_pow (m : ℕ) : Ith p ^ m =
    span {algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ m} := by
  rw [Ith, ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineThetaInvertP_Cp, Ideal.span_singleton_pow]
  rfl

/-- `B_dR^+ → A_inf[1/p] / (ker θ)^m` (Mathlib's `B_dR^+` is the `ker θ`-adic completion). -/
def evB (m : ℕ) : BDeRhamPlus 𝓞_ℂ_[p] p →+* AinfP p ⧸ Ith p ^ m :=
  (AdicCompletion.evalₐ (Ith p) m).toRingHom

theorem evB_evalB {x : AinfP p} (hx : x ∈ Ith p) (f : (AinfP p)⟦X⟧) (m : ℕ) :
    evB p m (evalB p hx f) = Ideal.Quotient.mk (Ith p ^ m) ((trunc m f).eval x) :=
  evalₐ_psEval (Ith p) hx f m

theorem ext_evB {x y : BDeRhamPlus 𝓞_ℂ_[p] p} (h : ∀ m, evB p m x = evB p m y) : x = y :=
  AdicCompletion.ext_evalₐ h

/-- Modulo `(ker θ)^m`, `p^m` times an element of `A_max` comes from `A_inf`. -/
theorem amax_mod {y : BDeRhamPlus 𝓞_ℂ_[p] p} (hy : y ∈ Amax p) (m : ℕ) :
    ∃ w : Ainf p, evB p m ((p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ m * y) =
      Ideal.Quotient.mk _ (algebraMap (Ainf p) (AinfP p) w) := by
  obtain ⟨f, -, rfl⟩ := hy
  refine ⟨∑ i ∈ Finset.range m, PowerSeries.coeff i f * ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ i *
    (p : Ainf p) ^ (m - i), ?_⟩
  change evB p m ((p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ m *
    evalB p (omegaP_mem p) (PowerSeries.map (algebraMap (Ainf p) (AinfP p)) f)) = _
  rw [map_mul, evB_evalB, map_pow, map_natCast, ← map_natCast (Ideal.Quotient.mk _),
    ← map_pow, ← map_mul]
  congr 1
  rw [Polynomial.eval, eval₂_trunc_eq_sum_range, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := (Finset.mem_range.mp hi).le
  simp only [RingHom.id_apply, PowerSeries.coeff_map, map_mul, map_pow, map_natCast]
  have hpq : (p : AinfP p) * qpToLoc p ((p : ℚ_[p])⁻¹) = 1 :=
    natCast_mul_qp p p (Fact.out : p.Prime).ne_zero
  have hm : (p : AinfP p) ^ m = (p : AinfP p) ^ (m - i) * (p : AinfP p) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  have hx : ZInQ.Contrib.G9.BdrKer.Cp.xi' p =
      algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) := rfl
  rw [hm, omegaP, hx]
  calc (p : AinfP p) ^ (m - i) * (p : AinfP p) ^ i *
        (algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff i f) *
          (algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) *
            qpToLoc p ((p : ℚ_[p])⁻¹)) ^ i)
      = (p : AinfP p) ^ (m - i) * ((p : AinfP p) * qpToLoc p ((p : ℚ_[p])⁻¹)) ^ i *
        (algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff i f) *
          algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ^ i) := by ring
    _ = _ := by rw [hpq, one_pow]; ring

/-- **`A_max ⊆ B_dR^+` is `p`-adically separated**: an element of `B_dR^+` lying in `p^k A_max`
for every `k` is `0`. -/
theorem amax_sep (x : BDeRhamPlus 𝓞_ℂ_[p] p)
    (h : ∀ k : ℕ, ∃ y ∈ Amax p, x = (p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ k * y) : x = 0 := by
  refine ext_evB p fun m => ?_
  rw [map_zero]
  choose y hy hxy using h
  choose w hw using fun k => amax_mod p (hy k) m
  have hk : ∀ k, evB p m ((p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ m * x) =
      Ideal.Quotient.mk _ (algebraMap (Ainf p) (AinfP p) ((p : Ainf p) ^ k * w k)) := by
    intro k
    rw [hxy k, mul_left_comm, map_mul, hw k, map_pow, map_natCast, map_mul, map_pow, map_natCast,
      map_mul, map_pow, map_natCast]
  have hw0 : w 0 ∈ span {ZInQ.Contrib.G9.BdrKer.Cp.xi p ^ m} := by
    refine mem_xi_pow_of_forall p m (w 0) fun k => ?_
    have e := (hk 0).symm.trans (hk k)
    rw [Ideal.Quotient.eq, ← map_sub, ith_pow] at e
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (mem_xi_pow_of_algebraMap p m _ e)
    exact ⟨w k, b, by rw [pow_zero, one_mul] at hb; linear_combination -hb⟩
  have h0 : evB p m ((p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ m * x) = 0 := by
    rw [hk 0, pow_zero, one_mul, Ideal.Quotient.eq_zero_iff_mem, ith_pow]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hw0
    exact Ideal.mem_span_singleton'.mpr ⟨algebraMap (Ainf p) (AinfP p) c, by
      rw [← hc, map_mul, map_pow]⟩
  rw [map_mul, map_pow, map_natCast] at h0
  have hu : IsUnit ((p : AinfP p ⧸ Ith p ^ m) ^ m) := by
    refine IsUnit.pow _ ?_
    have := IsLocalization.Away.algebraMap_isUnit (S := AinfP p) (p : Ainf p)
    rw [map_natCast] at this
    simpa using this.map (Ideal.Quotient.mk (Ith p ^ m))
  exact (hu.mul_right_eq_zero).mp h0

/-! ## §3. The tilt: `ε = ε₀^b · η^{p^k}` and `log [ε] ≡ b log [ε₀] mod p^k A_max` -/

open ZInQ.Contrib.G9.BdrKer.Cp (root root_pow root_succ_pow)

/-- **A generator of `ℤ_p(1)` in the tilt**: `ε₀ ∈ 𝓞_ℂ_p♭` with `ε₀^♯ = 1` and `ε₀^{(1)} = ζ_p ≠ 1`, i.e.
`ε₀ = (1, ζ_p, ζ_{p²}, …)` for a compatible system of primitive `p^n`-th roots of unity; `t = log [ε₀]`. -/
def IsGenEps (ε₀ : PreTilt 𝓞_ℂ_[p] p) : Prop := PreTilt.untilt ε₀ = 1 ∧ root ε₀ 1 ≠ 1

theorem iter_mul (n : ℕ) (x y : PreTilt 𝓞_ℂ_[p] p) :
    ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) (x * y) =
      ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) x *
        ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      map_mul]

theorem iter_one (n : ℕ) : ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_one]

theorem iter_pow (k : ℕ) (x : PreTilt 𝓞_ℂ_[p] p) :
    ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[k] x) ^ p ^ k = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p, ih]

theorem root_mul (x y : PreTilt 𝓞_ℂ_[p] p) (n : ℕ) : root (x * y) n = root x n * root y n := by
  simp only [ZInQ.Contrib.G9.BdrKer.Cp.root, iter_mul, map_mul]

theorem root_one (n : ℕ) : root (1 : PreTilt 𝓞_ℂ_[p] p) n = 1 := by
  simp only [ZInQ.Contrib.G9.BdrKer.Cp.root, iter_one, map_one]

theorem root_npow (x : PreTilt 𝓞_ℂ_[p] p) (n c : ℕ) : root (x ^ c) n = root x n ^ c := by
  induction c with
  | zero => rw [pow_zero, pow_zero, root_one]
  | succ c ih => rw [pow_succ, root_mul, ih, pow_succ]

theorem root_zero (x : PreTilt 𝓞_ℂ_[p] p) : root x 0 = PreTilt.untilt x := rfl

theorem root_add_pow (x : PreTilt 𝓞_ℂ_[p] p) (j m : ℕ) : root x (j + m) ^ p ^ m = root x j := by
  induction m with
  | zero => simp
  | succ m ih => rw [← Nat.add_assoc, pow_succ', pow_mul, root_succ_pow, ih]

theorem isPrimitiveRoot_root {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (k : ℕ) :
    IsPrimitiveRoot (root ε₀ k) (p ^ k) := by
  rcases k with _ | k
  · rw [pow_zero, IsPrimitiveRoot.one_right_iff, root_zero]
    exact h.1
  · rw [IsPrimitiveRoot.iff_orderOf]
    apply orderOf_eq_prime_pow
    · rw [show k + 1 = 1 + k by ring, root_add_pow]
      exact h.2
    · rw [root_pow]
      exact h.1

theorem exists_pow_eq {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {ε : PreTilt 𝓞_ℂ_[p] p}
    (hε : PreTilt.untilt ε = 1) (k : ℕ) : ∃ b < p ^ k, root ε₀ k ^ b = root ε k := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  exact (isPrimitiveRoot_root p h k).eq_pow_of_pow_eq_one (by rw [root_pow, hε])

theorem logTeich_congr {x y : PreTilt 𝓞_ℂ_[p] p} (hxy : x = y) (hx : PreTilt.untilt x = 1)
    (hy : PreTilt.untilt y = 1) : logTeich p hx = logTeich p hy := by
  subst hxy
  rfl

theorem logTeich_mul {x y : PreTilt 𝓞_ℂ_[p] p} (hx : PreTilt.untilt x = 1)
    (hy : PreTilt.untilt y = 1) (hxy : PreTilt.untilt (x * y) = 1) :
    logTeich p hxy = logTeich p hx + logTeich p hy := by
  have e := logPlus_add p (teich_sub_one_mem p hx) (teich_sub_one_mem p hy)
  change logPlus p (teich_sub_one_mem p hxy) = logPlus p _ + logPlus p _
  rw [← e]
  refine evalB_congr' p _ _ ?_ (logSeries p)
  rw [map_mul (WittVector.teichmuller p)]
  simp only [map_sub, map_mul, map_one]
  ring

theorem logTeich_one (h : PreTilt.untilt (1 : PreTilt 𝓞_ℂ_[p] p) = 1) : logTeich p h = 0 := by
  have h0 : (0 : AinfP p) ∈ Ith p := Ideal.zero_mem _
  change evalB p (teich_sub_one_mem p h) (logSeries p) = 0
  rw [evalB_congr' p _ h0 (by simp) (logSeries p)]
  rw [show evalB p h0 (logSeries p) = evalB p h0 0 from
    psEval_eq_of_terms (Ith p) h0 h0 _ _ (fun k => ?_), map_zero]
  rcases k with _ | k
  · simp [logSeries]
  · simp

theorem logTeich_pow {x : PreTilt 𝓞_ℂ_[p] p} (hx : PreTilt.untilt x = 1) (n : ℕ)
    (hxn : PreTilt.untilt (x ^ n) = 1) :
    logTeich p hxn = (n : BDeRhamPlus 𝓞_ℂ_[p] p) * logTeich p hx := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul, logTeich_congr p (pow_zero x) hxn (map_one _)]
    exact logTeich_one p _
  | succ n ih =>
    have hxn' : PreTilt.untilt (x ^ n) = 1 := by rw [map_pow, hx, one_pow]
    rw [logTeich_congr p (pow_succ x n) hxn (by rw [map_mul, hxn', hx, one_mul]),
      logTeich_mul p hxn' hx, ih hxn']
    push_cast
    ring

/-- **`log [ε] = b log [ε₀] + p^k z`, `z ∈ A_max`**, when `ε^{(k)} = (ε₀^{(k)})^b`, `b ≤ p^k`:
`ε ε₀^{p^k − b} = η^{p^k}` with `η^♯ = 1`. -/
theorem log_decomp {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {ε : PreTilt 𝓞_ℂ_[p] p}
    (hε : PreTilt.untilt ε = 1) (k b : ℕ) (hbk : b ≤ p ^ k) (hb : root ε₀ k ^ b = root ε k) :
    ∃ z ∈ Amax p, logTeich p hε =
      (b : BDeRhamPlus 𝓞_ℂ_[p] p) * logTeich p h.1 + (p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ k * z := by
  set c := p ^ k - b with hc
  set x := ε * ε₀ ^ c with hx
  set η := (frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[k] x with hη
  have hc0 : PreTilt.untilt (ε₀ ^ c) = 1 := by rw [map_pow, h.1, one_pow]
  have hx1 : PreTilt.untilt x = 1 := by rw [hx, map_mul, hε, hc0, one_mul]
  have hη1 : PreTilt.untilt η = 1 := by
    change root x k = 1
    rw [hx, root_mul, root_npow, ← hb, ← pow_add, hc, Nat.add_sub_cancel' hbk, root_pow, h.1]
  have hηp : η ^ p ^ k = x := iter_pow p k x
  have hηp1 : PreTilt.untilt (η ^ p ^ k) = 1 := by rw [hηp]; exact hx1
  have e1 : logTeich p hx1 = logTeich p hε + (c : BDeRhamPlus 𝓞_ℂ_[p] p) * logTeich p h.1 := by
    rw [logTeich_mul p hε hc0 hx1, logTeich_pow p h.1 c hc0]
  have e2 : logTeich p hηp1 = ((p ^ k : ℕ) : BDeRhamPlus 𝓞_ℂ_[p] p) * logTeich p hη1 :=
    logTeich_pow p hη1 (p ^ k) hηp1
  rw [logTeich_congr p hηp hηp1 hx1] at e2
  refine ⟨logTeich p hη1 - logTeich p h.1,
    Subring.sub_mem _ (logTeich_mem_amax p hη1) (logTeich_mem_amax p h.1), ?_⟩
  have hcast : (c : BDeRhamPlus 𝓞_ℂ_[p] p) = (p : BDeRhamPlus 𝓞_ℂ_[p] p) ^ k - b := by
    rw [hc, Nat.cast_sub hbk]
    push_cast
    ring
  rw [hcast] at e1
  push_cast at e2
  linear_combination (-1 : BDeRhamPlus 𝓞_ℂ_[p] p) * (e2.symm.trans e1)

/-! ## §4. The `p`-adic limit of the exponents -/

omit [Fact p.Prime] in
theorem modEq_of_le (b : ℕ → ℕ) (hb : ∀ k, b (k + 1) ≡ b k [MOD p ^ k]) {k m : ℕ} (hkm : k ≤ m) :
    b m ≡ b k [MOD p ^ k] := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    exact ((hb m).of_dvd (pow_dvd_pow p hkm)).trans ih

theorem exists_padic_limit (b : ℕ → ℕ) (hb : ∀ k, b (k + 1) ≡ b k [MOD p ^ k]) :
    ∃ a : ℤ_[p], ∀ k, a - (b k : ℤ_[p]) ∈ span {(p : ℤ_[p]) ^ k} := by
  have hmem : ∀ k m, k ≤ m → (b m : ℤ_[p]) - (b k : ℤ_[p]) ∈ span {(p : ℤ_[p]) ^ k} := by
    intro k m hkm
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd.mp (modEq_of_le p b hb hkm))
    refine Ideal.mem_span_singleton'.mpr ⟨-(c : ℤ_[p]), ?_⟩
    have := congrArg (fun z : ℤ => (z : ℤ_[p])) hc
    push_cast at this
    linear_combination this
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hcs : CauchySeq (fun k => (b k : ℤ_[p])) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp1)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    calc ‖(b n : ℤ_[p]) - b N‖ ≤ (p : ℝ) ^ (-(N : ℤ)) :=
          (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr (hmem N n hn)
      _ = (p : ℝ)⁻¹ ^ N := by rw [zpow_neg, zpow_natCast, inv_pow]
      _ < ε := hN
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨a, fun k => ?_⟩
  rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
  exact le_of_tendsto (ha.sub_const (b k : ℤ_[p])).norm
    (Filter.eventually_atTop.mpr ⟨k, fun m hm =>
      (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr (hmem k m hm)⟩)

/-! ## §5. `log [ε] = a · log [ε₀]`, `a ∈ ℤ_p` -/

/-- `ℤ_p → W(𝓞_ℂ_p♭) → B_dR^+`. -/
def zpB : ℤ_[p] →+* BDeRhamPlus 𝓞_ℂ_[p] p :=
  (ofLoc p).comp ((algebraMap (Ainf p) (AinfP p)).comp (zpToW p))

theorem zpB_mem (c : ℤ_[p]) : zpB p c ∈ Amax p := by
  refine ⟨PowerSeries.C (zpToW p c), fun k => ⟨1, fun n hn => ?_⟩, ?_⟩
  · beta_reduce
    rw [PowerSeries.coeff_C, ite_eq_right (by omega)]
    exact dvd_zero _
  · change evalB p (omegaP_mem p) (PowerSeries.map (algebraMap (Ainf p) (AinfP p))
      (PowerSeries.C (zpToW p c))) = _
    rw [PowerSeries.map_C]
    exact psEval_C (Ith p) (omegaP_mem p) _

theorem logTeich_eq_mul {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {ε : PreTilt 𝓞_ℂ_[p] p}
    (hε : PreTilt.untilt ε = 1) : ∃ a : ℤ_[p], logTeich p hε = zpB p a * logTeich p h.1 := by
  choose b hblt hb using fun k => exists_pow_eq p h hε k
  have hcompat : ∀ k, b (k + 1) ≡ b k [MOD p ^ k] := by
    intro k
    have hP := isPrimitiveRoot_root p h k
    have hfin : IsOfFinOrder (root ε₀ k) :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ k, pow_pos (Fact.out : p.Prime).pos k, hP.pow_eq_one⟩
    rw [hP.eq_orderOf]
    apply hfin.pow_eq_pow_iff_modEq.mp
    rw [hb k, ← root_succ_pow ε k, ← hb (k + 1), ← root_succ_pow ε₀ k, ← pow_mul, ← pow_mul,
      mul_comm]
  obtain ⟨a, ha⟩ := exists_padic_limit p b hcompat
  refine ⟨a, sub_eq_zero.mp (amax_sep p _ fun k => ?_)⟩
  obtain ⟨z, hz, hlog⟩ := log_decomp p h hε k (b k) (hblt k).le (hb k)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (ha k)
  have hac : a = (b k : ℤ_[p]) + c * (p : ℤ_[p]) ^ k := by linear_combination -hc
  refine ⟨z - zpB p c * logTeich p h.1,
    Subring.sub_mem _ hz (Subring.mul_mem _ (zpB_mem p c) (logTeich_mem_amax p h.1)), ?_⟩
  rw [hlog, hac, map_add, map_mul, map_pow, map_natCast, map_natCast]
  ring

/-! ## §6. `B_max = B_max^+[1/t]` and `B_st = B_max[log [p̃]]` for one `t = log [ε₀]` -/

/-- **`t = log [ε₀] ∈ B_dR`** for a generator `ε₀` of `ℤ_p(1)`. -/
def tOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) : BdR p := toBdR p (logTeich p h.1)

/-- **`B_max = B_max^+[1/t]`** with `t = log [ε₀]` (one `t`), inside `B_dR`. -/
def BmaxOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) : Subalgebra ℚ_[p] (BdR p) :=
  Algebra.adjoin ℚ_[p] (toBdR p '' Amax p ∪ {Ring.inverse (tOf p h)})

/-- **`B_st = B_max[log [p̃]] = B_max^+[1/t][log [p̃]]`** with `t = log [ε₀]`, inside `B_dR`. -/
def BstOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) : Subalgebra ℚ_[p] (BdR p) :=
  Algebra.adjoin ℚ_[p] (toBdR p '' Amax p ∪ {Ring.inverse (tOf p h)} ∪ {toBdR p (logPTilde p)})

theorem ne_one_of_isGenEps {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) : ε₀ ≠ 1 := by
  rintro rfl
  exact h.2 (root_one p 1)

theorem toBdR_zpB (a : ℤ_[p]) :
    toBdR p (zpB p a) = algebraMap ℚ_[p] (BdR p) (algebraMap ℤ_[p] ℚ_[p] a) := by
  change _ = qpToBdR p _
  rw [qpToBdR, RingHom.comp_apply, RingHom.comp_apply, qpToLoc_algebraMap]
  rfl

/-- **Every inverted `log [ε]` is in `B_max^+[1/t]`**: `log [ε] = a t` with `a ∈ ℤ_p ∖ 0`. -/
theorem tInv_mem {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {z : BdR p} (hz : z ∈ tInvSet p) :
    z ∈ BmaxOf p h := by
  obtain ⟨ε, hε, hne, rfl⟩ := hz
  obtain ⟨a, ha⟩ := logTeich_eq_mul p h hε
  set q : ℚ_[p] := algebraMap ℤ_[p] ℚ_[p] a with hqdef
  have hq : q ≠ 0 := by
    intro hq0
    have ha0 : a = 0 := by
      rw [hqdef] at hq0
      exact PadicInt.coe_eq_zero.mp hq0
    apply logTeich_ne_zero p hε hne
    rw [ha, ha0, map_zero, zero_mul]
  have e : toBdR p (logTeich p hε) = algebraMap ℚ_[p] (BdR p) q * tOf p h := by
    rw [ha, map_mul, toBdR_zpB]
    rfl
  rw [e, Ring.mul_inverse_rev' (Commute.all _ _)]
  have hu : IsUnit (algebraMap ℚ_[p] (BdR p) q) := (IsUnit.mk0 q hq).map _
  have h1 : algebraMap ℚ_[p] (BdR p) q * algebraMap ℚ_[p] (BdR p) q⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hq, map_one]
  have hinv : Ring.inverse (algebraMap ℚ_[p] (BdR p) q) = algebraMap ℚ_[p] (BdR p) q⁻¹ :=
    calc Ring.inverse (algebraMap ℚ_[p] (BdR p) q)
        = Ring.inverse (algebraMap ℚ_[p] (BdR p) q) *
            (algebraMap ℚ_[p] (BdR p) q * algebraMap ℚ_[p] (BdR p) q⁻¹) := by rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  rw [hinv]
  exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inr rfl)) (Subalgebra.algebraMap_mem _ _)

/-- **bst-construct's `B_max` (every `log [ε]` inverted) is `B_max^+[1/t]` for one `t = log [ε₀]`.** -/
theorem bmaxOf_eq {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) : BmaxOf p h = Bmax p := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro z (hz | rfl)
    · exact Algebra.subset_adjoin (Or.inl hz)
    · exact Algebra.subset_adjoin (Or.inr ⟨ε₀, h.1, ne_one_of_isGenEps p h, rfl⟩)
  · apply Algebra.adjoin_le
    rintro z (hz | hz)
    · exact Algebra.subset_adjoin (Or.inl hz)
    · exact tInv_mem p h hz

/-- **bst-construct's `B_st` is `B_max^+[1/t][log [p̃]]` for one `t = log [ε₀]`.** -/
theorem bstOf_eq {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) : BstOf p h = Bst p := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro z ((hz | rfl) | rfl)
    · exact Algebra.subset_adjoin (Or.inl (Or.inl hz))
    · exact Algebra.subset_adjoin (Or.inl (Or.inr ⟨ε₀, h.1, ne_one_of_isGenEps p h, rfl⟩))
    · exact Algebra.subset_adjoin (Or.inr rfl)
  · apply Algebra.adjoin_le
    rintro z ((hz | hz) | rfl)
    · exact Algebra.subset_adjoin (Or.inl (Or.inl hz))
    · exact (Algebra.adjoin_mono Set.subset_union_left : BmaxOf p h ≤ BstOf p h) (tInv_mem p h hz)
    · exact Algebra.subset_adjoin (Or.inr rfl)

/-- **A generator exists**: `ε₀ = (1, ζ_p, ζ_{p²}, …)` with `ζ_p` a primitive `p`-th root of unity. -/
theorem exists_isGenEps : ∃ ε₀ : PreTilt 𝓞_ℂ_[p] p, IsGenEps p ε₀ := by
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
  refine ⟨ε, ?_, ?_⟩
  · rw [untilt_eq_of_coeff p c hc ε hx]
    exact Subtype.ext (by simp [c, zetaSeq])
  · rw [root_eq_of_coeff p c hc ε hx 1]
    intro h1
    apply hζ1
    have := congrArg Subtype.val h1
    simpa [c, zetaSeq] using this

/-! ## §7. Potential semistability over `B_max^+[1/t][log [p̃]]`; the restated leaves -/

section Pst

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- **`V` is potentially semistable**, over `B_st = B_max^+[1/t][log [p̃]]` with `t = log [ε₀]`:
`dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V` for some finite `K/ℚ_p` inside `ℚ̄_p`. -/
def IsPstBOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    IsAdmissible p (BstOf p h) K.fixingSubgroup ρ

theorem isPstBOf_iff {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (ρ : GQp p →* GL (Fin n) E) :
    IsPstBOf p h ρ ↔ IsPstB p ρ := by
  unfold IsPstBOf IsPstB IsSemistableB
  rw [bstOf_eq]

/-- A `ℚ̄_p`-valued `ρ` is potentially semistable over `B_max^+[1/t][log [p̃]]` (on a model `E^n`). -/
def LocalIsPstBOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (n : ℕ)
    (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsPstBOf p h ρE

theorem localIsPstBOf_iff {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (n : ℕ)
    (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : LocalIsPstBOf p h n ρ ↔ LocalIsPstB p n ρ := by
  unfold LocalIsPstBOf LocalIsPstB
  simp only [isPstBOf_iff]

end Pst

/-! ## §8. Fontaine's admissibility as printed: `B ⊗_{ℚ_p} V ≅ B^d` with trivial action on the basis -/

section AdmT

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- **`V` is `B`-admissible as a representation of `H`** (Fontaine's definition, Astérisque 223, Exp. III
§1.4-1.5, UNVERIFIED numbering): `B ⊗_{ℚ_p} V` is a free `B`-module with a basis of `H`-invariant vectors, i.e.
`B ⊗_{ℚ_p} V ≅ B^d` as `B`-modules with semilinear `H`-action (trivial on the standard basis of `B^d`). -/
def IsAdmissibleT (B : Subalgebra ℚ_[p] (BdR p)) (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Prop :=
  ∃ (ι : Type) (b : Basis ι B (B ⊗[ℚ_[p]] (Fin n → E))),
    ∀ i, inclT p B (b i) ∈ PanBergerSplit.tensorInv p (PanBergerSplit.bdrLin p) H ρ

theorem inclT_injective (B : Subalgebra ℚ_[p] (BdR p)) :
    Function.Injective (inclT p B (E := E) (n := n)) :=
  have : Module.Free ℚ_[p] (Fin n → E) := Module.Free.of_divisionRing _ _
  have : Module.Flat ℚ_[p] (Fin n → E) := Module.Flat.of_free
  Module.Flat.rTensor_preserves_injective_linearMap (M := Fin n → E) B.val.toLinearMap
    Subtype.val_injective

set_option maxHeartbeats 300000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Admissible (basis form) ⇒ admissible (dimension form)** for a `G_{ℚ_p}`-stable `B ⊆ B_dR`: an invariant
`B`-basis of `B ⊗ V` is a `B^H`-basis of `D_B(V) = (B ⊗ V)^H`, so `dim_{B^H} D_B(V) = rk_B (B ⊗ V) = dim_{ℚ_p} V`. -/
theorem isAdmissible_of_T [FiniteDimensional ℚ_[p] E] (B : Subalgebra ℚ_[p] (BdR p))
    (hB : ∀ σ : GQp p, ∀ x ∈ B, bdrAct p σ x ∈ B) (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E)
    (h : IsAdmissibleT p B H ρ) : IsAdmissible p B H ρ := by
  obtain ⟨ι, b, hb⟩ := h
  have : Nontrivial (BdR p) := by
    have : IsDomain (BdR p) := (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).isDomain
    infer_instance
  have : Module.Free ℚ_[p] (Fin n → E) := Module.Free.of_divisionRing _ _
  have : Module.Finite ℚ_[p] (Fin n → E) := Module.Finite.pi
  have hfinι : Finite ι := Module.Finite.finite_basis b
  have := Fintype.ofFinite ι
  -- `σ` on `B`
  let sB : GQp p → B → B := fun σ c => ⟨bdrAct p σ c, hB σ c c.2⟩
  have hact : ∀ σ ∈ H, ∀ (c : ι → B),
      TensorProduct.map (PanBergerSplit.bdrLin p σ) (PanBergerSplit.vAct p ρ σ)
        (inclT p B (∑ i, c i • b i)) = inclT p B (∑ i, sB σ (c i) • b i) := by
    intro σ hσ c
    rw [map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inclT_smul, inclT_smul, tensorAct_smul, hb i σ hσ]
  have hrepr : ∀ x : B ⊗[ℚ_[p]] (Fin n → E), x = ∑ i, b.repr x i • b i :=
    fun x => (b.sum_repr x).symm
  have hkey : ∀ c : ι → B, ∑ i, c i • b i = 0 → ∀ i, c i = 0 := by
    intro c hc i
    have := congrArg (fun y => b.repr y i) hc
    simpa only [b.repr_sum_self, map_zero, Finsupp.zero_apply] using this
  have hcoef : ∀ x ∈ dB p B H ρ, ∀ σ ∈ H, ∀ i, sB σ (b.repr x i) = b.repr x i := by
    intro x hx σ hσ
    have hx' : inclT p B x ∈ PanBergerSplit.tensorInv p (PanBergerSplit.bdrLin p) H ρ := hx
    have h1 : inclT p B (∑ i, sB σ (b.repr x i) • b i) = inclT p B (∑ i, b.repr x i • b i) := by
      rw [← hact σ hσ, ← hrepr x]
      exact hx' σ hσ
    have h2 := inclT_injective p B h1
    intro i
    have h3 := congrArg (fun y => b.repr y i) h2
    simpa only [b.repr_sum_self] using h3
  let v : ι → dB p B H ρ := fun i => ⟨b i, hb i⟩
  have hliB : LinearIndependent (fixedSub p B H) (fun i => b i) :=
    b.linearIndependent.restrict_scalars (fun r s h => Subtype.ext (by
      have h' : (r : B) * 1 = (s : B) * 1 := h
      rwa [mul_one, mul_one] at h'))
  have hli : LinearIndependent (fixedSub p B H) v :=
    LinearIndependent.of_comp (dB p B H ρ).subtype hliB
  have hsp : ⊤ ≤ Submodule.span (fixedSub p B H) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    have hmem : ∀ i, b.repr x i ∈ fixedSub p B H := fun i σ hσ =>
      congrArg (fun z : B => (z : BdR p)) (hcoef x hx σ hσ i)
    have hx2 : x ∈ Submodule.span (fixedSub p B H) (Set.range b) := by
      rw [hrepr x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have := Submodule.smul_mem (Submodule.span (fixedSub p B H) (Set.range b))
        (⟨b.repr x i, hmem i⟩ : fixedSub p B H) (Submodule.subset_span ⟨i, rfl⟩)
      rwa [Subalgebra.smul_def] at this
    have hspan : Submodule.span (fixedSub p B H) (Set.range b) =
        (Submodule.span (fixedSub p B H) (Set.range v)).map (dB p B H ρ).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hspan] at hx2
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx2
    have hyx' : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← hyx']
    exact hy
  let bD : Basis ι (fixedSub p B H) (dB p B H ρ) := Basis.mk hli hsp
  have : Nontrivial (fixedSub p B H) :=
    ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun z : fixedSub p B H => ((z : B) : BdR p)) h)⟩⟩
  have : Nontrivial B := ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun z : B => (z : BdR p)) h)⟩⟩
  rw [IsAdmissible, Module.finrank_eq_card_basis bD,
    ← Module.finrank_baseChange (R := B) (S := ℚ_[p]) (M' := Fin n → E),
    Module.finrank_eq_card_basis b]

/-- **`V` is potentially semistable**, Fontaine's admissibility as printed: for some finite `K/ℚ_p` inside `ℚ̄_p`,
`B_st ⊗_{ℚ_p} V` has a `B_st`-basis of `G_K`-invariant vectors (`B_st = B_max^+[1/t][log [p̃]]`, `t = log [ε₀]`). -/
def IsPstT {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    IsAdmissibleT p (BstOf p h) K.fixingSubgroup ρ

theorem bstOf_stable {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (σ : GQp p) (x : BdR p)
    (hx : x ∈ BstOf p h) : bdrAct p σ x ∈ BstOf p h := by
  rw [bstOf_eq] at hx ⊢
  exact bst_stable p σ hx

/-- **Basis form ⇒ dimension form** of potential semistability. -/
theorem isPstBOf_of_T [FiniteDimensional ℚ_[p] E] {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀)
    (ρ : GQp p →* GL (Fin n) E) (hT : IsPstT p h ρ) : IsPstBOf p h ρ := by
  obtain ⟨K, hK, hadm⟩ := hT
  exact ⟨K, hK, isAdmissible_of_T p (BstOf p h) (bstOf_stable p h) _ ρ hadm⟩

end AdmT

end BmaxOne

namespace PanDict

open BmaxOne BergerBst PanBergerSplit

/-- **Berger, Théorème 0.7, printed form, with `B_max = B_max^+[1/t]` for one `t`** (L. Berger,
*Représentations p-adiques et équations différentielles*, Invent. Math. 148 (2002), 219-284;
Théorème 0.7 = Corollaire 5.22 of the published version (locator audit row R11) = Théorème 0.6 =
Théorème 5.19 of arXiv:math/0102179v3), at `K = ℚ_p`: a de Rham `p`-adic representation of `G_{ℚ_p}`
is potentially semistable. Stated for every generator `ε₀ = (1, ζ_p, ζ_{p²}, …)` of `ℤ_p(1)` in
`𝓞_ℂ_p♭` (`IsGenEps`), with `t = log [ε₀]` and
`B_st = B_max[log [p̃]]`, `B_max = B_max^+[1/t]`, `B_max^+ = A_max[1/p]`,
`A_max = {Σ a_n (ω/p)^n : a_n ∈ A_inf, a_n → 0}` inside Mathlib's `B_dR` (`BstOf`). `V = E^n` for a finite
`E/ℚ_p` inside `ℚ̄_p` with a continuous `ρ : G_{ℚ_p} → GL_n(E)`:

* de Rham: `dim_{ℚ_p} (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}} = dim_{ℚ_p} V` (`IsDeRhamU`);
* potentially semistable: `dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V` for some finite
  `K/ℚ_p` (`IsPstBOf`). -/
def BergerPrintedVt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (n : ℕ)
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ρE : GQp p →* GL (Fin n) E),
    Continuous ρE → IsDeRhamU p ρE → IsPstBOf p h ρE

/-- **pb-fix3's `BergerPrintedV` from the one-`t` form** (`bstOf_eq`; a generator exists). -/
theorem bergerPrintedV_of_t (hB : BergerPrintedVt) : BergerPrintedV := by
  intro p _ n E _ ρE hc hdr
  obtain ⟨ε₀, h⟩ := exists_isGenEps p
  exact (isPstBOf_iff p h ρE).mp (hB p ε₀ h n E ρE hc hdr)

/-- **Berger, Théorème 0.7, printed form: one `t`, and Fontaine's admissibility in its basis form** (L. Berger,
*Représentations p-adiques et équations différentielles*, Invent. Math. 148 (2002), 219-284; Théorème 0.7 =
Corollaire 5.22 of the published version (locator audit row R11) = Théorème 0.6 = Théorème 5.19 of
arXiv:math/0102179v3), at `K = ℚ_p`: a de Rham `p`-adic representation of `G_{ℚ_p}` is potentially semistable.
For every generator `ε₀ = (1, ζ_p, ζ_{p²}, …)` of `ℤ_p(1)` (`IsGenEps`), `t = log [ε₀]`,
`B_st = B_max[log [p̃]]`, `B_max = B_max^+[1/t]`, `B_max^+ = A_max[1/p]`,
`A_max = {Σ a_n (ω/p)^n : a_n ∈ A_inf, a_n → 0}` inside Mathlib's `B_dR` (`BstOf`). `V = E^n`, `E/ℚ_p` finite inside
`ℚ̄_p`, `ρ : G_{ℚ_p} → GL_n(E)` continuous:

* de Rham: `dim_{ℚ_p} (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}} = dim_{ℚ_p} V` (`IsDeRhamU`);
* potentially semistable (Fontaine, Astérisque 223, Exp. III §1.4-1.5 (numbering UNVERIFIED): `V|_{G_K}` is
  `B_st`-admissible, i.e. `B_st ⊗_{ℚ_p} V ≅ B_st^d` with `G_K` acting trivially on the basis): for some finite
  `K/ℚ_p`, `B_st ⊗_{ℚ_p} V` has a `B_st`-basis of `G_K`-invariant vectors (`IsPstT`). -/
def BergerPrintedVT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (n : ℕ)
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (ρE : GQp p →* GL (Fin n) E),
    Continuous ρE → IsDeRhamU p ρE → IsPstT p h ρE

/-- `BergerPrintedVt` (dimension form) from the basis form (`isPstBOf_of_T`). -/
theorem bergerPrintedVt_of_T (hB : BergerPrintedVT) : BergerPrintedVt := fun p _ ε₀ h n E _ ρE hc hdr =>
  isPstBOf_of_T p h ρE (hB p ε₀ h n E ρE hc hdr)

/-- **pb-fix3's `BergerPrintedV` from the one-`t`, basis-form leaf.** -/
theorem bergerPrintedV_of_T (hB : BergerPrintedVT) : BergerPrintedV :=
  bergerPrintedV_of_t (bergerPrintedVt_of_T hB)

/-- **Pan, Theorem 1.0.4, printed form, with `B_max = B_max^+[1/t]` for one `t`**: `PanPrintedP` with
potential semistability over `B_st = B_max^+[1/t][log [p̃]]`, `t = log [ε₀]`, for every generator `ε₀`
(`LocalIsPstBOf`); everything else as `PanPrintedP` (L. Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169,
Theorem 1.0.4 = arXiv:1901.07166v2 Theorem 1.0.4 with Conjecture 1.0.1; JAMS numbering UNVERIFIED). -/
def PanPrintedPt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀)
    (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    IsIrreducibleP ρ → ρ.FinitelyRamified → LocalIsPstBOf p h 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTP p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (_ : NeZero N) (k : ℤ) (g : HeckeRing.GL2.EigenformAwayFromLevel N k)
      (ρg : GaloisRep p 2) (ψ : GaloisChar p),
      IsAttachedVia p ιp g ρg ∧ IsTwistOf p ρ ρg ψ

/-- **pb-fix3's `PanPrintedP` from the one-`t` form** (`localIsPstBOf_iff`; a generator exists). -/
theorem panPrintedP_of_t (hP : PanPrintedPt) : PanPrintedP := by
  intro p _ hp ιp ρ hirr hfr hpst hodd hht
  obtain ⟨ε₀, h⟩ := exists_isGenEps p
  exact hP p hp ε₀ h ιp ρ hirr hfr ((localIsPstBOf_iff p h 2 _).mpr hpst) hodd hht

end PanDict
end PkgI4
end HDec



noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace HTFinite

open Module PanBergerSplit
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

/-- `ℂ_p^{G_{ℚ_p}} = ℚ_p` (Ax–Sen–Tate at `K = ℚ_p`). -/
theorem fixed_eq_algebraMap (c : ℂ_[p]) (hc : ∀ σ : GQp p, cpAct p σ c = c) :
    ∃ q : ℚ_[p], c = algebraMap ℚ_[p] ℂ_[p] q := by
  obtain ⟨y, hy⟩ := ZInQ.Contrib.CloudB3W11.axSenTate_proof p
    (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) c (fun σ _ => hc σ)
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp y.2
  refine ⟨q, ?_⟩
  rw [hy, ← hq, IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq]

section Descent

variable {M : Type*} [AddCommGroup M] [Module ℂ_[p] M] [Module ℚ_[p] M]
  [IsScalarTower ℚ_[p] ℂ_[p] M]

open Classical in
/-- **Galois descent for `ℂ_p`-semilinear actions**: if `T σ` is additive and `σ`-semilinear, every
`ℂ_p`-linear relation among `T`-invariant vectors comes from a nonzero `ℚ_p`-linear relation. -/
theorem exists_rat_relation (T : GQp p → M →+ M)
    (hT : ∀ σ (c : ℂ_[p]) (x : M), T σ (c • x) = cpAct p σ c • T σ x)
    {ι : Type*} [Fintype ι] (x : ι → M) (hx : ∀ σ i, T σ (x i) = x i) :
    ∀ (N : ℕ) (c : ι → ℂ_[p]), (Finset.univ.filter fun i => c i ≠ 0).card = N → c ≠ 0 →
      ∑ i, c i • x i = 0 → ∃ q : ι → ℚ_[p], q ≠ 0 ∧ ∑ i, q i • x i = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro c hcard hc0 hrel
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc0 (funext h)
  set c' : ι → ℂ_[p] := fun i => (c j)⁻¹ * c i with hc'
  have hc'j : c' j = 1 := inv_mul_cancel₀ hj
  have hrel' : ∑ i, c' i • x i = 0 := by
    simp only [hc', mul_smul, ← Finset.smul_sum, hrel, smul_zero]
  have hsupp' : ∀ i, c' i ≠ 0 ↔ c i ≠ 0 := fun i => by
    simp only [hc', ne_eq, mul_eq_zero, inv_eq_zero, hj, false_or]
  rcases Classical.em (∀ σ i, cpAct p σ (c' i) = c' i) with hfix | hfix
  · choose q hq using fun i => fixed_eq_algebraMap p (c' i) (fun σ => hfix σ i)
    refine ⟨q, fun h0 => ?_, ?_⟩
    · have := hq j
      rw [hc'j, congrFun h0 j, Pi.zero_apply, map_zero] at this
      exact one_ne_zero this
    · rw [← hrel']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hq i, algebraMap_smul]
  · push Not at hfix
    obtain ⟨σ, i₀, hi₀⟩ := hfix
    set d : ι → ℂ_[p] := fun i => cpAct p σ (c' i) - c' i with hd
    have hdrel : ∑ i, d i • x i = 0 := by
      have h1 : T σ (∑ i, c' i • x i) = ∑ i, cpAct p σ (c' i) • x i := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hT, hx]
      rw [hrel', map_zero] at h1
      simp only [hd, sub_smul, Finset.sum_sub_distrib, ← h1, hrel', sub_zero]
    have hdj : d j = 0 := by simp only [hd, hc'j, map_one, sub_self]
    have hd0 : d ≠ 0 := fun h0 => hi₀ (sub_eq_zero.mp (congrFun h0 i₀))
    have hsub : (Finset.univ.filter fun i => d i ≠ 0) ⊂ (Finset.univ.filter fun i => c i ≠ 0) := by
      refine Finset.ssubset_iff_of_subset (fun i hi => ?_) |>.mpr ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        rw [← hsupp']
        intro h0
        apply hi
        simp only [hd, h0, map_zero, sub_zero]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdj, ne_eq, not_true_eq_false,
          not_false_eq_true]
    exact ih _ (hcard ▸ Finset.card_lt_card hsub) d rfl hd0 hdrel

/-- `ℚ_p`-linearly independent invariant vectors are `ℂ_p`-linearly independent. -/
theorem linearIndependent_of_invariant (T : GQp p → M →+ M)
    (hT : ∀ σ (c : ℂ_[p]) (x : M), T σ (c • x) = cpAct p σ c • T σ x)
    {ι : Type*} [Fintype ι] (x : ι → M) (hx : ∀ σ i, T σ (x i) = x i)
    (hli : LinearIndependent ℚ_[p] x) : LinearIndependent ℂ_[p] x := by
  classical
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  obtain ⟨q, hq0, hq⟩ := exists_rat_relation p T hT x hx _ c rfl
    (fun h0 => hi (congrFun h0 i)) hc
  exact hq0 (funext (hli q hq))

/-- **The invariants are finite-dimensional over `ℚ_p`**, of dimension `≤ dim_{ℂ_p} M`. -/
theorem finrank_invariants_le [Module.Finite ℂ_[p] M] (T : GQp p → M →+ M)
    (hT : ∀ σ (c : ℂ_[p]) (x : M), T σ (c • x) = cpAct p σ c • T σ x)
    (W : Submodule ℚ_[p] M) (hW : ∀ w ∈ W, ∀ σ, T σ w = w) :
    FiniteDimensional ℚ_[p] W ∧ finrank ℚ_[p] W ≤ finrank ℂ_[p] M := by
  have hbound : ∀ s : Finset W, (LinearIndependent ℚ_[p] fun i : s => (i : W)) →
      s.card ≤ finrank ℂ_[p] M := by
    intro s hs
    have h1 : LinearIndependent ℚ_[p] fun i : s => ((i : W) : M) :=
      hs.map' W.subtype (Submodule.ker_subtype W)
    have h2 := linearIndependent_of_invariant p T hT (fun i : s => ((i : W) : M))
      (fun σ i => hW _ (i : W).2 σ) h1
    simpa using h2.fintype_card_le_finrank
  have hrank := rank_le hbound
  have hfin : FiniteDimensional ℚ_[p] W :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0)
  refine ⟨hfin, ?_⟩
  have := Module.finrank_le_of_rank_le hrank
  exact this

end Descent

/-! ## The Hodge–Tate spaces -/

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- `σ` on `ℂ_p(w) ⊗ V` is `σ`-semilinear for the `ℂ_p`-structure on the first factor. -/
theorem tensorAct_smul (ρ : GQp p →* GL (Fin n) E) (w : ℤ) (σ : GQp p) (c : ℂ_[p])
    (x : ℂ_[p] ⊗[ℚ_[p]] (Fin n → E)) :
    TensorProduct.map (htLin p w σ) (vAct p ρ σ) (c • x) =
      cpAct p σ c • TensorProduct.map (htLin p w σ) (vAct p ρ σ) x := by
  induction x using TensorProduct.inductionOn with
  | tmul z v =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul]
    congr 1
    change (cycPow p σ w • cpLin p σ) (c * z) = cpAct p σ c * (cycPow p σ w • cpLin p σ) z
    rw [LinearMap.smul_apply, LinearMap.smul_apply]
    change cycPow p σ w • cpAct p σ (c * z) = cpAct p σ c * (cycPow p σ w • cpAct p σ z)
    rw [map_mul, mul_smul_comm]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **`(ℂ_p(w) ⊗_{ℚ_p} V)^{G_{ℚ_p}}` is finite-dimensional over `ℚ_p`**, of dimension `≤ dim_{ℚ_p} V`. -/
theorem finiteDimensional_htU [FiniteDimensional ℚ_[p] E] (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    FiniteDimensional ℚ_[p] (htU p ρ w) ∧ finrank ℚ_[p] (htU p ρ w) ≤ finrank ℚ_[p] (Fin n → E) := by
  have h := finrank_invariants_le p
    (fun σ => (TensorProduct.map (htLin p w σ) (vAct p ρ σ)).toAddMonoidHom)
    (fun σ c x => tensorAct_smul p ρ w σ c x) (htU p ρ w)
    (fun x hx σ => hx σ (Subgroup.mem_top σ))
  have : Module.Free ℚ_[p] (Fin n → E) := Module.Free.of_divisionRing _ _
  have hM : finrank ℂ_[p] (ℂ_[p] ⊗[ℚ_[p]] (Fin n → E)) = finrank ℚ_[p] (Fin n → E) :=
    Module.finrank_baseChange
  exact ⟨h.1, hM ▸ h.2⟩

/-- **P2: `htSpaceE ρ w = (V ⊗_{ℚ_p} ℂ_p(w))^{G_{ℚ_p}}` is finite-dimensional over `E`**, so `htMultE ρ w` is its
genuine dimension. -/
theorem finiteDimensional_htSpaceE [FiniteDimensional ℚ_[p] E] (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    FiniteDimensional E (PanDict.htSpaceE p ρ w) := by
  have h1 : FiniteDimensional ℚ_[p] (htU p ρ w) := (finiteDimensional_htU p ρ w).1
  have h2 : FiniteDimensional ℚ_[p] ((PanDict.htSpaceE p ρ w).restrictScalars ℚ_[p]) := by
    rw [← PanDict.map_comm_htU]
    exact Module.Finite.map _ _
  have : Module.Finite ℚ_[p] (PanDict.htSpaceE p ρ w) :=
    Module.Finite.equiv (((PanDict.htSpaceE p ρ w).restrictScalarsEquiv ℚ_[p]).restrictScalars ℚ_[p])
  exact Module.Finite.of_restrictScalars_finite ℚ_[p] E _

/-- **`dim_E (V ⊗ ℂ_p(w))^{G_{ℚ_p}} ≤ n`**: the Hodge–Tate multiplicities are bounded by the dimension. -/
theorem htMultE_le [FiniteDimensional ℚ_[p] E] (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    PanDict.htMultE p ρ w ≤ n := by
  rw [PanDict.htMultE_eq_htMultU, htMultU]
  have h := (finiteDimensional_htU p ρ w).2
  rw [finrank_fun] at h
  exact Nat.div_le_of_le_mul (by linarith)

end HTFinite
end PkgI4
end HDec

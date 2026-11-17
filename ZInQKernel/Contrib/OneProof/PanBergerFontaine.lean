import ZInQKernel.Contrib.OneProof.PanBergerPst

/-!
Copyright: this file is part of the fork Deicyde/diophantine-z-q (task pb-p1, 2026-11-17; restated in place by task
pb-dimform, 2026-11-17). Reports `docs/research/pb-p1.md` and `docs/research/pb-dimform.md`; first generated from
`scratch/pb-p1/FontaineSt.lean.txt` by `scratch/pb-p1/mkcontrib.py`, then edited in place by pb-dimform.

# pb-p1 / pb-dimform: Fontaine's `B_st = B_cris[log [p̃]]`, and the two leaves of `r11r12` over it

Fontaine's rings inside Mathlib's `B_dR`, at definition level as in Brinon-Conrad, *CMI summer school notes on p-adic
Hodge theory* (preliminary version June 24, 2009; cited in the manuscript as `brinon-conrad`), with the same objects in
Berger's survey *An introduction to the theory of p-adic representations* (arXiv:math/0210184v1, II.2.2 p. 11, II.2.3
p. 12, II.3.1 p. 13, II.3.3 pp. 14-15; not in the manuscript's bibliography):

* `A_cris = {Σ a_n ω^n/n! : a_n ∈ A_inf, a_n → 0 p-adically}` (Brinon-Conrad p. 129; `AcrisOf w`, for a generator `w`
  of `ker θ`), and `B_cris^+` the `ℚ_p`-algebra it generates (`BcrisPlusOf`);
* `B_cris = B_cris^+[1/t]`, `t = log [ε]` (Brinon-Conrad Def. 9.1.4 p. 131; `BcrisOf`);
* `B_st = B_cris[log [p̃]]` with `log [p̃] = log_dR([p̃]/p) = −Σ (1 − [p̃]/p)^n/n`, `log(p) = 0` (Brinon-Conrad
  Def. 9.2.3 p. 138, p. 142, Thm 9.2.10 p. 143; `BstFOf`), which is bst-construct's `logPTilde`;
* admissibility in Fontaine's dimension form (Brinon-Conrad §5.2 pp. 67-68; bst-construct's `IsAdmissible`) and
  potential semistability (Brinon-Conrad Thm 9.3.5 p. 148; `IsPstF`, pb-dimform).

Proved: `A_cris` is a ring and `B_cris^+` is exactly the printed set `{Σ x_n ω^n/n! : x_n ∈ B̃^+, x_n → 0}`
(`acrisOf_mul`, `bcrisPlusOf_eq_set`), `B_st` is `G_{ℚ_p}`-stable (`bstF_stable`), `A_cris ⊆ A_max` (`acrisOf_le_amaxOf`,
from `p^n/n! ∈ ℤ_p`), `A_cris` does not depend on the generator (`acrisOf_le`, `acrisOf_eq`, `bstFOf_eq_xi`),
`B_st^{Fontaine} ⊆ B_st^{tree}` (`bstFOf_le`), the basis form of admissibility passes from a subring to a larger one
(`isAdmissibleT_mono`) and implies the dimension form (`isPstF_of_basis`). Pan's theorem and Berger's theorem, both
with Fontaine's pst in the dimension form, give `r11r12 : PanBerger` directly (`panBerger_of_F`: the predicate is passed
from Berger's conclusion to Pan's hypothesis, with no comparison of rings and no dimension-to-basis step).
pb-p1's basis-form leaves are kept as `BergerSurveyFBasis` and `PanPrintedFBasis` (`bergerSurveyF_of_basis`,
`panPrintedFBasis_of_F` compare them with the new ones).
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace HDec
namespace PkgI4
namespace FontaineSt

open Module PowerSeries Ideal
open scoped TensorProduct
open BergerBst BmaxOne
open PanBergerSplit (Ainf AinfP theta)

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## §1. `p^n/n! ∈ ℤ_p` -/

theorem factorial_val_le (n v m : ℕ) (hpm : ¬ p ∣ m) (h : n.factorial = p ^ v * m) : v ≤ n := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)
  have hval : padicValNat p n.factorial = v := by
    rw [h, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hpm, add_zero]
  have h1 := sub_one_mul_padicValNat_factorial (p := p) n
  rw [hval] at h1
  have h2 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have h3 : v ≤ (p - 1) * v := Nat.le_mul_of_pos_left v h2
  omega

theorem exists_dpCoeff (n : ℕ) : ∃ e : ℤ_[p], (e : ℚ_[p]) * (n.factorial : ℚ_[p]) = (p : ℚ_[p]) ^ n := by
  obtain ⟨v, m, hpm, hvm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) p hp.out.ne_one
  have hu : IsUnit (m : ℤ_[p]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm))
  have hv : v ≤ n := factorial_val_le p n v m hpm hvm
  refine ⟨(p : ℤ_[p]) ^ (n - v) * ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ?_⟩
  have hum : ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (m : ℤ_[p]) = 1 := hu.val_inv_mul
  have hum' : (((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (m : ℚ_[p]) = 1 := by
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hum
    rwa [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_one] at this
  rw [hvm]
  push_cast
  calc ((p : ℚ_[p]) ^ (n - v) * (((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) *
        ((p : ℚ_[p]) ^ v * (m : ℚ_[p]))
      = (p : ℚ_[p]) ^ (n - v) * (p : ℚ_[p]) ^ v *
          ((((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (m : ℚ_[p])) := by ring
    _ = (p : ℚ_[p]) ^ n := by rw [hum', mul_one, ← pow_add, Nat.sub_add_cancel hv]

/-- `p^n/n! ∈ ℤ_p`. -/
def dpCoeff (n : ℕ) : ℤ_[p] := Classical.choose (exists_dpCoeff p n)

theorem dpCoeff_spec (n : ℕ) : (dpCoeff p n : ℚ_[p]) * (n.factorial : ℚ_[p]) = (p : ℚ_[p]) ^ n :=
  Classical.choose_spec (exists_dpCoeff p n)

/-- `1/n! = (p^n/n!) · p^{−n}` in `ℚ_p`. -/
theorem inv_factorial_eq (n : ℕ) :
    ((n.factorial : ℚ_[p]))⁻¹ = (dpCoeff p n : ℚ_[p]) * ((p : ℚ_[p])⁻¹) ^ n := by
  have h1 := dpCoeff_spec p n
  have hn' : (n.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hp' : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have he : (dpCoeff p n : ℚ_[p]) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact pow_ne_zero _ hp' h1.symm
  rw [inv_pow, ← h1, mul_inv, ← mul_assoc, mul_inv_cancel₀ he, one_mul]

/-! ## §2. `A_cris`, `B_cris^+`, `B_cris`, `B_st` (Brinon-Conrad pp. 128-143; Berger 2004, II.3.1 and II.3.3) -/

theorem algebraMap_mem_ith {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    algebraMap (Ainf p) (AinfP p) w ∈ Ith p := by
  have hk : w ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := hw
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, rfl⟩ := hk
  rw [map_mul]
  have : algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) ∈ Ith p := by
    have h := xi'_mem p
    exact h
  exact Ideal.mul_mem_left _ _ this

/-- The divided-power series `Σ a_n X^n / n!` of `Σ a_n X^n`, over `W(𝓞_ℂ_p♭)[1/p]`. -/
def dpSeries (f : (Ainf p)⟦X⟧) : (AinfP p)⟦X⟧ :=
  PowerSeries.mk fun n => algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff n f) *
    qpToLoc p (((n.factorial : ℕ) : ℚ_[p]))⁻¹

/-- **`A_cris`** (Brinon-Conrad, CMI notes, preliminary version June 24, 2009, p. 129, with p. 128: generated by the
divided powers of any generator of `ker θ`; also Berger's survey arXiv:math/0210184v1 II.3.1 p. 13, which does not name
the topology): the elements `Σ a_n ω^n/n!` of `B_dR^+`, `ω` a generator of `ker θ`, `a_n ∈ A_inf = W(𝓞_ℂ_p♭)` tending
to `0` for the `p`-adic topology (as on Brinon-Conrad p. 129), the series evaluated `ker θ`-adically. -/
def AcrisOf (w : Ainf p) (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : Set (BDeRhamPlus 𝓞_ℂ_[p] p) :=
  {x | ∃ f ∈ restricted p, x = evalB p (algebraMap_mem_ith p hw) (dpSeries p f)}

/-- **`B_cris^+ = A_cris[1/p]`** (Brinon-Conrad Def. 9.1.4 p. 131): the `ℚ_p`-algebra generated by `A_cris` in
`B_dR`; it is exactly the set `{Σ x_n ω^n/n! : x_n ∈ B̃^+ = A_inf[1/p], x_n → 0}` printed in Berger's survey II.3.1
(`bcrisPlusOf_eq_set` with `p^{−k} A_cris`, and pb-dimform's `bcrisPlusOf_eq_printed` with the literal set). -/
def BcrisPlusOf (w : Ainf p) (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : Subalgebra ℚ_[p] (BdR p) :=
  Algebra.adjoin ℚ_[p] (toBdR p '' AcrisOf p w hw)

/-- **`B_cris = B_cris^+[1/t] = A_cris[1/t]` inside `B_dR`**, `t = log [ε₀]` (Brinon-Conrad Def. 9.1.4 p. 131; also
Berger's survey II.3.1, II.2.3). -/
def BcrisOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : Subalgebra ℚ_[p] (BdR p) :=
  Algebra.adjoin ℚ_[p] (toBdR p '' AcrisOf p w hw ∪ {Ring.inverse (tOf p h)})

/-- **Fontaine's `B_st = B_cris[log [p̃]] ⊆ B_dR`** (Brinon-Conrad Def. 9.2.3 p. 138, `B_st = B_cris[X]` abstractly,
embedded in `B_dR` on p. 142 by `X ↦ log([q]) = log_dR([q]/q) + log_K(q)`, canonical once `log_K(p)` is fixed (p. 143),
injective by Thm 9.2.10 p. 143; here `q = p`, `q̃ = p̃ = (p, p^{1/p}, …)`, `log(p) = 0`, so the image is
`B_cris[log_dR([p̃]/p)]` with `log_dR([p̃]/p) = −Σ_{n ≥ 1} (1 − [p̃]/p)^n/n`, the tree's `logPTilde`). Berger's survey
II.3.3 pp. 14-15 prints the same embedding with two misprints (the series with exponent `n − 1` for `n`, and
`φ(Y) = Y^p` for `pY`; neither affects this definition, which has exponent `n` and no Frobenius). -/
def BstFOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : Subalgebra ℚ_[p] (BdR p) :=
  Algebra.adjoin ℚ_[p] (toBdR p '' AcrisOf p w hw ∪ {Ring.inverse (tOf p h)} ∪ {toBdR p (logPTilde p)})

theorem bcrisPlusOf_le_bcrisOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : BcrisPlusOf p w hw ≤ BcrisOf p h w hw :=
  Algebra.adjoin_mono Set.subset_union_left

theorem bcrisOf_le_bstFOf {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : BcrisOf p h w hw ≤ BstFOf p h w hw :=
  Algebra.adjoin_mono Set.subset_union_left

/-! ## §2b. `A_cris` is a ring, and `B_cris^+` is the printed set `{Σ x_n ω^n/n! : x_n ∈ B̃^+, x_n → 0}` -/

/-- Coefficients of the product of two divided-power series: `c_k = Σ_{i+j=k} C(k,i) a_i b_j`. -/
def dpMul (f g : (Ainf p)⟦X⟧) : (Ainf p)⟦X⟧ :=
  PowerSeries.mk fun k => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k,
    (k.choose ij.1 : Ainf p) * PowerSeries.coeff ij.1 f * PowerSeries.coeff ij.2 g

theorem dpSeries_mul (f g : (Ainf p)⟦X⟧) : dpSeries p f * dpSeries p g = dpSeries p (dpMul p f g) := by
  ext k
  rw [PowerSeries.coeff_mul]
  simp only [dpSeries, dpMul, PowerSeries.coeff_mk]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  have key : qpToLoc p (((ij.1.factorial : ℕ) : ℚ_[p]))⁻¹ * qpToLoc p (((ij.2.factorial : ℕ) : ℚ_[p]))⁻¹ =
      qpToLoc p ((k.choose ij.1 : ℕ) : ℚ_[p]) * qpToLoc p (((k.factorial : ℕ) : ℚ_[p]))⁻¹ := by
    rw [← map_mul, ← map_mul]
    congr 1
    have h := Nat.choose_mul_factorial_mul_factorial (show ij.1 ≤ k by omega)
    have h2 : k - ij.1 = ij.2 := by omega
    rw [h2] at h
    have h1 : (ij.1.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2' : (ij.2.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hk : (k.factorial : ℚ_[p]) = (k.choose ij.1 : ℚ_[p]) * ij.1.factorial * ij.2.factorial := by
      exact_mod_cast h.symm
    have hC : (k.choose ij.1 : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    rw [hk]
    field_simp
  have hc : ((k.choose ij.1 : ℕ) : AinfP p) = qpToLoc p ((k.choose ij.1 : ℕ) : ℚ_[p]) := (map_natCast _ _).symm
  simp only [map_mul, map_natCast]
  rw [hc]
  linear_combination (algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff ij.1 f) *
    algebraMap (Ainf p) (AinfP p) (PowerSeries.coeff ij.2 g)) * key

theorem dpMul_mem {f g : (Ainf p)⟦X⟧} (hf : f ∈ restricted p) (hg : g ∈ restricted p) :
    dpMul p f g ∈ restricted p := fun k => by
  obtain ⟨N, hN⟩ := hf k
  obtain ⟨M, hM⟩ := hg k
  refine ⟨N + M, fun n hn => ?_⟩
  change (p : Ainf p) ^ k ∣ PowerSeries.coeff n (dpMul p f g)
  rw [dpMul, PowerSeries.coeff_mk]
  refine Finset.dvd_sum fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hi : N ≤ ij.1
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (hN _ hi) _) _
  · exact Dvd.dvd.mul_left (hM _ (by omega)) _

theorem dpSeries_add (f g : (Ainf p)⟦X⟧) : dpSeries p (f + g) = dpSeries p f + dpSeries p g := by
  ext n
  simp only [dpSeries, PowerSeries.coeff_mk, map_add, add_mul]

theorem dpSeries_C (a : Ainf p) :
    dpSeries p (PowerSeries.C a) = PowerSeries.C (algebraMap (Ainf p) (AinfP p) a) := by
  ext n
  simp only [dpSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C]
  split_ifs with hn
  · subst hn
    simp
  · simp

theorem C_mem_restricted (a : Ainf p) : PowerSeries.C a ∈ restricted p := fun k => ⟨1, fun n hn => by
  change (p : Ainf p) ^ k ∣ PowerSeries.coeff n (PowerSeries.C a)
  rw [PowerSeries.coeff_C, if_neg (by omega)]
  exact dvd_zero _⟩

theorem acrisOf_mul {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) {x y : BDeRhamPlus 𝓞_ℂ_[p] p}
    (hx : x ∈ AcrisOf p w hw) (hy : y ∈ AcrisOf p w hw) : x * y ∈ AcrisOf p w hw := by
  obtain ⟨f, hf, rfl⟩ := hx
  obtain ⟨g, hg, rfl⟩ := hy
  exact ⟨dpMul p f g, dpMul_mem p hf hg, by rw [← map_mul, dpSeries_mul]⟩

theorem acrisOf_add {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) {x y : BDeRhamPlus 𝓞_ℂ_[p] p}
    (hx : x ∈ AcrisOf p w hw) (hy : y ∈ AcrisOf p w hw) : x + y ∈ AcrisOf p w hw := by
  obtain ⟨f, hf, rfl⟩ := hx
  obtain ⟨g, hg, rfl⟩ := hy
  exact ⟨f + g, Subring.add_mem _ hf hg, by rw [dpSeries_add, map_add]⟩

theorem acrisOf_zpB {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) (z : ℤ_[p]) :
    zpB p z ∈ AcrisOf p w hw :=
  ⟨PowerSeries.C (zpToW p z), C_mem_restricted p _, by
    rw [dpSeries_C]
    exact (psEval_C (Ith p) (algebraMap_mem_ith p hw) _).symm⟩

/-- The set printed in Berger 2004 II.3.1: `{Σ x_n ω^n/n! : x_n ∈ B̃^+ = A_inf[1/p], x_n → 0}`, i.e. `p^{−k} A_cris`. -/
def BcrisPlusSet (w : Ainf p) (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : Set (BdR p) :=
  {x | ∃ (k : ℕ) (y : BDeRhamPlus 𝓞_ℂ_[p] p), y ∈ AcrisOf p w hw ∧ x = ((p : ℚ_[p])⁻¹ ^ k) • toBdR p y}

theorem exists_pow_mul_mem (c : ℚ_[p]) : ∃ k : ℕ, ‖(p : ℚ_[p]) ^ k * c‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖c‖ (show (1 : ℝ) < p by exact_mod_cast hp.out.one_lt)
  refine ⟨k, ?_⟩
  rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by exact_mod_cast hp.out.pos) k
  rw [inv_mul_le_iff₀ hpk, mul_one]
  exact hk.le

/-- **`B_cris^+` (the `ℚ_p`-algebra generated by `A_cris`) is exactly the printed set `p^{−k} A_cris`.** -/
theorem bcrisPlusOf_eq_set {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    (BcrisPlusOf p w hw : Set (BdR p)) = BcrisPlusSet p w hw := by
  have hpB : ∀ k : ℕ, ∀ y ∈ AcrisOf p w hw, (p : ℚ_[p]) ^ k • toBdR p y ∈ toBdR p '' AcrisOf p w hw := by
    intro k y hy
    refine ⟨zpB p ((p : ℤ_[p]) ^ k) * y, acrisOf_mul p hw (acrisOf_zpB p hw _) hy, ?_⟩
    rw [map_mul, toBdR_zpB, Algebra.smul_def]
    congr 2
  apply Set.Subset.antisymm
  · intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨0, y, hy, by rw [pow_zero, one_smul]⟩
    | algebraMap c =>
      obtain ⟨k, hk⟩ := exists_pow_mul_mem p c
      let z : ℤ_[p] := ⟨_, (PadicInt.mem_subring_iff p).mpr hk⟩
      refine ⟨k, zpB p z, acrisOf_zpB p hw z, ?_⟩
      rw [toBdR_zpB, Algebra.smul_def, ← map_mul]
      congr 1
      change c = (p : ℚ_[p])⁻¹ ^ k * ((p : ℚ_[p]) ^ k * c)
      have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, one_mul]
    | add x y _ _ hx hy =>
      obtain ⟨k, a, ha, rfl⟩ := hx
      obtain ⟨l, b, hb, rfl⟩ := hy
      obtain ⟨a', ha', ea⟩ := hpB l a ha
      obtain ⟨b', hb', eb⟩ := hpB k b hb
      refine ⟨k + l, a' + b', acrisOf_add p hw ha' hb', ?_⟩
      rw [map_add, ea, eb, smul_add, smul_smul, smul_smul, pow_add]
      have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
      congr 1
      · rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, mul_one]
      · rw [mul_comm ((p : ℚ_[p])⁻¹ ^ k), mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, mul_one]
    | mul x y _ _ hx hy =>
      obtain ⟨k, a, ha, rfl⟩ := hx
      obtain ⟨l, b, hb, rfl⟩ := hy
      refine ⟨k + l, a * b, acrisOf_mul p hw ha hb, ?_⟩
      rw [map_mul, smul_mul_smul_comm, pow_add]
  · rintro x ⟨k, y, hy, rfl⟩
    have hmem : toBdR p y ∈ BcrisPlusOf p w hw := Algebra.subset_adjoin ⟨y, hy, rfl⟩
    exact (BcrisPlusOf p w hw).smul_mem hmem _

/-! ## §3. `A_cris` does not depend on the generator; `A_cris ⊆ A_max` -/

theorem acrisOf_le {w w' : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hw' : WittVector.fontaineTheta 𝓞_ℂ_[p] p w' = 0) (c : Ainf p) (hc : w' = w * c) :
    AcrisOf p w' hw' ⊆ AcrisOf p w hw := by
  rintro _ ⟨f, hf, rfl⟩
  refine ⟨PowerSeries.rescale c f, restricted_rescale p c hf, ?_⟩
  apply psEval_eq_of_terms
  intro k
  rw [dpSeries, dpSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_rescale, hc,
    map_mul, map_mul, map_pow]
  ring

/-- **`A_cris` is the same for every generator of `ker(θ : A_inf → 𝓞_ℂ_p)`** (Berger 2004 II.2.2's
`ω = ([ε] − 1)/([ε_1] − 1)`, `ξ = p − [p̃]`, …). -/
theorem acrisOf_eq {w w' : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hw' : WittVector.fontaineTheta 𝓞_ℂ_[p] p w' = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w})
    (hgen' : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w'}) :
    AcrisOf p w hw = AcrisOf p w' hw' := by
  apply le_antisymm
  · have : w ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := hw
    rw [hgen', Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact acrisOf_le p hw' hw c (by rw [← hc, mul_comm])
  · have : w' ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := hw'
    rw [hgen, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    exact acrisOf_le p hw hw' c (by rw [← hc, mul_comm])

/-- **`A_cris ⊆ A_max`**: `Σ a_n ω^n/n! = Σ (a_n p^n/n!) (ω/p)^n` and `p^n/n! ∈ ℤ_p`. -/
theorem acrisOf_le_amaxOf {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    AcrisOf p w hw ⊆ (AmaxOf p w hw : Set (BDeRhamPlus 𝓞_ℂ_[p] p)) := by
  rintro _ ⟨f, hf, rfl⟩
  let g : (Ainf p)⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff n f * zpToW p (dpCoeff p n)
  have hg : g ∈ restricted p := fun k => by
    obtain ⟨N, hN⟩ := hf k
    refine ⟨N, fun n hn => ?_⟩
    change (p : Ainf p) ^ k ∣ PowerSeries.coeff n g
    rw [PowerSeries.coeff_mk]
    exact Dvd.dvd.mul_right (hN n hn) _
  refine ⟨g, hg, ?_⟩
  change evalB p (alg_mem_of_theta p hw) (PowerSeries.map (algebraMap (Ainf p) (AinfP p)) g) = _
  apply psEval_eq_of_terms
  intro n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, dpSeries, PowerSeries.coeff_mk]
  have hq : qpToLoc p (dpCoeff p n : ℚ_[p]) = algebraMap _ _ (zpToW p (dpCoeff p n)) :=
    qpToLoc_algebraMap p _
  rw [inv_factorial_eq p n]
  simp only [map_mul, map_pow]
  rw [← hq]
  ring

theorem acrisOf_le_amax {w : Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w}) :
    AcrisOf p w hw ⊆ (Amax p : Set (BDeRhamPlus 𝓞_ℂ_[p] p)) := by
  rw [← amaxOf_eq_amax p hw hgen]
  exact acrisOf_le_amaxOf p hw

/-- **Fontaine's `B_st` lies in the tree's `B_st = B_max^+[1/t][log [p̃]]`.** -/
theorem bstFOf_le {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w}) :
    BstFOf p h w hw ≤ BstOf p h := by
  rw [BstFOf, Algebra.adjoin_le_iff]
  rintro x ((⟨y, hy, rfl⟩ | hx) | hx)
  · exact Algebra.subset_adjoin (Or.inl (Or.inl ⟨y, acrisOf_le_amax p hw hgen hy, rfl⟩))
  · exact Algebra.subset_adjoin (Or.inl (Or.inr hx))
  · exact Algebra.subset_adjoin (Or.inr hx)

/-! ## §4. The basis form of admissibility passes to a larger ring -/

section Mono

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

theorem inclT_tmul (B : Subalgebra ℚ_[p] (BdR p)) (b : B) (v : Fin n → E) :
    inclT p B (b ⊗ₜ[ℚ_[p]] v) = (b : BdR p) ⊗ₜ v := by
  rw [inclT, TensorProduct.map_tmul]
  rfl

/-- **Fontaine admissibility (basis form) over `B ⊆ B'` implies it over `B'`**: the image of a `B`-basis of
`B ⊗ V` of `H`-invariant vectors is a `B'`-basis of `B' ⊗ V` (`B' ⊗_B (B ⊗_{ℚ_p} V) ≅ B' ⊗_{ℚ_p} V`), with the same
image in `B_dR ⊗ V`. -/
theorem isAdmissibleT_mono {B B' : Subalgebra ℚ_[p] (BdR p)} (hBB' : B ≤ B') (H : Subgroup (GQp p))
    (ρ : GQp p →* GL (Fin n) E) (h : IsAdmissibleT p B H ρ) : IsAdmissibleT p B' H ρ := by
  obtain ⟨ι, b, hb⟩ := h
  let _ : Algebra B B' := (Subalgebra.inclusion hBB').toRingHom.toAlgebra
  have : IsScalarTower ℚ_[p] B B' := IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    rfl
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ_[p] B B' B' (Fin n → E)
  refine ⟨ι, (b.baseChange B').map e, fun i => ?_⟩
  have key : ∀ x : B ⊗[ℚ_[p]] (Fin n → E),
      inclT p B' (e ((1 : B') ⊗ₜ[B] x)) = inclT p B x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c v =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, inclT_tmul, inclT_tmul]
      congr 1
      change ((c • (1 : B') : B') : BdR p) = (c : BdR p)
      rw [Algebra.smul_def, mul_one]
      rfl
    | add x y hx hy => rw [TensorProduct.tmul_add, LinearEquiv.map_add, map_add, hx, hy, map_add]
  rw [Basis.map_apply, Basis.baseChange_apply, key]
  exact hb i

end Mono

/-! ## §5. Potential semistability in Fontaine's sense

pb-dimform: `IsPstF` is now Fontaine's **dimension form** (Brinon-Conrad §5.2 pp. 67-68 and Thm 9.3.5 p. 148:
`dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`, bst-construct's `IsAdmissible`); pb-p1's basis form is kept as
`IsPstFBasis` (it implies `IsPstF`, `isPstF_of_basis`; the converse needs the `G_K`-regularity of `B_st`, not proved in
the tree). -/

section Pst

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- **`V` is potentially semistable in Fontaine's sense** (Brinon-Conrad, *CMI summer school notes on p-adic Hodge
theory*, preliminary version June 24, 2009, Thm 9.3.5 p. 148, where the definition is printed inside the statement:
`V|_{G_K}` is semistable for some finite `K/ℚ_p`; semistable = `B_st`-admissible, §5.2 p. 68): for some finite `K/ℚ_p`
inside `ℚ̄_p`, `V|_{G_K}` is `B_st`-admissible in the **dimension form** of §5.2 pp. 67-68,
`dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V` (`IsAdmissible`), with `B_st = B_cris[log [p̃]] ⊆ B_dR`
(`BstFOf`). (pb-dimform; pb-p1's basis form is `IsPstFBasis`.) -/
def IsPstF {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    IsAdmissible p (BstFOf p h w hw) K.fixingSubgroup ρ

/-- pb-p1's `IsPstF` (kept for comparison): potential semistability over `BstFOf` in the **basis form**
`B_st ⊗_{ℚ_p} V ≃ B_st^d` as `B_st[G_K]`-modules (a `B_st`-basis of `G_K`-invariant vectors). Implies `IsPstF`
(`isPstF_of_basis`). -/
def IsPstFBasis {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    IsAdmissibleT p (BstFOf p h w hw) K.fixingSubgroup ρ

/-- A `ℚ̄_p`-valued `ρ` is potentially semistable in Fontaine's sense (dimension form): on a model `V = E^n`.
That the choice of model does not matter is `localIsPstF_iff_forall` (pb-dimform, `PstModel.lean`). -/
def LocalIsPstF {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) (n : ℕ)
    (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsPstF p h w hw ρE

/-- pb-p1's `LocalIsPstF` (basis form on a model), kept for comparison. -/
def LocalIsPstFBasis {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) (n : ℕ)
    (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsPstFBasis p h w hw ρE

/-- Fontaine's pst in the basis form implies pst over the tree's `B_st` (basis form). -/
theorem isPstT_of_FBasis {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w})
    (ρ : GQp p →* GL (Fin n) E) (hF : IsPstFBasis p h w hw ρ) : IsPstT p h ρ := by
  obtain ⟨K, hK, hadm⟩ := hF
  exact ⟨K, hK, isAdmissibleT_mono p (bstFOf_le p h hw hgen) _ ρ hadm⟩

end Pst

/-! ## §6. The generator `ξ = p − [p̃]` -/

theorem theta_xi' : WittVector.fontaineTheta 𝓞_ℂ_[p] p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) = 0 := by
  have : ZInQ.Contrib.G9.BdrKer.Cp.xi p ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) := by
    rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp]
    exact Ideal.mem_span_singleton_self _
  exact this

/-- A chosen generator `ε₀` of `ℤ_p(1)`. -/
def eps0 : PreTilt 𝓞_ℂ_[p] p := Classical.choose (exists_isGenEps p)

theorem eps0_spec : IsGenEps p (eps0 p) := Classical.choose_spec (exists_isGenEps p)

/-- Fontaine's pst at the chosen `ε₀` and `ξ`. -/
abbrev LocalIsPstF0 (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  LocalIsPstF p (eps0_spec p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p) n ρ

/-! ## §7. Fontaine's `B_st` is `G_{ℚ_p}`-stable (at the generator `ξ`) -/

section Stable

open PanBergerSplit (locAct flatAct)

theorem pow_dvd_factorial_mul (k : ℕ) : p ^ k ∣ (p * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (p * (k + 1)).factorial = (p * k + p) * (p * k + p - 1).factorial := by
      have : p * (k + 1) = (p * k + p - 1) + 1 := by have := hp.out.pos; rw [mul_add, mul_one]; omega
      rw [this, Nat.factorial_succ, ← this, mul_add, mul_one]
    have h2 : (p * k).factorial ∣ (p * k + p - 1).factorial :=
      Nat.factorial_dvd_factorial (by have := hp.out.pos; omega)
    rw [h1, pow_succ, mul_comm (p ^ k) p]
    exact Nat.mul_dvd_mul ⟨k + 1, by ring⟩ (dvd_trans ih h2)

/-- **`log [ε] ∈ A_cris`** for `ε^♯ = 1`: `[ε] − 1 = ξ c` and `([ε] − 1)^n/n = (n − 1)! c^n ξ^n/n!`. -/
theorem logTeich_mem_acris {ε : PreTilt 𝓞_ℂ_[p] p} (h : PreTilt.untilt ε = 1) :
    logTeich p h ∈ AcrisOf p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p) := by
  have hk : WittVector.teichmuller p ε - 1 ∈ RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) :=
    PanBergerSplit.theta_teich_sub_one p h
  rw [ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp, Ideal.mem_span_singleton'] at hk
  obtain ⟨c, hc⟩ := hk
  let f : (Ainf p)⟦X⟧ := PowerSeries.mk fun n =>
    if n = 0 then 0 else (-1) ^ (n + 1) * ((n - 1).factorial : Ainf p) * c ^ n
  have hf : f ∈ restricted p := fun k => ⟨p * k + 1, fun n hn => by
    change (p : Ainf p) ^ k ∣ PowerSeries.coeff n f
    rw [PowerSeries.coeff_mk, ite_eq_right (by omega)]
    have hd : p ^ k ∣ (n - 1).factorial :=
      dvd_trans (pow_dvd_factorial_mul p k) (Nat.factorial_dvd_factorial (by omega))
    obtain ⟨d, hd⟩ := hd
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ⟨(d : Ainf p), ?_⟩ _) _
    rw [hd, Nat.cast_mul, Nat.cast_pow]⟩
  refine ⟨f, hf, ?_⟩
  rw [logTeich, logPlus]
  apply psEval_eq_of_terms
  intro n
  simp only [dpSeries, logSeries, f, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · simp [hn]
  · rw [ite_eq_right hn, ite_eq_right hn, ← hc]
    have key : qpToLoc p ((n : ℚ_[p]))⁻¹ =
        qpToLoc p (((n - 1).factorial : ℕ) : ℚ_[p]) * qpToLoc p ((n.factorial : ℕ) : ℚ_[p])⁻¹ := by
      rw [← map_mul]
      congr 1
      have hn1 : n = (n - 1) + 1 := by omega
      have hf0 : ((n - 1).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hn0 : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn
      conv_rhs => rw [hn1, Nat.factorial_succ, ← hn1]
      push_cast
      field_simp
    rw [key]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring

/-- `1/log [ε] ∈ B` for every `ℚ_p`-subalgebra `B ⊆ B_dR` containing `1/t` (`log [ε] = a t`, `a ∈ ℤ_p ∖ 0`). -/
theorem tInv_mem_of {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (B : Subalgebra ℚ_[p] (BdR p))
    (hB : Ring.inverse (tOf p h) ∈ B) {z : BdR p} (hz : z ∈ tInvSet p) : z ∈ B := by
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
  exact Subalgebra.mul_mem _ hB (Subalgebra.algebraMap_mem _ _)

/-- **`A_cris` is `G_{ℚ_p}`-stable**: `σ(Σ a_n ξ^n/n!) = Σ σ(a_n) c^n ξ^n/n!`, `σ(ξ) = ξ c`. -/
theorem bdrAct_acris (σ : GQp p) {y : BDeRhamPlus 𝓞_ℂ_[p] p}
    (hy : y ∈ AcrisOf p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p)) :
    ∃ y' ∈ AcrisOf p (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p),
      bdrAct p σ (toBdR p y) = toBdR p y' := by
  obtain ⟨f, hf, rfl⟩ := hy
  obtain ⟨c, hc⟩ := wittMap_xi_mem p σ
  refine ⟨_, ⟨PowerSeries.rescale c (PowerSeries.map (WittVector.map (flatAct p σ)) f),
    restricted_rescale p c (restricted_map p _ hf), rfl⟩, ?_⟩
  rw [bdrAct_evalB]
  congr 1
  apply psEval_eq_of_terms
  intro k
  simp only [dpSeries, PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_rescale]
  rw [map_mul, PanBergerSplit.locAct_algebraMap, PanBergerSplit.locAct_qpToLoc,
    PanBergerSplit.locAct_algebraMap, hc, map_mul, map_mul, map_pow]
  ring

/-- **Fontaine's `B_st` is `G_{ℚ_p}`-stable** (at `ξ`; `A_cris` does not depend on the generator). -/
theorem bstF_stable {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (σ : GQp p) (x : BdR p)
    (hx : x ∈ BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p)) :
    bdrAct p σ x ∈ BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p) := by
  have hle : BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p) ≤
      (BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p)).comap (bdrAlg p σ) := by
    rw [BstFOf, Algebra.adjoin_le_iff]
    intro z hz
    rw [SetLike.mem_coe, Subalgebra.mem_comap, bdrAlg_apply]
    rcases hz with (⟨y, hy, rfl⟩ | hz) | hz
    · obtain ⟨y', hy', he⟩ := bdrAct_acris p σ hy
      rw [he]
      exact Algebra.subset_adjoin (Or.inl (Or.inl ⟨y', hy', rfl⟩))
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      refine tInv_mem_of p h _ (Algebra.subset_adjoin (Or.inl (Or.inr rfl))) ?_
      exact tInvSet_stable p σ ⟨ε₀, h.1, ne_one_of_isGenEps p h, rfl⟩
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      obtain ⟨u, hu, hu1⟩ := exists_uSigma p σ
      rw [bdrAct_logPTilde p σ hu hu1]
      exact Subalgebra.add_mem _ (Algebra.subset_adjoin (Or.inl (Or.inl
        ⟨_, logTeich_mem_acris p hu1, rfl⟩))) (Algebra.subset_adjoin (Or.inr rfl))
  exact hle hx

/-- The basis form implies Fontaine's dimension form `dim_{B_st^{G_K}} D_st = dim V` (`isAdmissible_of_T`, `B_st`
being `G_{ℚ_p}`-stable). Since pb-dimform the leaves use the dimension form directly. -/
theorem isAdmissible_of_pstF {E' : Type*} [Field E'] [Algebra ℚ_[p] E'] [FiniteDimensional ℚ_[p] E'] {n : ℕ}
    {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E')
    (hT : IsAdmissibleT p (BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p)) H ρ) :
    IsAdmissible p (BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p)) H ρ :=
  isAdmissible_of_T p _ (bstF_stable p h) H ρ hT

/-- `B_st^{Fontaine}` does not depend on the generator `w` of `ker θ` (`acrisOf_eq`). -/
theorem bstFOf_eq_xi {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w}) :
    BstFOf p h w hw = BstFOf p h (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (theta_xi' p) := by
  unfold BstFOf
  rw [acrisOf_eq p hw (theta_xi' p) hgen (ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp p)]

/-- **pb-p1's basis form implies the dimension form** `IsPstF` (`isAdmissible_of_T`, `B_st` being
`G_{ℚ_p}`-stable). The converse would need the `G_K`-regularity of `B_st`, which the tree does not prove. -/
theorem isPstF_of_basis {E' : Type*} [Field E'] [Algebra ℚ_[p] E'] [FiniteDimensional ℚ_[p] E'] {n : ℕ}
    {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w})
    (ρ : GQp p →* GL (Fin n) E') (hT : IsPstFBasis p h w hw ρ) : IsPstF p h w hw ρ := by
  obtain ⟨K, hK, hadm⟩ := hT
  refine ⟨K, hK, ?_⟩
  rw [bstFOf_eq_xi p h hw hgen] at hadm ⊢
  exact isAdmissible_of_pstF p h _ ρ hadm

/-- On a model: the basis form implies the dimension form. -/
theorem localIsPstF_of_basis {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w}) (n : ℕ)
    (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) (hT : LocalIsPstFBasis p h w hw n ρ) :
    LocalIsPstF p h w hw n ρ := by
  obtain ⟨E, hE, ρE, hmod, hpst⟩ := hT
  exact ⟨E, hE, ρE, hmod, isPstF_of_basis p h hw hgen ρE hpst⟩

end Stable

/-! ## §8. B1, algebraic half: `B_max[ℓ] = B_max[log [p̃]]` once `(p−1)ℓ − p(c + log [p̃]) ∈ B_max^+`

Berger's `log [π̄]` (arXiv:math/0102179v3 §1.2 p. 11) would satisfy `(p − 1) log [π̄] = p (log p + log [p̃]) + log [u]`
with `u = π̄^{p−1}/p̃^p ∈ (𝓞_ℂ_p♭)^×` and `log [u] ∈ B_max^+` (Prop. 2.23's proof). The analytic half (a Lean
definition of `log [π̄]`, which needs a `p`-adic logarithm on `A_max`) is not formalized; this is the algebra. -/

theorem bmax_adjoin_eq_bst (ℓ : BdR p) (c : ℚ_[p])
    (hℓ : ((p : ℚ_[p]) - 1) • ℓ - (p : ℚ_[p]) • (algebraMap ℚ_[p] (BdR p) c + toBdR p (logPTilde p)) ∈
      BmaxPlus p) :
    Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {ℓ}) = Bst p := by
  have hp1 : ((p : ℚ_[p]) - 1) ≠ 0 := by
    have e1 : ((p : ℚ_[p]) - 1) = ((p - 1 : ℕ) : ℚ_[p]) := by
      rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
    rw [e1]
    exact Nat.cast_ne_zero.mpr (by have := hp.out.two_le; omega)
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  set m := ((p : ℚ_[p]) - 1) • ℓ - (p : ℚ_[p]) • (algebraMap ℚ_[p] (BdR p) c + toBdR p (logPTilde p))
    with hm
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro x (hx | hx)
    · exact bmax_le_bst p hx
    · rw [Set.mem_singleton_iff.mp hx]
      have hℓeq : ℓ = ((p : ℚ_[p]) - 1)⁻¹ •
          (m + (p : ℚ_[p]) • (algebraMap ℚ_[p] (BdR p) c + toBdR p (logPTilde p))) := by
        rw [hm, sub_add_cancel, smul_smul, inv_mul_cancel₀ hp1, one_smul]
      rw [hℓeq]
      refine Subalgebra.smul_mem _ (Subalgebra.add_mem _ (bmax_le_bst p (bmaxPlus_le_bmax p hℓ))
        (Subalgebra.smul_mem _ (Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ c)
          (logPTilde_mem_bst p)) _)) _
  · rw [Bst, Algebra.adjoin_le_iff]
    have hB : ((Bmax p : Set (BdR p))) ⊆ Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {ℓ}) :=
      fun x hx => Algebra.subset_adjoin (Or.inl hx)
    rintro x ((hx | hx) | hx)
    · exact hB (Algebra.subset_adjoin (Or.inl hx))
    · exact hB (Algebra.subset_adjoin (Or.inr hx))
    · rw [Set.mem_singleton_iff.mp hx]
      have hL : toBdR p (logPTilde p) = (p : ℚ_[p])⁻¹ • (((p : ℚ_[p]) - 1) • ℓ - m) -
          algebraMap ℚ_[p] (BdR p) c := by
        rw [hm, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hp0, one_smul, add_sub_cancel_left]
      rw [hL]
      have hℓmem : ℓ ∈ Algebra.adjoin ℚ_[p] ((Bmax p : Set (BdR p)) ∪ {ℓ}) :=
        Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_singleton ℓ))
      refine Subalgebra.sub_mem _ (Subalgebra.smul_mem _ (Subalgebra.sub_mem _
        (Subalgebra.smul_mem _ hℓmem _)
        (hB (bmaxPlus_le_bmax p hℓ))) _) (Subalgebra.algebraMap_mem _ c)

end FontaineSt

namespace PanDict

open BmaxOne BergerBst PanBergerSplit FontaineSt

/-- **R11. Berger's theorem, with Fontaine's `B_st` and Fontaine's (dimension) form of admissibility**: every de
Rham representation is potentially semistable (L. Berger, *Représentations p-adiques et équations différentielles*,
Invent. Math. 148 (2002), cited in the manuscript at L739; Thm 0.6 = Thm 5.19 (arXiv v3, arXiv:math/0102179v3); the
statement is read in Berger's survey *An introduction to the theory of p-adic representations*, arXiv:math/0210184v1,
IV.5.1 p. 30, as the same theorem; the survey is not in the manuscript's bibliography), at `K = ℚ_p`, for a `p`-adic
representation `V = E^n` (`E/ℚ_p` finite inside `ℚ̄_p`, `ρ_E : G_{ℚ_p} → GL_n(E)` continuous):

* de Rham: `dim_{ℚ_p} (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}} = dim_{ℚ_p} V` (`IsDeRhamU`; survey II.2.3 p. 12, Brinon-Conrad §5.2
  with `B = B_dR`);
* potentially semistable in Fontaine's sense (`IsPstF`): for some finite `K/ℚ_p`,
  `dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`, the definitions at definition level in Brinon-Conrad
  (preliminary version June 24, 2009; cited in the manuscript as `brinon-conrad`): admissibility §5.2 pp. 67-68
  (dimension form), potentially semistable Thm 9.3.5 p. 148, `B_st` Def. 9.2.3 p. 138 embedded in `B_dR` p. 142 and
  Thm 9.2.10 p. 143 (`BstFOf`, with `q̃ = p̃`, `log p = 0`), `B_cris = A_cris[1/t]` Def. 9.1.4 p. 131 (`BcrisOf`),
  `A_cris` p. 129 (`AcrisOf`, `p`-adic topology). The survey's I.2.3 p. 6 defines admissibility by the same dimension
  equality, so the conclusion is the printed one with no dimension-to-basis step.

Stated for every generator `ε₀` of `ℤ_p(1)` and every generator `w` of `ker θ` (`A_cris` does not depend on it,
`acrisOf_eq`). (pb-dimform: restated from pb-p1's basis form, kept as `BergerSurveyFBasis`; `BergerSurveyFBasis`
implies `BergerSurveyF`, `bergerSurveyF_of_basis`.) -/
def BergerSurveyF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
      (ρE : GQp p →* GL (Fin n) E),
      Continuous ρE → IsDeRhamU p ρE → IsPstF p h w hw ρE

/-- pb-p1's `BergerSurveyF` (basis form of admissibility in the conclusion), kept for comparison: not used by the
fold. -/
def BergerSurveyFBasis : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
      (ρE : GQp p →* GL (Fin n) E),
      Continuous ρE → IsDeRhamU p ρE → IsPstFBasis p h w hw ρE

/-- **The new (dimension-form) Berger leaf is a consequence of pb-p1's (basis-form) one.** -/
theorem bergerSurveyF_of_basis (hB : BergerSurveyFBasis) : BergerSurveyF := by
  intro p _ ε₀ h w hw hgen n E _ ρE hc hdr
  exact isPstF_of_basis p h hw hgen ρE (hB p ε₀ h w hw hgen n E ρE hc hdr)

/-- pb-pst's `BergerPrintedVT` (the tree's `B_st`, basis form) from pb-p1's basis-form Berger leaf
(`B_st^{Fontaine} ⊆ B_st^{tree}`, `isPstT_of_FBasis`; `ξ` generates `ker θ`). Not available from the dimension-form
`BergerSurveyF` without the regularity of `B_st`; not used by the fold. -/
theorem bergerPrintedVT_of_surveyBasis (hB : BergerSurveyFBasis) : BergerPrintedVT := by
  intro p _ ε₀ h n E _ ρE hc hdr
  exact isPstT_of_FBasis p h (theta_xi' p) (ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp p) ρE
    (hB p ε₀ h _ (theta_xi' p) (ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp p) n E ρE hc hdr)

/-- The field `bergerPrintedV` from pb-p1's basis-form Berger leaf (not used by the fold). -/
theorem bergerPrintedV_of_surveyBasis (hB : BergerSurveyFBasis) : BergerPrintedV :=
  bergerPrintedV_of_T (bergerPrintedVT_of_surveyBasis hB)

/-- **R12. Pan, Theorem 1.0.4, with potential semistability in the sense of Fontaine** (L. Pan, *The
Fontaine–Mazur conjecture in the residually reducible case*, J. Amer. Math. Soc. 35 (2022), 1031-1169; cited in the
manuscript at L756-757 as Theorem 1.0.4 of arXiv:1901.07166v2, "the version used here": Thm 1.0.4 p. 5 with
Conjecture 1.0.1 p. 2, "the restriction of ρ at the decomposition group at p is potentially semi-stable in the sense of
Fontaine"; JAMS numbering UNVERIFIED), `p ≥ 5`: as pb-fix3's `PanPrintedP`, with "potentially semistable in the sense
of Fontaine" read at definition level in Brinon-Conrad (Thm 9.3.5 p. 148, admissibility in the dimension form §5.2
pp. 67-68, `B_st` Def. 9.2.3 p. 138 inside `B_dR` p. 142 / Thm 9.2.10 p. 143, i.e. `BstFOf`): `LocalIsPstF`, on a
model `V = E^n`, `dim_{B_st^{G_K}} (B_st ⊗ V)^{G_K} = dim V` for some finite `K/ℚ_p`; for every generator `ε₀` of
`ℤ_p(1)` and every generator `w` of `ker θ`. The model clause is harmless: pst on one finite model is pst on every
model (`localIsPstF_iff_forall`, pb-dimform `PstModel.lean`). (pb-dimform: restated from pb-p1's basis form, kept as
`PanPrintedFBasis`; `PanPrintedF` implies `PanPrintedFBasis`, `panPrintedFBasis_of_F`.) -/
def PanPrintedF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    IsIrreducibleP ρ → ρ.FinitelyRamified → LocalIsPstF p h w hw 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTP p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (_ : NeZero N) (k : ℤ) (g : HeckeRing.GL2.EigenformAwayFromLevel N k)
      (ρg : GaloisRep p 2) (ψ : GaloisChar p),
      IsAttachedVia p ιp g ρg ∧ IsTwistOf p ρ ρg ψ

/-- pb-p1's `PanPrintedF` (basis form of admissibility in the hypothesis), kept for comparison: not used by the
fold. -/
def PanPrintedFBasis : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    IsIrreducibleP ρ → ρ.FinitelyRamified → LocalIsPstFBasis p h w hw 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTP p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (_ : NeZero N) (k : ℤ) (g : HeckeRing.GL2.EigenformAwayFromLevel N k)
      (ρg : GaloisRep p 2) (ψ : GaloisChar p),
      IsAttachedVia p ιp g ρg ∧ IsTwistOf p ρ ρg ψ

/-- **The new (dimension-form) Pan leaf implies pb-p1's (basis-form) one** (its hypothesis is weaker). -/
theorem panPrintedFBasis_of_F (hP : PanPrintedF) : PanPrintedFBasis := by
  intro p _ hp ε₀ h w hw hgen ιp ρ hirr hfr hpst hodd hht
  exact hP p hp ε₀ h w hw hgen ιp ρ hirr hfr (localIsPstF_of_basis p h hw hgen 2 _ hpst) hodd hht

/-- `PanPrintedB` (bst-construct's form, kernel eigenform conclusion) with Fontaine's pst at `ε₀`, `ξ`:
`panPrintedB_of_printedP` verbatim with the potential-semistability hypothesis passed through. -/
theorem panPrintedB_F_of_printedF (hP : PanPrintedF) :
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    ρ.IsIrreducible → ρ.FinitelyRamified → LocalIsPstF0 p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTU p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (S : Finset ℕ), ∀ q : ℕ, q.Prime → q ∉ S →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v q → IsArithFrob σ v q →
          (ρ.mat σ⁻¹).trace = (ψ.toHom σ⁻¹ : PadicAlgCl p) * ιp.symm (coeff g q) := by
  intro p _ hp ιp ρ hirr hfr hpst hodd hht
  obtain ⟨N, _, k, g, ρg, ψ, ⟨S, hatt⟩, htw⟩ := hP p hp (eps0 p) (eps0_spec p) _ (theta_xi' p)
    (ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp p) ιp ρ (isIrreducibleP_of ρ hirr) hfr hpst hodd
    ((localDistinctHTP_iff p _).mpr hht)
  obtain ⟨M, χ, g', hM, hk, hg', hcoef⟩ := exists_normalized_of_eigenform g
  refine ⟨M, k, χ, g', hM, hk, hg', ψ, S ∪ Finset.range (N + 1), fun q hq hqS v σ hv hσ => ?_⟩
  simp only [Finset.mem_union, Finset.mem_range, not_or, not_lt] at hqS
  obtain ⟨hqS, hqN1⟩ := hqS
  have hqN : ¬ q ∣ N := fun hd => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hd
    omega
  rw [trace_of_twist p htw, (hatt q hq hqN hqS).2 v σ hv hσ, hcoef q hq hqN]

/-- Berger's theorem over Fontaine's `B_st` for a continuous `ℚ̄_p`-valued `ρ` de Rham on a model. -/
theorem bergerB_F_of_survey (hB : BergerSurveyF) :
    ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
      Continuous ρ → LocalIsDeRhamU p n ρ → LocalIsPstF0 p n ρ := by
  intro p _ n ρ hρ hdr
  obtain ⟨E, hE, ρE, hmod, hdrE⟩ := hdr
  exact ⟨E, hE, ρE, hmod, hB p (eps0 p) (eps0_spec p) _ (theta_xi' p)
    (ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp p) n E ρE (continuous_model hmod hρ) hdrE⟩

/-- **`r11r12 : PanBerger` from Pan's and Berger's theorems, both over Fontaine's `B_st`**, and the current
bundle's Diamond–Shurman 9.6.5 / Deligne–Serre fields: bst-construct's `panBerger_of_printedB` verbatim with
Fontaine's pst in place of the tree's (the predicate is only passed from Berger's conclusion to Pan's hypothesis,
so no comparison of period rings is used). -/
theorem panBerger_of_F (hP : PanPrintedF) (hB : BergerSurveyF)
    (h965 : DSCoeffExt.DSThm965Printed) (hK : DSCoeffExt.EigenformCoeffFieldFinite)
    (h966 : DSThm966EV.DSThm966Printed) : PanBerger := by
  have hD : ZInQ.Contrib.HodgeSplit.DSThm965 :=
    DS965Weak.dsThm965_of_weak (DSCoeffExt.dsThm965Weak_of_printed h965 hK)
  have hDS : ZInQ.Contrib.HodgeSplit.DSThm966 := DSThm966EV.dsThm966_of_printed h966
  intro p _ hp ρ hirr hfr hdr hodd hdist
  have hdr' : LocalIsDeRhamU p 2 ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localIsDeRhamU_dualHom p _ hdr
  have hpst' := bergerB_F_of_survey hB p 2 _ ((dualRep ρ).continuous_toHom.comp
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous) hdr'
  have hht' : LocalDistinctHTU p ((dualRep ρ).restrictLocal p) := by
    rw [dualRep_restrictLocal]
    exact localDistinctHTU_dualHom p ρ hdist
  obtain ⟨Φ⟩ := exists_complex_equiv p
  obtain ⟨N, k, χ, g, hN, hk, hg, ψ, S, htr⟩ := panPrintedB_F_of_printedF hP p hp Φ.symm (dualRep ρ)
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

/-- **Not a leaf, and not used by the fold**: the comparison that would give the old field `panPrintedP` from
`PanPrintedF`, namely that potential semistability over the tree's `B_st = B_max[log [p̃]]` (bst-construct's
dimension form) implies it over Fontaine's `B_cris[log [p̃]]` (dimension form, pb-dimform). It holds (Fontaine's `D_st`
is computed by either ring: `φ(B_max^+) ⊆ B_cris^+ ⊆ B_max^+`), but no print read here states it for
`B_max[log [p̃]]`: Berger 2002 §1.2 p. 11 states it for his `B_max[log [π̄]]`, and Berger 2004 II.3.5 p. 16 for
crystalline periods. Its proof needs Frobenius on `A_max` and `A_cris`, which the tree lacks. Recorded so that the gap
is explicit. -/
def BmaxStToFontaine : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
      (ρE : GQp p →* GL (Fin n) E), IsPstB p ρE → IsPstF p h w hw ρE

/-- The old field `panPrintedP` from the new Pan leaf and the comparison `BmaxStToFontaine` (not used by the fold). -/
theorem panPrintedP_of_F (hP : PanPrintedF) (hC : BmaxStToFontaine) : PanPrintedP := by
  intro p _ hp ιp ρ hirr hfr hpst hodd hht
  obtain ⟨E, hE, ρE, hmod, hpstE⟩ := hpst
  have := hE
  exact hP p hp (eps0 p) (eps0_spec p) _ (theta_xi' p) (ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp p) ιp ρ
    hirr hfr ⟨E, hE, ρE, hmod, hC p (eps0 p) (eps0_spec p) _ (theta_xi' p)
      (ZInQ.Contrib.G9.BdrKer.Cp.ker_fontaineTheta_Cp p) 2 E ρE hpstE⟩ hodd hht

end PanDict
end PkgI4
end HDec

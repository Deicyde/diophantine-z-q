import ZInQKernel.Contrib.OneProof.LogPTranscendenceBdR
import ZInQKernel.Contrib.OneProof.FontaineLogCore

/-!
# `log [p̃] ∉ Frac(B_max)`, hence `BergerBst.LogPTildeTranscendental` (Fontaine, Lemme 4.3.1)

Instantiates `FontaineLogCore.notMem_mul_log` (Fontaine, *Le corps des périodes p-adiques*,
Astérisque 223 (1994), Exp. II, 4.3.1-4.3.2, pp. 87-88; Brinon-Conrad, CMI notes, June 24, 2009,
proof of Thm 9.2.10, p. 143) at `A = W(𝓞_{ℂ_p}^♭)`, `P = A[1/p]`, `I = ker θ`, `ξ = p − [p̃]`,
`β = ξ/p`, using only results already proved in this tree: `ker θ = (ξ)` (`ith_pow`),
`A ∩ (ker θ)^k = ξ^k A` (`mem_xi_pow_of_algebraMap`), `⋂_k (p^k A + ξ^m A) = ξ^m A`
(`mem_xi_pow_of_forall`), `B_dR` a field containing `B_dR^+` (`isField_BDeRham`,
`toBdR_injective`). With `LogPTransc.logPTildeTranscendental_of_notInFrac` this proves the open
Prop `BergerBst.LogPTildeTranscendental`, i.e. Brinon-Conrad Thm 9.2.10 at `K = ℚ_p`
(`LogPTransc.transcendental_bcrisOf`, `LogPTransc.bcrisPolyEquiv`).
-/

noncomputable section

namespace HDec
namespace PkgI4
namespace LogPFontaine

open PowerSeries BergerBst BmaxOne FontaineSt LogPTransc
open PanBergerSplit (Ainf AinfP theta)

variable (p : ℕ) [hp : Fact p.Prime]

theorem psEval_eq_core {x : AinfP p} (hx : x ∈ Ith p) (f : (AinfP p)⟦X⟧) :
    BergerBst.psEval (Ith p) hx f = FontaineLogCore.psEval (Ith p) hx f :=
  AdicCompletion.ext_evalₐ fun n => by
    rw [FontaineLogCore.evalₐ_psEval, BergerBst.evalₐ_psEval]

/-- `inv n = 1/n` in `W(𝓞_{ℂ_p}^♭)[1/p]`. -/
abbrev invQ (n : ℕ) : AinfP p := qpToLoc p ((n : ℚ_[p])⁻¹)

theorem hpβ : (p : AinfP p) * omegaP p =
    algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) := by
  have h := natCast_mul_qp p p (Fact.out : p.Prime).ne_zero
  have hx : ZInQ.Contrib.G9.BdrKer.Cp.xi' p =
      algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p) := rfl
  rw [omegaP, ← hx]
  linear_combination (ZInQ.Contrib.G9.BdrKer.Cp.xi' p) * h

theorem hint (n : ℕ) (hn : n ≠ 0) : ∃ w : Ainf p,
    algebraMap (Ainf p) (AinfP p) w * (n : AinfP p) = (p : AinfP p) ^ padicValNat p n := by
  obtain ⟨v, m, hpm, hvm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
  have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)
  have hval : padicValNat p n = v := by
    rw [hvm, padicValNat.mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hpm, add_zero]
  have hu : IsUnit (m : ℤ_[p]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm))
  refine ⟨zpToW p ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ?_⟩
  have hum : ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (m : ℤ_[p]) = 1 := hu.val_inv_mul
  have hum' : (((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * (m : ℚ_[p]) = 1 := by
    have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hum
    rwa [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_one] at this
  change (algebraMap ℤ_[p] ℚ_[p]) ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (m : ℚ_[p]) = 1 at hum'
  rw [← qpToLoc_algebraMap p, hval, hvm, ← map_natCast (qpToLoc p), ← map_mul,
    ← map_natCast (qpToLoc p) p, ← map_pow]
  congr 1
  push_cast
  linear_combination ((p : ℚ_[p]) ^ v) * hum'

theorem hreg (x : AdicCompletion (Ith p) (AinfP p))
    (hx : algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p))
      (algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p)) * x = 0) : x = 0 := by
  haveI : IsDomain (BdR p) := (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).isDomain
  set y : AdicCompletion (Ith p) (AinfP p) := algebraMap (AinfP p) (AdicCompletion (Ith p) (AinfP p))
    (algebraMap (Ainf p) (AinfP p) (ZInQ.Contrib.G9.BdrKer.Cp.xi p)) with hy
  have hy0 : y ≠ 0 := by
    intro h0
    have h2 : AdicCompletion.evalₐ (Ith p) 2 y = 0 :=
      (congrArg (AdicCompletion.evalₐ (Ith p) 2) h0).trans (map_zero _)
    rw [hy] at h2
    rw [FontaineLogCore.evalₐ_algebraMap, Ideal.Quotient.eq_zero_iff_mem, ith_pow] at h2
    have h3 := mem_xi_pow_of_algebraMap p 2 _ h2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h3
    have hξ := ZInQ.Contrib.G9.BdrKer.Cp.xi_ne_zero p
    have h4 : c * ZInQ.Contrib.G9.BdrKer.Cp.xi p = 1 := by
      apply mul_left_cancel₀ hξ
      linear_combination hc
    have h5 := congrArg (theta p) h4
    rw [map_mul, map_one, theta_xi, mul_zero] at h5
    exact zero_ne_one h5
  let j : AdicCompletion (Ith p) (AinfP p) →+* BdR p := toBdR p
  have hj : Function.Injective j := toBdR_injective p
  have h1 : j y * j x = 0 := (map_mul j y x).symm.trans (by rw [hx, map_zero])
  have h2 : j y ≠ 0 := fun h => hy0 (hj (h.trans (map_zero j).symm))
  have h3 : j x = 0 := (mul_eq_zero.mp h1).resolve_left h2
  exact hj (h3.trans (map_zero j).symm)

theorem amax_mem_subS {y : BDeRhamPlus 𝓞_ℂ_[p] p} (hy : y ∈ Amax p) :
    y ∈ FontaineLogCore.SubS (Ainf p) (Ith p) (omegaP_mem p) := by
  obtain ⟨f₀, -, rfl⟩ := hy
  change BergerBst.psEval (Ith p) (omegaP_mem p)
    (PowerSeries.map (algebraMap (Ainf p) (AinfP p)) f₀) ∈
      FontaineLogCore.SubS (Ainf p) (Ith p) (omegaP_mem p)
  rw [psEval_eq_core p]
  exact FontaineLogCore.psEval_map_mem (Ainf p) (Ith p) (omegaP_mem p) f₀

theorem logPTilde_eq_core : logPTilde p =
    FontaineLogCore.psEval (Ith p) (omegaP_mem p) (FontaineLogCore.logNeg (invQ p)) := by
  rw [logPTilde, logPlus, evalB, ← psEval_eq_core]
  apply psEval_eq_of_terms
  intro k
  simp only [logSeries, FontaineLogCore.logNeg, PowerSeries.coeff_mk, pTildeArg]
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk, if_neg hk, neg_pow]
    have h1 : ((-1 : AinfP p) ^ (k + 1)) * (-1) ^ k = -1 := by
      rw [← pow_add]
      exact Odd.neg_one_pow ⟨k, by ring⟩
    linear_combination (invQ p k * omegaP p ^ k) * h1

/-- Every element of `B_max` is `y/z` with `y, z ∈ A_max`, `z ≠ 0`. -/
theorem bmax_frac {x : BdR p} (hx : x ∈ Bmax p) :
    ∃ y ∈ Amax p, ∃ z ∈ Amax p, toBdR p z ≠ 0 ∧ x * toBdR p z = toBdR p y := by
  haveI : IsDomain (BdR p) := (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).isDomain
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨y, hy, rfl⟩ | ⟨ε, h, hne, rfl⟩
    · exact ⟨y, hy, 1, Subring.one_mem _, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one]⟩
    · have hz : toBdR p (logTeich p h) ≠ 0 := fun h0 =>
        logTeich_ne_zero p h hne ((toBdR_injective p) (h0.trans (map_zero _).symm))
      obtain ⟨w, hw⟩ := (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).mul_inv_cancel hz
      change (BdR p) at w
      have hu : IsUnit (toBdR p (logTeich p h)) := ⟨⟨_, w, hw, (mul_comm _ _).trans hw⟩, rfl⟩
      exact ⟨1, Subring.one_mem _, logTeich p h, logTeich_mem_amax p h, hz,
        by rw [Ring.inverse_mul_cancel _ hu, map_one]⟩
  | algebraMap c =>
    obtain ⟨k, hk⟩ := exists_pow_mul_mem p c
    let z : ℤ_[p] := ⟨_, (PadicInt.mem_subring_iff p).mpr hk⟩
    refine ⟨zpB p z, zpB_mem p z, zpB p ((p : ℤ_[p]) ^ k), zpB_mem p _, ?_, ?_⟩
    · rw [toBdR_zpB]
      intro h0
      have hp0 : ((p : ℤ_[p]) ^ k : ℤ_[p]) ≠ 0 :=
        pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      apply hp0
      have h1 := (algebraMap ℚ_[p] (BdR p)).injective (h0.trans (map_zero _).symm)
      exact PadicInt.coe_eq_zero.mp h1
    · rw [toBdR_zpB, toBdR_zpB, ← map_mul]
      congr 1
      change c * ((p : ℚ_[p]) ^ k) = (p : ℚ_[p]) ^ k * c
      push_cast
      ring
  | add x y _ _ hx hy =>
    obtain ⟨y1, hy1, z1, hz1, hz10, e1⟩ := hx
    obtain ⟨y2, hy2, z2, hz2, hz20, e2⟩ := hy
    refine ⟨y1 * z2 + y2 * z1, Subring.add_mem _ (Subring.mul_mem _ hy1 hz2)
      (Subring.mul_mem _ hy2 hz1), z1 * z2, Subring.mul_mem _ hz1 hz2, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hz10 hz20
    · rw [map_mul, map_add, map_mul, map_mul, ← e1, ← e2]; ring
  | mul x y _ _ hx hy =>
    obtain ⟨y1, hy1, z1, hz1, hz10, e1⟩ := hx
    obtain ⟨y2, hy2, z2, hz2, hz20, e2⟩ := hy
    refine ⟨y1 * y2, Subring.mul_mem _ hy1 hy2, z1 * z2, Subring.mul_mem _ hz1 hz2, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hz10 hz20
    · rw [map_mul, map_mul, ← e1, ← e2]; ring

/-- **`log [p̃] ∉ Frac(B_max)`** (Fontaine, Lemme 4.3.1, over `A_max ⊆ W(R)[β]`). -/
theorem notInFrac_bmax_logPTilde : NotInFrac p (Bmax p) (toBdR p (logPTilde p)) := by
  haveI : IsDomain (BdR p) := (ZInQ.Contrib.G9.BdrKer.Cp.isField_BDeRham p).isDomain
  intro a b ha he
  obtain ⟨y1, hy1, z1, hz1, hz10, e1⟩ := bmax_frac p a.2
  obtain ⟨y2, hy2, z2, hz2, hz20, e2⟩ := bmax_frac p b.2
  have hy10 : y1 * z2 ≠ 0 := by
    intro h0
    have h1 : toBdR p y1 = 0 := by
      have := congrArg (toBdR p) h0
      rw [map_mul, map_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hz20
    rw [← e1] at h1
    exact ha (Subtype.ext ((mul_eq_zero.mp h1).resolve_right hz10))
  have hrel : y1 * z2 * logPTilde p = y2 * z1 := by
    apply toBdR_injective p
    rw [map_mul, map_mul, map_mul, ← e1, ← e2, ← he]
    ring
  apply FontaineLogCore.notMem_mul_log (Ainf p) (Ith p) p (omegaP_mem p)
    (ZInQ.Contrib.G9.BdrKer.Cp.xi p) (hpβ p) (natCast_mul_qp p p (Fact.out : p.Prime).ne_zero)
    (xi'_mem p) (invQ p) (fun n hn => natCast_mul_qp p n hn) (hint p)
    (fun k a h => mem_xi_pow_of_algebraMap p k a (by rwa [ith_pow] at h))
    (fun m w h => mem_xi_pow_of_forall p m w h) (hreg p) (y1 * z2)
    (Subring.mul_mem _ (amax_mem_subS p hy1) (amax_mem_subS p hz2)) hy10
  let a0 : AdicCompletion (Ith p) (AinfP p) := y1
  let b0 : AdicCompletion (Ith p) (AinfP p) := y2
  let c0 : AdicCompletion (Ith p) (AinfP p) := z1
  let d0 : AdicCompletion (Ith p) (AinfP p) := z2
  let u : AdicCompletion (Ith p) (AinfP p) := logPTilde p
  change a0 * d0 * FontaineLogCore.psEval (Ith p) (omegaP_mem p)
    (FontaineLogCore.logNeg (invQ p)) ∈ _
  have hu : u = FontaineLogCore.psEval (Ith p) (omegaP_mem p) (FontaineLogCore.logNeg (invQ p)) :=
    logPTilde_eq_core p
  have hrel' : a0 * d0 * u = b0 * c0 := hrel
  rw [← hu, hrel']
  exact Subring.mul_mem _ (amax_mem_subS p hy2) (amax_mem_subS p hz1)

/-- **`BergerBst.LogPTildeTranscendental`, proved** (Brinon-Conrad Thm 9.2.10 at `K = ℚ_p`). -/
theorem logPTildeTranscendental_proof : LogPTildeTranscendental :=
  logPTildeTranscendental_of_notInFrac fun p _ => notInFrac_bmax_logPTilde p

end LogPFontaine
end PkgI4
end HDec

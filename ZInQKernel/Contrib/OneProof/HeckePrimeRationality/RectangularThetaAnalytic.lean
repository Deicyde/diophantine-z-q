import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.RectangularThetaLattice
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Analytic real-grid multiplication for a rectangular pair of quasi-theta functions

The hypotheses are independent entire-function, quasi-period, lattice-zero,
and simple-zero properties. The one-dimensional product identity is derived
by local cancellation and bounded elliptic uniqueness, not assumed.
-/

noncomputable section

open Complex Set Function Filter
open scoped Real UpperHalfPlane BigOperators Topology

namespace RectangularThetaAnalytic

open RectangularThetaLattice
local notation "κ" => ((Real.pi : ℂ)*Complex.I)

/-- The derivative ratio is used only at a simple denominator zero. -/
def quotient (F G : ℂ → ℂ) (z : ℂ) : ℂ :=
  if G z=0 then deriv F z/deriv G z else F z/G z

lemma dslope_entire {F : ℂ → ℂ} (hf : Differentiable ℂ F) (c : ℂ) :
    Differentiable ℂ (dslope F c) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (by simp)).mpr hf.differentiableOn

/-- Local cancellation is supplied by actual divided differences. -/
lemma quotient_entire {F G : ℂ → ℂ} (hf : Differentiable ℂ F) (hg : Differentiable ℂ G)
    (hz : ∀ c, G c=0 → F c=0 ∧ deriv G c≠0) : Differentiable ℂ (quotient F G) := by
  classical
  intro c
  by_cases hc : G c=0
  · obtain ⟨hfc,hgc⟩ := hz c hc
    have hdf := dslope_entire hf c
    have hdg := dslope_entire hg c
    have hn : dslope G c c≠0 := by simpa using hgc
    apply ((hdf c).div (hdg c) hn).congr_of_eventuallyEq
    filter_upwards [(hdg c).continuousAt.eventually_ne hn] with z hgz
    by_cases hzc : z=c
    · subst z
      simp [quotient,hc]
    · have hfacf : (z-c)*dslope F c z=F z := by simpa [hfc] using sub_smul_dslope F c z
      have hfacg : (z-c)*dslope G c z=G z := by simpa [hc] using sub_smul_dslope G c z
      have hGz : G z≠0 := by rw [← hfacg]; exact mul_ne_zero (sub_ne_zero.mpr hzc) hgz
      simp only [quotient,ite_eq_right hGz]
      rw [← hfacf,← hfacg]
      exact mul_div_mul_left _ _ (sub_ne_zero.mpr hzc)
  · apply ((hf c).div (hg c) hc).congr_of_eventuallyEq
    filter_upwards [(hg c).continuousAt.eventually_ne hc] with z hz
    simp [quotient,hz]

lemma simple_punctured {G : ℂ → ℂ} (hg : Differentiable ℂ G) {c : ℂ}
    (hc : G c=0) (hd : deriv G c≠0) : ∀ᶠ z in 𝓝[≠] c, G z≠0 := by
  have hn : dslope G c c≠0 := by simpa using hd
  filter_upwards [((dslope_entire hg c) c).continuousAt.eventually_ne hn |>.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hzc
  have hfac : (z-c)*dslope G c z=G z := by simpa [hc] using sub_smul_dslope G c z
  rw [← hfac]
  exact mul_ne_zero (sub_ne_zero.mpr hzc) hz

lemma quotient_period {F G A : ℂ → ℂ} {a : ℂ}
    (hf : Differentiable ℂ F) (hg : Differentiable ℂ G)
    (hz : ∀ c, G c=0 → F c=0 ∧ deriv G c≠0) (ha : ∀ z, A z≠0)
    (hfa : ∀ z, F (z+a)=A z*F z) (hga : ∀ z, G (z+a)=A z*G z) :
    Function.Periodic (quotient F G) a := by
  have hq := quotient_entire hf hg hz
  have hoff (z : ℂ) (hGz : G z≠0) : quotient F G (z+a)=quotient F G z := by
    simp [quotient,hga,hfa,ha z,hGz,mul_div_mul_left]
  intro c
  by_cases hc : G c=0
  · have hn := simple_punctured hg hc (hz c hc).2
    have hleft : Tendsto (fun z => quotient F G (z+a)) (𝓝[≠] c) (𝓝 (quotient F G (c+a))) :=
      (hq.continuous.comp (continuous_id.add continuous_const)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hright := (hq c).continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {c}ᶜ))
    exact tendsto_nhds_unique (hleft.congr' (hn.mono fun z hz => hoff z hz)) hright
  · exact hoff c hc

/-- Compact parallelogram reduction gives an actual global bound. -/
lemma elliptic_bounded (τ : ℍ) {Q : ℂ → ℂ} (hc : Continuous Q)
    (h1 : Function.Periodic Q 1) (ht : Function.Periodic Q (τ : ℂ)) : Bornology.IsBounded (range Q) := by
  let p : ℝ×ℝ → ℂ := fun x => (x.1 : ℂ)+(x.2 : ℂ)*(τ : ℂ)
  have hp : Continuous p := by fun_prop
  have hk : IsCompact (p '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := (isCompact_Icc.prod isCompact_Icc).image hp
  obtain ⟨B,hB⟩ := hk.bddAbove_image hc.norm.continuousOn
  rw [isBounded_iff_forall_norm_le]
  refine ⟨B,?_⟩
  rintro _ ⟨z,rfl⟩
  let v : ℝ := z.im/τ.im
  let u : ℝ := z.re-v*τ.re
  let m : ℤ := ⌊u⌋
  let n : ℤ := ⌊v⌋
  let w : ℂ := p (u-m,v-n)
  have hu : u-(m : ℝ)∈Icc (0 : ℝ) 1 := ⟨by linarith [Int.floor_le u],by linarith [Int.lt_floor_add_one u]⟩
  have hv : v-(n : ℝ)∈Icc (0 : ℝ) 1 := ⟨by linarith [Int.floor_le v],by linarith [Int.lt_floor_add_one v]⟩
  have hw : w∈p '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := ⟨(u-m,v-n),⟨hu,hv⟩,rfl⟩
  have he : z=(w+(n : ℂ)*(τ : ℂ))+(m : ℂ) := by
    apply Complex.ext
    · simp [w,p,u,v,Complex.mul_re]
      ring
    · simp [w,p,v,Complex.mul_im]
      field_simp [τ.im_ne_zero]
      ring
  have hqw : Q z=Q w := by
    rw [he]
    simpa only [mul_one] using (h1.int_mul m (w+(n : ℂ)*(τ : ℂ))).trans (ht.int_mul n w)
  rw [hqw]
  exact hB ⟨w,hw,rfl⟩

lemma half_nonzero (τ : ℍ) {K : ℂ → ℂ}
    (hk : ∀ z, K z=0 ↔ ∃ a b : ℤ,z=(a : ℂ)+(b : ℂ)*(τ : ℂ)) : K (1/2)≠0 := by
  intro hz
  obtain ⟨a,b,hab⟩ := (hk _).mp hz
  have hi := congrArg Complex.im hab
  norm_num [Complex.mul_im] at hi
  have hb : b=0 := hi.resolve_right τ.im_ne_zero
  subst b
  have hr := congrArg Complex.re hab
  norm_num at hr
  have he : (2 : ℤ)*a=1 := by exact_mod_cast (show (2 : ℝ)*(a : ℝ)=1 by linarith)
  omega

/-- Honest analytic rectangular multiplication for a pair of entire quasi-theta
functions on τ and nτ. Neither product multiplication nor elliptic constancy is a premise. -/
theorem real_multiplication (n : ℕ) (hn : 0<n) (τ : ℍ) (H K : ℂ → ℂ)
    (hH : Differentiable ℂ H) (hK : Differentiable ℂ K)
    (hH1 : ∀ z,H (z+1)=-H z)
    (hHt : ∀ z,H (z+(τ : ℂ))=-cexp (-κ*(τ : ℂ)-2*κ*z)*H z)
    (hK1 : ∀ z,K (z+1)=-K z)
    (hKt : ∀ z,K (z+(upTau n hn τ : ℂ))=-cexp (-κ*(upTau n hn τ : ℂ)-2*κ*z)*K z)
    (hHz : ∀ z,H z=0 ↔ ∃ a b : ℤ,z=(a : ℂ)+(b : ℂ)*(τ : ℂ))
    (hKz : ∀ z,K z=0 ↔ ∃ a b : ℤ,z=(a : ℂ)+(b : ℂ)*(upTau n hn τ : ℂ))
    (hKd : ∀ z,K z=0 → deriv K z≠0) :
    ∃ C : ℂ,C≠0 ∧ ∀ z,realProduct n H z=C*K ((n : ℂ)*z) := by
  let G : ℂ → ℂ := fun z => K ((n : ℂ)*z)
  have hnC : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  have hg : Differentiable ℂ G := hK.fun_comp (differentiable_id.const_mul _)
  have hp := realProduct_differentiable n hH
  have hziff (z : ℂ) : realProduct n H z=0 ↔ G z=0 := by
    rw [realProduct_zero_iff hn τ hHz]
    simpa only [G,upTau_coe] using (hKz ((n : ℂ)*z)).symm
  have hd (z : ℂ) (hz : G z=0) : deriv G z≠0 := by
    have hl : HasDerivAt (fun w : ℂ => (n : ℂ)*w) (n : ℂ) z := by simpa using! (hasDerivAt_id z).const_mul (n : ℂ)
    have he : deriv G z=deriv K ((n : ℂ)*z)*(n : ℂ) := by
      simpa only [G,Function.comp_def] using! ((hK _).hasDerivAt.comp z hl).deriv
    rw [he]
    exact mul_ne_zero (hKd _ hz) hnC
  have hz : ∀ z,G z=0 → realProduct n H z=0 ∧ deriv G z≠0 := fun z h => ⟨(hziff z).mpr h,hd z h⟩
  have hg1 (z : ℂ) : G (z+1)=(-1 : ℂ)^n*G z := by
    dsimp [G]
    rw [show (n : ℂ)*(z+1)=(n : ℂ)*z+(n : ℂ) by ring]
    exact quasi_nat_one hK1 n _
  have hgt (z : ℂ) : G (z+(τ : ℂ))=-cexp (-κ*(n : ℂ)*(τ : ℂ)-2*κ*(n : ℂ)*z)*G z := by
    dsimp [G]
    rw [show (n : ℂ)*(z+(τ : ℂ))=(n : ℂ)*z+(upTau n hn τ : ℂ) by rw [upTau_coe]; ring]
    simpa only [upTau_coe,mul_assoc] using hKt ((n : ℂ)*z)
  have hq := quotient_entire hp hg hz
  have hq1 := quotient_period (A := fun _ => (-1 : ℂ)^n) hp hg hz
    (fun _ => pow_ne_zero _ (by norm_num)) (realProduct_one n hH1) hg1
  have hqt := quotient_period (A := fun z => -cexp (-κ*(n : ℂ)*(τ : ℂ)-2*κ*(n : ℂ)*z)) hp hg hz
    (fun _ => neg_ne_zero.mpr (Complex.exp_ne_zero _)) (realProduct_tau hn τ hHt) hgt
  have hbounded := elliptic_bounded τ hq.continuous hq1 hqt
  let w : ℂ := 1/(2*(n : ℂ))
  let C : ℂ := quotient (realProduct n H) G w
  have hc (z : ℂ) : quotient (realProduct n H) G z=C := hq.apply_eq_apply_of_bounded hbounded z w
  have hgw : G w≠0 := by
    dsimp [G,w]
    rw [show (n : ℂ)*(1/(2*(n : ℂ)))=1/2 by field_simp [hnC]]
    exact half_nonzero _ hKz
  have hpw : realProduct n H w≠0 := fun h => hgw ((hziff w).mp h)
  have hC : C≠0 := by
    dsimp [C,quotient]
    rw [ite_eq_right hgw]
    exact div_ne_zero hpw hgw
  refine ⟨C,hC,?_⟩
  intro z
  have hid : quotient (realProduct n H) G z*G z=realProduct n H z := by
    by_cases hGz : G z=0
    · simp [quotient,hGz,(hz z hGz).1]
    · simp [quotient,hGz]
  rw [hc z] at hid
  exact hid.symm

/-- Honest analytic imaginary-grid multiplication for periods τ and τ/n.
The necessary phase is derived from the mismatched real quasi-period. -/
theorem imag_multiplication (n : ℕ) (hn : 0<n) (τ : ℍ) (H K : ℂ → ℂ)
    (hH : Differentiable ℂ H) (hK : Differentiable ℂ K)
    (hH1 : ∀ z,H (z+1)=-H z)
    (hHt : ∀ z,H (z+(τ : ℂ))=-cexp (-κ*(τ : ℂ)-2*κ*z)*H z)
    (hK1 : ∀ z,K (z+1)=-K z)
    (hKt : ∀ z,K (z+(downTau n hn τ : ℂ))=-cexp (-κ*(downTau n hn τ : ℂ)-2*κ*z)*K z)
    (hHz : ∀ z,H z=0 ↔ ∃ a b : ℤ,z=(a : ℂ)+(b : ℂ)*(τ : ℂ))
    (hKz : ∀ z,K z=0 ↔ ∃ a b : ℤ,z=(a : ℂ)+(b : ℂ)*(downTau n hn τ : ℂ))
    (hKd : ∀ z,K z=0 → deriv K z≠0) :
    ∃ C : ℂ,C≠0 ∧ ∀ z,imagProduct n τ H z=C*cexp (-κ*((n-1 : ℕ) : ℂ)*z)*K z := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  let E : ℂ → ℂ := fun z => cexp (-κ*((n-1 : ℕ) : ℂ)*z)*K z
  have hE : Differentiable ℂ E := by dsimp [E];fun_prop
  have hP := imagProduct_differentiable n τ hH
  have hziff (z : ℂ) : imagProduct n τ H z=0 ↔ E z=0 := by
    rw [imagProduct_zero_iff hn τ hHz,← hKz z]
    simp [E,Complex.exp_ne_zero]
  have hs (z : ℂ) (hz : E z=0) : deriv E z≠0 := by
    have hKzero : K z=0 := by simpa [E,Complex.exp_ne_zero] using hz
    have hlin : HasDerivAt (fun w : ℂ => -κ*((n-1 : ℕ) : ℂ)*w) (-κ*((n-1 : ℕ) : ℂ)) z := by
      simpa using! (hasDerivAt_id z).const_mul (-κ*((n-1 : ℕ) : ℂ))
    have hd : deriv E z=cexp (-κ*((n-1 : ℕ) : ℂ)*z)*deriv K z := by
      simpa only [E,Pi.mul_apply,hKzero,mul_zero,zero_add] using! (hlin.cexp.mul (hK z).hasDerivAt).deriv
    rw [hd]
    exact mul_ne_zero (Complex.exp_ne_zero _) (hKd z hKzero)
  have hz : ∀ z,E z=0 → imagProduct n τ H z=0 ∧ deriv E z≠0 := fun z h => ⟨(hziff z).mpr h,hs z h⟩
  have hphase : cexp (-κ*((n-1 : ℕ) : ℂ))*(-1 : ℂ)=(-1 : ℂ)^n := by
    have hexp : cexp (-κ)=-1 := by rw [Complex.exp_neg,Complex.exp_pi_mul_I];norm_num
    have hh : cexp (-κ*((n-1 : ℕ) : ℂ))=(-1 : ℂ)^(n-1) := by
      rw [mul_comm,Complex.exp_nat_mul,hexp]
    rw [hh]
    have he : n-1+1=n := by omega
    rw [← pow_succ,he]
  have hE1 (z : ℂ) : E (z+1)=(-1 : ℂ)^n*E z := by
    dsimp [E]
    rw [hK1,show -κ*((n-1 : ℕ) : ℂ)*(z+1)=(-κ*((n-1 : ℕ) : ℂ)*z)+(-κ*((n-1 : ℕ) : ℂ)) by ring,
      Complex.exp_add]
    calc
      _ = (cexp (-κ*((n-1 : ℕ) : ℂ))*(-1 : ℂ))*(cexp (-κ*((n-1 : ℕ) : ℂ)*z)*K z) := by ring
      _ = _ := by rw [hphase]
  have hEt (z : ℂ) : E (z+(τ : ℂ))=(-1 : ℂ)^n*
      cexp (-κ*(2*(n : ℂ)-1)*(τ : ℂ)-2*κ*(n : ℂ)*z)*E z := by
    have hKtN : K (z+(τ : ℂ))=(-1 : ℂ)^n*cexp (-κ*(n : ℂ)*(τ : ℂ)-2*κ*(n : ℂ)*z)*K z := by
      have hh := quasi_nat_tau (downTau n hn τ) hKt n z
      rw [downTau_coe] at hh
      have he : (n : ℂ)*((τ : ℂ)/(n : ℂ))=(τ : ℂ) := by field_simp [hnC]
      rw [he] at hh
      convert hh using 2
      congr 1
      field_simp [hnC]
    dsimp [E]
    rw [hKtN]
    have he : (-κ*((n-1 : ℕ) : ℂ)*(z+(τ : ℂ)))+
        (-κ*(n : ℂ)*(τ : ℂ)-2*κ*(n : ℂ)*z)=
        (-κ*(2*(n : ℂ)-1)*(τ : ℂ)-2*κ*(n : ℂ)*z)+(-κ*((n-1 : ℕ) : ℂ)*z) := by
      rw [Nat.cast_sub (show 1≤n by omega),Nat.cast_one]
      ring
    calc
      _ = (-1 : ℂ)^n*(cexp (-κ*((n-1 : ℕ) : ℂ)*(z+(τ : ℂ)))*
        cexp (-κ*(n : ℂ)*(τ : ℂ)-2*κ*(n : ℂ)*z))*K z := by ring
      _ = _ := by rw [← Complex.exp_add,he,Complex.exp_add];ring
  have hQ := quotient_entire hP hE hz
  have hQ1 := quotient_period (A := fun _ => (-1 : ℂ)^n) hP hE hz (fun _ => pow_ne_zero _ (by norm_num))
    (imagProduct_one n τ hH1) hE1
  have hQt := quotient_period (A := fun z => (-1 : ℂ)^n*cexp (-κ*(2*(n : ℂ)-1)*(τ : ℂ)-2*κ*(n : ℂ)*z))
    hP hE hz (fun _ => mul_ne_zero (pow_ne_zero _ (by norm_num)) (Complex.exp_ne_zero _))
    (imagProduct_tau hn τ hHt) hEt
  have hb := elliptic_bounded τ hQ.continuous hQ1 hQt
  let C : ℂ := quotient (imagProduct n τ H) E (1/2)
  have hc (z : ℂ) : quotient (imagProduct n τ H) E z=C := hQ.apply_eq_apply_of_bounded hb z (1/2)
  have hEhalf : E (1/2)≠0 := by dsimp [E];exact mul_ne_zero (Complex.exp_ne_zero _) (half_nonzero _ hKz)
  have hPhalf : imagProduct n τ H (1/2)≠0 := fun h => hEhalf ((hziff _).mp h)
  have hC : C≠0 := by dsimp [C,quotient];rw [ite_eq_right hEhalf];exact div_ne_zero hPhalf hEhalf
  refine ⟨C,hC,?_⟩
  intro z
  have hid : quotient (imagProduct n τ H) E z*E z=imagProduct n τ H z := by
    by_cases hEz : E z=0
    · simp [quotient,hEz,(hz z hEz).1]
    · simp [quotient,hEz]
  rw [hc z] at hid
  simpa only [E,mul_assoc] using hid.symm

end RectangularThetaAnalytic

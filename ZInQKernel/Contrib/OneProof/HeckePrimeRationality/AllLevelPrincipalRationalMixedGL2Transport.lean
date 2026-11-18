import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.RectangularMixedTransport
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPrincipalRationalGL2Transport

/-!
# Positive rational transport of the actual mixed x-lambda span

All modular representatives are in the independently generated Good mixed
span. Integral covariance, verified rectangular mixed diagonals, the actual
weight-three scalar law and exact rational Gaussian factorization supply
all generators. No rational stability or representation hypothesis is
passed to the final positive-determinant endpoint.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

open Complex Function Set
open scoped Real UpperHalfPlane BigOperators MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.RationalMixedTransport

open RationalGaussian RationalPrincipalTransport RectangularMixedTransport
open TorsionWeierstrassData TorsionRectangularHomogeneous AllLevelForms
open CongruenceSubgroup Matrix.SpecialLinearGroup

/-- The unchanged actual completed weight-one family at every integer label. -/
def lambdaFun (N : ℕ) (Q : ℤ × ℤ) : ℍ → ℂ := fun τ => lambdaValue N Q.1 Q.2 τ

lemma lambdaFun_bad (N : ℕ) (Q : ℤ × ℤ) (hQ : (N : ℤ)∣Q.1 ∧ (N : ℤ)∣Q.2) :
    lambdaFun N Q=0 := by
  funext τ
  simp [lambdaFun,lambdaValue,TorsionDistributionTwo.reg_of_bad hQ]

lemma bad_act (N : ℕ) (Q : ℤ × ℤ) (γ : SL(2,ℤ))
    (hQ : (N : ℤ)∣Q.1 ∧ (N : ℤ)∣Q.2) :
    (N : ℤ)∣(ThetaFiveTorsion.act Q γ).1 ∧ (N : ℤ)∣(ThetaFiveTorsion.act Q γ).2 := by
  unfold ThetaFiveTorsion.act
  exact ⟨dvd_add (dvd_mul_of_dvd_left hQ.1 _) (dvd_mul_of_dvd_left hQ.2 _),
    dvd_add (dvd_mul_of_dvd_left hQ.1 _) (dvd_mul_of_dvd_left hQ.2 _)⟩

lemma lambdaFun_good (N : ℕ) (Q : ℤ × ℤ) (hQ : Good N Q) :
    lambdaFun N Q=scale • AllLevelForms.F N Q := by
  funext τ
  change lambdaValue N Q.1 Q.2 τ=scale*Torsion.torsionLogDerivative N Q.1 Q.2 τ
  exact lambdaValue_of_good N Q.1 Q.2 τ hQ

/-- Actual integral covariance of lambda at all labels, with bad labels proved zero. -/
theorem lambdaFun_slash (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) (Q : ℤ × ℤ) :
    lambdaFun N Q ∣[(1 : ℤ)] γ=lambdaFun N (ThetaFiveTorsion.act Q γ) := by
  by_cases hQ : (N : ℤ)∣Q.1 ∧ (N : ℤ)∣Q.2
  · rw [lambdaFun_bad N Q hQ,lambdaFun_bad N _ (bad_act N Q γ hQ),SlashAction.zero_slash]
  · have hg : Good N Q := hQ
    rw [lambdaFun_good N Q hg,lambdaFun_good N _ (good_act hg γ),
      _root_.ModularForm.SL_smul_slash,AllLevelForms.F_slash hN γ Q hg]

/-- The actual x-lambda mixed value, not a homogeneous lambda product. -/
def mixedFun (N : ℕ) (P Q : ℤ × ℤ) : ℍ → ℂ := WeierstrassForms.X N P * lambdaFun N Q

lemma mixedFun_apply (N : ℕ) (P Q : ℤ × ℤ) (τ : ℍ) :
    mixedFun N P Q τ=xValue N P.1 P.2 τ*lambdaValue N Q.1 Q.2 τ := rfl

lemma coe_mixedForm (N : ℕ) (hN : 0<N) (P Q : ℤ × ℤ) :
    (mixedForm N hN P Q : ℍ → ℂ)=mixedFun N P Q := by
  funext τ
  rw [mixedForm_apply,mixedFun_apply]

/-- Multiplication of lower-weight slashes is used only for integral SL₂,
where determinant one makes the actual multiplication law valid. -/
theorem mixedFun_slash (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) (P Q : ℤ × ℤ) :
    mixedFun N P Q ∣[(3 : ℤ)] γ=
      mixedFun N (ThetaFiveTorsion.act P γ) (ThetaFiveTorsion.act Q γ) := by
  unfold mixedFun
  rw [show (3 : ℤ)=2+1 by rfl,_root_.ModularForm.mul_slash_SL2,
    WeierstrassForms.X_slash hN γ P,lambdaFun_slash N hN γ Q]

/-- The generic actual integral translate/restrict map transports every mixed generator. -/
theorem integral_mixedForm (γ : SL(2,ℤ)) (N : ℕ) (hN : 0<N) (P Q : ℤ × ℤ) :
    integralMap γ N 3 (mixedForm N hN P Q)=
      mixedForm N hN (ThetaFiveTorsion.act P γ) (ThetaFiveTorsion.act Q γ) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [integralMap_apply]
  have hmap : mapGL ℝ γ=(γ : GLR) := by
    ext i j
    rfl
  have hs := congrFun (mixedFun_slash N hN γ P Q) τ
  rw [_root_.ModularForm.SL_slash,← hmap,← coe_mixedForm N hN P Q,
    ← coe_mixedForm N hN (ThetaFiveTorsion.act P γ) (ThetaFiveTorsion.act Q γ)] at hs
  exact hs

/-- Integral SL₂ preserves the actual Good mixed span at its original level. -/
theorem integral_mixedSpan (γ : SL(2,ℤ)) (N : ℕ) (hN : 0<N)
    {f : _root_.ModularForm (PrincipalGroup N) 3} (hf : f∈mixedSpan N hN) :
    integralMap γ N 3 f∈mixedSpan N hN := by
  have hle : mixedSpan N hN ≤ (mixedSpan N hN).comap (integralMap γ N 3) := by
    apply Submodule.span_le.mpr
    rintro f ⟨P,Q,hP,hQ,rfl⟩
    change integralMap γ N 3 (mixedForm N hN P Q)∈mixedSpan N hN
    rw [integral_mixedForm]
    exact mixedForm_mem N hN _ _
  exact hle hf

/-- A concrete mixed modular representative with the level bound as a parameter. -/
def RepresentsMixedAt (M : ℕ) (hM : 0<M) (u : ℍ → ℂ) : Prop :=
  ∃ F : _root_.ModularForm (PrincipalGroup M) 3, F∈mixedSpan M hM ∧ ∀ τ : ℍ,F τ=u τ

lemma representsMixedAt_level {M L : ℕ} {hM : 0<M} {hL : 0<L} {u : ℍ → ℂ}
    (hlevel : M=L) (h : RepresentsMixedAt M hM u) : RepresentsMixedAt L hL u := by
  cases hlevel
  exact h

/-- A uniform positive level multiplier, independent of the input level or form. -/
def UniformMixedTransport (g : GLR) : Prop :=
  ∃ (D : ℕ) (hD : 0<D), ∀ (N : ℕ) (hN : 0<N)
    (f : _root_.ModularForm (PrincipalGroup N) 3), f∈mixedSpan N hN →
      RepresentsMixedAt (D*N) (Nat.mul_pos hD hN) (⇑f ∣[(3 : ℤ)] g)

theorem uniform_mixed_mul {g h : GLR} (hg : UniformMixedTransport g) (hh : UniformMixedTransport h) :
    UniformMixedTransport (g*h) := by
  obtain ⟨D,hD,hg⟩ := hg
  obtain ⟨E,hE,hh⟩ := hh
  refine ⟨E*D,Nat.mul_pos hE hD,?_⟩
  intro N hN f hf
  obtain ⟨F,hF,hFeq⟩ := hg N hN f hf
  obtain ⟨G,hG,hGeq⟩ := hh (D*N) (Nat.mul_pos hD hN) F hF
  have hrep : (⇑F : ℍ → ℂ)=(⇑f ∣[(3 : ℤ)] g) := funext hFeq
  have hout : RepresentsMixedAt (E*(D*N)) (Nat.mul_pos hE (Nat.mul_pos hD hN))
      (⇑f ∣[(3 : ℤ)] (g*h)) := by
    refine ⟨G,hG,?_⟩
    intro τ
    rw [hGeq τ,hrep,← SlashAction.slash_mul]
  exact representsMixedAt_level (Nat.mul_assoc E D N).symm hout

theorem uniform_mixed_integral (γ : SL(2,ℤ)) : UniformMixedTransport (mapGL ℝ γ) := by
  refine ⟨1,by omega,?_⟩
  intro N hN f hf
  have hrep : RepresentsMixedAt N hN (⇑f ∣[(3 : ℤ)] mapGL ℝ γ) :=
    ⟨integralMap γ N 3 f,integral_mixedSpan γ N hN hf,integralMap_apply γ N 3 f⟩
  exact representsMixedAt_level (Nat.one_mul N).symm hrep

/-- The verified actual mixed rectangular theorem supplies the forward integer atom. -/
theorem uniform_mixed_integer_diagonal (n : ℕ) [NeZero n] : UniformMixedTransport (TauCeti.scaleGL n) := by
  refine ⟨n,NeZero.pos n,?_⟩
  intro N hN f hf
  exact ⟨forwardWeightMap (n := n) N 3 f,forward_mixedSpan N hN hf,forwardWeightMap_apply N 3 f⟩

/-- Inverse mixed transport uses its separate actual weight-three n^-2 normalization. -/
theorem uniform_mixed_inverse_integer_diagonal (n : ℕ) [NeZero n] :
    UniformMixedTransport ((TauCeti.scaleGL n)⁻¹) := by
  refine ⟨n,NeZero.pos n,?_⟩
  intro N hN f hf
  exact ⟨inverseWeightMap (n := n) N 3 f,inverse_mixedSpan N hN hf,inverseWeightMap_apply N 3 f⟩

/-- The actual scalar law at weight three has coefficient t, not the product
of weight-two and weight-one scalar slash coefficients. -/
theorem uniform_mixed_scalar (t : ℚ) (ht : 0<t) : UniformMixedTransport (mapR (scalarQ t ht)) := by
  refine ⟨1,by omega,?_⟩
  intro N hN f hf
  have hrep : RepresentsMixedAt N hN (⇑f ∣[(3 : ℤ)] mapR (scalarQ t ht)) := by
    refine ⟨(t : ℂ) • f,Submodule.smul_mem _ _ hf,?_⟩
    intro τ
    rw [_root_.smul_apply,smul_eq_mul,RationalPrincipalTransport.scalar_slash_apply]
    norm_num
  exact representsMixedAt_level (Nat.one_mul N).symm hrep

theorem uniform_mixed_upper (x : ℚ) : UniformMixedTransport (mapR (upperQ x)) := by
  let _ : NeZero x.den := ⟨(Rat.den_pos x).ne'⟩
  have hq : (TauCeti.scaleGLRat x.den)⁻¹ * mapGL ℚ (ModularGroup.T^x.num) * TauCeti.scaleGLRat x.den=upperQ x := by
    simpa only [Rat.num_div_den] using upperQ_fraction x.num x.den
  have hr : (TauCeti.scaleGL x.den)⁻¹ * mapGL ℝ (ModularGroup.T^x.num) * TauCeti.scaleGL x.den=mapR (upperQ x) := by
    simpa only [map_mul,map_inv,mapR_integer_diagonal,mapR_sl] using congrArg mapR hq
  rw [← hr]
  exact uniform_mixed_mul (uniform_mixed_mul (uniform_mixed_inverse_integer_diagonal x.den)
    (uniform_mixed_integral (ModularGroup.T^x.num))) (uniform_mixed_integer_diagonal x.den)

theorem uniform_mixed_lower (x : ℚ) : UniformMixedTransport (mapR (lowerQ x)) := by
  have hr : mapGL ℝ ModularGroup.S*mapR (upperQ (-x))*mapGL ℝ (ModularGroup.S⁻¹)=mapR (lowerQ x) := by
    simpa only [map_mul,map_inv,mapR_sl] using congrArg mapR (lowerQ_S x)
  rw [← hr]
  exact uniform_mixed_mul (uniform_mixed_mul (uniform_mixed_integral ModularGroup.S) (uniform_mixed_upper (-x)))
    (uniform_mixed_integral ModularGroup.S⁻¹)

theorem uniform_mixed_positive_diagonal (q : ℚ) (hq : 0<q) : UniformMixedTransport (mapR (diagonalQ q hq)) := by
  obtain ⟨m,n,hm,hn,hEq⟩ := diagonalQ_fraction q hq
  let _ : NeZero m := ⟨hm.ne'⟩
  let _ : NeZero n := ⟨hn.ne'⟩
  have hr : TauCeti.scaleGL m*(TauCeti.scaleGL n)⁻¹=mapR (diagonalQ q hq) := by
    simpa only [map_mul,map_inv,mapR_integer_diagonal] using congrArg mapR hEq
  rw [← hr]
  exact uniform_mixed_mul (uniform_mixed_integer_diagonal m) (uniform_mixed_inverse_integer_diagonal n)

/-- Full positive rational mixed transport, with all atom and Gaussian obligations filled. -/
theorem uniform_mixed_positive_rational (A : GLQ) (hA : 0<detQ A) : UniformMixedTransport (mapR A) := by
  obtain ⟨γ,x,y,t,q,ht,hq,hEq⟩ := exists_positive_gaussian A hA
  have hr : mapR A=mapGL ℝ γ*mapR (lowerQ x)*mapR (scalarQ t ht)*mapR (diagonalQ q hq)*mapR (upperQ y) := by
    simpa only [map_mul,mapR_sl] using congrArg mapR hEq
  rw [hr]
  exact uniform_mixed_mul (uniform_mixed_mul (uniform_mixed_mul
    (uniform_mixed_mul (uniform_mixed_integral γ) (uniform_mixed_lower x)) (uniform_mixed_scalar t ht))
    (uniform_mixed_positive_diagonal q hq)) (uniform_mixed_upper y)

/-- An actual common-level mixed-span endpoint with no rational factorization,
closure or representation premise, and with a proved positive integer multiple of N. -/
theorem actual_positive_rational_mixed_transport (N : ℕ) (hN : 0<N)
    (f : _root_.ModularForm (PrincipalGroup N) 3) (hf : f∈mixedSpan N hN)
    (A : GLQ) (hA : 0<(A.det : ℚ)) :
    ∃ (M : ℕ) (hM : 0<M),N∣M ∧
      ∃ F : _root_.ModularForm (PrincipalGroup M) 3,F∈mixedSpan M hM ∧
        ∀ τ : ℍ,F τ=(⇑f ∣[(3 : ℤ)] Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) A) τ := by
  obtain ⟨D,hD,htransport⟩ := uniform_mixed_positive_rational A hA
  obtain ⟨F,hF,hFeq⟩ := htransport N hN f hf
  exact ⟨D*N,Nat.mul_pos hD hN,Nat.dvd_mul_left N D,F,hF,hFeq⟩

/-- Every actual all-label mixed generator has the same rational transport,
using the separately proved zero cases to establish its Good-span membership. -/
theorem actual_all_label_mixed_transport (N : ℕ) (hN : 0<N) (P Q : ℤ × ℤ)
    (A : GLQ) (hA : 0<(A.det : ℚ)) :
    ∃ (M : ℕ) (hM : 0<M),N∣M ∧
      ∃ F : _root_.ModularForm (PrincipalGroup M) 3,F∈mixedSpan M hM ∧
        ∀ τ : ℍ,F τ=(mixedFun N P Q ∣[(3 : ℤ)] mapR A) τ := by
  obtain ⟨M,hM,hNM,F,hF,hFeq⟩ := actual_positive_rational_mixed_transport N hN
    (mixedForm N hN P Q) (mixedForm_mem N hN P Q) A hA
  refine ⟨M,hM,hNM,F,hF,?_⟩
  intro τ
  rw [hFeq τ,coe_mixedForm]
  rfl

end ZInQ.Contrib.HeckePrimeRationality.RationalMixedTransport

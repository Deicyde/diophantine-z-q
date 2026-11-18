import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PositiveRationalMatrixGaussian
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightTorsionRectangularScale

/-!
# Actual principal torsion-product transport under positive rational matrices

Every transport is constructed at a positive finite principal level which is
an explicit integer multiple of the input level. Integral determinant-one
covariance, the rectangular diagonal operators and the actual scalar slash
law supply the generators. Gaussian factorization closes the arbitrary
positive-determinant rational endpoint without an assumed stability or
representation predicate.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Complex Function Set
open scoped Real UpperHalfPlane BigOperators MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.RationalPrincipalTransport

open RationalGaussian TorsionRectangularHomogeneous AllLevelProducts AllLevelForms
open CongruenceSubgroup Matrix.SpecialLinearGroup

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- An actual modular representative in the genuine homogeneous product subspace.
Keeping the level as a bound parameter avoids rewriting specialized instances. -/
def RepresentsAt (M : ℕ) (hM : 0<M) (k : ℕ) (u : ℍ → ℂ) : Prop :=
  ∃ F : _root_.ModularForm (ΓP M) (k : ℤ), F∈homogeneousSpan M hM k ∧
    ∀ τ : ℍ,F τ=u τ

lemma representsAt_level {M L : ℕ} {hM : 0<M} {hL : 0<L} {k : ℕ} {u : ℍ → ℂ}
    (hlevel : M=L) (h : RepresentsAt M hM k u) : RepresentsAt L hL k u := by
  cases hlevel
  exact h

/-- A uniform positive multiplier, not just an unconstrained existential level.
The predicate is discharged by proved generators before the actual endpoint. -/
def UniformTransport (g : GLR) : Prop :=
  ∃ (D : ℕ) (hD : 0<D), ∀ (N : ℕ) (hN : 0<N) (k : ℕ)
    (f : _root_.ModularForm (ΓP N) (k : ℤ)), f∈homogeneousSpan N hN k →
      RepresentsAt (D*N) (Nat.mul_pos hD hN) k (⇑f ∣[(k : ℤ)] g)

/-- The uniform multiplier is multiplied in the actual order of successive slashes. -/
theorem uniform_mul {g h : GLR} (hg : UniformTransport g) (hh : UniformTransport h) :
    UniformTransport (g*h) := by
  obtain ⟨D,hD,hg⟩ := hg
  obtain ⟨E,hE,hh⟩ := hh
  refine ⟨E*D,Nat.mul_pos hE hD,?_⟩
  intro N hN k f hf
  obtain ⟨F,hF,hFeq⟩ := hg N hN k f hf
  obtain ⟨G,hG,hGeq⟩ := hh (D*N) (Nat.mul_pos hD hN) k F hF
  have hrep : (⇑F : ℍ → ℂ)=(⇑f ∣[(k : ℤ)] g) := funext hFeq
  have hout : RepresentsAt (E*(D*N)) (Nat.mul_pos hE (Nat.mul_pos hD hN)) k
      (⇑f ∣[(k : ℤ)] (g*h)) := by
    refine ⟨G,hG,?_⟩
    intro τ
    rw [hGeq τ,hrep,← SlashAction.slash_mul]
  exact representsAt_level (Nat.mul_assoc E D N).symm hout

/-- Principal congruence groups are normalized by each actual integral SL₂ matrix. -/
theorem principal_SL_inclusion (N : ℕ) (γ : SL(2,ℤ)) :
    (ΓP N) ≤ ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (ΓP N) := by
  rintro _ ⟨δ,hδ,rfl⟩
  change δ∈CongruenceSubgroup.Gamma N at hδ
  rw [map_inv,(ΓP N).mem_inv_pointwise_smul_iff,ConjAct.toConjAct_smul]
  refine ⟨γ*δ*γ⁻¹,(CongruenceSubgroup.Gamma_normal N).conj_mem δ hδ γ,?_⟩
  simp only [map_mul,map_inv]

/-- The actual integral SL₂ translate restricted back to the unchanged principal level. -/
def integralMap (γ : SL(2,ℤ)) (N k : ℕ) :
    _root_.ModularForm (ΓP N) (k : ℤ) →ₗ[ℂ] _root_.ModularForm (ΓP N) (k : ℤ) :=
  (_root_.ModularForm.restrictₗ (k : ℤ) ℂ (principal_SL_inclusion N γ)).comp
    (_root_.ModularForm.translateₗ (mapGL ℝ γ) (by simp))

lemma integralMap_apply (γ : SL(2,ℤ)) (N k : ℕ) (f : _root_.ModularForm (ΓP N) (k : ℤ)) (τ : ℍ) :
    integralMap γ N k f τ=(⇑f ∣[(k : ℤ)] mapGL ℝ γ) τ := by
  change _root_.ModularForm.restrict (principal_SL_inclusion N γ)
    (_root_.ModularForm.translate f (mapGL ℝ γ)) τ = _
  rw [← _root_.ModularForm.coe_translate]
  rfl

/-- The generator is transported by the already proved actual label covariance. -/
theorem integral_product (γ : SL(2,ℤ)) (N : ℕ) (hN : 0<N) (k : ℕ) (v : Fin k → ℤ × ℤ)
    (hv : ∀ i,Good N (v i)) :
    integralMap γ N k (productForm N hN k v hv)=
      productForm N hN k (fun i => ThetaFiveTorsion.act (v i) γ) (good_act_tuple hv γ) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [integralMap_apply]
  have hmap : mapGL ℝ γ=(γ : GLR) := by
    ext i j
    rfl
  have hs := congrFun (productForm_slash hN k v hv γ) τ
  rw [_root_.ModularForm.SL_slash,← hmap] at hs
  exact hs

/-- Integral covariance preserves the genuine homogeneous subspace at the same level. -/
theorem integral_mem (γ : SL(2,ℤ)) (N : ℕ) (hN : 0<N) (k : ℕ)
    {f : _root_.ModularForm (ΓP N) (k : ℤ)} (hf : f∈homogeneousSpan N hN k) :
    integralMap γ N k f∈homogeneousSpan N hN k := by
  have hle : homogeneousSpan N hN k ≤ (homogeneousSpan N hN k).comap (integralMap γ N k) := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,hv,rfl⟩
    change integralMap γ N k (productForm N hN k v hv)∈homogeneousSpan N hN k
    rw [integral_product]
    exact Submodule.subset_span ⟨fun i => ThetaFiveTorsion.act (v i) γ,good_act_tuple hv γ,rfl⟩
  exact hle hf

theorem uniform_integral (γ : SL(2,ℤ)) : UniformTransport (mapGL ℝ γ) := by
  refine ⟨1,by omega,?_⟩
  intro N hN k f hf
  have hrep : RepresentsAt N hN k (⇑f ∣[(k : ℤ)] mapGL ℝ γ) :=
    ⟨integralMap γ N k f,integral_mem γ N hN k hf,integralMap_apply γ N k f⟩
  exact representsAt_level (Nat.one_mul N).symm hrep

/-- The accepted actual rectangular forward operator supplies multiplier n. -/
theorem uniform_integer_diagonal (n : ℕ) [NeZero n] : UniformTransport (TauCeti.scaleGL n) := by
  refine ⟨n,NeZero.pos n,?_⟩
  intro N hN k f hf
  exact ⟨forwardWeightMap (n := n) N k f,forward_homogeneous_mem N hN k hf,forwardWeightMap_apply N k f⟩

/-- The accepted inverse rectangular operator supplies the same multiplier n. -/
theorem uniform_inverse_integer_diagonal (n : ℕ) [NeZero n] : UniformTransport ((TauCeti.scaleGL n)⁻¹) := by
  refine ⟨n,NeZero.pos n,?_⟩
  intro N hN k f hf
  exact ⟨inverseWeightMap (n := n) N k f,inverse_homogeneous_mem N hN k hf,inverseWeightMap_apply N k f⟩

/-- The positive scalar factor is derived from the actual determinant/denominator
slash formula. It is t^(k-2), including weights zero and one. -/
theorem scalar_slash_apply (t : ℚ) (ht : 0<t) (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] mapR (scalarQ t ht)) τ=(t : ℂ)^(k-2)*f τ := by
  let u : ℝˣ := Units.map (algebraMap ℚ ℝ).toMonoidHom (Units.mk0 t ht.ne')
  have hu : (u : ℝ)=(t : ℝ) := rfl
  have hs : mapR (scalarQ t ht)=Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    exact Matrix.GeneralLinearGroup.map_scalar (algebraMap ℚ ℝ) (Units.mk0 t ht.ne')
  have htR : (0 : ℝ)<t := by exact_mod_cast ht
  have htC : (t : ℂ)≠0 := by exact_mod_cast ht.ne'
  have hdet : 0<((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det : ℝ) := by
    rw [Matrix.GeneralLinearGroup.det_scalar]
    simpa only [Fintype.card_fin,Units.val_pow_eq_pow_val,hu] using pow_pos htR 2
  rw [hs,_root_.ModularForm.slash_apply,UpperHalfPlane.σ_eq_refl_of_det_pos hdet]
  simp only [ContinuousAlgEquiv.refl_apply,UpperHalfPlane.glScalar_smul,
    Matrix.GeneralLinearGroup.det_scalar,Fintype.card_fin,Units.val_pow_eq_pow_val,
    UpperHalfPlane.denom_scalar,hu]
  rw [abs_of_pos (pow_pos htR 2)]
  push_cast
  have hp : ((t : ℂ)^2)^(k-1)*(t : ℂ)^(-k)=(t : ℂ)^(k-2) := by
    rw [← zpow_natCast,← zpow_mul,← zpow_add₀ htC]
    congr 1
    ring
  calc
    f τ*((t : ℂ)^2)^(k-1)*(t : ℂ)^(-k) =
      (((t : ℂ)^2)^(k-1)*(t : ℂ)^(-k))*f τ := by ring
    _ = _ := by rw [hp]

/-- Positive scalar matrices keep the level and multiply by the actual constant. -/
theorem uniform_scalar (t : ℚ) (ht : 0<t) : UniformTransport (mapR (scalarQ t ht)) := by
  refine ⟨1,by omega,?_⟩
  intro N hN k f hf
  have hrep : RepresentsAt N hN k (⇑f ∣[(k : ℤ)] mapR (scalarQ t ht)) := by
    refine ⟨(t : ℂ)^((k : ℤ)-2) • f,Submodule.smul_mem _ _ hf,?_⟩
    intro τ
    rw [_root_.smul_apply,smul_eq_mul,scalar_slash_apply]
  exact representsAt_level (Nat.one_mul N).symm hrep

/-- Every rational upper translation is supplied by an exact integer-denominator
conjugation; its level multiplier is the product of the two denominator steps. -/
theorem uniform_upper (x : ℚ) : UniformTransport (mapR (upperQ x)) := by
  let _ : NeZero x.den := ⟨(Rat.den_pos x).ne'⟩
  have hq : (TauCeti.scaleGLRat x.den)⁻¹ * mapGL ℚ (ModularGroup.T^x.num) * TauCeti.scaleGLRat x.den=upperQ x := by
    simpa only [Rat.num_div_den] using upperQ_fraction x.num x.den
  have hr : (TauCeti.scaleGL x.den)⁻¹ * mapGL ℝ (ModularGroup.T^x.num) * TauCeti.scaleGL x.den=mapR (upperQ x) := by
    simpa only [map_mul,map_inv,mapR_integer_diagonal,mapR_sl] using congrArg mapR hq
  rw [← hr]
  exact uniform_mul (uniform_mul (uniform_inverse_integer_diagonal x.den)
    (uniform_integral (ModularGroup.T^x.num))) (uniform_integer_diagonal x.den)

/-- Every rational lower translation uses the verified pinned S conjugation. -/
theorem uniform_lower (x : ℚ) : UniformTransport (mapR (lowerQ x)) := by
  have hr : mapGL ℝ ModularGroup.S * mapR (upperQ (-x)) * mapGL ℝ (ModularGroup.S⁻¹)=mapR (lowerQ x) := by
    simpa only [map_mul,map_inv,mapR_sl] using congrArg mapR (lowerQ_S x)
  rw [← hr]
  exact uniform_mul (uniform_mul (uniform_integral ModularGroup.S) (uniform_upper (-x)))
    (uniform_integral ModularGroup.S⁻¹)

/-- Positive rational diagonal ratios are supplied by positive integer diagonal
operators and inverse operators, with no assumed rational stability statement. -/
theorem uniform_positive_diagonal (q : ℚ) (hq : 0<q) : UniformTransport (mapR (diagonalQ q hq)) := by
  obtain ⟨m,n,hm,hn,hEq⟩ := diagonalQ_fraction q hq
  let _ : NeZero m := ⟨hm.ne'⟩
  let _ : NeZero n := ⟨hn.ne'⟩
  have hr : TauCeti.scaleGL m*(TauCeti.scaleGL n)⁻¹=mapR (diagonalQ q hq) := by
    simpa only [map_mul,map_inv,mapR_integer_diagonal] using congrArg mapR hEq
  rw [← hr]
  exact uniform_mul (uniform_integer_diagonal m) (uniform_inverse_integer_diagonal n)

/-- Every actual positive-determinant rational matrix has a proved uniform level
multiplier. All generator and factorization obligations are filled internally. -/
theorem uniform_positive_rational (A : GLQ) (hA : 0<detQ A) : UniformTransport (mapR A) := by
  obtain ⟨γ,x,y,t,q,ht,hq,hEq⟩ := exists_positive_gaussian A hA
  have hr : mapR A=mapGL ℝ γ*mapR (lowerQ x)*mapR (scalarQ t ht)*mapR (diagonalQ q hq)*mapR (upperQ y) := by
    simpa only [map_mul,mapR_sl] using congrArg mapR hEq
  rw [hr]
  exact uniform_mul (uniform_mul (uniform_mul (uniform_mul (uniform_integral γ) (uniform_lower x))
    (uniform_scalar t ht)) (uniform_positive_diagonal q hq)) (uniform_upper y)

/-- Actual rational GL₂ transport at a constructed positive common principal
level divisible by N. No factorization, stability, closure or representation
hypothesis occurs at this endpoint. -/
theorem actual_positive_rational_transport (N : ℕ) (hN : 0<N) (k : ℕ)
    (f : _root_.ModularForm (ΓP N) (k : ℤ)) (hf : f∈homogeneousSpan N hN k)
    (A : GLQ) (hA : 0<(A.det : ℚ)) :
    ∃ (M : ℕ) (hM : 0<M), N∣M ∧
      ∃ F : _root_.ModularForm (ΓP M) (k : ℤ), F∈homogeneousSpan M hM k ∧
        ∀ τ : ℍ,F τ=(⇑f ∣[(k : ℤ)] Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) A) τ := by
  obtain ⟨D,hD,htransport⟩ := uniform_positive_rational A hA
  obtain ⟨F,hF,hFeq⟩ := htransport N hN k f hf
  exact ⟨D*N,Nat.mul_pos hD hN,Nat.dvd_mul_left N D,F,hF,hFeq⟩

end ZInQ.Contrib.HeckePrimeRationality.RationalPrincipalTransport

import ZInQKernel.Contrib.OneProof.AbVarQuotientComplement
import ZInQKernel.Contrib.OneProof.ShimuraQuotientImageSum
import ZInQKernel.Contrib.OneProof.EigenformCoeffFieldFiniteProof
import ZInQKernel.Contrib.OneProof.HeckePin
import Mathlib.RingTheory.Localization.BaseChange

/-! The abelian variety quotient and coefficient-field action in `AfShimura`. -/

noncomputable section

namespace AfTateLam

open CategoryTheory AlgebraicGeometry LeafModCurves PkgI3
open PkgI4 (CF coeff IsNormalizedEigenform)
open R16Thm1 (Rel comp preC postC)
open ShimuraSteps.Quotient (imageSum_exists abVarQuotientBySubvarietyExists
  kills_iff_kills_imageSum)
open scoped TensorProduct nonZeroDivisors

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {f : CF N 2} {J A : AbVar ℚ}
  {tp : Nat.Primes → AbVar.End J} {δ : (ZMod N)ˣ → AbVar.End J} {π : AbVar.Hom J A}

private theorem exists_afQuotient (χ : DirichletCharacter ℂ N) (f : CF N 2)
    (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J) :
    ∃ (A : AbVar ℚ) (π : AbVar.Hom J A), IsAfQuotient χ f tp δ A π := by
  let I : Set (AbVar.End J) := {t | ∃ h : HeckeFree N, evF χ f h = 0 ∧ heckeJ tp δ h = t}
  obtain ⟨C, i, hi⟩ := imageSum_exists I
  obtain ⟨A, π, hπ⟩ := abVarQuotientBySubvarietyExists J C i hi.closed
  have kills_iff {B : AbVar ℚ} (φ : AbVar.Hom J B) :
      KillsIf χ f tp δ φ ↔ i.hom ≫ φ.hom = (0 : AbVar.Hom C B).hom := by
    rw [← kills_iff_kills_imageSum hi φ]
    constructor
    · rintro h _ ⟨g, hg, rfl⟩
      exact h g hg
    · intro h g hg
      exact h _ ⟨g, hg, rfl⟩
  exact ⟨A, π, hπ.surjective, (kills_iff π).mpr hπ.kernel.w,
    fun B φ hφ => hπ.lift_unique B φ ((kills_iff φ).mp hφ)⟩

private theorem af_coeffField_finite (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ) :
    FiniteDimensional ℚ (coeffField f) := by
  let _ : NeZero N := ⟨by omega⟩
  exact eigenformCoeffFieldFinite_proof N 2 χ f le_rfl
    (DSCoeffExt.isNormalizedEigenformDS_of hf)

/-- The universal property descends the free Hecke action integrally. -/
private def inducedHecke (hQ : IsAfQuotient χ f tp δ A π) : HeckeFree N →+* AbVar.End A := by
  let descend (g : HeckeFree N) := (R16Thm1.exists_rel hQ g).choose
  have rel (g : HeckeFree N) : Rel π (heckeJ tp δ g) (descend g) :=
    (R16Thm1.exists_rel hQ g).choose_spec
  refine
    { toFun := descend
      map_zero' := ?zero
      map_one' := ?one
      map_add' := ?add
      map_mul' := ?mul }
  case zero =>
    apply R16Thm1.hom_ext_of_isAfQuotient hQ
    rw [← rel 0, map_zero]
    exact (map_zero (preC π)).trans (map_zero (postC π)).symm
  case one =>
    apply R16Thm1.hom_ext_of_isAfQuotient hQ
    rw [← rel 1, map_one]
    exact R16Thm1.rel_one π
  case add =>
    intro g h
    apply R16Thm1.hom_ext_of_isAfQuotient hQ
    rw [← rel (g + h), map_add]
    change preC π (heckeJ tp δ g + heckeJ tp δ h) = postC π (descend g + descend h)
    rw [map_add, map_add]
    exact congrArg₂ (· + ·) (rel g) (rel h)
  case mul =>
    intro g h
    apply R16Thm1.hom_ext_of_isAfQuotient hQ
    rw [← rel (g * h), map_mul]
    exact R16Thm1.rel_mul (rel g) (rel h)

private theorem inducedHecke_rel (hQ : IsAfQuotient χ f tp δ A π) (g : HeckeFree N) :
    Rel π (heckeJ tp δ g) (inducedHecke hQ g) :=
  (R16Thm1.exists_rel hQ g).choose_spec

/-- The induced action kills the kernel of evaluation. -/
private theorem inducedHecke_eq_zero (hQ : IsAfQuotient χ f tp δ A π) {g : HeckeFree N}
    (hg : evF χ f g = 0) : inducedHecke hQ g = 0 := by
  apply R16Thm1.hom_ext_of_isAfQuotient hQ
  rw [← inducedHecke_rel hQ g]
  have hz : comp (heckeJ tp δ g) π = 0 := by
    apply AbVar.Hom.ext'
    exact hQ.2.1 g hg
  exact hz.trans (map_zero (postC π)).symm

/-- The prime-square recurrence and Dirichlet's theorem put the diamond eigenvalues in
the field of Fourier coefficients. -/
private theorem diamond_mem_coeffField (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (d : (ZMod N)ˣ) : χ (d : ZMod N) ∈ coeffField f := by
  let _ : NeZero N := ⟨by omega⟩
  obtain ⟨p, -, hp, hpd⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := N) d.isUnit N
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hχ : (coeff f p * coeff f p - coeff f (p * p)) / (p : ℂ) = χ (d : ZMod N) := by
    rw [R16Thm1.coeff_sq_relation hf hp, hpd, mul_div_cancel_right₀ _ hp0]
  have hp_mem : (p : ℂ) ∈ coeffField f := by
    simpa only [map_natCast] using IntermediateField.algebraMap_mem (coeffField f) (p : ℚ)
  rw [← hχ]
  exact div_mem (sub_mem (mul_mem (coeff_mem_coeffField f p) (coeff_mem_coeffField f p))
    (coeff_mem_coeffField f (p * p))) hp_mem

private def integralEvaluation (χ : DirichletCharacter ℂ N) (f : CF N 2)
    (hχ : ∀ d : (ZMod N)ˣ, χ (d : ZMod N) ∈ coeffField f) :
    HeckeFree N →ₐ[ℤ] coeffField f :=
  FreeAlgebra.lift ℤ (Sum.elim
    (fun p : Nat.Primes => ⟨coeff f p, coeff_mem_coeffField f p⟩)
    (fun d => ⟨χ (d : ZMod N), hχ d⟩))

private theorem integralEvaluation_coe
    (hχ : ∀ d : (ZMod N)ˣ, χ (d : ZMod N) ∈ coeffField f) (g : HeckeFree N) :
    (integralEvaluation χ f hχ g : ℂ) = evF χ f g := by
  have h : ((coeffField f).val.restrictScalars ℤ).comp (integralEvaluation χ f hχ) = evF χ f := by
    apply FreeAlgebra.hom_ext
    funext x
    cases x <;> simp [Function.comp_apply, integralEvaluation, evF]
  exact DFunLike.congr_fun h g

private def rationalEvaluation {K : Type*} [Field K] [Algebra ℚ K] (S : Subalgebra ℤ K) :
    ℚ ⊗[ℤ] S →ₐ[ℚ] K :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ K) S.val
    (fun q s => Algebra.commutes (R := ℚ) q (s : K))

private theorem rationalEvaluation_one_tmul {K : Type*} [Field K] [Algebra ℚ K]
    (S : Subalgebra ℤ K) (r : S) : rationalEvaluation S ((1 : ℚ) ⊗ₜ[ℤ] r) = (r : K) := by
  change algebraMap ℚ K 1 * (r : K) = r
  rw [map_one, one_mul]

private theorem rationalEvaluation_injective {K : Type*} [Field K] [Algebra ℚ K]
    (S : Subalgebra ℤ K) : Function.Injective (rationalEvaluation S) := by
  intro x y hxy
  have hzero : rationalEvaluation S (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  let ι := TensorProduct.mk ℤ ℚ S 1
  let _ : IsLocalizedModule ℤ⁰ ι := IsLocalization.tensorProduct_isLocalizedModule ..
  obtain ⟨⟨r, n⟩, hn⟩ := IsLocalizedModule.surj ℤ⁰ ι (x - y)
  change (n : ℤ) • (x - y) = (1 : ℚ) ⊗ₜ[ℤ] r at hn
  let evaluation := (rationalEvaluation S).toLinearMap.restrictScalars ℤ
  have applied := congrArg evaluation hn
  rw [map_smul] at applied
  change (n : ℤ) • rationalEvaluation S (x - y) = rationalEvaluation S _ at applied
  rw [hzero, smul_zero, rationalEvaluation_one_tmul] at applied
  have hnr : n • (x - y) = 0 := by
    change (n : ℤ) • (x - y) = 0
    rw [hn, show r = 0 from Subtype.ext applied.symm, TensorProduct.tmul_zero]
  have hreg := ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units ι n)).1
  apply sub_eq_zero.mp
  apply hreg
  change (n : ℤ) • (x - y) = (n : ℤ) • (0 : ℚ ⊗[ℤ] S)
  rw [smul_zero]
  exact hnr

private theorem rationalEvaluation_surjective
    (hχ : ∀ d : (ZMod N)ˣ, χ (d : ZMod N) ∈ coeffField f)
    (hf : IsNormalizedEigenform f χ) [FiniteDimensional ℚ (coeffField f)] :
    Function.Surjective (rationalEvaluation (integralEvaluation χ f hχ).range) := by
  let E := integralEvaluation χ f hχ
  let F := rationalEvaluation E.range
  let T : IntermediateField ℚ (coeffField f) :=
    (show F.range.IsAlgebraic from fun x _ => Algebra.IsAlgebraic.isAlgebraic x).toIntermediateField
  have hr (g : HeckeFree N) : evF χ f g ∈ T.map (coeffField f).val := by
    exact ⟨E g, ⟨(1 : ℚ) ⊗ₜ[ℤ] E.rangeRestrict g,
      rationalEvaluation_one_tmul E.range _⟩, integralEvaluation_coe hχ g⟩
  have hgen : HeckePin.genField χ f ≤ T.map (coeffField f).val := by
    rw [HeckePin.genField, IntermediateField.adjoin_le_iff]
    rintro _ (⟨p, rfl⟩ | ⟨d, rfl⟩)
    · simpa [evF] using hr (FreeAlgebra.ι ℤ (Sum.inl p))
    · simpa [evF] using hr (FreeAlgebra.ι ℤ (Sum.inr d))
  have hcoeff : coeffField f ≤ T.map (coeffField f).val := by
    change IntermediateField.adjoin ℚ (Set.range (coeff f)) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨n, rfl⟩
    exact hgen (HeckePin.coeff_mem_genField χ f hf n)
  intro x
  have hx : (x : ℂ) ∈ T.map (coeffField f).val := hcoeff x.2
  obtain ⟨y, hy, hxy⟩ := hx
  have heq : y = x := Subtype.ext hxy
  exact F.mem_range.mp (heq ▸ hy)

private theorem exists_afAction (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    [FiniteDimensional ℚ (coeffField f)] (hQ : IsAfQuotient χ f tp δ A π) :
    ∃ θ : coeffField f →+* A.End0, IsAfAction χ f tp δ π θ := by
  let hχ := diamond_mem_coeffField hN hf
  let E := integralEvaluation χ f hχ
  let r := E.rangeRestrict.toRingHom
  have hker : RingHom.ker r ≤ RingHom.ker (inducedHecke hQ) := by
    intro g hg
    rw [RingHom.mem_ker] at hg ⊢
    apply inducedHecke_eq_zero hQ
    rw [← integralEvaluation_coe hχ]
    have hz : E g = 0 := congrArg (fun x : E.range => (x : coeffField f)) hg
    exact congrArg Subtype.val hz
  let hsurj : Function.Surjective r := E.rangeRestrict_surjective
  let action := r.liftOfSurjective hsurj ⟨inducedHecke hQ, hker⟩
  let equiv : ℚ ⊗[ℤ] E.range ≃ₐ[ℚ] coeffField f :=
    AlgEquiv.ofBijective (rationalEvaluation E.range)
    ⟨rationalEvaluation_injective _, rationalEvaluation_surjective hχ hf⟩
  let extend : ℚ ⊗[ℤ] E.range →ₐ[ℚ] A.End0 :=
    Algebra.TensorProduct.lift (Algebra.ofId ℚ A.End0)
      (Algebra.TensorProduct.includeRight.comp action.toIntAlgHom)
      (fun q e => Algebra.commutes (R := ℚ) q _)
  let θ : coeffField f →ₐ[ℚ] A.End0 := extend.comp equiv.symm.toAlgHom
  have hθ (g : HeckeFree N) : θ (E g) = (1 : ℚ) ⊗ₜ[ℤ] inducedHecke hQ g := by
    have h : equiv ((1 : ℚ) ⊗ₜ[ℤ] r g) = E g :=
      rationalEvaluation_one_tmul E.range _
    rw [← h]
    change extend (equiv.symm (equiv ((1 : ℚ) ⊗ₜ[ℤ] r g))) = _
    rw [AlgEquiv.symm_apply_apply]
    change algebraMap ℚ A.End0 1 * ((1 : ℚ) ⊗ₜ[ℤ] action (r g)) = _
    rw [map_one, one_mul, RingHom.liftOfSurjective_comp_apply r hsurj _ g]
  refine ⟨θ.toRingHom, ?_, ?_⟩
  · intro p
    let g := FreeAlgebra.ι ℤ (Sum.inl p : HeckeGen N)
    have he := inducedHecke_rel hQ g
    refine ⟨inducedHecke hQ g, ?_, ?_⟩
    · have := congrArg AbVar.Hom.hom he
      simpa [g, comp, heckeJ] using this
    · simpa [E, integralEvaluation, g] using hθ g
  · intro d
    let g := FreeAlgebra.ι ℤ (Sum.inr d : HeckeGen N)
    have he := inducedHecke_rel hQ g
    refine ⟨⟨χ (d : ZMod N), hχ d⟩, inducedHecke hQ g, rfl, ?_, ?_⟩
    · have := congrArg AbVar.Hom.hom he
      simpa [g, comp, heckeJ] using this
    · simpa [E, integralEvaluation, g] using hθ g

/-- The quotient by the scheme-theoretic image sum of the Hecke annihilator, with its
coefficient-field action. -/
theorem afShimura_proof : AfShimura := by
  intro N χ f hN hf _ _ _ _ _ _ _ J _ _ tp δ _ _
  let _ := af_coeffField_finite hN hf.1
  obtain ⟨A, π, hQ⟩ := exists_afQuotient χ f tp δ
  obtain ⟨θ, hθ⟩ := exists_afAction hN hf.1 hQ
  exact ⟨inferInstance, A, π, θ, hQ, hθ⟩

end AfTateLam

end

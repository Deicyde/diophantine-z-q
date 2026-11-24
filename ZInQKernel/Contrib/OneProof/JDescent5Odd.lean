import ZInQKernel.Contrib.OneProof.JDescent5Inversion
import ZInQKernel.Contrib.OneProof.JDescent2
import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula

/-! Inversion negates the normalized ordinate. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TauCeti
open scoped UpperHalfPlane _root_.PeriodPair IntermediateField
open _root_.ZInQ.LeafPush2 (CPts IsUniformization)

noncomputable section
attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private theorem generate_of_poleOrders_two_three {k F : Type} [Field k] [Field F] [Algebra k F]
    (hF : IsFunctionField k F) (P : Place k F) (hP : P.degree = 1)
    {x y : F} (hx : P.ord x = -2) (hy : P.ord y = -3)
    (hreg : ∀ Q, Q ≠ P → 0 ≤ Q.ord x ∧ 0 ≤ Q.ord y) :
    IntermediateField.adjoin k ({x, y} : Set F) = ⊤ := by
  let K := IntermediateField.adjoin k ({x, y} : Set F)
  have h₂ : Module.finrank k⟮x⟯ F = 2 := by
    simpa [hP] using Place.finrank_adjoin_eq_mul_degree_of_ord_eq_neg
      (P := P) (n := 2) hF (by decide) hx (fun Q hQ => (hreg Q hQ).1)
  have h₃ : Module.finrank k⟮y⟯ F = 3 := by
    simpa [hP] using Place.finrank_adjoin_eq_mul_degree_of_ord_eq_neg
      (P := P) (n := 3) hF (by decide) hy (fun Q hQ => (hreg Q hQ).2)
  have hX : k⟮x⟯ ≤ K := IntermediateField.adjoin.mono _ _ _ (by simp)
  have hY : k⟮y⟯ ≤ K := IntermediateField.adjoin.mono _ _ _ (by simp)
  have d₂ := IntermediateField.finrank_dvd_of_le_left hX
  have d₃ := IntermediateField.finrank_dvd_of_le_left hY
  rw [h₂] at d₂
  rw [h₃] at d₃
  exact IntermediateField.finrank_eq_one_iff_eq_top.mp
    (Nat.dvd_one.mp (show Module.finrank K F ∣ Nat.gcd 2 3 from Nat.dvd_gcd d₂ d₃))

private theorem fix_of_fix_generators {k F : Type} [Field k] [Field F] [Algebra k F]
    (f : F ≃ₐ[k] F) {x y : F}
    (hgen : IntermediateField.adjoin k ({x, y} : Set F) = ⊤)
    (hx : f x = x) (hy : f y = y) (z : F) : f z = z := by
  have hz : z ∈ IntermediateField.adjoin k ({x, y} : Set F) := by rw [hgen]; trivial
  refine IntermediateField.adjoin_induction (F := k) (motive := fun z _ => f z = z) ?_ ?_ ?_ ?_ ?_ hz
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  · exact f.commutes
  · intro u v _ _ hu hv
    rw [map_add, hu, hv]
  · intro u _ hu
    rw [map_inv₀, hu]
  · intro u v _ _ hu hv
    rw [map_mul, hu, hv]

private theorem abVar_period_inversion_ne_id {L : Type} [Field L] (A : PkgI3.AbVar L)
    {σ : L →+* ℂ} {τ : ℍ} {Λ : Submodule ℤ (Fin 1 → ℂ)} {Φ : (Fin 1 → ℂ) → CPts A σ}
    {s : ℂ} (hΦ : IsUniformization σ Λ Φ) (hs : s ≠ 0)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ))) :
    abVarInv A ≠ 𝟙 _ := by
  intro hi
  let v : Fin 1 → ℂ := fun _ => s * (1 / 3)
  have hg : (Φ v)⁻¹ = Φ v := by
    apply Over.OverMorphism.ext
    change (Φ v).left ≫ abVarInv A = (Φ v).left
    rw [hi, Category.comp_id]
  have hunit : Φ (v + v) = 1 := by
    rw [hΦ.1]
    calc Φ v * Φ v = (Φ v)⁻¹ * Φ v := by rw [hg]
         _ = 1 := inv_mul_cancel _
  obtain ⟨m, n, hm⟩ := (hΛ _).mp ((hΦ.2.1 _).mp hunit)
  have he : (2 / 3 : ℂ) = (m : ℂ) + (n : ℂ) * (τ : ℂ) := by
    apply mul_left_cancel₀ hs
    rw [← hm]
    change s * (2 / 3) = s * (1 / 3) + s * (1 / 3)
    ring
  have him := congrArg Complex.im he
  have hn : (n : ℝ) * (τ : ℂ).im = 0 := by
    simpa [Complex.add_im, Complex.mul_im, eq_comm] using him
  have hn' : n = 0 := by
    have h := (mul_eq_zero.mp hn).resolve_right τ.2.ne'
    exact_mod_cast h
  have hre := congrArg Complex.re he
  have hm' : (2 / 3 : ℝ) = (m : ℝ) := by simpa [hn'] using hre
  have h : (3 : ℤ) * m = 2 := by
    exact_mod_cast (show (3 : ℝ) * (m : ℝ) = 2 by rw [← hm']; norm_num)
  omega

private theorem abVar_germInversion_nontrivial {L : Type} [Field L] (A : PkgI3.AbVar L)
    (hinv : abVarInv A ≠ 𝟙 _) : ¬ ∀ z, abVarInvFunctionField A z = z := by
  intro hall
  apply hinv
  exact abVarInv_eq_id_of_germInversion_trivial A hall

/-- Inversion negates the normalized ordinate in the actual function field. The two
coordinates generate that field: their separate subfields have degrees two and three. -/
theorem abVarInv_ordinate_of_genusOne {L : Type} [Field L] [NumberField L]
    (hg : AbVarFunctionFieldGenusOne) (A : PkgI3.AbVar L) (hdim : A.dim = 1)
    {σ : L →+* ℂ} {τ : ℍ} {Λ : Submodule ℤ (Fin 1 → ℂ)} {Φ : (Fin 1 → ℂ) → CPts A σ}
    {s : ℂ} (hΦ : IsUniformization σ Λ Φ) (hs : s ≠ 0)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ)))
    (P : Place L (AbVarFunctionField A))
    (hP : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring)
    {x y : AbVarFunctionField A} {a b : L}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxo : P.ord x = -2) (hyo : P.ord y = -3)
    (hreg : ∀ Q, Q ≠ P → 0 ≤ Q.ord x ∧ 0 ≤ Q.ord y)
    (heq : y ^ 2 = x ^ 3 + algebraMap L (AbVarFunctionField A) a * x +
      algebraMap L (AbVarFunctionField A) b) : abVarInvFunctionField A y = -y := by
  let f := abVarInvFunctionField A
  have hfix : f x = x := abVarInv_abscissa_of_genusOne hg A hdim P hP hx hy hxo hyo hreg heq
  have he' : (f y) ^ 2 = y ^ 2 := by
    have h := congrArg (fun z => f z) heq
    simp only [map_pow, map_add, map_mul, AlgEquiv.commutes, hfix] at h
    exact h.trans heq.symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he' with hy' | hy'
  · obtain ⟨P', hd', hP'⟩ := abVar_exists_identityPlace A hdim
    have hPP' : P = P' := Place.integers_injective
      (ValuationSubring.toSubring_injective (hP.symm.trans hP'))
    have hdeg : P.degree = 1 := hPP'.symm ▸ hd'
    have hgen := generate_of_poleOrders_two_three (abVar_isFunctionField A hdim) P hdeg hxo hyo hreg
    exact False.elim ((abVar_germInversion_nontrivial A (abVar_period_inversion_ne_id A hΦ hs hΛ))
      (fix_of_fix_generators f hgen hfix hy'))
  · exact hy'

/-- Inversion fixes the abscissa and negates the ordinate as regular sections. -/
theorem abVarInv_sections_of_genusOne {L : Type} [Field L] [NumberField L]
    (hg : AbVarFunctionFieldGenusOne) (A : PkgI3.AbVar L) (hdim : A.dim = 1)
    {σ : L →+* ℂ} {τ : ℍ} {Λ : Submodule ℤ (Fin 1 → ℂ)}
    {Φ : (Fin 1 → ℂ) → CPts A σ} {s : ℂ} (hΦ : IsUniformization σ Λ Φ) (hs : s ≠ 0)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ)))
    (P : Place L (AbVarFunctionField A))
    (hp : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring) (x y : Γ(A.X.left, abVarPunctured A)) (a b : L)
    (hx : letI := abVarPunctured_nonempty A P hp
          P.ord (A.X.left.germToFunctionField (abVarPunctured A) x) = -2)
    (hy : letI := abVarPunctured_nonempty A P hp
          P.ord (A.X.left.germToFunctionField (abVarPunctured A) y) = -3)
    (hreg : letI := abVarPunctured_nonempty A P hp
      ∀ Q, Q ≠ P → 0 ≤ Q.ord (A.X.left.germToFunctionField (abVarPunctured A) x) ∧
        0 ≤ Q.ord (A.X.left.germToFunctionField (abVarPunctured A) y))
    (heq : y ^ 2 = x ^ 3 + abVarSectionConst A _ a * x + abVarSectionConst A _ b) :
    (abVarInv A).appLE (abVarPunctured A) (abVarPunctured A) (abVarInv_stable_punctured A) x = x ∧
    (abVarInv A).appLE (abVarPunctured A) (abVarPunctured A) (abVarInv_stable_punctured A) y = -y := by
  have := abVarPunctured_nonempty A P hp
  let U := abVarPunctured A
  let X := A.X.left
  let F := AbVarFunctionField A
  let Xf : F := X.germToFunctionField U x
  let Yf : F := X.germToFunctionField U y
  have hx' : P.ord Xf = -2 := hx
  have hy' : P.ord Yf = -3 := hy
  have hX : Xf ≠ 0 := fun he => by rw [he, P.ord_zero] at hx'; omega
  have hY : Yf ≠ 0 := fun he => by rw [he, P.ord_zero] at hy'; omega
  have hEq : Yf ^ 2 = Xf ^ 3 + algebraMap L F a * Xf + algebraMap L F b := by
    have hh := congrArg (X.germToFunctionField U).hom heq
    rw [map_pow, map_add, map_add, map_mul, map_pow] at hh
    change Yf ^ 2 = Xf ^ 3 +
      X.germToFunctionField U (abVarSectionConst A U a) * Xf +
      X.germToFunctionField U (abVarSectionConst A U b) at hh
    rwa [germToFunctionField_abVarSectionConst, germToFunctionField_abVarSectionConst] at hh
  have hxInv := abVarInv_abscissa_of_genusOne hg A hdim P hp hX hY hx hy hreg hEq
  have hyInv := abVarInv_ordinate_of_genusOne hg A hdim hΦ hs hΛ P hp hX hY hx hy hreg hEq
  refine ⟨?_, ?_⟩
  · apply X.germToFunctionField_injective U
    rw [← abVarInvFunctionField_section A U (abVarInv_stable_punctured A)]
    exact hxInv
  · apply X.germToFunctionField_injective U
    rw [← abVarInvFunctionField_section A U (abVarInv_stable_punctured A)]
    change abVarInvFunctionField A Yf = (X.germToFunctionField U).hom (-y)
    rw [map_neg]
    exact hyInv

#print axioms generate_of_poleOrders_two_three
#print axioms fix_of_fix_generators
#print axioms abVar_period_inversion_ne_id
#print axioms abVar_germInversion_nontrivial
#print axioms abVarInv_ordinate_of_genusOne
#print axioms abVarInv_sections_of_genusOne

end

end HDec.CMBranch.CMjBridges

import ZInQKernel.Contrib.OneProof.QuotientP1.Lichtenbaum
import ZInQKernel.Contrib.OneProof.QuotientP1.QuotProper
import ZInQKernel.Contrib.CloudW02Connectedness.Basic
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# p1-quot3, L4 part A: the special fibre of a smooth proper model of `P¹_ℚ` is irreducible (scratch)
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Polynomial Opposite

namespace HDec.MCRGlue.P1Model

open VertWitness LeafQM.AV

/-! ## Global sections of a `P¹` by charts over `ℚ` -/

section GlobalSections

variable (Z : Over (Spec (CommRingCat.of ℚ))) (σ : ToP1 Z.left) (hσ : IsP1CoordinateQ Z σ)

/-- The structure map `ℚ → Γ(Z, ⊤)`. -/
def psiTop : ℚ →+* Γ(Z.left, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ Z.hom.appTop).hom

theorem baseToSectionsOver_eq (W : Z.left.Opens) (a : ℚ) :
    baseToSectionsOver (CommRingCat.of ℚ) Z W a =
      Z.left.presheaf.map (homOfLE le_top).op (psiTop Z a) := rfl

theorem baseToSectionsOver_res (W W' : Z.left.Opens) (h : W' ≤ W) (a : ℚ) :
    Z.left.presheaf.map (homOfLE h).op (baseToSectionsOver (CommRingCat.of ℚ) Z W a) =
      baseToSectionsOver (CommRingCat.of ℚ) Z W' a := by
  rw [baseToSectionsOver_eq, baseToSectionsOver_eq, Scheme.presheaf_map_map]

/-- Restriction to a basic open of an affine open whose sections form a domain is injective, if the
function is nonzero. -/
theorem res_basicOpen_injective {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] (f : Γ(X, U)) (hf : f ≠ 0) :
    Function.Injective (X.presheaf.map (homOfLE (X.basicOpen_le f)).op) := by
  have := hU.isLocalization_basicOpen f
  exact IsLocalization.injective (M := Submonoid.powers f) Γ(X, X.basicOpen f)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

/-- Restriction from `U` to `W ≤ U` is injective if it is injective to a basic open equal to `W`. -/
theorem res_injective_of_eq_basicOpen {X : Scheme.{0}} {U W : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] (f : Γ(X, U)) (hf : f ≠ 0) (hW : X.basicOpen f = W) (h : W ≤ U) :
    Function.Injective (X.presheaf.map (homOfLE h).op) := by
  subst hW
  exact res_basicOpen_injective hU f hf

include hσ in
theorem isDomain_U : IsDomain Γ(Z.left, σ.U) :=
  Function.Injective.isDomain (RingEquiv.ofBijective _ hσ.2.2.1).symm
    (RingEquiv.ofBijective _ hσ.2.2.1).symm.injective

include hσ in
theorem isDomain_V : IsDomain Γ(Z.left, σ.V) :=
  Function.Injective.isDomain (RingEquiv.ofBijective _ hσ.2.2.2).symm
    (RingEquiv.ofBijective _ hσ.2.2.2).symm.injective

include hσ in
theorem f_ne_zero : σ.f ≠ 0 := by
  intro h
  have h1 : eval₂RingHom (baseToSectionsOver _ Z σ.U) σ.f (X : ℚ[X]) =
      eval₂RingHom (baseToSectionsOver _ Z σ.U) σ.f 0 := by
    simp [h]
  have := hσ.2.2.1.1 h1
  exact X_ne_zero this

include hσ in
theorem g_ne_zero : σ.g ≠ 0 := by
  intro h
  have h1 : eval₂RingHom (baseToSectionsOver _ Z σ.V) σ.g (X : ℚ[X]) =
      eval₂RingHom (baseToSectionsOver _ Z σ.V) σ.g 0 := by
    simp [h]
  have := hσ.2.2.2.1 h1
  exact X_ne_zero this

include hσ in
theorem res_injective_U : Function.Injective
    (Z.left.presheaf.map (homOfLE (inf_le_left : σ.U ⊓ σ.V ≤ σ.U)).op) := by
  haveI := isDomain_U Z σ hσ
  exact res_injective_of_eq_basicOpen hσ.1 σ.f (f_ne_zero Z σ hσ) σ.basicOpen_f _

include hσ in
theorem res_injective_V : Function.Injective
    (Z.left.presheaf.map (homOfLE (inf_le_right : σ.U ⊓ σ.V ≤ σ.V)).op) := by
  haveI := isDomain_V Z σ hσ
  exact res_injective_of_eq_basicOpen hσ.2.1 σ.g (g_ne_zero Z σ hσ) σ.basicOpen_g _

/-- `eval₂` commutes with restriction. -/
theorem res_eval₂ (W W' : Z.left.Opens) (h : W' ≤ W) (t : Γ(Z.left, W)) (P : ℚ[X]) :
    Z.left.presheaf.map (homOfLE h).op (eval₂ (baseToSectionsOver _ Z W) t P) =
      eval₂ (baseToSectionsOver _ Z W') (Z.left.presheaf.map (homOfLE h).op t) P := by
  rw [Polynomial.hom_eval₂]
  congr 1
  ext a
  exact baseToSectionsOver_res Z W W' h a

include hσ in
/-- **A `P¹` by charts over `ℚ` has global sections `ℚ`.** -/
theorem psiTop_surjective : Function.Surjective (psiTop Z) := by
  intro b
  set W := σ.U ⊓ σ.V
  set rU := Z.left.presheaf.map (homOfLE (inf_le_left : W ≤ σ.U)).op
  set rV := Z.left.presheaf.map (homOfLE (inf_le_right : W ≤ σ.V)).op
  obtain ⟨P, hP⟩ := hσ.2.2.1.2 (Z.left.presheaf.map (homOfLE le_top : σ.U ⟶ ⊤).op b)
  obtain ⟨Q, hQ⟩ := hσ.2.2.2.2 (Z.left.presheaf.map (homOfLE le_top : σ.V ⟶ ⊤).op b)
  simp only [coe_eval₂RingHom] at hP hQ
  set f' := rU σ.f
  set g' := rV σ.g
  have hfg : f' * g' = 1 := σ.inv
  letI : Invertible g' := invertibleOfRightInverse _ _ (by rw [mul_comm]; exact hfg)
  have hinvg : ⅟g' = f' := by
    rw [← mul_one (⅟g'), ← hfg, ← mul_assoc, mul_comm (⅟g') f', mul_assoc, invOf_mul_self, mul_one]
  have hW : rU (Z.left.presheaf.map (homOfLE le_top : σ.U ⟶ ⊤).op b) =
      rV (Z.left.presheaf.map (homOfLE le_top : σ.V ⟶ ⊤).op b) := by
    simp only [rU, rV, Scheme.presheaf_map_map]
  rw [← hP, ← hQ, res_eval₂, res_eval₂] at hW
  -- `P(f') = Q(g') = reflect(Q)(f') g'^n`
  set n := Q.natDegree
  have hrefl := eval₂_reflect_mul_pow (baseToSectionsOver _ Z W) g' n Q le_rfl
  rw [hinvg] at hrefl
  have hPX : eval₂ (baseToSectionsOver _ Z W) f' (P * X ^ n) =
      eval₂ (baseToSectionsOver _ Z W) f' (reflect n Q) := by
    rw [eval₂_mul, eval₂_X_pow, hW, ← hrefl, mul_assoc, ← mul_pow, mul_comm g' f', hfg, one_pow,
      mul_one]
  have hinj : Function.Injective (fun R : ℚ[X] => eval₂ (baseToSectionsOver _ Z W) f' R) := by
    intro R₁ R₂ h
    simp only at h
    rw [← res_eval₂, ← res_eval₂] at h
    exact hσ.2.2.1.1 (res_injective_U Z σ hσ h)
  have hPQ := hinj hPX
  -- degrees: `P` is constant
  have hdeg : P.natDegree = 0 := by
    by_cases hP0 : P = 0
    · rw [hP0, natDegree_zero]
    · have h1 : (P * X ^ n).natDegree = P.natDegree + n := by
        rw [natDegree_mul hP0 (pow_ne_zero _ X_ne_zero), natDegree_X_pow]
      have h2 : (reflect n Q).natDegree ≤ n := by
        have := natDegree_reflect_le (N := n) (p := Q)
        rwa [max_self] at this
      rw [hPQ] at h1
      omega
  rw [natDegree_eq_zero] at hdeg
  obtain ⟨a, rfl⟩ := hdeg
  refine ⟨a, ?_⟩
  -- equal on `U` and on `V`
  have hUeq : Z.left.presheaf.map (homOfLE le_top : σ.U ⟶ ⊤).op (psiTop Z a) =
      Z.left.presheaf.map (homOfLE le_top : σ.U ⟶ ⊤).op b := by
    rw [← hP, eval₂_C]; rfl
  have hVeq : Z.left.presheaf.map (homOfLE le_top : σ.V ⟶ ⊤).op (psiTop Z a) =
      Z.left.presheaf.map (homOfLE le_top : σ.V ⟶ ⊤).op b := by
    apply res_injective_V Z σ hσ
    have e1 := congrArg rU hUeq
    simp only [rU, Scheme.presheaf_map_map] at e1 ⊢
    exact e1
  exact Z.left.sheaf.eq_of_locally_eq₂ (homOfLE le_top) (homOfLE le_top)
    (by rw [σ.cover]) _ _ hUeq hVeq

end GlobalSections

end HDec.MCRGlue.P1Model

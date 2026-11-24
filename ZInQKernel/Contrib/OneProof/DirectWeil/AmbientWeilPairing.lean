import ZInQKernel.Contrib.OneProof.DirectWeil.RationalWeilPairing
import ZInQKernel.Contrib.OneProof.DirectWeil.ClosureTransport
import ZInQKernel.Contrib.OneProof.DirectWeil.InertiaRoots
import ZInQKernel.Contrib.OneProof.SZThm33
import TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter

noncomputable section

open PkgI3 PkgI3.AbVar TensorProduct
open scoped CategoryTheory.MonObj
open ReductSplit (TΩ galTΩ)

namespace SZRaynaud

open PicDict.DirectPairing (tateEquiv tateEquiv_gal tatePairing polarization
  exists_finite_polarization_kernel exists_rationalWeilForm_of_finite_kernel)

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  {ℓ : ℕ} [Fact ℓ.Prime]

private abbrev rationalTateEquiv (A : AbVar K) (e : AlgebraicClosure K ≃ₐ[K] Ω) :
    A.V ℓ ≃ₗ[ℚ_[ℓ]] VΩ A Ω ℓ :=
  LinearEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ (tateEquiv A e)

private theorem rationalTateEquiv_gal (A : AbVar K) (e : AlgebraicClosure K ≃ₐ[K] Ω)
    (σ : Ω ≃ₐ[K] Ω) (x : A.V ℓ) :
    rationalTateEquiv A e (A.galRep ℓ (e.autCongr.symm σ) x) =
      galVΩ A ℓ σ (rationalTateEquiv A e x) := by
  let E := (tateEquiv A e (ℓ := ℓ)).toLinearMap
  have h : E.comp (A.galT (e.autCongr.symm σ)) = (galTΩ A ℓ σ).comp E := by
    apply LinearMap.ext
    exact tateEquiv_gal A e σ
  have h' := congrArg (LinearMap.baseChange ℚ_[ℓ]) h
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h'
  exact LinearMap.congr_fun h' x

/-- The Weil form of a specified polarization on the geometric Tate space. -/
theorem exists_ambientWeilForm_of_finite_kernel (A : AbVar K) (L : A.X.left.Pic)
    (e : AlgebraicClosure K ≃ₐ[K] Ω) (hℓ : (ℓ : K) ≠ 0)
    (hL : {x : A.Pt (AlgebraicClosure K) | polarization A L x = 1}.Finite)
    (g : ℕ) (hg : A.dim = g) :
    ∃ (_ : FiniteDimensional ℚ_[ℓ] (VΩ A Ω ℓ)) (B : LinearMap.BilinForm ℚ_[ℓ] (VΩ A Ω ℓ)),
      Module.finrank ℚ_[ℓ] (VΩ A Ω ℓ) = 2 * g ∧ B.Nondegenerate ∧ (∀ x, B x x = 0) ∧
      (∀ (σ : Ω ≃ₐ[K] Ω) (x y : VΩ A Ω ℓ),
        B (galVΩ A ℓ σ x) (galVΩ A ℓ σ y) =
          algebraMap ℤ_[ℓ] ℚ_[ℓ] (cyclotomicCharacter Ω ℓ σ.toRingEquiv) * B x y) ∧
      ∀ x y : TΩ A Ω ℓ, B (1 ⊗ₜ[ℤ_[ℓ]] x) (1 ⊗ₜ[ℤ_[ℓ]] y) = 0 ↔
        tatePairing A L hℓ ((tateEquiv A e).symm x) ((tateEquiv A e).symm y) = 0 := by
  obtain ⟨hfin, B, hrank, hB, halt, hgal, hzero⟩ :=
    exists_rationalWeilForm_of_finite_kernel A L hℓ hL g hg
  let E := rationalTateEquiv A e (ℓ := ℓ)
  let B' := B.comp E.symm.toLinearMap E.symm.toLinearMap
  refine ⟨Module.Finite.of_surjective E.toLinearMap E.surjective, B',
    E.finrank_eq.symm.trans hrank, ?_, fun x => halt (E.symm x), ?_, ?_⟩
  · constructor
    · intro x hx
      apply E.symm.injective
      rw [map_zero]
      exact hB.1 _ fun y => by simpa only [B', LinearMap.BilinForm.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hx (E y)
    · intro y hy
      apply E.symm.injective
      rw [map_zero]
      exact hB.2 _ fun x => by simpa only [B', LinearMap.BilinForm.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hy (E x)
  · intro σ x y
    have hσ (x : VΩ A Ω ℓ) : E.symm (galVΩ A ℓ σ x) = A.galRep ℓ (e.autCongr.symm σ) (E.symm x) := by
      apply E.injective
      rw [LinearEquiv.apply_symm_apply, rationalTateEquiv_gal, LinearEquiv.apply_symm_apply]
    have hχ : cyclotomicCharacter Ω ℓ σ.toRingEquiv =
        cyclotomicCharacter (AlgebraicClosure K) ℓ (e.autCongr.symm σ).toRingEquiv := by
      apply TauCeti.cyclotomicCharacter_eq_of_injective ℓ (f := e.toRingHom) e.injective
      · intro x
        exact (e.apply_symm_apply (σ (e x))).symm
      · intro h i
        obtain ⟨ζ, hζ⟩ := h i
        exact ⟨e.symm ζ, hζ.map_of_injective e.symm.injective⟩
    change B (E.symm (galVΩ A ℓ σ x)) (E.symm (galVΩ A ℓ σ y)) = _
    rw [hσ, hσ, hgal, hχ]
    rfl
  · intro x y
    change B (E.symm (1 ⊗ₜ x)) (E.symm (1 ⊗ₜ y)) = 0 ↔ _
    simp only [E, LinearEquiv.baseChange_symm_tmul, hzero]

/-- The Weil form on the exact geometric Tate space used in the semistable reduction criterion. -/
theorem exists_ambientWeilForm [IsAlgClosure K Ω] (A : AbVar K) (hℓ : (ℓ : K) ≠ 0)
    (g : ℕ) (hg : A.dim = g) :
    ∃ (_ : FiniteDimensional ℚ_[ℓ] (VΩ A Ω ℓ)) (B : LinearMap.BilinForm ℚ_[ℓ] (VΩ A Ω ℓ)),
      Module.finrank ℚ_[ℓ] (VΩ A Ω ℓ) = 2 * g ∧ B.Nondegenerate ∧ (∀ x, B x x = 0) ∧
      ∀ (σ : Ω ≃ₐ[K] Ω) (x y : VΩ A Ω ℓ),
        B (galVΩ A ℓ σ x) (galVΩ A ℓ σ y) =
          algebraMap ℤ_[ℓ] ℚ_[ℓ] (cyclotomicCharacter Ω ℓ σ.toRingEquiv) * B x y := by
  obtain ⟨L, hL⟩ := exists_finite_polarization_kernel A
  obtain ⟨hfin, B, hrank, hB, halt, hgal, _⟩ :=
    exists_ambientWeilForm_of_finite_kernel A L (IsAlgClosure.equiv K (AlgebraicClosure K) Ω) hℓ hL g hg
  exact ⟨hfin, B, hrank, hB, halt, hgal⟩

/-- On prime-to-residue-characteristic Tate modules the Weil multiplier is one on inertia. -/
theorem cyclotomicCharacter_eq_one_of_inertia [IsAlgClosure K Ω] (w : ValuationSubring Ω)
    (hℓ : IsUnit (ℓ : w)) (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) :
    cyclotomicCharacter Ω ℓ σ.toRingEquiv = 1 := by
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let : NeZero (ℓ : Ω) := ⟨by simpa using (hℓ.map w.subtype).ne_zero⟩
  apply (TauCeti.cyclotomicCharacter_eq_one_iff ℓ).mpr
  intro n x hx
  exact inertia_fixes_root_of_unity w σ hσ (by simpa only [Nat.cast_pow] using hℓ.pow n) x hx

/-- The rational geometric Tate module has a nondegenerate alternating form preserved by inertia. -/
theorem exists_inertiaInvariantWeilForm [IsAlgClosure K Ω] (A : AbVar K) (O : ValuationSubring K)
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) (hℓ : IsUnit (ℓ : O))
    (g : ℕ) (hg : A.dim = g) :
    ∃ (_ : FiniteDimensional ℚ_[ℓ] (VΩ A Ω ℓ)) (B : LinearMap.BilinForm ℚ_[ℓ] (VΩ A Ω ℓ)),
      Module.finrank ℚ_[ℓ] (VΩ A Ω ℓ) = 2 * g ∧ B.Nondegenerate ∧ (∀ x, B x x = 0) ∧
      ∀ (σ : Ω ≃ₐ[K] Ω), PkgI2.IsInertia w σ → ∀ x y : VΩ A Ω ℓ,
        B (galVΩ A ℓ σ x) (galVΩ A ℓ σ y) = B x y := by
  have hℓK : (ℓ : K) ≠ 0 := by simpa using (hℓ.map O.subtype).ne_zero
  have hℓw : IsUnit (ℓ : w) := by simpa using hℓ.map (ReductSplit.comapHom hw)
  obtain ⟨hfin, B, hrank, hB, halt, hgal⟩ := exists_ambientWeilForm (Ω := Ω) A hℓK g hg
  refine ⟨hfin, B, hrank, hB, halt, ?_⟩
  intro σ hσ x y
  rw [hgal, cyclotomicCharacter_eq_one_of_inertia w hℓw σ hσ, Units.val_one, map_one, one_mul]

end SZRaynaud

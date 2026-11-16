def MainTheoremCMPolMaxPrim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
    IsPrimitiveType Φ →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
    IsOLattice 𝔞 → (∃ ζ : E, IsRiemannDatum Φ 𝔞 ζ) →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞))
      θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) * (1 ⊗ₜ y) - 1 ⊗ₜ x ∈
          latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

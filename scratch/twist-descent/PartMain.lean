/-! # twist-descent, part MAIN: `TwistDescent` (kf-glue) proved

For `σ ∈ G_ℚ` with restriction `ρ = σ|_L`: the hypothesis gives a twisted isomorphism
`φ : B_{e₀} ≅ B_{σ⁻¹e₀}` over `ℚ̄` (`e₀ : K ↪ ℚ̄`); it is `G_L`-invariant (`L` is a Hom field,
`td_hom_inv`), so it descends to `φ_L : B_L → B ×_{K,τ∘(K↪L)} L` (`hfd`, `τ = σ⁻¹|_L`); then
`E = φ_L ≫ c_τ`, with `c_τ` the comparison over `Spec τ`. `φ_L` is a homomorphism by rigidity
(`G0FibreSimple.rigidityHom`, proved in kf-glue). `E` and `α` are chosen as functions of `σ|_L`,
with `E = 𝟙`, `α = id` on the trivial class (`twistDescent`). -/

section TwistDescentMain

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open TwistDescentXC TwistDescentHFD

namespace G0ModField.KernelField

open G0ModField

/-- **`G_L` fixes homomorphisms between conjugates** (from the Hom-field hypothesis of
`TwistDescent`): `k ∘ φ = φ ∘ k` for `k ∈ G_L` and `φ : B_{e₁} → B_{e₂}`. -/
theorem td_hom_inv {K : IF} [IsGalois ℚ K] (B : PkgI3.AbVar K) {L : IF} (hKL : K ≤ L)
    (hHF : ∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K B σ = 1)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₁) ((G4WeilRes.conjData K B).A e₂))
    (k : Qbar ≃ₐ[ℚ] Qbar) (hk : k ∈ L.fixingSubgroup)
    (k₁ : sp (e₁ : K →+* Qbar) = sp (k : Qbar →+* Qbar) ≫ sp (e₁ : K →+* Qbar))
    (k₂ : sp (e₂ : K →+* Qbar) = sp (k : Qbar →+* Qbar) ≫ sp (e₂ : K →+* Qbar)) :
    xc B.X (sp (k : Qbar →+* Qbar)) k₁ ≫ φ.hom.left =
      φ.hom.left ≫ xc B.X (sp (k : Qbar →+* Qbar)) k₂ := by
  classical
  have hs : ∀ e : K →ₐ[ℚ] Qbar, (G4WeilRes.embAct K k).symm e = e := by
    intro e
    ext x
    have hx : e x ∈ L :=
      hKL ((SetLike.ext_iff.mp (AlgHom.fieldRange_of_normal e) (e x)).mp ⟨x, rfl⟩)
    exact (IntermediateField.mem_fixingSubgroup_iff L _).mp (inv_mem hk) _ hx
  let m : G4WeilRes.HomLattice (G4WeilRes.conjData K B).A := Pi.single (e₁, e₂) φ
  have hm : G4WeilRes.conjAct K B k m = m := LinearEquiv.congr_fun (hHF k hk) m
  have h0 := G4WeilRes.conjAct_isConjAction K B k m e₁ e₂
  dsimp only at h0
  rw [hm] at h0
  have hme : m (e₁, e₂) = φ := Pi.single_eq_same _ _
  rw [hme] at h0
  have gen : ∀ (x y : K →ₐ[ℚ] Qbar) (hx : x = e₁) (hy : y = e₂)
      (p₁ : G4WeilRes.specEmb K e₁ = G4WeilRes.specGal k ≫ G4WeilRes.specEmb K x)
      (p₂ : G4WeilRes.specEmb K e₂ = G4WeilRes.specGal k ≫ G4WeilRes.specEmb K y),
      φ.hom.left ≫ G4Conj.cmp B.X (G4WeilRes.specGal k) p₂ =
        G4Conj.cmp B.X (G4WeilRes.specGal k) p₁ ≫ (m (x, y)).hom.left →
      xc B.X (sp (k : Qbar →+* Qbar)) k₁ ≫ φ.hom.left =
        φ.hom.left ≫ xc B.X (sp (k : Qbar →+* Qbar)) k₂ := by
    intro x y hx hy p₁ p₂ h
    subst hx hy
    rw [hme] at h
    exact h.symm
  exact gen _ _ (hs e₁) (hs e₂) (G4WeilRes.specEmb_symm K k e₁) (G4WeilRes.specEmb_symm K k e₂) h0

/-- The clauses of `SemilinearTwistAt` at one `σ`, in terms of `ρ = σ|_L`. -/
def TwistClause (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A) (ρ : L ≃ₐ[ℚ] L)
    (E : A.X.left ⟶ A.X.left) (α : O ≃+* O) : Prop :=
  IsIso E ∧
    (∃ τ : L ≃+* L, (∀ x : L, τ x = ρ⁻¹ x) ∧
      ∃ hτ : E ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)),
        μ[A.X].left ≫ E =
          pullback.map A.X.hom A.X.hom A.X.hom A.X.hom E E
            (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm ≫ μ[A.X].left ∧
        η[A.X].left ≫ E = Spec.map (CommRingCat.ofHom (τ : L →+* L)) ≫ η[A.X].left) ∧
    (∀ a : O, (ι' a).hom.left ≫ E = E ≫ (ι' (α a)).hom.left)

/-- `Spec ℚ̄ → Spec L` is an epimorphism. -/
theorem specQbar_epi (L : IF) : Epi (sp (algebraMap L Qbar)) := by
  obtain ⟨h1, h2, h3⟩ := TwistDescentGD.spec_field_props L Qbar
  infer_instance

/-- The trivial class: `E = 𝟙`, `α = id`. -/
theorem twistClause_one (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A) :
    TwistClause L A ι' 1 (𝟙 _) (RingEquiv.refl O) := by
  have hid : Spec.map (CommRingCat.ofHom ((RingEquiv.refl L : L ≃+* L) : L →+* L)) = 𝟙 _ := by
    rw [← Spec.map_id]; rfl
  refine ⟨inferInstance, ⟨RingEquiv.refl _, fun x => rfl, ?_, ?_, ?_⟩, fun a => ?_⟩
  · rw [hid, Category.id_comp, Category.comp_id]
  · rw [Category.comp_id]
    symm
    refine Eq.trans (congrArg (fun m => m ≫ μ[A.X].left) ?_) (Category.id_comp _)
    apply pullback.hom_ext <;> simp
  · rw [hid, Category.id_comp, Category.comp_id]
  · simp

end G0ModField.KernelField

end TwistDescentMain

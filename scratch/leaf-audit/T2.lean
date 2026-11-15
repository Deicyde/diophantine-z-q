import ZInQKernel.Contrib.OneProof.MumfordRigidity
import ZInQKernel.Contrib.OneProof.FaltingsTateSurj

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace LeafAudit1115

/-! ## FaltingsTateSurj at the zero abelian variety -/

instance subsingleton_pt_zero (K L : Type) [Field K] [Field L] [Algebra K L] :
    Subsingleton ((PkgI3.AbVar.zero K).Pt L) :=
  ⟨fun a b => CartesianMonoidalCategory.toUnit_unique a b⟩

instance subsingleton_T_zero (K : Type) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] :
    Subsingleton ((PkgI3.AbVar.zero K).T ℓ) :=
  ⟨fun a b => Subtype.ext (funext fun n => by
    exact Additive.toMul.injective (Subsingleton.elim _ _))⟩

/-- **FaltingsTateSurj, sanity case (unconditional):** its conclusion holds for `A = B = 0` over `ℚ`. -/
theorem faltingsTateSurj_zero (ℓ : ℕ) [Fact ℓ.Prime] :
    {φ | PkgI3.AbVar.IsGalEquivariant φ} ⊆
      Set.range (PkgI3.AbVar.tateHomZl ℓ (PkgI3.AbVar.zero ℚ) (PkgI3.AbVar.zero ℚ)) := by
  intro φ _
  refine ⟨0, ?_⟩
  rw [map_zero]
  exact LinearMap.ext fun x => Subsingleton.elim _ _

/-! ## MumfordGroupLaw at the trivial family `Spec ℚ → Spec ℚ` -/

/-- The trivial family over `S = Spec ℚ`: `F = 𝟙_ (Over S)` (`F.hom = 𝟙 S`). -/
abbrev Striv : Scheme.{0} := Spec (CommRingCat.of ℚ)

theorem one_pt_zero_comp (K : Type) [Field K] {T : Scheme.{0}} (s : Spec (CommRingCat.of K) ⟶ T) :
    ((1 : (PkgI3.AbVar.zero K).Pt K)).left ≫ s = s := by
  have w := Over.w (1 : (PkgI3.AbVar.zero K).Pt K)
  have e : (PkgI3.AbVar.ptObj (K := K) K).hom = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (algebraMap K K)) = _
    rw [show CommRingCat.ofHom (algebraMap K K) = 𝟙 _ from rfl, Spec.map_id]; rfl
  rw [e] at w
  erw [Category.comp_id] at w
  erw [w, Category.id_comp]

instance isIso_zero_hom (K : Type) [Field K] : IsIso (PkgI3.AbVar.zero K).X.hom := by
  change IsIso (𝟙 _); infer_instance

instance isIso_unit_hom (S : Scheme.{0}) : IsIso (𝟙_ (Over S)).hom := by
  change IsIso (𝟙 _); infer_instance

/-- **MumfordGroupLaw, non-vacuity:** every hypothesis is met by the trivial family `F = Spec ℚ` over
`S = Spec ℚ` with `e = 𝟙` (every field fibre is the zero abelian variety). -/
theorem mumfordGroupLaw_premises_trivial :
    IsLocallyNoetherian Striv ∧ IsProper (𝟙_ (Over Striv)).hom ∧ Smooth (𝟙_ (Over Striv)).hom ∧
      GeometricallyConnected (𝟙_ (Over Striv)).hom ∧ (𝟙 Striv : Striv ⟶ (𝟙_ (Over Striv)).left) ≫
        (𝟙_ (Over Striv)).hom = 𝟙 Striv ∧
      (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Striv),
        ∃ (A : PkgI3.AbVar K) (g : A.X.left ⟶ (𝟙_ (Over Striv)).left),
          LeafQM.AV.R1UnivRigid.IsAbVarFibre (𝟙_ (Over Striv)) (𝟙 Striv) s A g) := by
  refine ⟨inferInstance, by dsimp; infer_instance, by dsimp; infer_instance, ?_, by simp, ?_⟩
  · have : GeometricallyIntegral (𝟙_ (Over Striv)).hom := by dsimp; infer_instance
    dsimp; infer_instance
  · intro K _ s
    refine ⟨PkgI3.AbVar.zero K, s, ?_, ?_⟩
    · exact IsPullback.of_vert_isIso ⟨by simp [PkgI3.AbVar.zero]⟩
    · rw [one_pt_zero_comp]; rfl

/-- **MumfordGroupLaw, sanity case (unconditional):** its conclusion holds at the trivial family. -/
theorem mumfordGroupLaw_trivial_conclusion :
    ∃ _G : GrpObj (𝟙_ (Over Striv)), η[𝟙_ (Over Striv)].left = (𝟙 Striv : Striv ⟶ (𝟙_ (Over Striv)).left) :=
  ⟨inferInstance, rfl⟩

end LeafAudit1115

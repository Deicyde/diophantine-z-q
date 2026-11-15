import ZInQKernel.HDecomp.Analytic.Uniformization

/-! # unif-printed, stage 2c: `A(ℂ)` is a compact connected complex Lie group (from the printed leaves)

(Part of `Unif.lean`; uses stages 1, 2a, 2b.) -/

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonObj MonoidalCategory
  CartesianMonoidalCategory

set_option linter.unusedSectionVars false

noncomputable section

namespace UnifPrinted

open BPAnalytic BPAnalytic.Uniformization
open PkgI3 (AbVar)

/-! ## The scheme `A × A` and its `ℂ`-points -/

section Product

variable (A : AbVar ℂ)

instance irreducibleSpace_abVar : IrreducibleSpace A.X.left :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton A.X.hom

instance isIntegral_abVar : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

theorem smooth_prod : Smooth (A.X ⊗ A.X).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

theorem isProper_prod : IsProper (A.X ⊗ A.X).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

instance irreducibleSpace_prod : IrreducibleSpace (A.X ⊗ A.X).left := by
  rw [Over.tensorObj_left]
  infer_instance

theorem ptObj_hom : (AbVar.ptObj (K := ℂ) ℂ).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = 𝟙 _
  rw [show CommRingCat.ofHom (algebraMap ℂ ℂ) = 𝟙 (CommRingCat.of ℂ) from rfl, Spec.map_id]

instance isIso_toUnit_ptObj : IsIso (toUnit (AbVar.ptObj (K := ℂ) ℂ)) := by
  have : IsIso ((Over.forget _).map (toUnit (AbVar.ptObj (K := ℂ) ℂ))) := by
    change IsIso (toUnit (AbVar.ptObj (K := ℂ) ℂ)).left
    rw [Over.toUnit_left, ptObj_hom]
    exact IsIso.id _
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The section `P ↦ (P, Q)` of `A × A → A`, as a morphism of schemes. -/
def secL (Q : CPt A.X) : A.X ⟶ A.X ⊗ A.X :=
  lift (𝟙 A.X) (toUnit A.X ≫ inv (toUnit (AbVar.ptObj (K := ℂ) ℂ)) ≫ Q)

/-- The section `Q ↦ (P, Q)`. -/
def secR (P : CPt A.X) : A.X ⟶ A.X ⊗ A.X :=
  lift (toUnit A.X ≫ inv (toUnit (AbVar.ptObj (K := ℂ) ℂ)) ≫ P) (𝟙 A.X)

theorem toUnit_inv_comp (P Q : CPt A.X) :
    P ≫ toUnit A.X ≫ inv (toUnit (AbVar.ptObj (K := ℂ) ℂ)) ≫ Q = Q := by
  rw [← Category.assoc, comp_toUnit, IsIso.hom_inv_id_assoc]

theorem comp_secL (P Q : CPt A.X) : P ≫ secL A Q = lift P Q := by
  rw [secL, comp_lift, Category.comp_id, toUnit_inv_comp]

theorem comp_secR (P Q : CPt A.X) : Q ≫ secR A P = lift P Q := by
  rw [secR, comp_lift, Category.comp_id, toUnit_inv_comp]

end Product

/-! ## Assembly -/

/-- **`A(ℂ)` is a compact connected complex Lie group with the analytic structure of regular functions**
(proved from the printed leaves `SmoothComplexManifold`, `ProperCompact`, `ConnectedConnected`). -/
theorem abVarAnalyticLieGroup_of_printed (hMan : SmoothComplexManifold) (hPC : ProperCompact)
    (hCC : ConnectedConnected) : AbVarAnalyticLieGroup := by
  intro A
  letI tA : TopologicalSpace (CPt A.X) := classicalTopology A.X
  letI tA2 : TopologicalSpace (CPt (A.X ⊗ A.X)) := classicalTopology (A.X ⊗ A.X)
  obtain ⟨g, csA, hMA, holoA, coordsA⟩ := hMan A.X inferInstance inferInstance inferInstance
  obtain ⟨n, cs2, hM2, holo2, coords2⟩ := hMan (A.X ⊗ A.X) (smooth_prod A) (isProper_prod A) inferInstance
  -- regular maps are holomorphic
  have hreg : ∀ α : A.X ⟶ A.X, ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω
      (fun P : CPt A.X => P ≫ α) :=
    fun α => contMDiff_comp rfl rfl holoA coordsA α
  have hreg21 : ∀ α : A.X ⊗ A.X ⟶ A.X, ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin g → ℂ) ω
      (fun P : CPt (A.X ⊗ A.X) => P ≫ α) :=
    fun α => contMDiff_comp rfl rfl holo2 coordsA α
  have hreg12 : ∀ α : A.X ⟶ A.X ⊗ A.X, ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin n → ℂ) ω
      (fun P : CPt A.X => P ≫ α) :=
    fun α => contMDiff_comp rfl rfl holoA coords2 α
  -- the comparison map `ι : (A × A)(ℂ) → A(ℂ) × A(ℂ)` and its inverse
  set pr : CPt (A.X ⊗ A.X) → CPt A.X × CPt A.X := fun R => (R ≫ fst _ _, R ≫ snd _ _) with hprdef
  set σ : CPt A.X × CPt A.X → CPt (A.X ⊗ A.X) := fun x => lift x.1 x.2 with hσdef
  have hprσ : ∀ x, pr (σ x) = x := fun x => by simp [hprdef, hσdef]
  have hprinj : Function.Injective pr := by
    intro R R' h
    simp only [hprdef, Prod.mk.injEq] at h
    exact CartesianMonoidalCategory.hom_ext _ _ h.1 h.2
  have hpr : ContMDiff 𝓘(ℂ, Fin n → ℂ) (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin g → ℂ)) ω pr :=
    (hreg21 (fst _ _)).prodMk (hreg21 (snd _ _))
  have hσ : ContMDiff (𝓘(ℂ, Fin g → ℂ).prod 𝓘(ℂ, Fin g → ℂ)) 𝓘(ℂ, Fin n → ℂ) ω σ := by
    rintro ⟨P₀, Q₀⟩
    have hsurj := surjective_mfderiv_of_sections pr (lift P₀ Q₀) ((hpr _).mdifferentiableAt (by simp))
      (fun P => P ≫ secL A Q₀) (fun Q => Q ≫ secR A P₀) P₀ Q₀
      ((hreg12 _ _).mdifferentiableAt (by simp)) ((hreg12 _ _).mdifferentiableAt (by simp))
      (comp_secL A P₀ Q₀) (comp_secR A P₀ Q₀) (fun P => by simp [hprdef, comp_secL])
      (fun Q => by simp [hprdef, comp_secR])
    have := contMDiffAt_rightInverse pr (lift P₀ Q₀) (hpr _) hprinj hsurj σ hprσ
    simpa [hprdef] using this
  -- the Lie group structure
  have hmul : ContMDiff ((𝓘(ℂ, Fin g → ℂ)).prod 𝓘(ℂ, Fin g → ℂ)) 𝓘(ℂ, Fin g → ℂ) ω
      (fun p : CPt A.X × CPt A.X => p.1 * p.2) := by
    have h := (hreg21 μ[A.X]).comp hσ
    refine h.congr fun p => ?_
    simp [hσdef, Hom.mul_def]
  have hinv : ContMDiff 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin g → ℂ) ω (fun P : CPt A.X => P⁻¹) := by
    refine (hreg ι[A.X]).congr fun P => ?_
    simp [Hom.inv_def]
  haveI hLie : LieGroup 𝓘(ℂ, Fin g → ℂ) ω (A.Pt ℂ) :=
    { toIsManifold := hMA, contMDiff_mul := hmul, contMDiff_inv := hinv }
  haveI : T1Space (CPt A.X) := ChartedSpace.t1Space (Fin g → ℂ) (CPt A.X)
  haveI := topologicalGroup_of_lieGroup 𝓘(ℂ, Fin g → ℂ) ω (G := A.Pt ℂ)
  have hT2 : T2Space (A.Pt ℂ) := IsTopologicalGroup.t2Space_iff_one_closed.mpr isClosed_singleton
  refine ⟨g, tA, csA, hMA, hLie, hT2, hPC A.X inferInstance, hCC A.X inferInstance inferInstance,
    ⟨fun U => isOpen_ptIn U, holoA, coordsA, fun P₀ N hN => nhds_classical P₀ N hN⟩⟩

/-- **Main reduction (proved).** `UniformizationLeafAll` from four printed leaves. -/
theorem uniformizationLeafAll_of_printed (hM : MumfordComplexTorus) (hMan : SmoothComplexManifold)
    (hPC : ProperCompact) (hCC : ConnectedConnected) : UniformizationLeafAll :=
  uniformizationLeafAll_of_lieGroup hM (abVarAnalyticLieGroup_of_printed hMan hPC hCC)

end UnifPrinted

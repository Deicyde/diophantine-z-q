import ZInQKernel.Contrib.OneProof.CMHeight62.ShortModel

/-! # cmheight62-p1: complex points of `E_L` at `σ` and of `E` at `σ|_K`

`ptL σ : E_L(ℂ)_σ ≃* E(ℂ)_{σ|K}` (`AbVarBC.bcPt` with `Ω = ℂ`), composition with the projection
`E_L → E` on underlying schemes, its compatibility with evaluation of regular functions, and the
transport of uniformizations (the `K → L` analogue of `AvSplit.isUniformization_ptE`). -/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ.LeafPush2 (CPts cptObj cDom cEvalAt IsUniformization)

variable {K : Type} [Field K] (E : PkgI3.AbVar K) {L : Type} [Field L] [Algebra K L]
  (σ : L →+* ℂ)

/-- `E_L(ℂ)_σ ≃* E(ℂ)_{σ|K}`. -/
def ptL : CPts (E.baseChange L) σ ≃* CPts E (σ.comp (algebraMap K L)) := by
  letI : Algebra L ℂ := σ.toAlgebra
  letI : Algebra K ℂ := (σ.comp (algebraMap K L)).toAlgebra
  haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ZInQ.Contrib.AbVarBC.bcPt E ℂ

theorem ptL_left (q : CPts (E.baseChange L) σ) : (ptL E σ q).left = q.left ≫ bcProj E L := by
  change 𝟙 _ ≫ q.left ≫ pullback.fst _ _ = _
  rw [Category.id_comp]
  rfl

theorem preimage_ptL (q : CPts (E.baseChange L) σ) (U : E.X.left.Opens) :
    (ptL E σ q).left ⁻¹ᵁ U = q.left ⁻¹ᵁ (bcProj E L ⁻¹ᵁ U) := by
  rw [ptL_left]
  rfl

theorem cEvalAt_ptL (q : CPts (E.baseChange L) σ) (U : E.X.left.Opens) (s : Γ(E.X.left, U)) :
    cEvalAt (ptL E σ q) U s = cEvalAt q (bcProj E L ⁻¹ᵁ U) ((bcProj E L).app U s) := by
  have key : ∀ (f : (cptObj (σ.comp (algebraMap K L))).left ⟶ E.X.left)
      (hf : f = q.left ≫ bcProj E L)
      (h : ⊤ ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ q.left ⁻¹ᵁ (bcProj E L ⁻¹ᵁ U)),
      f.appLE U ⊤ h s = q.left.appLE (bcProj E L ⁻¹ᵁ U) ⊤ h' ((bcProj E L).app U s) := by
    rintro f rfl h h'
    have := Scheme.Hom.comp_appLE q.left (bcProj E L) U ⊤ h
    exact (congrArg (fun φ => φ.hom s) this).trans rfl
  unfold cEvalAt
  split <;> split <;> rename_i h1 h2
  · exact congrArg _ (key _ (ptL_left E σ q) h1 h2)
  · exact absurd ((preimage_ptL E σ q U) ▸ h1) h2
  · exact absurd ((preimage_ptL E σ q U).symm ▸ h2) h1
  · rfl

theorem cDom_ptL {g : ℕ} (Φ' : (Fin g → ℂ) → CPts (E.baseChange L) σ) (U : E.X.left.Opens) :
    cDom (fun z => ptL E σ (Φ' z)) U = cDom Φ' (bcProj E L ⁻¹ᵁ U) := by
  ext z
  change ⊤ ≤ (ptL E σ (Φ' z)).left ⁻¹ᵁ U ↔ ⊤ ≤ (Φ' z).left ⁻¹ᵁ (bcProj E L ⁻¹ᵁ U)
  rw [preimage_ptL]
  exact Iff.rfl

/-- A uniformization of `E_L` at `σ` gives one of `E` at `σ|_K`. -/
theorem isUniformization_ptL {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ' : (Fin g → ℂ) → CPts (E.baseChange L) σ} (hΦ : IsUniformization σ Λ Φ') :
    IsUniformization (σ.comp (algebraMap K L)) Λ (fun z => ptL E σ (Φ' z)) := by
  obtain ⟨hmul, hker, hsurj, hopen, hhol⟩ := hΦ
  refine ⟨fun z w => ?_, fun z => ?_, ?_, fun U => ?_, fun U s => ?_⟩
  · simp only [hmul, map_mul]
  · rw [MulEquiv.map_eq_one_iff]
    exact hker z
  · exact (ptL E σ).surjective.comp hsurj
  · rw [cDom_ptL]
    exact hopen _
  · rw [cDom_ptL]
    have := hhol (bcProj E L ⁻¹ᵁ U) ((bcProj E L).app U s)
    refine this.congr fun z _ => ?_
    exact cEvalAt_ptL E σ (Φ' z) U s

end ZInQ.Contrib.CMHeight62

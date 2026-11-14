
/-! ## §11. `QMDescentCM` replaced by the kernel's rigidity leaf T11b and a CM-descent leaf

Route: base change `P ↦ P_ℂ` of QM pairs (`bcPair`), with `End` and isomorphisms controlled by the
kernel's textbook leaf `ZInQ.LeafPush2.T11b_Rigidity` (`Hom_ℚ̄ = Hom_ℂ`), and the leaf `CMDescent`
(a QM pair over `ℂ` with CM by `R` is isomorphic to the base change of one over `ℚ̄`). -/

namespace ZInQ.HeightGlue.QM

open LeafQM LeafQM.AV NumberField ZInQ.HeightSplit.R5
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

section BaseChangeEnd

variable {K : Type} [Field K]

open scoped CategoryTheory.Obj in
/-- **Base change on endomorphisms** (copied verbatim from alg-frob-red's copy of bp-qmmoduli's
`endBC`, `scratch/alg-frob-red/AlgFrobRed.lean` l. 1592-1618). -/
noncomputable def endBC (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    PkgI3.AbVar.End A →+* PkgI3.AbVar.End (A.baseChange L) where
  toFun f := @PkgI3.AbVar.Hom.mk' L _ (A.baseChange L) (A.baseChange L)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (f := f.hom))
  map_one' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (𝟙 A.X) = 𝟙 _
    exact (Over.pullback _).map_id _
  map_mul' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (g.hom ≫ f.hom) = _
    rw [Functor.map_comp]; rfl
  map_zero' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (1 : A.X ⟶ A.X) = 1
    exact Functor.map_one _
  map_add' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (f.hom * g.hom) = _
    rw [Functor.map_mul]; rfl

end BaseChangeEnd

section Descent

variable [Algebra Qbar ℂ]

/-- `Over.pullback (Spec ℂ → Spec ℚ̄)`. -/
noncomputable abbrev bcF :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Qbar ℂ)))

open scoped CategoryTheory.Obj in
theorem bcF_isMonHom {A B : PkgI3.AbVar Qbar} (f : A.X ⟶ B.X) [IsMonHom f] :
    IsMonHom (M := (A.baseChange ℂ).X) (N := (B.baseChange ℂ).X) (bcF.map f) :=
  Functor.map.instIsMonHom (F := bcF) (f := f)

theorem bc_unique (hT : ZInQ.LeafPush2.T11b_Rigidity) {A B : PkgI3.AbVar Qbar}
    {φ₁ φ₂ : A.X ⟶ B.X} [IsMonHom φ₁] [IsMonHom φ₂] (h : bcF.map φ₁ = bcF.map φ₂) : φ₁ = φ₂ := by
  obtain ⟨φ, -, hφ⟩ := hT Qbar ℂ A B (bcF.map φ₁) (bcF_isMonHom φ₁)
  exact (hφ φ₁ ⟨inferInstance, rfl⟩).trans (hφ φ₂ ⟨inferInstance, h.symm⟩).symm

theorem bc_exists (hT : ZInQ.LeafPush2.T11b_Rigidity) {A B : PkgI3.AbVar Qbar}
    (ψ : (A.baseChange ℂ).X ⟶ (B.baseChange ℂ).X) [IsMonHom ψ] :
    ∃ φ : A.X ⟶ B.X, IsMonHom φ ∧ bcF.map φ = ψ :=
  (hT Qbar ℂ A B ψ inferInstance).exists

theorem endBC_injective (hT : ZInQ.LeafPush2.T11b_Rigidity) (A : PkgI3.AbVar Qbar) :
    Function.Injective (endBC A ℂ) := fun f g h =>
  PkgI3.AbVar.Hom.ext' (bc_unique hT (congrArg PkgI3.AbVar.Hom.hom h))

/-- **The base change `P_ℂ` of a QM pair over `ℚ̄`.** -/
noncomputable def bcPair (hT : ZInQ.LeafPush2.T11b_Rigidity) (P : QMPair Qbar) : QMPair ℂ where
  A := P.A.baseChange ℂ
  surface := by rw [PkgI3.AbVar.dim_baseChange]; exact P.surface
  q := ⟨(endBC P.A ℂ).comp P.q.iota, (endBC_injective hT P.A).comp P.q.injective⟩

end Descent

end ZInQ.HeightGlue.QM

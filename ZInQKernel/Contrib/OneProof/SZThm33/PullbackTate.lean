import ZInQKernel.Contrib.OneProof.SZThm33.TateSpecialization

/-!
# Tate towers of points and pullback
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace SmoothGroup

theorem pullback_homEquiv_fst {S B : Scheme.{0}} (d : B ⟶ S) (P : Over B) (X : Over S)
    (a : (Over.map d).obj P ⟶ X) :
    ((Over.mapPullbackAdj d).homEquiv P X a).left ≫ pullback.fst X.hom d = a.left := by
  dsimp [Over.mapPullbackAdj]
  simp

section Points

variable {S B T : Scheme.{0}} (d : B ⟶ S) (g : T ⟶ B)
    (g₀ : T ⟶ S) (h : g ≫ d = g₀) (X : Over S) [GrpObj X]

private def overPointIso : (Over.map d).obj (Over.mk g) ≅ Over.mk g₀ :=
  Over.isoMk (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp]; exact h.symm)

/-- Relative points of a group scheme and of its pullback are identified by
the pullback adjunction. The test scheme can be arbitrary. -/
def pullbackTestPointEquiv :
    letI : GrpObj ((Over.pullback d).obj X) := Functor.grpObjObj
    (Over.mk g₀ ⟶ X) ≃* (Over.mk g ⟶ (Over.pullback d).obj X) := by
  let F := Over.pullback d
  letI : GrpObj (F.obj X) := Functor.grpObjObj
  let e := (Over.mapPullbackAdj d).homEquiv (Over.mk g) X
  let t := overPointIso d g g₀ h
  refine ⟨⟨fun x => e (t.hom ≫ x), fun x => t.inv ≫ e.symm x, ?_, ?_⟩, ?_⟩
  · intro x
    change t.inv ≫ e.symm (e (t.hom ≫ x)) = x
    rw [Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]
  · intro x
    change e (t.hom ≫ t.inv ≫ e.symm x) = x
    rw [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  · intro x y
    change e (t.hom ≫ (x * y)) = e (t.hom ≫ x) * e (t.hom ≫ y)
    rw [MonObj.comp_mul]
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      F.map_mul, MonObj.comp_mul]

theorem pullbackTestPointEquiv_fst (x : Over.mk g₀ ⟶ X) :
    letI : GrpObj ((Over.pullback d).obj X) := Functor.grpObjObj
    (pullbackTestPointEquiv d g g₀ h X x).left ≫ pullback.fst X.hom d = x.left := by
  let e := (Over.mapPullbackAdj d).homEquiv (Over.mk g) X
  change (e ((overPointIso d g g₀ h).hom ≫ x)).left ≫ pullback.fst X.hom d = x.left
  rw [pullback_homEquiv_fst]
  exact Category.id_comp _

end Points

section Towers

variable {S B T : Scheme.{0}}
  (d : B ⟶ S) (g : T ⟶ B) (g₀ : T ⟶ S) (h : g ≫ d = g₀) (X : Over S) [GrpObj X] [IsCommMonObj X]
  {ℓ : ℕ} [Fact ℓ.Prime]

local instance : GrpObj ((Over.pullback d).obj X) := Functor.grpObjObj
local instance : IsCommMonObj ((Over.pullback d).obj X) := Functor.isCommMonObj_obj (F := Over.pullback d)

/-- Pullback of a compatible tower of points over the same test scheme. -/
def pullbackTestTate :
    PkgI3.Tate.T ℓ (Additive (Over.mk g₀ ⟶ X)) →ₗ[ℤ_[ℓ]]
      PkgI3.Tate.T ℓ (Additive (Over.mk g ⟶ (Over.pullback d).obj X)) :=
  PkgI3.Tate.map (pullbackTestPointEquiv d g g₀ h X).toMonoidHom.toAdditive

theorem pullbackTestTate_bijective :
    Function.Bijective (pullbackTestTate (ℓ := ℓ) d g g₀ h X) := by
  let e := pullbackTestPointEquiv d g g₀ h X
  constructor
  · intro x y h
    apply Subtype.ext
    funext n
    apply Additive.toMul.injective
    apply e.injective
    exact congrArg (fun t : PkgI3.Tate.T ℓ (Additive (Over.mk g ⟶ (Over.pullback d).obj X)) =>
      Additive.toMul (t.1 n)) h
  · intro y
    refine ⟨PkgI3.Tate.map e.symm.toMonoidHom.toAdditive y, ?_⟩
    apply Subtype.ext
    funext n
    exact congrArg Additive.ofMul (e.apply_symm_apply _)

end Towers

section Restriction

variable {S B : Type} [CommRing S] [CommRing B] {T : Scheme.{0}}
  (d : Spec (.of B) ⟶ Spec (.of S)) (g : T ⟶ Spec (.of B)) (g₀ : T ⟶ Spec (.of S))
  (h : g ≫ d = g₀) (X : Over (Spec (.of S))) [GrpObj X] [IsCommMonObj X]
  {ℓ : ℕ} [Fact ℓ.Prime]

local instance : GrpObj ((Over.pullback d).obj X) := Functor.grpObjObj
local instance : IsCommMonObj ((Over.pullback d).obj X) := Functor.isCommMonObj_obj (F := Over.pullback d)

/-- Pulling back a tower commutes with changing the test scheme. -/
theorem pullbackTestTate_restrict {T' : Scheme.{0}} (a : T' ⟶ T)
    (x : PkgI3.Tate.T ℓ (Additive (Over.mk g₀ ⟶ X))) :
    restrictTate (g := g) a (pullbackTestTate d g g₀ h X x) =
      pullbackTestTate d (a ≫ g) (a ≫ g₀) (by rw [Category.assoc, h]) X
        (restrictTate (g := g₀) a x) := by
  apply Subtype.ext
  funext n
  apply Additive.toMul.injective
  apply Over.OverMorphism.ext
  let y := Additive.toMul (x.1 n)
  let c : Over.mk (a ≫ g₀) ⟶ Over.mk g₀ := Over.homMk a rfl
  let h₁ : (a ≫ g) ≫ d = a ≫ g₀ := by rw [Category.assoc, h]
  let p := pullbackTestPointEquiv d g g₀ h X y
  let q := pullbackTestPointEquiv d (a ≫ g) (a ≫ g₀) h₁ X (c ≫ y)
  change a ≫ p.left = q.left
  apply pullback.hom_ext
  · let pr := pullback.fst X.hom d
    have h₁' : p.left ≫ pr = y.left := pullbackTestPointEquiv_fst d g g₀ h X y
    have h₂' : q.left ≫ pr = (c ≫ y).left :=
      pullbackTestPointEquiv_fst d (a ≫ g) (a ≫ g₀) h₁ X (c ≫ y)
    calc
      (a ≫ p.left) ≫ pr = a ≫ (p.left ≫ pr) := Category.assoc _ _ _
      _ = a ≫ y.left := congrArg (a ≫ ·) h₁'
      _ = (c ≫ y).left := rfl
      _ = q.left ≫ pr := h₂'.symm
  · let pr := pullback.snd X.hom d
    have h₁' : p.left ≫ pr = g := p.w
    have h₂' : q.left ≫ pr = a ≫ g := q.w
    exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) h₁').trans h₂'.symm)


end Restriction

#print axioms pullbackTestTate_bijective
#print axioms pullbackTestTate_restrict

end SmoothGroup

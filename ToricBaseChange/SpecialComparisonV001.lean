import ToricBaseChange.ComparisonMonV002

/-!
# The special-fibre comparison homomorphism over a common geometric point

`s : Spec k → S` (the closed point of `S = Spec O`), `σ' : Spec Ω → S'` (a geometric point of
`S' = Spec O'`) and `φ : Spec Ω → Spec k` with `σ' ≫ h = φ ≫ s`. For the comparison
`u : N ×_S S' → N'` and a subgroup `inc : U → N ×_S k` (the identity component of the special fibre
over the residue field `k` of `O`), `specialComparison` is the composite
`U_Ω → (N_k)_Ω ≅ N ×_S Ω ≅ (N ×_S S') ×_{S'} Ω → N'_Ω`. It is a homomorphism of group schemes over
`Ω` (`isMonHom_specialComparison`) whenever `u` and `inc` are; this is the map `ψ` of the toric rank
inequality, with target the geometric special fibre `N'_Ω` of the second model.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Limits
open scoped CategoryTheory.Obj

namespace ToricBaseChange.Comparison

variable {S S' Sk SΩ : Scheme.{0}} (h : S' ⟶ S) (s : Sk ⟶ S) (σ' : SΩ ⟶ S') (φ : SΩ ⟶ Sk)
  (hsq : σ' ≫ h = φ ≫ s)

/-- `(N_k)_Ω ≅ (N ×_S S')_Ω`, from `σ' ≫ h = φ ≫ s`. -/
def specialIso (N : Over S) :
    (Over.pullback φ).obj ((Over.pullback s).obj N) ≅ (Over.pullback σ').obj (bc h N) :=
  ((Over.pullbackComp φ s).app N).symm ≪≫
    (eqToIso (congrArg (fun f : SΩ ⟶ S => Over.pullback f) hsq.symm)).app N ≪≫
    (Over.pullbackComp σ' h).app N

/-- **The special-fibre comparison** `U_Ω → N'_Ω`. -/
def specialComparison (N : Over S) (N' : Over S') (u : bc h N ⟶ N')
    (U : Over Sk) (inc : U ⟶ (Over.pullback s).obj N) :
    (Over.pullback φ).obj U ⟶ (Over.pullback σ').obj N' :=
  (Over.pullback φ).map inc ≫ (specialIso h s σ' φ hsq N).hom ≫ (Over.pullback σ').map u

theorem isMonHom_specialIso (N : Over S) [GrpObj N] :
    IsMonHom (specialIso h s σ' φ hsq N).hom := by
  have h1 := isMonHom_app_comp_left (Over.pullback s) (Over.pullback φ) (Over.pullback (φ ≫ s))
    (Over.pullbackComp φ s).inv N
  have h2 := isMonHom_app (Over.pullback (φ ≫ s)) (Over.pullback (σ' ≫ h))
    (eqToIso (congrArg (fun f : SΩ ⟶ S => Over.pullback f) hsq.symm)).hom N
  have h3 := isMonHom_app_comp_right (Over.pullback h) (Over.pullback σ') (Over.pullback (σ' ≫ h))
    (Over.pullbackComp σ' h).hom N
  change IsMonHom ((show (Over.pullback φ).obj ((Over.pullback s).obj N) ⟶
        (Over.pullback (φ ≫ s)).obj N from (Over.pullbackComp φ s).inv.app N) ≫
    (eqToIso (congrArg (fun f : SΩ ⟶ S => Over.pullback f) hsq.symm)).hom.app N ≫
    (show (Over.pullback (σ' ≫ h)).obj N ⟶ (Over.pullback σ').obj ((Over.pullback h).obj N) from
        (Over.pullbackComp σ' h).hom.app N))
  infer_instance

/-- **The special-fibre comparison is a homomorphism** when `u` and `inc` are. -/
theorem isMonHom_specialComparison (N : Over S) [GrpObj N] (N' : Over S') [GrpObj N']
    (u : bc h N ⟶ N') [IsMonHom u] (U : Over Sk) [GrpObj U] (inc : U ⟶ (Over.pullback s).obj N)
    [IsMonHom inc] : IsMonHom (specialComparison h s σ' φ hsq N N' u U inc) := by
  haveI := isMonHom_specialIso h s σ' φ hsq N
  unfold specialComparison
  infer_instance

end ToricBaseChange.Comparison

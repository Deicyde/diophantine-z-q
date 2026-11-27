import ZInQKernel.Contrib.OneProof.ColmezProperModel.Points
import ZInQKernel.Contrib.OneProof.ColmezTorsionIso.Basic

/-!
# `𝒳(O_{C_p}) = X(C_p)` for a proper model, and the statement `ProperModelPoints`

Colmez, *Périodes p-adiques des variétés abéliennes*, Math. Ann. 292 (1992), p. 638: "Dans la
suite de cette section, X sera une variété abélienne, 𝒳 un modèle propre de X sur O_K. [...] Par
construction, 𝒳(O_{C_p}) s'identifie à X(C_p)". This file states that presupposition for the row
`colmez1992DeRhamAbVar` (`ProperModelPoints`, the Lean form of the schematic statement in
`ColmezTiltIso/PRINTED.md`) and proves the identification for *every* proper model:

* `OF p F`: the integral closure of `ℤ_p` in `F` (`F` a `ℤ_p`-algebra through `ℚ_p`), and
  `iotaO p F : O_F →+* 𝓞_ℂ_[p]`, the restriction of the tree's `F → ℂ_p` (`algCp`); its values
  have norm at most `1` because `𝓞_ℂ_[p]` is integrally closed (`algCp_mem_O`).
* `ModelPtsCp p F π`: `𝒳(O_{C_p}) = {x : Spec 𝓞_ℂ_[p] ⟶ 𝒳 | x ≫ π = Spec ι}`, with `σ ∈ G_F`
  acting by `x ↦ Spec (oAct (gfToGqp σ)) ≫ x` (`galModel`).
* **`modelPtsEquiv`** and **`modelPtsEquiv_gal`**: for a proper `π : 𝒳 ⟶ Spec O_F` with generic
  fibre `A`, `𝒳(O_{C_p}) ≃ A.Pt ℂ_[p]`, `G_F`-equivariantly, with `G_F` acting on `A.Pt ℂ_[p]`
  through `cpGal` (the action behind the tree's `TCp`, `galTCp`).
* **`properModelPoints_iff`**: `ProperModelPoints ↔ ProperModelExists`. The only remaining input
  is the existence of a proper model of `A` over `O_F` with generic fibre `A`.

The tree's abelian varieties (`ZInQ.Contrib.G9.PkgI4.I3.AbVar`) carry properness, smoothness and
geometric integrality over `F`, not a projective embedding, so the closure of `A` in some
`ℙⁿ_{O_F}` is not available, and Mathlib has no Nagata compactification. `ProperModelExists` is
therefore left open here.
-/

open CategoryTheory AlgebraicGeometry Limits
open ZInQ.Contrib.ColmezTorsionIso (algCp cpGal cpGal_apply)

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

noncomputable section

namespace ZInQ.Contrib.ColmezProperModel

section Colmez

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

attribute [local instance] algCp

/-- `F` as a `ℤ_p`-algebra through `ℚ_p`. -/
def algZp : Algebra ℤ_[p] F := ((algebraMap ℚ_[p] F).comp PadicInt.Coe.ringHom).toAlgebra

/-- **`O_F`**: the integral closure of `ℤ_p` in `F`, as a subring of `F`. -/
def OF : Subring F :=
  letI := algZp p F
  (integralClosure ℤ_[p] F).toSubring

theorem mem_OF_iff (x : F) : x ∈ OF p F ↔ letI := algZp p F; IsIntegral ℤ_[p] x := Iff.rfl

/-- `ℚ_p → ℂ_p` through `ℚ̄_p`, the route of `algCp`. -/
def qpToCp : ℚ_[p] →+* ℂ_[p] :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).comp (algebraMap ℚ_[p] (PadicAlgCl p))

/-- `ℚ_p → ℂ_p` is an isometry. -/
theorem norm_qpToCp (c : ℚ_[p]) : ‖qpToCp p c‖ = ‖c‖ := by
  rw [qpToCp, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends,
    PadicAlgCl.norm_extends]

/-- `ℤ_p → 𝓞_ℂ_[p]`. -/
def zpToO : ℤ_[p] →+* 𝓞_ℂ_[p] :=
  ((qpToCp p).comp PadicInt.Coe.ringHom).codRestrict 𝓞_ℂ_[p] fun c => by
    rw [ZInQ.Contrib.G9.PkgI4.Cp.mem_O_iff, RingHom.comp_apply, norm_qpToCp]
    exact PadicInt.norm_le_one c

theorem algebraMap_zpToO (c : ℤ_[p]) :
    algebraMap 𝓞_ℂ_[p] ℂ_[p] (zpToO p c) = qpToCp p (PadicInt.Coe.ringHom c) := rfl

/-- **`O_F` lands in `𝓞_ℂ_[p]`**: an element of `F` integral over `ℤ_p` has image of norm at
most `1` in `ℂ_p`, because `𝓞_ℂ_[p]` is an integrally closed valuation subring of `ℂ_p`. -/
theorem algCp_mem_O (x : OF p F) : algebraMap F ℂ_[p] x ∈ 𝓞_ℂ_[p] := by
  letI := algZp p F
  obtain ⟨P, hPm, hP⟩ := (mem_OF_iff p F x).mp x.2
  have hcomp : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (zpToO p) =
      (algebraMap F ℂ_[p]).comp (algebraMap ℤ_[p] F) := by
    ext c
    change algebraMap (PadicAlgCl p) ℂ_[p]
        (algebraMap ℚ_[p] (PadicAlgCl p) (PadicInt.Coe.ringHom c)) =
      algebraMap (PadicAlgCl p) ℂ_[p]
        (ZInQ.Contrib.G9.phiF p F (algebraMap ℚ_[p] F (PadicInt.Coe.ringHom c)))
    rw [AlgHom.commutes]
  have hint : IsIntegral 𝓞_ℂ_[p] (algebraMap F ℂ_[p] x) := by
    refine ⟨P.map (zpToO p), hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hP, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

/-- **`ι : O_F →+* 𝓞_ℂ_[p]`**, the restriction of `algCp : F → ℂ_p`. -/
def iotaO : OF p F →+* 𝓞_ℂ_[p] :=
  ((algebraMap F ℂ_[p]).comp (OF p F).subtype).codRestrict 𝓞_ℂ_[p] (algCp_mem_O p F)

theorem algebraMap_iotaO (x : OF p F) :
    algebraMap 𝓞_ℂ_[p] ℂ_[p] (iotaO p F x) = algebraMap F ℂ_[p] x := rfl

theorem iotaO_comp : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (iotaO p F) =
    (algebraMap F ℂ_[p]).comp (algebraMap (OF p F) F) := rfl

/-- `σ ∈ G_F` acting on `𝓞_ℂ_[p]`: the tree's `oAct (gfToGqp σ)`. -/
abbrev oGal (σ : Field.absoluteGaloisGroup F) : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p] :=
  ZInQ.Contrib.G9.PkgI4.oAct p (ZInQ.Contrib.G9.PkgI4.gfToGqp p F σ)

/-- `G_F` fixes `ι(O_F)`. -/
theorem oAct_comp_iotaO (σ : Field.absoluteGaloisGroup F) :
    (oGal p F σ).comp (iotaO p F) = iotaO p F := by
  ext x
  change cpGal p F σ (algebraMap F ℂ_[p] x) = algebraMap F ℂ_[p] x
  exact (cpGal p F σ).commutes _

theorem algebraMap_oAct (σ : Field.absoluteGaloisGroup F) (r : 𝓞_ℂ_[p]) :
    algebraMap 𝓞_ℂ_[p] ℂ_[p] (oGal p F σ r) =
      cpGal p F σ (algebraMap 𝓞_ℂ_[p] ℂ_[p] r) := rfl

/-- **`𝒳(O_{C_p})`** for `π : 𝒳 ⟶ Spec O_F`: the sections `x` with `x ≫ π = Spec ι`. -/
abbrev ModelPtsCp {𝒳 : Scheme} (π : 𝒳 ⟶ Spec (CommRingCat.of (OF p F))) : Type :=
  {x : Spec (CommRingCat.of 𝓞_ℂ_[p]) ⟶ 𝒳 // x ≫ π = Spec.map (CommRingCat.ofHom (iotaO p F))}

/-- `σ ∈ G_F` acting on `𝒳(O_{C_p})`: `x ↦ Spec (oAct (gfToGqp σ)) ≫ x`. -/
def galModel {𝒳 : Scheme} (π : 𝒳 ⟶ Spec (CommRingCat.of (OF p F)))
    (σ : Field.absoluteGaloisGroup F) (x : ModelPtsCp p F π) : ModelPtsCp p F π :=
  modelAct π (iotaO p F) (oGal p F σ) (oAct_comp_iotaO p F σ) x

theorem galModel_coe {𝒳 : Scheme} (π : 𝒳 ⟶ Spec (CommRingCat.of (OF p F)))
    (σ : Field.absoluteGaloisGroup F) (x : ModelPtsCp p F π) :
    (galModel p F π σ x).1 = Spec.map (CommRingCat.ofHom (oGal p F σ)) ≫ x.1 := rfl

variable {p F}

/-- **`𝒳(O_{C_p}) ≃ X(C_p)`** for a proper model `𝒳` of `A` over `O_F`. -/
def modelPtsEquiv (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) {𝒳 : Scheme}
    (π : 𝒳 ⟶ Spec (CommRingCat.of (OF p F))) [IsProper π]
    (e : pullback π (Spec.map (CommRingCat.ofHom (algebraMap (OF p F) F))) ≅ A.X.left)
    (he : e.hom ≫ A.X.hom = pullback.snd _ _) : ModelPtsCp p F π ≃ A.Pt ℂ_[p] :=
  modelEquiv π A e he (iotaO p F) (iotaO_comp p F)

/-- **`G_F`-equivariance** of `modelPtsEquiv`. -/
theorem modelPtsEquiv_gal (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) {𝒳 : Scheme}
    (π : 𝒳 ⟶ Spec (CommRingCat.of (OF p F))) [IsProper π]
    (e : pullback π (Spec.map (CommRingCat.ofHom (algebraMap (OF p F) F))) ≅ A.X.left)
    (he : e.hom ≫ A.X.hom = pullback.snd _ _) (σ : Field.absoluteGaloisGroup F)
    (x : ModelPtsCp p F π) :
    modelPtsEquiv A π e he (galModel p F π σ x) =
      A.galAct (cpGal p F σ) (modelPtsEquiv A π e he x) :=
  modelEquiv_act π A e he (iotaO p F) (iotaO_comp p F) _ (oAct_comp_iotaO p F σ) _
    (algebraMap_oAct p F σ) x

end Colmez

attribute [local instance] algCp

/-- **`ProperModelPoints`** (the statement of `ColmezTiltIso/PRINTED.md`, made precise): every
abelian variety `A` over a finite `F/ℚ_p` has a proper model `π : 𝒳 ⟶ Spec O_F` whose generic
fibre is `A` as an `F`-scheme, and `𝒳(O_{C_p})` is `G_F`-equivariantly in bijection with
`A.Pt ℂ_[p]`. -/
def ProperModelPoints : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (𝒳 : Scheme) (π : 𝒳 ⟶ Spec (CommRingCat.of (OF p F))) (_ : IsProper π)
      (e : pullback π (Spec.map (CommRingCat.ofHom (algebraMap (OF p F) F))) ≅ A.X.left)
      (_ : e.hom ≫ A.X.hom = pullback.snd _ _),
      ∃ φ : ModelPtsCp p F π ≃ A.Pt ℂ_[p],
        ∀ (σ : Field.absoluteGaloisGroup F) (x : ModelPtsCp p F π),
          φ (galModel p F π σ x) = A.galAct (cpGal p F σ) (φ x)

/-- **`ProperModelExists`**: every abelian variety `A` over a finite `F/ℚ_p` has a proper model
over `O_F` with generic fibre `A`. This is the only input of `ProperModelPoints` not proved
here. -/
def ProperModelExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (𝒳 : Scheme) (π : 𝒳 ⟶ Spec (CommRingCat.of (OF p F))) (_ : IsProper π)
      (e : pullback π (Spec.map (CommRingCat.ofHom (algebraMap (OF p F) F))) ≅ A.X.left),
      e.hom ≫ A.X.hom = pullback.snd _ _

/-- **`ProperModelPoints` from the existence of a proper model.** -/
theorem properModelPoints_of_exists (h : ProperModelExists) : ProperModelPoints := by
  intro p _ F _ _ _ A
  obtain ⟨𝒳, π, hπ, e, he⟩ := h p F A
  exact ⟨𝒳, π, hπ, e, he, modelPtsEquiv A π e he, modelPtsEquiv_gal A π e he⟩

/-- **The remaining gap is exactly the existence of a proper model.** -/
theorem properModelPoints_iff : ProperModelPoints ↔ ProperModelExists := by
  refine ⟨fun h p _ F _ _ _ A => ?_, properModelPoints_of_exists⟩
  obtain ⟨𝒳, π, hπ, e, he, -⟩ := h p F A
  exact ⟨𝒳, π, hπ, e, he⟩

end ZInQ.Contrib.ColmezProperModel

end

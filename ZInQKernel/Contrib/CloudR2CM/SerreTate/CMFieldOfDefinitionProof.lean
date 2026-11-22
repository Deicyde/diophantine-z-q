import ZInQKernel.Contrib.CloudR2CM.SerreTate.CMFieldOfDefinition
import ZInQKernel.Contrib.CloudR2CM.SerreTate.CMGeneratorDescentProof
import ZInQKernel.Contrib.CloudR2CM.SerreTate.BaseChangeEndTransportProof

/-!
# P0: `CMFieldOfDefinition`

Let `E/L` be an elliptic curve over a number field with `End(E_{L̄}) ≅ R`, an order of the
imaginary quadratic field `k`.

* `R`, hence `End(E_{L̄})`, is a finitely generated abelian group (`order_moduleFinite`).
* Each of finitely many generators lies over an endomorphism defined over a finite subextension
  (P0-A, `EndDescent.end_descends_finite`). Let `L'` be the compositum of these subextensions and of
  an image of `k`. Then `End(E_{L'}) → End(E_{L̄})` is onto (P0-B, `bcEndTower_eq_of_comp_bcCmp`,
  `bcEndTower_comp`).
* For a finite `M` receiving `L'`, an `L'`-isomorphism `\overline{M} ≅ L̄` carries base change from
  `L'` through `M` to base change from `L'` (P0-B, `trEquiv_comp_bcEndTower`). So
  `End(E_M) → End(E_{\overline{M}})` is onto, hence bijective, and `End(E_M) ≅ End(E_{L̄}) ≅ R`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace HDec.CMSerreTate

/-- An order of a number field is a finitely generated `ℤ`-module. -/
theorem order_moduleFinite {k : Type} [Field k] [NumberField k] (R : Subring k)
    (hR : R ≤ (integralClosure ℤ k).toSubring) : Module.Finite ℤ R := by
  let R' : Subalgebra ℤ k :=
    { R.toSubsemiring with algebraMap_mem' := fun r => by simpa using intCast_mem R r }
  have h : R' ≤ integralClosure ℤ k := fun x hx => hR hx
  haveI : Module.Finite ℤ (integralClosure ℤ k) :=
    inferInstanceAs (Module.Finite ℤ (NumberField.RingOfIntegers k))
  haveI : Module.Finite ℤ R' :=
    Module.Finite.of_injective (Subalgebra.inclusion h).toLinearMap
      (Subalgebra.inclusion_injective h)
  exact Module.Finite.equiv (AddEquiv.toIntLinearEquiv
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl } : ↥R' ≃ₗ[ℤ] ↥R)

/-- **P0.** -/
theorem cmFieldOfDefinition_proof : CMFieldOfDefinition := by
  classical
  intro L _ _ E _ k _ _ R hR hCM
  obtain ⟨φ⟩ := hCM
  generalize hA : HDec.LeafAdopt.abVarEquiv L E = A at φ ⊢
  -- `End(A_{L̄})` is finitely generated
  haveI : Module.Finite ℤ R := order_moduleFinite R hR.2.2.1
  haveI : Module.Finite ℤ (_root_.PkgI3.AbVar.End (A.baseChange (AlgebraicClosure L))) :=
    Module.Finite.equiv φ.toAddEquiv.toIntLinearEquiv.symm
  obtain ⟨S, hS⟩ :=
    (Module.Finite.fg_top : (⊤ : Submodule ℤ
      (_root_.PkgI3.AbVar.End (A.baseChange (AlgebraicClosure L)))).FG)
  -- each generator descends
  choose F hF g₀ hg₀ using fun s : _root_.PkgI3.AbVar.End (A.baseChange (AlgebraicClosure L)) =>
    EndDescent.end_descends_finite A s
  -- an image of `k`
  haveI : Module.IsTorsionFree ℚ k := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree ℚ (AlgebraicClosure L) := DivisionSemiring.to_moduleIsTorsionFree
  let jk : k →ₐ[ℚ] AlgebraicClosure L := IsAlgClosed.lift
  let b := Module.finBasis ℚ k
  let Fk : IntermediateField L (AlgebraicClosure L) :=
    IntermediateField.adjoin L (Set.range fun i => jk (b i))
  haveI : FiniteDimensional L Fk := by
    haveI : Finite (Set.range fun i => jk (b i)) := (Set.finite_range _).to_subtype
    exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  have hjk : ∀ x : k, jk x ∈ Fk := by
    intro x
    rw [← b.sum_repr x, map_sum]
    refine sum_mem (fun i _ => ?_)
    rw [show jk (b.repr x i • b i) = b.repr x i • jk (b i) from jk.toLinearMap.map_smul _ _,
      Algebra.smul_def, eq_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem Fk _)
      (IntermediateField.subset_adjoin L _ ⟨i, rfl⟩)
  -- the field `L'`
  let L₀ : IntermediateField L (AlgebraicClosure L) := (⨆ s ∈ S, F s) ⊔ Fk
  haveI : FiniteDimensional L (⨆ s ∈ S, F s : IntermediateField L (AlgebraicClosure L)) :=
    IntermediateField.finiteDimensional_iSup_of_finset' (fun s _ => hF s)
  haveI : FiniteDimensional L L₀ :=
    show FiniteDimensional L ↥((⨆ s ∈ S, F s) ⊔ Fk) from inferInstance
  haveI : NumberField L₀ := NumberField.of_module_finite L L₀
  -- `End(A_{L₀}) → End(A_{L̄})` is onto
  have hgen : ∀ s ∈ S, s ∈ (bcEndTower A L₀ (AlgebraicClosure L)).range := by
    intro s hs
    have hle : F s ≤ L₀ := (le_iSup₂ (f := fun s _ => F s) s hs).trans le_sup_left
    letI : Algebra (F s) L₀ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    haveI : IsScalarTower L (F s) L₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower (F s) L₀ (AlgebraicClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    refine ⟨bcEndTower A (F s) L₀ (g₀ s), ?_⟩
    rw [← RingHom.comp_apply, bcEndTower_comp A (F s) L₀ (AlgebraicClosure L)]
    exact bcEndTower_eq_of_comp_bcCmp A (F s) (AlgebraicClosure L) (g₀ s) s (hg₀ s)
  have hsurj₀ : Function.Surjective (bcEndTower A L₀ (AlgebraicClosure L)) := by
    have hrange : LinearMap.range
        (bcEndTower A L₀ (AlgebraicClosure L)).toAddMonoidHom.toIntLinearMap = ⊤ := by
      rw [eq_top_iff, ← hS, Submodule.span_le]
      intro s hs
      obtain ⟨t, ht⟩ := hgen s hs
      exact ⟨t, ht⟩
    intro y
    have hy : y ∈ LinearMap.range
        (bcEndTower A L₀ (AlgebraicClosure L)).toAddMonoidHom.toIntLinearMap := by
      rw [hrange]; exact Submodule.mem_top
    obtain ⟨t, ht⟩ := hy
    exact ⟨t, ht⟩
  refine ⟨L₀, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(jk : k →+* AlgebraicClosure L).codRestrict L₀
      (fun x => (le_sup_right : Fk ≤ L₀) (hjk x))⟩, ?_⟩
  intro M _ _ _ hj
  obtain ⟨j⟩ := hj
  letI : Algebra L₀ M := j.toRingHom.toAlgebra
  haveI : IsScalarTower L L₀ M := IsScalarTower.of_algebraMap_eq (fun x => (j.commutes x).symm)
  haveI : Algebra.IsAlgebraic L₀ M := Algebra.IsAlgebraic.tower_top (K := L) L₀
  haveI : Algebra.IsAlgebraic L₀ (AlgebraicClosure M) :=
    Algebra.IsAlgebraic.trans L₀ M (AlgebraicClosure M)
  haveI : Module.IsTorsionFree L₀ (AlgebraicClosure M) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree L₀ (AlgebraicClosure L) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L₀ (AlgebraicClosure M) := ⟨inferInstance, inferInstance⟩
  haveI : IsAlgClosure L₀ (AlgebraicClosure L) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := L) L₀⟩
  obtain ⟨ψ⟩ : Nonempty (AlgebraicClosure M ≃ₐ[L₀] AlgebraicClosure L) :=
    ⟨IsAlgClosure.equiv L₀ (AlgebraicClosure M) (AlgebraicClosure L)⟩
  have hcomp :
      (HDec.CMBranch.FibreSplit.trEquiv (X := A) (σ := ψ.restrictScalars L)).toRingHom.comp
        ((bcEndTower A M (AlgebraicClosure M)).comp (bcEndTower A L₀ M)) =
      bcEndTower A L₀ (AlgebraicClosure L) := by
    rw [bcEndTower_comp A L₀ M (AlgebraicClosure M),
      trEquiv_comp_bcEndTower A L₀ (AlgebraicClosure M) (AlgebraicClosure L) ψ]
  have hsurjM : Function.Surjective (bcEndTower A M (AlgebraicClosure M)) := by
    intro z
    obtain ⟨t, ht⟩ :=
      hsurj₀ (HDec.CMBranch.FibreSplit.trEquiv (X := A) (σ := ψ.restrictScalars L) z)
    refine ⟨bcEndTower A L₀ M t, ?_⟩
    apply (HDec.CMBranch.FibreSplit.trEquiv (X := A) (σ := ψ.restrictScalars L)).injective
    rw [← ht, ← hcomp, RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
  have hbij : Function.Bijective (bcEndTower A M (AlgebraicClosure M)) :=
    ⟨bcEndTower_injective A M (AlgebraicClosure M), hsurjM⟩
  exact ⟨(bijective_bcHom_iff_bcEndTower A M (AlgebraicClosure M)).mpr hbij,
    ⟨(RingEquiv.ofBijective (bcEndTower A M (AlgebraicClosure M)) hbij).trans
      ((HDec.CMBranch.FibreSplit.trEquiv (X := A) (σ := ψ.restrictScalars L)).trans φ)⟩⟩

end HDec.CMSerreTate

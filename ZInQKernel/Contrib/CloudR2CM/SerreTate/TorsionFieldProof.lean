import ZInQKernel.Contrib.CloudR2CM.SerreTate.SerreRigidity
import ZInQKernel.Contrib.OneProof.H.TailZ7
import ZInQKernel.Contrib.CloudB3W16Torsion.NativeBridges
import ZInQKernel.Contrib.AbVarBC.Points

/-!
# P2, the choice of `L₁`: `P2TorsionField`

For a number field `L`, an abelian variety `A/L`, a finite extension `L'/L` and two prime powers
`m₁ = ℓ₁^k₁`, `m₂ = ℓ₂^k₂`:

* `A(L̄)[mᵢ]` is finite (`finite_pt_torsion`, from the finiteness of torsion over an algebraically
  closed field of characteristic `0`, `ZInQ.Contrib.CloudB3W16Torsion.finite_torsion`, through the
  base change `A_{L̄}`);
* every point of `A(L̄)` is fixed by the automorphisms fixing a finite subextension
  (`ReductSplit.exists_fixing_field`);
* `L₁` is the compositum, inside `L̄`, of an image of `L'` and these finitely many subextensions;
* an `mᵢ`-torsion point of `A_{L₁}` over `\overline{L₁}` corresponds, through an `L₁`-isomorphism
  `\overline{L₁} ≅ L̄` and the base-change comparison of points, to a point of `A(L̄)[mᵢ]`; so it is
  fixed by `Aut(\overline{L₁}/L₁)` and, `L₁` being perfect, it is `L₁`-rational
  (`ReductSplit.exists_rational_of_fixed`).
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace HDec.CMSerreTate

/-- In characteristic `0`, the points of `A(K̄)` killed by `m ≠ 0` form a finite set. -/
theorem finite_pt_torsion {K : Type} [Field K] [CharZero K] (A : _root_.PkgI3.AbVar K) (m : ℕ)
    (hm : m ≠ 0) : {x : A.Pt (AlgebraicClosure K) | x ^ m = 1}.Finite := by
  have hmK : ((m : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K))]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hm)
  haveI : Finite (_root_.PkgI2.torsion
      (_root_.ObjBridge.toGrp (A.baseChange (AlgebraicClosure K))) (AlgebraicClosure K) m) :=
    _root_.ZInQ.Contrib.CloudB3W16Torsion.finite_torsion _ m hmK
  have hT : (_root_.PkgI2.torsion (_root_.ObjBridge.toGrp (A.baseChange (AlgebraicClosure K)))
      (AlgebraicClosure K) m).Finite := Set.toFinite _
  refine (hT.image (_root_.ZInQ.Contrib.AbVarBC.bcPt A (AlgebraicClosure K))).subset ?_
  intro x hx
  refine ⟨(_root_.ZInQ.Contrib.AbVarBC.bcPt A (AlgebraicClosure K)).symm x, ?_,
    MulEquiv.apply_symm_apply _ _⟩
  show ((_root_.ZInQ.Contrib.AbVarBC.bcPt A (AlgebraicClosure K)).symm x) ^ m = 1
  rw [← map_pow, show x ^ m = 1 from hx, map_one]

/-- **P2, the choice of `L₁`.** -/
theorem p2TorsionField_proof : P2TorsionField := by
  classical
  intro L _ _ A L' _ _ _ ℓ₁ ℓ₂ k₁ k₂ h₁ h₂
  have hfin₁ := finite_pt_torsion A (ℓ₁ ^ k₁) (pow_ne_zero _ h₁.ne_zero)
  have hfin₂ := finite_pt_torsion A (ℓ₂ ^ k₂) (pow_ne_zero _ h₂.ne_zero)
  choose F hF1 hF2 using fun x : A.Pt (AlgebraicClosure L) =>
    _root_.ReductSplit.exists_fixing_field A.X x
  let iota : L' →ₐ[L] AlgebraicClosure L := IsAlgClosed.lift
  let S : Finset (A.Pt (AlgebraicClosure L)) := hfin₁.toFinset ∪ hfin₂.toFinset
  let L₀ : IntermediateField L (AlgebraicClosure L) := iota.fieldRange ⊔ ⨆ x ∈ S, F x
  haveI : FiniteDimensional L iota.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField iota).toLinearEquiv
  haveI : FiniteDimensional L (⨆ x ∈ S, F x : IntermediateField L (AlgebraicClosure L)) :=
    IntermediateField.finiteDimensional_iSup_of_finset' (fun x _ => hF1 x)
  haveI : FiniteDimensional L L₀ :=
    show FiniteDimensional L ↥(iota.fieldRange ⊔ ⨆ x ∈ S, F x) from inferInstance
  haveI : NumberField L₀ := NumberField.of_module_finite L L₀
  refine ⟨L₀, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(IntermediateField.inclusion (le_sup_left : iota.fieldRange ≤ L₀)).comp
      (AlgEquiv.ofInjectiveField iota).toAlgHom⟩, ?_⟩
  intro m hm x hx
  have hfixed : ∀ σ : AlgebraicClosure L₀ ≃ₐ[L₀] AlgebraicClosure L₀,
      _root_.PkgI3.AbVar.galHom σ ≫ x = x := by
    intro σ
    haveI : Module.IsTorsionFree L₀ (AlgebraicClosure L) :=
      DivisionSemiring.to_moduleIsTorsionFree
    haveI : Module.IsTorsionFree L₀ (AlgebraicClosure L₀) :=
      DivisionSemiring.to_moduleIsTorsionFree
    haveI : IsAlgClosure L₀ (AlgebraicClosure L) :=
      ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := L) L₀⟩
    obtain ⟨ψ⟩ : Nonempty (AlgebraicClosure L₀ ≃ₐ[L₀] AlgebraicClosure L) :=
      ⟨IsAlgClosure.equiv L₀ (AlgebraicClosure L₀) (AlgebraicClosure L)⟩
    have hφ : ∀ z, ((ψ.symm.trans (σ.trans ψ)).restrictScalars L) ((ψ.restrictScalars L) z) =
        (ψ.restrictScalars L) ((σ.restrictScalars L) z) := by
      intro z
      simp
    have hx₂ : (_root_.ZInQ.Contrib.AbVarBC.trPt A (ψ.restrictScalars L)
        (_root_.ZInQ.Contrib.AbVarBC.bcPt A (AlgebraicClosure L₀) x)) ^ m = 1 := by
      rw [← map_pow, ← map_pow, hx, map_one, map_one]
    have hxS : _root_.ZInQ.Contrib.AbVarBC.trPt A (ψ.restrictScalars L)
        (_root_.ZInQ.Contrib.AbVarBC.bcPt A (AlgebraicClosure L₀) x) ∈ S := by
      rcases hm with rfl | rfl
      · exact Finset.mem_union_left _ (hfin₁.mem_toFinset.mpr hx₂)
      · exact Finset.mem_union_right _ (hfin₂.mem_toFinset.mpr hx₂)
    have hle : F (_root_.ZInQ.Contrib.AbVarBC.trPt A (ψ.restrictScalars L)
        (_root_.ZInQ.Contrib.AbVarBC.bcPt A (AlgebraicClosure L₀) x)) ≤ L₀ :=
      (le_iSup₂ (f := fun x _ => F x) _ hxS).trans le_sup_right
    have hfix := hF2 (_root_.ZInQ.Contrib.AbVarBC.trPt A (ψ.restrictScalars L)
        (_root_.ZInQ.Contrib.AbVarBC.bcPt A (AlgebraicClosure L₀) x))
      ((ψ.symm.trans (σ.trans ψ)).restrictScalars L)
      (fun y hy => (ψ.symm.trans (σ.trans ψ)).commutes ⟨y, hle hy⟩)
    show (A.baseChange L₀).galAct σ x = x
    apply (_root_.ZInQ.Contrib.AbVarBC.bcPt A (AlgebraicClosure L₀)).injective
    apply (_root_.ZInQ.Contrib.AbVarBC.trPt A (ψ.restrictScalars L)).injective
    rw [_root_.ZInQ.Contrib.AbVarBC.bcPt_galAct, _root_.ZInQ.Contrib.AbVarBC.trPt_galAct A _ _ _ hφ]
    exact hfix

  obtain ⟨y, hy⟩ := _root_.ReductSplit.exists_rational_of_fixed (A.baseChange L₀).X x hfixed
  exact ⟨y, hy⟩

end HDec.CMSerreTate

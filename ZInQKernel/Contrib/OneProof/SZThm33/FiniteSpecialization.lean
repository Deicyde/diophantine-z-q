import ZInQKernel.Contrib.OneProof.SZThm33.GenericBaseChange
import ZInQKernel.Contrib.OneProof.SZThm33.PullbackTateLift
import ZInQKernel.Contrib.OneProof.SZThm33.TateModelNaturality
import ZInQKernel.Contrib.OneProof.SZThm33.RationalFixedTate

/-!
# Comparison of the two special-fibre Tate spaces over a shared valuation
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue SmoothGroup ZInQ.Contrib.AbVarBC
open ZInQ.FaltingsRestate (isCommMonObj_groupModelO)

namespace SZRaynaud.Ambient

variable {K L Ω : Type} [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
  {O : ValuationSubring K} {P : ValuationSubring L} {w : ValuationSubring Ω}
  (hw : w.comap (algebraMap K Ω) = O) (hp : w.comap (algebraMap L Ω) = P)
  (hP : P.comap (algebraMap K L) = O)
  (A : PkgI3.AbVar K) (M : GroupModelO A O)
  (N : GroupModelO (A.baseChange L) P) (hN : N.IsNeronModel)
  {ℓ : ℕ} [Fact ℓ.Prime]

local instance : IsCommMonObj M.G := isCommMonObj_groupModelO M
local instance : IsCommMonObj N.G := isCommMonObj_groupModelO N
local instance : IsMonHom (neronModelComparison (bcDVR hP M) N hN) := neronModelComparison_hom (bcDVR hP M) N hN

/-- The morphism on Tate towers in the common geometric residue field,
obtained from the canonical comparison of the base-changed model to the
Néron model of the extension. -/
def specialTateComparison : (PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ M.G))) →ₗ[ℤ_[ℓ]] (PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hp) ⟶ N.G))) :=
  mapModelTate (neronModelComparison (bcDVR hP M) N hN) (res ≫ base hp) ∘ₗ
    pullbackTestTate (gD hP) (res ≫ base hp) (res ≫ base hw)
      (by rw [Category.assoc, ambientBase_comp hw hp hP]) M.G

/-- The direct comparison on points over the common residue field. -/
def specialPointComparison :
    (Over.mk (res ≫ base hw) ⟶ M.G) →* (Over.mk (res ≫ base hp) ⟶ N.G) := by
  letI : GrpObj ((Over.pullback (gD hP)).obj M.G) := Functor.grpObjObj
  exact (IsMonHom.monoidHom (neronModelComparison (bcDVR hP M) N hN) _).comp
    (pullbackTestPointEquiv (gD hP) (res ≫ base hp) (res ≫ base hw)
      (by rw [Category.assoc, ambientBase_comp hw hp hP]) M.G).toMonoidHom

theorem specialTateComparison_eq_map :
    specialTateComparison (ℓ := ℓ) hw hp hP A M N hN =
      PkgI3.Tate.map (specialPointComparison hw hp hP A M N hN).toAdditive := by
  apply LinearMap.ext
  intro t
  exact Subtype.ext rfl

/-- Generic Tate transport with the shared algebraically closed field kept fixed. -/
abbrev genericTateProjection : TΩ (A.baseChange L) Ω ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
  PkgI3.Tate.map (bcPt A Ω).toMonoidHom.toAdditive

variable [IsAlgClosed Ω] (hu : IsUnit (ℓ : O)) (hu' : IsUnit (ℓ : P))

/-- Specialization commutes with the comparison to the Néron model of a
valuation extension. -/
theorem specialTateComparison_commutes (x : (PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ M.G)))) :
    genericTateProjection (Ω := Ω) (L := L) (ℓ := ℓ) A
      (modelEmbedTate hp (A.baseChange L) N hu' (specialTateComparison hw hp hP A M N hN x)) =
      modelEmbedTate hw A M hu x := by
  let h : base hp ≫ gD hP = base hw := ambientBase_comp hw hp hP
  let r : (PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ M.G))) →ₗ[ℤ_[ℓ]] PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hp) ⟶ (bcDVR hP M).G)) :=
    pullbackTestTate (ℓ := ℓ) (gD hP) (res ≫ base hp) (res ≫ base hw)
      (by rw [Category.assoc, h]) M.G
  change genericTateProjection A (modelEmbedTate hp (A.baseChange L) N hu'
    (mapModelTate (neronModelComparison (bcDVR hP M) N hN) (res ≫ base hp) (r x))) = _
  rw [modelEmbedTate_comparison hp (A.baseChange L) (bcDVR hP M) N (hN := hN) (hu := hu')]
  have : HenselianLocalRing w := henselianLocalRing_of_valuationSubring w
  let f : PkgI3.Tate.T ℓ (Additive (Over.mk (gen ≫ base hw) ⟶ M.G)) →ₗ[ℤ_[ℓ]]
      PkgI3.Tate.T ℓ (Additive (Over.mk (gen ≫ base hp) ⟶ (bcDVR hP M).G)) :=
    pullbackTestTate (ℓ := ℓ) (gD hP) (gen ≫ base hp) (gen ≫ base hw)
      (by rw [Category.assoc, h]) M.G
  let y := liftTateFromResidue (base hw) hu (gen (w := w)) x
  have e₁ : embedTate hp hu' (X := (bcDVR hP M).G) (r x) = f y :=
    liftTateFromResidue_pullbackTestTate (gD hP) (base hp) (base hw) h M.G
      hu hu' (gen (w := w)) x
  unfold modelEmbedTate
  simp only [LinearMap.comp_apply]
  rw [e₁]
  apply Subtype.ext
  funext n
  let t := Additive.toMul (y.1 n)
  let p := pullbackTestPointEquiv (gD hP) (gen ≫ base hp) (gen ≫ base hw)
    (by rw [Category.assoc, h]) M.G t
  change Additive.ofMul (bcPt A Ω (genPtHom hp (A.baseChange L) (bcDVR hP M) p)) =
    Additive.ofMul (genPtHom hw A M t)
  apply congrArg Additive.ofMul
  refine (genPtHom_bcDVR hw hp hP A M p).trans ?_
  apply congrArg (genPtHom hw A M)
  apply Over.OverMorphism.ext
  exact pullbackTestPointEquiv_fst (gD hP) (gen ≫ base hp) (gen ≫ base hw)
    (by rw [Category.assoc, h]) M.G t

/-- The same comparison after inverting the Tate prime. -/
abbrev specialRationalTateComparison :=
  (specialTateComparison (ℓ := ℓ) hw hp hP A M N hN).baseChange ℚ_[ℓ]

theorem specialRationalTateComparison_commutes :
    ((genericTateProjection (Ω := Ω) (L := L) (ℓ := ℓ) A).baseChange ℚ_[ℓ]) ∘ₗ
      modelEmbedRationalΩ hp (A.baseChange L) N hu' ∘ₗ
        specialRationalTateComparison hw hp hP A M N hN =
      modelEmbedRationalΩ hw A M hu := by
  have e : genericTateProjection (Ω := Ω) (L := L) (ℓ := ℓ) A ∘ₗ
      modelEmbedTate hp (A.baseChange L) N hu' ∘ₗ specialTateComparison hw hp hP A M N hN =
      modelEmbedTate hw A M hu :=
    LinearMap.ext (specialTateComparison_commutes hw hp hP A M N hN hu hu')
  simpa only [LinearMap.baseChange_comp] using
    congrArg (LinearMap.baseChange ℚ_[ℓ]) e

include hu hu' in
/-- If restriction to the extended inertia group has the same fixed vectors
as the original group, the canonical special-fibre comparison is surjective
after inverting the Tate prime. -/
theorem specialRationalTateComparison_surjective_of_fixed
    [IsAlgClosure K Ω] [IsAlgClosure L Ω] [IsDiscreteValuationRing O] [IsDiscreteValuationRing P]
    (hM : M.IsNeronModel)
    (hfix : ∀ y : TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TΩ (A.baseChange L) Ω ℓ),
      (∀ σ : Ω ≃ₐ[L] Ω, PkgI2.IsInertia w σ →
        (galTΩ (A.baseChange L) ℓ σ).baseChange ℚ_[ℓ] y = y) →
      ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ →
        (galTΩ A ℓ σ).baseChange ℚ_[ℓ]
          ((genericTateProjection (L := L) (Ω := Ω) (ℓ := ℓ) A).baseChange ℚ_[ℓ] y) =
        (genericTateProjection (L := L) (Ω := Ω) (ℓ := ℓ) A).baseChange ℚ_[ℓ] y) :
    Function.Surjective (specialRationalTateComparison (ℓ := ℓ) hw hp hP A M N hN) := by
  let p := genericTateProjection (L := L) (Ω := Ω) (ℓ := ℓ) A
  have hp' : Function.Injective p := by
    intro x y e
    apply Subtype.ext
    funext n
    apply Additive.toMul.injective
    apply (bcPt A Ω).injective
    exact congrArg (fun t : TΩ A Ω ℓ => Additive.toMul (t.1 n)) e
  have : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  have hpQ : Function.Injective (p.baseChange ℚ_[ℓ]) :=
    Module.Flat.lTensor_preserves_injective_linearMap p hp'
  intro y
  let z := modelEmbedRationalΩ hp (A.baseChange L) N hu' y
  have hz : ∀ σ : Ω ≃ₐ[L] Ω, PkgI2.IsInertia w σ →
      (galTΩ (A.baseChange L) ℓ σ).baseChange ℚ_[ℓ] z = z :=
    fun σ hσ => galVΩ_modelEmbedRationalΩ_fixed hp (A.baseChange L) N hu' σ hσ y
  have hy : p.baseChange ℚ_[ℓ] z ∈ (modelEmbedRationalΩ hw A M hu).range :=
    (mem_range_modelEmbedRationalΩ_iff hw A M hu hM _).2 (hfix z hz)
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, ?_⟩
  apply modelEmbedRationalΩ_injective hp (A.baseChange L) N hu'
  apply hpQ
  have e := LinearMap.congr_fun
    (specialRationalTateComparison_commutes hw hp hP A M N hN hu hu') x
  exact e.trans hx

#print axioms specialTateComparison_commutes
#print axioms specialRationalTateComparison_commutes
#print axioms specialRationalTateComparison_surjective_of_fixed

end SZRaynaud.Ambient

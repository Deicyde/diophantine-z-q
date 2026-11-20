import ZInQKernel.Contrib.OneProof.SZThm33.TateSpecialization
import ZInQKernel.Contrib.OneProof.SZThm33.AmbientValuationHenselian

/-!
# Comparing residue and geometric generic Tate towers

The comparison takes place at the original ambient valuation, and
intertwines the decomposition group of that valuation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open IsLocalRing
open ReductSplit (comapHom)

namespace SZRaynaud.Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  {O : ValuationSubring K} {w : ValuationSubring Ω}
  (hw : w.comap (algebraMap K Ω) = O)

abbrev base : Spec (.of w) ⟶ Spec (.of O) := Spec.map (CommRingCat.ofHom (comapHom hw))
abbrev gen : Spec (.of Ω) ⟶ Spec (.of w) := Spec.map (CommRingCat.ofHom w.subtype)
abbrev res : Spec (.of (ResidueField w)) ⟶ Spec (.of w) :=
  Spec.map (CommRingCat.ofHom (residue w))

variable (d : w.decompositionSubgroup K)

abbrev valAut : w ≃+* w := MulSemiringAction.toRingAut (w.decompositionSubgroup K) w d
abbrev resAut : ResidueField w ≃+* ResidueField w :=
  MulSemiringAction.toRingAut (w.decompositionSubgroup K) (ResidueField w) d

abbrev valEnd : Spec (.of w) ⟶ Spec (.of w) :=
  Spec.map (CommRingCat.ofHom (valAut d).toRingHom)
abbrev resEnd : Spec (.of (ResidueField w)) ⟶ Spec (.of (ResidueField w)) :=
  Spec.map (CommRingCat.ofHom (resAut d).toRingHom)
abbrev genEnd : Spec (.of Ω) ⟶ Spec (.of Ω) :=
  Spec.map (CommRingCat.ofHom (d.1 : Ω →+* Ω))

theorem valEnd_base : valEnd d ≫ base hw = base hw := by
  rw [← Spec.map_comp]
  congr 1
  ext x : 2
  apply Subtype.ext
  exact d.1.commutes (x : K)

theorem gen_valEnd : gen (w := w) ≫ valEnd d = genEnd d ≫ gen := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem res_valEnd : res (w := w) ≫ valEnd d = resEnd d ≫ res := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem genEnd_gen_base : genEnd d ≫ (gen ≫ base hw) = gen ≫ base hw := by
  rw [← Category.assoc, ← gen_valEnd, Category.assoc, valEnd_base]

theorem resEnd_res_base : resEnd d ≫ (res ≫ base hw) = res ≫ base hw := by
  rw [← Category.assoc, ← res_valEnd, Category.assoc, valEnd_base]

theorem isDominant_gen : IsDominant (gen (w := w)) := by
  constructor
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical w.subtype).mpr
  rw [(RingHom.injective_iff_ker_eq_bot w.subtype).mp Subtype.val_injective]
  exact bot_le

open SmoothGroup

variable [IsAlgClosed Ω] {X : Over (Spec (.of O))} [GrpObj X] [IsCommMonObj X]
  [Smooth X.hom] {ℓ : ℕ} [Fact ℓ.Prime] (hu : IsUnit (ℓ : O))

/-- The injection of residue Tate towers into the geometric generic
Tate module of a smooth separated model. -/
def embedTate :
    PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ X)) →ₗ[ℤ_[ℓ]]
      PkgI3.Tate.T ℓ (Additive (Over.mk (gen ≫ base hw) ⟶ X)) :=
  letI := henselianLocalRing_of_valuationSubring w
  liftTateFromResidue (base hw) hu gen

theorem embedTate_injective [IsSeparated X.hom] :
    Function.Injective (embedTate (X := X) hw hu) := by
  have := henselianLocalRing_of_valuationSubring w
  have := isDominant_gen (w := w)
  exact liftTateFromResidue_injective (base hw) hu gen

theorem embedTate_tateEnd
    (t : PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ X))) :
    embedTate hw hu (tateEnd _ (resEnd d) (resEnd_res_base hw d) t) =
      tateEnd _ (genEnd d) (genEnd_gen_base hw d) (embedTate hw hu t) := by
  have := henselianLocalRing_of_valuationSubring w
  exact liftTateFromResidue_tateEnd (base hw) hu gen (valEnd d) (valEnd_base hw d)
    (resEnd d) (resEnd_res_base hw d) (genEnd d) (genEnd_gen_base hw d)
    (res_valEnd d) (gen_valEnd d) t

/-- Inertia acts trivially on the image of the residue Tate module. -/
theorem embedTate_fixed_of_inertia (hd : d ∈ w.inertiaSubgroup K)
    (t : PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ X))) :
    tateEnd _ (genEnd d) (genEnd_gen_base hw d) (embedTate hw hu t) =
      embedTate hw hu t := by
  have he : resEnd d = 𝟙 _ := by
    have h : resAut d = 1 := hd
    change Spec.map (CommRingCat.ofHom (resAut d).toRingHom) = 𝟙 _
    rw [h]
    exact Spec.map_id _
  have h : tateEnd (res ≫ base hw) (resEnd d) (resEnd_res_base hw d) t = t := by
    apply Subtype.ext
    funext n
    apply Additive.toMul.injective
    apply Over.OverMorphism.ext
    change resEnd d ≫ (Additive.toMul (t.1 n)).left =
      (Additive.toMul (t.1 n)).left
    rw [he, Category.id_comp]
  rw [← embedTate_tateEnd hw d hu, h]

#print axioms embedTate_injective
#print axioms embedTate_tateEnd
#print axioms embedTate_fixed_of_inertia

end SZRaynaud.Ambient

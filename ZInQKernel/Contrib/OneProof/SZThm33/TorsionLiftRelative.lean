import ZInQKernel.Contrib.OneProof.SZThm33.EtaleLiftRelative
import ZInQKernel.Contrib.OneProof.FaltingsDVR.EtalePower

/-!
# Unique lifting for prime-to-residue torsion points

A torsion point over the residue of a henselian test ring lifts through
the étale multiplication kernel. The base can be an arbitrary
commutative ring.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace SmoothGroup

variable {S : Type} [CommRing S] {X : Over (Spec (.of S))} [GrpObj X]

/-- Restrict a point of an over-category group to a test scheme over its
source. -/
def restrictPoint {T T' : Scheme.{0}} {g : T ⟶ Spec (.of S)} (a : T' ⟶ T) :
    (Over.mk g ⟶ X) →* (Over.mk (a ≫ g) ⟶ X) where
  toFun x := (Over.homMk a rfl : Over.mk (a ≫ g) ⟶ Over.mk g) ≫ x
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

private theorem point_pow_eq_one_iff {T : Scheme.{0}} {g : T ⟶ Spec (.of S)}
    (n : ℕ) (x : Over.mk g ⟶ X) :
    x ^ n = 1 ↔ x.left ≫ (𝟙 X ^ n : X ⟶ X).left = g ≫ η[X].left := by
  have hmul : x ≫ (𝟙 X ^ n : X ⟶ X) = x ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  rw [← hmul]
  constructor
  · intro h
    exact congrArg Over.Hom.left h
  · intro h
    apply Over.OverMorphism.ext
    exact h

/-- Prime-to-residue torsion lifts uniquely over a henselian test ring. -/
theorem existsUnique_torsion_point_over_residue [IsCommMonObj X] [Smooth X.hom]
    {R : Type} [CommRing R] [HenselianLocalRing R] (g : Spec (.of R) ⟶ Spec (.of S))
    (n : ℕ) (hn : IsUnit (n : S))
    (z : Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ g) ⟶ X)
    (hz : z ^ n = 1) :
    ∃! a : Over.mk g ⟶ X, a ^ n = 1 ∧
      restrictPoint (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) a = z := by
  let j := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let M := (𝟙 X ^ n : X ⟶ X).left
  let Z := pullback M η[X].left
  let p : Z ⟶ Spec (.of S) := pullback.snd M η[X].left
  let q : Z ⟶ X.left := pullback.fst M η[X].left
  have hM : Etale M := etale_pow X n hn
  have : Etale p := inferInstanceAs (Etale (pullback.snd M η[X].left))
  let z' : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Z :=
    pullback.lift z.left (j ≫ g) ((point_pow_eq_one_iff n z).mp hz)
  have hz' : z' ≫ p = j ≫ g := pullback.lift_snd _ _ _
  obtain ⟨s, ⟨hs, hres⟩, huniq⟩ := existsUnique_lift_of_etale_over_residue p g z' hz'
  have hq : q ≫ X.hom = p := by
    rw [← Over.w (𝟙 X ^ n : X ⟶ X), ← Category.assoc]
    change (q ≫ M) ≫ X.hom = p
    rw [show q ≫ M = p ≫ η[X].left from pullback.condition, Category.assoc,
      Over.w η[X]]
    exact Category.comp_id _
  let a : Over.mk g ⟶ X := Over.homMk (s ≫ q) (by
    change (s ≫ q) ≫ X.hom = g
    rw [Category.assoc, hq, hs])
  have ha : a ^ n = 1 := (point_pow_eq_one_iff n a).mpr (by
    change (s ≫ q) ≫ M = g ≫ η[X].left
    rw [Category.assoc, show q ≫ M = p ≫ η[X].left from pullback.condition,
      ← Category.assoc, hs])
  have har : restrictPoint j a = z := by
    apply Over.OverMorphism.ext
    change j ≫ s ≫ q = z.left
    rw [← Category.assoc, hres, pullback.lift_fst]
  refine ⟨a, ⟨ha, har⟩, ?_⟩
  rintro a' ⟨ha', hres'⟩
  let s' : Spec (.of R) ⟶ Z := pullback.lift a'.left g ((point_pow_eq_one_iff n a').mp ha')
  have hs'p : s' ≫ p = g := pullback.lift_snd _ _ _
  have hs'q : s' ≫ q = a'.left := pullback.lift_fst _ _ _
  have hs' : s' = s := huniq s' ⟨hs'p, by
    change j ≫ s' = z'
    apply pullback.hom_ext
    · change (j ≫ s') ≫ q = z' ≫ q
      rw [Category.assoc, hs'q, show z' ≫ q = z.left from pullback.lift_fst _ _ _]
      exact congrArg Over.Hom.left hres'
    · change (j ≫ s') ≫ p = z' ≫ p
      rw [Category.assoc, hs'p, hz']⟩
  apply Over.OverMorphism.ext
  exact hs'q.symm.trans (congrArg (· ≫ q) hs')

#print axioms existsUnique_torsion_point_over_residue

end SmoothGroup

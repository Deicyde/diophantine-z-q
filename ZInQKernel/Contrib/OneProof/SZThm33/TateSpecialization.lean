import ZInQKernel.Contrib.OneProof.SZThm33.TorsionLiftRelative
import ZInQKernel.Contrib.OneProof.SZRaynaud

/-!
# Tate specialization over a henselian test ring

Every compatible tower of prime-to-residue torsion lifts uniquely to a
compatible tower over the test ring.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace SmoothGroup

variable {S : Type} [CommRing S] {X : Over (Spec (.of S))} [GrpObj X] [IsCommMonObj X]
  {ℓ : ℕ} [Fact ℓ.Prime]

/-- Restrict a compatible Tate tower along a map of test schemes. -/
def restrictTate {T T' : Scheme.{0}} {g : T ⟶ Spec (.of S)} (a : T' ⟶ T) :
    PkgI3.Tate.T ℓ (Additive (Over.mk g ⟶ X)) →ₗ[ℤ_[ℓ]]
      PkgI3.Tate.T ℓ (Additive (Over.mk (a ≫ g) ⟶ X)) :=
  PkgI3.Tate.map (restrictPoint a).toAdditive

/-- Specialization of Tate towers over a henselian local ring is
bijective when the prime is invertible in the base. -/
theorem restrictTate_bijective_of_residue [Smooth X.hom]
    {R : Type} [CommRing R] [HenselianLocalRing R]
    (g : Spec (.of R) ⟶ Spec (.of S)) (hu : IsUnit (ℓ : S)) :
    Function.Bijective (restrictTate (X := X) (ℓ := ℓ) (g := g)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) := by
  let i := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let f := restrictTate (X := X) (ℓ := ℓ) (g := g) i
  have unitPow (n : ℕ) : IsUnit ((ℓ ^ n : ℕ) : S) := by
    simpa only [Nat.cast_pow] using hu.pow n
  have powTors {M : Type} [CommGroup M] (t : PkgI3.Tate.T ℓ (Additive M)) (n : ℕ) :
      (Additive.toMul (t.1 n)) ^ (ℓ ^ n) = 1 :=
    SZRaynaud.pow_smul_tate t n
  have lift (x : Over.mk (i ≫ g) ⟶ X) {n : ℕ} (hx : x ^ (ℓ ^ n) = 1) :=
    existsUnique_torsion_point_over_residue g (ℓ ^ n) (unitPow n) x hx
  change Function.Bijective f
  constructor
  · intro t u h
    apply Subtype.ext
    funext n
    let x := Additive.toMul ((f t).1 n)
    have hx : x ^ (ℓ ^ n) = 1 := powTors (f t) n
    obtain ⟨y, _, hy⟩ := lift x hx
    have ht := hy (Additive.toMul (t.1 n)) ⟨powTors t n, rfl⟩
    have hu := hy (Additive.toMul (u.1 n)) ⟨powTors u n, by
      change Additive.toMul ((f u).1 n) = x
      rw [← h]⟩
    exact congrArg Additive.ofMul (ht.trans hu.symm)
  · intro t
    let x (n : ℕ) := Additive.toMul (t.1 n)
    choose y hyy hyuniq using fun n => lift (x n) (powTors t n)
    have hy (n : ℕ) : (y n) ^ (ℓ ^ n) = 1 := (hyy n).1
    have hres (n : ℕ) : restrictPoint i (y n) = x n := (hyy n).2
    have hcomp (n : ℕ) : (y (n + 1)) ^ ℓ = y n := by
      apply hyuniq n
      refine ⟨?_, ?_⟩
      · rw [← pow_mul, ← pow_succ']
        exact hy (n + 1)
      · rw [map_pow, hres]
        exact t.2.2 n
    let s : PkgI3.Tate.T ℓ (Additive (Over.mk g ⟶ X)) :=
      ⟨fun n => Additive.ofMul (y n), by
        change y 0 = 1
        simpa using hy 0, hcomp⟩
    refine ⟨s, Subtype.ext ?_⟩
    funext n
    exact congrArg Additive.ofMul (hres n)

/-- Restriction to a dominant test scheme is injective when the
group is separated and the original test scheme is reduced. -/
theorem restrictTate_injective_of_isDominant [IsSeparated X.hom]
    {T T' : Scheme.{0}} [IsReduced T] {g : T ⟶ Spec (.of S)}
    (a : T' ⟶ T) [IsDominant a] :
    Function.Injective (restrictTate (X := X) (ℓ := ℓ) (g := g) a) := by
  intro s t h
  apply Subtype.ext
  funext n
  apply Additive.toMul.injective
  apply Over.OverMorphism.ext
  let x := Additive.toMul (s.1 n)
  let y := Additive.toMul (t.1 n)
  apply ext_of_isDominant_of_isSeparated (X := T) X.hom (x.w.trans y.w.symm) a
  exact congrArg (fun v : PkgI3.Tate.T ℓ (Additive (Over.mk (a ≫ g) ⟶ X)) =>
    (Additive.toMul (v.1 n)).left) h

/-- Precomposition by a base-preserving endomorphism of the test
scheme induces an endomorphism on its Tate towers. -/
def tateEnd {T : Scheme.{0}} (g : T ⟶ Spec (.of S)) (a : T ⟶ T) (ha : a ≫ g = g) :
    PkgI3.Tate.T ℓ (Additive (Over.mk g ⟶ X)) →ₗ[ℤ_[ℓ]]
      PkgI3.Tate.T ℓ (Additive (Over.mk g ⟶ X)) :=
  PkgI3.Tate.map (show (Over.mk g ⟶ X) →* (Over.mk g ⟶ X) from
    { toFun := fun x => (Over.homMk a ha : Over.mk g ⟶ Over.mk g) ≫ x
      map_one' := MonObj.comp_one _
      map_mul' := MonObj.comp_mul _ }).toAdditive

/-- A commutative square of test scheme maps gives commuting
endomorphisms and restriction on Tate towers. -/
theorem restrictTate_tateEnd {T T' : Scheme.{0}}
    {g : T ⟶ Spec (.of S)} (i : T' ⟶ T)
    (a : T ⟶ T) (ha : a ≫ g = g) (b : T' ⟶ T') (hb : b ≫ (i ≫ g) = i ≫ g)
    (h : i ≫ a = b ≫ i) (t : PkgI3.Tate.T ℓ (Additive (Over.mk g ⟶ X))) :
    restrictTate i (tateEnd g a ha t) = tateEnd (i ≫ g) b hb (restrictTate i t) := by
  apply Subtype.ext
  funext n
  apply Additive.toMul.injective
  apply Over.OverMorphism.ext
  change i ≫ a ≫ (Additive.toMul (t.1 n)).left =
    b ≫ i ≫ (Additive.toMul (t.1 n)).left
  rw [← Category.assoc, h, Category.assoc]

/-- The identity of a test scheme acts trivially on its Tate towers. -/
theorem tateEnd_id {T : Scheme.{0}} (g : T ⟶ Spec (.of S))
    (t : PkgI3.Tate.T ℓ (Additive (Over.mk g ⟶ X))) :
    tateEnd g (𝟙 _) (Category.id_comp _) t = t := by
  apply Subtype.ext
  funext n
  apply Additive.toMul.injective
  apply Over.OverMorphism.ext
  exact Category.id_comp _

section ResidueEmbedding

variable [Smooth X.hom] {R : Type} [CommRing R] [HenselianLocalRing R]
  {T : Scheme.{0}} (g : Spec (.of R) ⟶ Spec (.of S)) (hu : IsUnit (ℓ : S))
  (j : T ⟶ Spec (.of R))

/-- Lift a residue Tate tower and restrict it to another test scheme. -/
def liftTateFromResidue :
    PkgI3.Tate.T ℓ (Additive (Over.mk ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) ⟶ X)) →ₗ[ℤ_[ℓ]]
      PkgI3.Tate.T ℓ (Additive (Over.mk (j ≫ g) ⟶ X)) :=
  let e := LinearEquiv.ofBijective _ (restrictTate_bijective_of_residue g hu)
  (restrictTate j).comp e.symm.toLinearMap

theorem liftTateFromResidue_injective [IsReduced (Spec (.of R))]
    [IsSeparated X.hom] [IsDominant j] :
    Function.Injective (liftTateFromResidue (X := X) g hu j) := by
  apply Function.Injective.comp (restrictTate_injective_of_isDominant j)
  exact (LinearEquiv.ofBijective _
    (restrictTate_bijective_of_residue (X := X) g hu)).symm.injective

/-- The lift of Tate towers is equivariant under actions on all three
test schemes agreeing with the restriction maps. -/
theorem liftTateFromResidue_tateEnd
    (a : Spec (.of R) ⟶ Spec (.of R)) (ha : a ≫ g = g)
    (b : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of (IsLocalRing.ResidueField R)))
    (hb : b ≫ ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) = (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g)
    (c : T ⟶ T) (hc : c ≫ (j ≫ g) = j ≫ g)
    (hab : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ a = b ≫ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) (hac : j ≫ a = c ≫ j)
    (t : PkgI3.Tate.T ℓ (Additive (Over.mk ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) ⟶ X))) :
    liftTateFromResidue g hu j (tateEnd ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) b hb t) =
      tateEnd (j ≫ g) c hc (liftTateFromResidue g hu j t) := by
  let e := LinearEquiv.ofBijective _ (restrictTate_bijective_of_residue (X := X) g hu)
  have h : e.symm (tateEnd ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) b hb t) = tateEnd g a ha (e.symm t) := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    have h₁ := restrictTate_tateEnd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) a ha b hb hab (e.symm t)
    change e (tateEnd g a ha (e.symm t)) = tateEnd ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) b hb (e (e.symm t)) at h₁
    rw [LinearEquiv.apply_symm_apply] at h₁
    exact h₁.symm
  change restrictTate j (e.symm (tateEnd ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) b hb t)) =
    tateEnd (j ≫ g) c hc (restrictTate j (e.symm t))
  rw [h, restrictTate_tateEnd j a ha c hc hac]

end ResidueEmbedding

#print axioms restrictTate_bijective_of_residue
#print axioms restrictTate_injective_of_isDominant
#print axioms restrictTate_tateEnd
#print axioms liftTateFromResidue_injective
#print axioms liftTateFromResidue_tateEnd

end SmoothGroup

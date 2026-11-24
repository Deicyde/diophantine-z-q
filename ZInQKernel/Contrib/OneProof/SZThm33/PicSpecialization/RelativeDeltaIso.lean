import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.RelativeDeltaClass

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace ZInQ.ToricOrthogonality

/-- A flat open family with geometrically integral fibres over a locally
finite-type geometrically integral family is geometrically integral over the base. -/
theorem geometricallyIntegral_comp {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [LocallyOfFiniteType g] [GeometricallyIntegral g] :
    GeometricallyIntegral (f ≫ g) := by
  constructor
  intro K instK t Z a b h
  let sq := IsPullback.of_hasPullback g t
  let l : Z ⟶ pullback g t := sq.lift (a ≫ f) b (by rw [Category.assoc, h.w])
  have hs : IsPullback a l f (pullback.fst g t) := IsPullback.of_bot' h sq
  have : IsIntegral (pullback g t) :=
    GeometricallyIntegral.geometrically_isIntegral (f := g) t _ _ sq
  have : IsLocallyNoetherian (pullback g t) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g t)
  have : GeometricallyIntegral l := MorphismProperty.of_isPullback hs inferInstance
  have : Flat l := MorphismProperty.of_isPullback hs inferInstance
  have : UniversallyOpen l := MorphismProperty.of_isPullback hs inferInstance
  exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian l

section Product

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

/-- The normalized polarization class on the product of the model. -/
def productDeltaClass (L : G.left.Pic) : (G ⊗ G).left.Pic :=
  deltaClass (fst G G) (snd G G) L

/-- Multiply the first coordinate by `n`. -/
def powerFirst (n : ℕ) : G ⊗ G ⟶ G ⊗ G := lift ((fst G G) ^ n) (snd G G)

/-- Multiply the second coordinate by `n`. -/
def powerSecond (n : ℕ) : G ⊗ G ⟶ G ⊗ G := lift (fst G G) ((snd G G) ^ n)

end Product

set_option backward.isDefEq.respectTransparency false in
/-- On the relative product, the two multiplication pullbacks of a
polarization class agree. -/
theorem map_productDeltaClass_powerFirst_eq_powerSecond
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (G : Over (Spec (.of R))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [GeometricallyIntegral G.hom]
    [IsProper (pullback.snd G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    (L : G.left.Pic) (n : ℕ) :
    Scheme.Pic.map (powerFirst G n).left (productDeltaClass G L) =
      Scheme.Pic.map (powerSecond G n).left (productDeltaClass G L) := by
  let X := G ⊗ G
  let s : 𝟙_ (Over (Spec (.of R))) ⟶ X := lift η[G] η[G]
  let x : X ⟶ G := fst G G
  let y : X ⟶ G := snd G G
  have hsx : s ≫ x = 1 := by simp only [s, x, lift_fst, CategoryTheory.Hom.one_def, toUnit_unit, Category.id_comp]
  have hsy : s ≫ y = 1 := by simp only [s, y, lift_snd, CategoryTheory.Hom.one_def, toUnit_unit, Category.id_comp]
  have : Smooth x.left := show Smooth (pullback.fst G.hom G.hom) from inferInstance
  have : GeometricallyIntegral x.left :=
    show GeometricallyIntegral (pullback.fst G.hom G.hom) from inferInstance
  have : Smooth X.hom := by rw [← Over.w x]; infer_instance
  have : GeometricallyIntegral X.hom := by
    rw [← Over.w x]
    exact geometricallyIntegral_comp x.left G.hom
  have hpow₁ := deltaClass_pow_left_dvr (K := K) s x y (Or.inl hsx) L n
  have hpow₂ := deltaClass_pow_left_dvr (K := K) s y x (Or.inl hsy) L n
  have h₁ : Scheme.Pic.map (powerFirst G n).left (productDeltaClass G L) =
      deltaClass (x ^ n) y L := by
    simp only [productDeltaClass, map_deltaClass, powerFirst, lift_fst, lift_snd, x, y]
  have h₂ : Scheme.Pic.map (powerSecond G n).left (productDeltaClass G L) =
      deltaClass x (y ^ n) L := by
    simp only [productDeltaClass, map_deltaClass, powerSecond, lift_fst, lift_snd, x, y]
  rw [h₁, h₂, hpow₁, deltaClass_comm x (y ^ n), hpow₂, deltaClass_comm x y]

/-- Equality of the two classes supplies an actual isomorphism of sheaves on the model. -/
theorem nonempty_iso_powerFirst_powerSecond
    {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (G : Over (Spec (.of R))) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [GeometricallyIntegral G.hom]
    [IsProper (pullback.snd G.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))]
    (L : G.left.Pic) (M : (G ⊗ G).left.Modules) [M.IsInvertible]
    (hM : Scheme.Pic.mk M = productDeltaClass G L) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback (powerFirst G n).left).obj M ≅
      (Scheme.Modules.pullback (powerSecond G n).left).obj M) := by
  apply (Scheme.Pic.mk_eq_mk_iff _ _).mp
  rw [← Scheme.Pic.map_mk, ← Scheme.Pic.map_mk, hM]
  exact map_productDeltaClass_powerFirst_eq_powerSecond (K := K) G L n

end ZInQ.ToricOrthogonality

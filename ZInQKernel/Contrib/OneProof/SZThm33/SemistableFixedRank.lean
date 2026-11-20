import ZInQKernel.Contrib.OneProof.SZThm33.SemistableTateRank

/-!
# Fixed-space and toric ranks from the split special-fibre presentation
-/

noncomputable section

set_option maxHeartbeats 1200000

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ZInQ.HeightSplit

namespace SZRaynaud

private def precompPointEquiv {S : Scheme.{0}} {P Q G : Over S} [GrpObj G]
    (e : P ≅ Q) : (P ⟶ G) ≃* (Q ⟶ G) where
  toFun p := e.inv ≫ p
  invFun p := e.hom ≫ p
  left_inv _ := Iso.hom_inv_id_assoc _ _
  right_inv _ := Iso.inv_hom_id_assoc _ _
  map_mul' _ _ := MonObj.comp_mul _ _ _

private def unitPointIso (k : Type) [Field k] :
    𝟙_ (Over (Spec (.of k))) ≅ algPt k k :=
  Over.isoMk (Iso.refl (Spec (.of k))) (by
    change (𝟙 (Spec (.of k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
    rw [Category.id_comp, Algebra.algebraMap_self]
    exact Spec.map_id _)

variable {ℓ : ℕ} [Fact ℓ.Prime]

private def mulEquivTate {P Q : Type*} [CommGroup P] [CommGroup Q] (e : P ≃* Q) :
    PkgI3.Tate.T ℓ (Additive P) ≃ₗ[ℤ_[ℓ]] PkgI3.Tate.T ℓ (Additive Q) :=
  let f := PkgI3.Tate.map e.toMonoidHom.toAdditive (ℓ := ℓ)
  LinearEquiv.ofBijective f ⟨by
    intro x y h
    apply Subtype.ext
    funext n
    apply Additive.toMul.injective
    apply e.injective
    exact congrArg (fun t : PkgI3.Tate.T ℓ (Additive Q) => Additive.toMul (t.1 n)) h,
    by
      intro y
      refine ⟨PkgI3.Tate.map e.symm.toMonoidHom.toAdditive y, ?_⟩
      apply Subtype.ext
      funext n
      exact congrArg Additive.ofMul (e.apply_symm_apply _)⟩

private theorem mapGroupPoint_injective {S : Scheme.{0}} {P G H : Over S}
    [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] [Mono f.left] :
    Function.Injective (mapGroupPoint f (P := P)) := fun _ _ h =>
  Over.OverMorphism.ext ((cancel_mono f.left).mp (congrArg Over.Hom.left h))

private theorem isCommMonObj_of_mono {S : Scheme.{0}} {G H : Over S}
    [GrpObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f] [Mono f.left] :
    IsCommMonObj G := by
  apply (isCommMonObj_iff_isMulCommutative G).mpr
  intro P
  refine ⟨⟨fun a b => ?_⟩⟩
  apply mapGroupPoint_injective f
  rw [map_mul, map_mul, _root_.mul_comm]

/-- Rational points of the connected open subgroup suffice for geometric
special-fibre Tate, with the literal point type used by the semistable witness. -/
def tateEquiv_connectedOpenSubgroup {k : Type} [Field k] [IsAlgClosed k]
    {G U : Over (Spec (.of k))} [GrpObj G] [GrpObj U] [IsCommMonObj G] [IsCommMonObj U]
    [LocallyOfFiniteType (G).hom] [QuasiCompact (G).hom] [ConnectedSpace U.left]
    (i : U ⟶ G) [IsOpenImmersion i.left] [IsMonHom i] :
    PkgI3.Tate.T ℓ (Additive (algPt k k ⟶ U)) ≃ₗ[ℤ_[ℓ]]
      PkgI3.Tate.T ℓ (Additive (algPt k k ⟶ G)) :=
  let eU := mulEquivTate (ℓ := ℓ) (precompPointEquiv (unitPointIso k) (G := U))
  let eG := mulEquivTate (ℓ := ℓ) (precompPointEquiv (unitPointIso k) (G := G))
  let e := LinearEquiv.ofBijective _ (bijective_tate_map_connectedOpenSubgroup (ℓ := ℓ) i)
  eU.symm.trans (e.trans eG)

namespace Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] [IsAlgClosed Ω]
  {O : ValuationSubring K} [IsDiscreteValuationRing O] {w : ValuationSubring Ω}
  (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (M : GroupModelO A O)
  (hu : IsUnit (ℓ : O))

local instance : IsCommMonObj (geomSpecialFibre M) := isCommMonObj_geomSpecialFibre A M

omit [Fact ℓ.Prime] [IsDiscreteValuationRing O] in
include hu in
theorem prime_ne_zero_in_geometric_residue : (ℓ : (ResBarO O)) ≠ 0 := by
  simpa only [map_natCast] using (hu.map (algebraMap O (ResBarO O))).ne_zero

/-- The actual rational inertia-fixed subspace from the model. -/
abbrev inertiaFixedTateSubspace : Submodule ℚ_[ℓ] (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TΩ A Ω ℓ)) :=
  (geomSpecialEmbedRational hw A M hu).range

omit [IsDiscreteValuationRing O] in
/-- The fixed space has dimension twice the abelian quotient dimension
plus the torus rank of the specified split special-fibre presentation. -/
theorem finrank_inertiaFixedTateSubspace_of_split
    (U : Over (Spec (.of (ResBarO O)))) [GrpObj U] [ConnectedSpace U.left]
    (i : U ⟶ (geomSpecialFibre M)) [IsOpenImmersion i.left] [IsMonHom i]
    (B : PkgI3.AbVar (ResBarO O)) (π : U ⟶ B.X) [IsMonHom π] [Surjective π.left]
    (r b : ℕ) (hb : B.dim = (b : WithBot ℕ∞))
    (e : (Fin r → (ResBarO O)ˣ) →* (algPt (ResBarO O) (ResBarO O) ⟶ U)) (he : Function.Injective e)
    (hk : ∀ u : algPt (ResBarO O) (ResBarO O) ⟶ U, u ≫ π = 1 ↔ u ∈ e.range) :
    Module.finrank ℚ_[ℓ] (inertiaFixedTateSubspace hw A M hu) = 2 * b + r := by
  have : LocallyOfFiniteType (geomSpecialFibre M).hom := by
    change LocallyOfFiniteType (pullback.snd M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))))
    infer_instance
  have : QuasiCompact (geomSpecialFibre M).hom := by
    change QuasiCompact (pullback.snd M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))))
    infer_instance
  have : LocallyOfFiniteType U.hom := by
    rw [← i.w]
    infer_instance
  have : LocallyOfFiniteType π.left := by
    have : LocallyOfFiniteType (π.left ≫ B.X.hom) := by rw [π.w]; infer_instance
    exact locallyOfFiniteType_of_comp π.left B.X.hom
  have := isCommMonObj_of_mono i
  obtain ⟨E⟩ := semiabelian_tate_equiv U B π r b hb (prime_ne_zero_in_geometric_residue hu) e he hk
  let E' := (tateEquiv_connectedOpenSubgroup (ℓ := ℓ) i).symm.trans E
  have : Module.Free ℤ_[ℓ] (PkgI3.Tate.T ℓ (Additive (algPt (ResBarO O) (ResBarO O) ⟶ (geomSpecialFibre M)))) :=
    Module.Free.of_equiv E'.symm
  rw [LinearMap.finrank_range_of_inj (geomSpecialEmbedRational_injective hw A M hu),
    Module.finrank_baseChange, E'.finrank_eq, Module.finrank_fin_fun]

#print axioms finrank_inertiaFixedTateSubspace_of_split

end Ambient
end SZRaynaud

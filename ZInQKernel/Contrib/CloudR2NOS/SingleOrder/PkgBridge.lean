/-
# H5 / NOS round 2, lane 1: bridge from the original `PkgI2` inertia condition to the
# source single-order hypothesis `hunr`, for a model given as a `Grp (Over (Spec R))`

Newly authored glue (H5 round-2 lane 1, 2026-11-14). The source objects are those of the
lane-4 canonical port of anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
(Apache-2.0, Copyright 2026 Anthropic, PBC; see the H76 `LICENSE`/`NOTICE`); the source law is
`ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp` (lead's `AVInput.lean`, built on the published H76
`relativeLawOfGrpObj`) of the SAME group object. The adjunction-multiplicativity argument follows
H4's `ZInQ.Contrib.CloudR2Raynaud.GenericPoints.homEquiv_mul` (derived from
`ZInQKernel/Contrib/AbVarBC/Points.lean` of Deicyde/diophantine-z-q), generalized here from a field
extension to the generic-fibre map `Spec K → Spec R` of an arbitrary ring.

Content (no new hypothesis is asserted as a theorem; nothing here is a model supplier):
* `isInertia_iff_mem_inertiaSubgroupIn`: the source's `inertiaSubgroupIn` membership IS the
  target's `PkgI2.IsInertia`;
* `inertiaTrivialOn_of_iso` / `inertiaTrivialOn_iso_iff`: `PkgI2.InertiaTrivialOn` is invariant
  under isomorphisms of group objects over `Spec K`;
* `genericGrp K 𝒜 := (Over.pullback (Spec.map (algebraMap R K))).mapGrp.obj 𝒜` — literally the
  generic fibre of `PkgI2.HasGoodReduction`;
* `homEquiv_mul` / `homMulEquiv`: the `Over.map ⊣ Over.pullback` adjunction along `Spec K → Spec R`
  is multiplicative on points;
* `toPts`: the literal identification of source generic-fibre points over `Ω` with morphisms
  `specOver K Ω ⟶` the pulled-back group object (= `PkgI2.Pts (genericGrp K 𝒜) Ω`), same
  underlying scheme morphism;
* `isTorsionPoint_genericFibre_iff`: source generic-fibre `m`-torsion ⟺ `toPts x ^ m = 1`;
* `specMap_comp_eq_iff_galHom`: the source Galois condition ⟺ `galHom σ ≫ toPts x = toPts x`
  (`= PkgI2.galAct`);
* `sourceHunr_of_inertiaTrivialOn`: `PkgI2.InertiaTrivialOn (genericGrp K 𝒜) V m` for every `V`
  containing `R` gives the source single-order `hunr` at `m` (all valuations containing `R`, any `Ω`);
* `abelianSchemePropertyBundle_of_grp_of_infinite_setOf`: the infinite-orders converse for such a
  model with orders in the target's exact set shape;
* `abelianSchemePropertyBundle_of_targetOrders`: the same at the ORIGINAL `K, O, w (comap = O), A`
  and the literal target set `{m | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}`, for a
  group-object model over `O` with generic fibre `≅ A` and the (explicit) Néron property `hN`.
-/
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.Converse
import ZInQKernel.Contrib.CloudR2NOS.AVInput
import ZInQKernel.Contrib.CloudR2NOS.Valuation.Points
import ZInQKernel.HDecomp.Objects

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder.PkgBridge

open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra (SchemeHomOver specGenericFibreInclusion
  schemeHomOverToOverHom overHomToSchemeHomOver)

/-! ### Inertia membership -/

/-- The source's `inertiaSubgroupIn` (image of the inertia group under the decomposition-group
inclusion) is exactly the target's `PkgI2.IsInertia`. -/
theorem isInertia_iff_mem_inertiaSubgroupIn {K L : Type u} [Field K] [Field L] [Algebra K L]
    (V : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    PkgI2.IsInertia V σ ↔
      σ ∈ ZInQ.Contrib.CloudW03NeronSurj.FLT.ValuationSubring.inertiaSubgroupIn K V := by
  constructor
  · rintro ⟨h, hσ⟩
    exact Subgroup.mem_map.mpr ⟨⟨σ, h⟩, hσ, rfl⟩
  · intro hσ
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσ
    exact ⟨τ.2, hτ⟩

/-! ### The source law of a group object: powers -/

section Law

variable {R : Type u} [CommRing R] (G : Grp (Over (Spec (CommRingCat.of R))))

theorem relativeLawOfGrp_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (y : SchemeHomOver t G.X.hom) :
    letI : GrpObj (Over.mk G.X.hom) := G.grp
    schemeHomOverToOverHom ((ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp G).nsmul t n y) =
      (schemeHomOverToOverHom y) ^ n := by
  letI : GrpObj (Over.mk G.X.hom) := G.grp
  induction n with
  | zero =>
    show schemeHomOverToOverHom (overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk G.X.hom)) = _
    rw [ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver,
      pow_zero]
  | succ n ih =>
    show schemeHomOverToOverHom (overHomToSchemeHomOver
      (schemeHomOverToOverHom ((ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp G).nsmul t n y) *
        schemeHomOverToOverHom y)) = _
    rw [ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver,
      ih, pow_succ]

theorem relativeLawOfGrp_isTorsionPoint_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (y : SchemeHomOver t G.X.hom) :
    letI : GrpObj (Over.mk G.X.hom) := G.grp
    (ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp G).IsTorsionPoint t n y ↔
      (schemeHomOverToOverHom y) ^ n = 1 := by
  letI : GrpObj (Over.mk G.X.hom) := G.grp
  rw [ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.RelativeGroupLaw.isTorsionPoint_def,
    ← relativeLawOfGrp_nsmul G t n y]
  constructor
  · intro h
    rw [h]
    exact ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver _
  · intro h
    have h' := congrArg overHomToSchemeHomOver h
    rwa [ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom] at h'

end Law

/-! ### Transport of the target inertia condition along a group-object isomorphism -/

/-- `PkgI2.InertiaTrivialOn` transfers along an isomorphism of group objects over `Spec K`
(points are post-composed with the isomorphism, which is a monoid morphism). -/
theorem inertiaTrivialOn_of_iso {K : Type u} [Field K]
    {G A : Grp (Over (Spec (CommRingCat.of K)))} (e : G ≅ A)
    {L : Type u} [Field L] [Algebra K L] (w : ValuationSubring L) (m : ℕ)
    (hA : PkgI2.InertiaTrivialOn A w m) : PkgI2.InertiaTrivialOn G w m := by
  intro σ hσ x hx
  have hx' : x ≫ e.hom.hom.hom ∈ PkgI2.torsion A L m := by
    show (x ≫ e.hom.hom.hom) ^ m = 1
    rw [← MonObj.pow_comp, show x ^ m = 1 from hx, MonObj.one_comp]
  have h := hA σ hσ _ hx'
  have h' : PkgI2.galAct G σ x ≫ e.hom.hom.hom = x ≫ e.hom.hom.hom := by
    simpa only [PkgI2.galAct, Category.assoc] using h
  exact (cancel_mono e.hom.hom.hom).mp h'

/-- Both directions: `PkgI2.InertiaTrivialOn` is invariant under group-object isomorphisms. -/
theorem inertiaTrivialOn_iso_iff {K : Type u} [Field K]
    {G A : Grp (Over (Spec (CommRingCat.of K)))} (e : G ≅ A)
    {L : Type u} [Field L] [Algebra K L] (w : ValuationSubring L) (m : ℕ) :
    PkgI2.InertiaTrivialOn G w m ↔ PkgI2.InertiaTrivialOn A w m :=
  ⟨inertiaTrivialOn_of_iso e.symm w m, inertiaTrivialOn_of_iso e w m⟩

/-! ### The generic fibre: source points, torsion and Galois action vs target points -/

section Generic

-- The group structure Mathlib's `Functor.mapGrp` puts on a pulled-back group object.
attribute [local instance] Functor.grpObjObj

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
  (𝒜 : Grp (Over (Spec (CommRingCat.of R))))

/-- The generic-fibre group object of `𝒜`, exactly as in `PkgI2.HasGoodReduction`. -/
def genericGrp : Grp (Over (Spec (CommRingCat.of K))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.obj 𝒜

theorem genericGrp_eq :
    genericGrp K 𝒜 =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.obj 𝒜 :=
  rfl

/-- The pullback/forgetful adjunction along `Spec K → Spec R` is multiplicative on points
(H4 `GenericPoints.homEquiv_mul`, generalized from a field extension to `Spec K → Spec R`). -/
theorem homEquiv_mul (X : Over (Spec (CommRingCat.of K)))
    (p q : (Over.map (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X ⟶ 𝒜.X) :
    (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap R K)))).homEquiv X 𝒜.X (p * q) =
      (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap R K)))).homEquiv X 𝒜.X p *
        (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap R K)))).homEquiv X 𝒜.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- The same adjunction as a multiplicative equivalence of point monoids. -/
def homMulEquiv (X : Over (Spec (CommRingCat.of K))) :
    ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X ⟶ 𝒜.X) ≃*
      (X ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj 𝒜.X) :=
  { (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap R K)))).homEquiv X 𝒜.X with
    map_mul' := homEquiv_mul K 𝒜 X }

variable (Ω : Type u) [Field Ω] [Algebra K Ω]

/-- Source generic-fibre points over `Ω` ARE morphisms `specOver K Ω ⟶` the pulled-back group
object (the same underlying morphism `Spec Ω → pullback`), i.e. target points of `genericGrp`. -/
def toPts (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      (pullback.snd 𝒜.X.hom (specGenericFibreInclusion R K))) :
    PkgI2.specOver K Ω ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj 𝒜.X :=
  Over.homMk x.1 x.2

theorem toPts_left (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      (pullback.snd 𝒜.X.hom (specGenericFibreInclusion R K))) :
    (toPts K 𝒜 Ω x).left = x.1 :=
  rfl

theorem toPts_injective : Function.Injective (toPts K 𝒜 Ω) := by
  intro x y h
  apply Subtype.ext
  exact congrArg CommaMorphism.left h

/-- Under the adjunction, `toPts x` corresponds to the source's base-change point of `x`
(underlying morphism `x ≫ pullback.fst`). -/
theorem homMulEquiv_symm_toPts_left
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      (pullback.snd 𝒜.X.hom (specGenericFibreInclusion R K))) :
    ((homMulEquiv K 𝒜 (PkgI2.specOver K Ω)).symm (toPts K 𝒜 Ω x)).left =
      x.1 ≫ pullback.fst 𝒜.X.hom (specGenericFibreInclusion R K) := by
  show (((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap R K)))).homEquiv
      (PkgI2.specOver K Ω) 𝒜.X).symm (toPts K 𝒜 Ω x)).left = _
  rw [Adjunction.homEquiv_counit, Over.comp_left, Over.mapPullbackAdj_counit_app]
  rfl

/-- **Torsion.** Source generic-fibre `m`-torsion (for the law of the SAME group object) is
`m`-torsion of the identified point in the pulled-back group object. -/
theorem isTorsionPoint_genericFibre_iff (m : ℕ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      (pullback.snd 𝒜.X.hom (specGenericFibreInclusion R K))) :
    ((ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp 𝒜).genericFibre K).IsTorsionPoint
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) m x ↔
      (toPts K 𝒜 Ω x) ^ m = 1 := by
  rw [ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self.P2mSerreTateLemmaTwo.isTorsionPoint_baseChange_iff,
    relativeLawOfGrp_isTorsionPoint_iff]
  have key : (toPts K 𝒜 Ω x) ^ m = 1 ↔
      ((homMulEquiv K 𝒜 (PkgI2.specOver K Ω)).symm (toPts K 𝒜 Ω x)) ^ m = 1 := by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  rw [key]
  have hab : ((homMulEquiv K 𝒜 (PkgI2.specOver K Ω)).symm (toPts K 𝒜 Ω x) :
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
          specGenericFibreInclusion R K) ⟶ Over.mk 𝒜.X.hom) =
      ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.schemeHomOverToOverHom
        (ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase
          (specGenericFibreInclusion R K) x) := by
    apply Over.OverMorphism.ext
    exact homMulEquiv_symm_toPts_left K 𝒜 Ω x
  rw [← hab]
  -- both sides are the same proposition up to the (definitionally equal) point-monoid instances
  exact Iff.rfl

/-- **Galois action.** The source condition `Spec.map σ ≫ x = x` is `galHom σ ≫ toPts x = toPts x`
(i.e. `PkgI2.galAct σ (toPts x) = toPts x`). -/
theorem specMap_comp_eq_iff_galHom (σ : Ω ≃ₐ[K] Ω)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
      (pullback.snd 𝒜.X.hom (specGenericFibreInclusion R K))) :
    Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1 ↔
      PkgI2.galHom Ω σ ≫ toPts K 𝒜 Ω x = toPts K 𝒜 Ω x := by
  constructor
  · intro h
    apply Over.OverMorphism.ext
    exact h
  · intro h
    exact congrArg CommaMorphism.left h

/-- **The bridge.** If, for every valuation subring `V` of `Ω` containing (the image of) `R`, the
inertia group fixes the target `m`-torsion of the generic-fibre group object `genericGrp K 𝒜`,
then the source single-order hypothesis `hunr` at `m` holds for the source law of `𝒜`
(`ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp 𝒜`) on its generic-fibre points over `Ω`. -/
theorem sourceHunr_of_inertiaTrivialOn (m : ℕ)
    (h : ∀ V : ValuationSubring Ω, (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ V) →
      PkgI2.InertiaTrivialOn (genericGrp K 𝒜) V m) :
    ∀ (A : ValuationSubring Ω), (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) →
      ∀ σ : Ω ≃ₐ[K] Ω,
        σ ∈ ZInQ.Contrib.CloudW03NeronSurj.FLT.ValuationSubring.inertiaSubgroupIn K A →
      ∀ (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
          (pullback.snd 𝒜.X.hom (specGenericFibreInclusion R K))),
        ((ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp 𝒜).genericFibre K).IsTorsionPoint
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) m x →
          Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1 := by
  intro A hA σ hσ x hx
  have hT : (toPts K 𝒜 Ω x : PkgI2.Pts (genericGrp K 𝒜) Ω) ∈
      PkgI2.torsion (genericGrp K 𝒜) Ω m :=
    (isTorsionPoint_genericFibre_iff K 𝒜 Ω m x).mp hx
  have hfix := h A hA σ ((isInertia_iff_mem_inertiaSubgroupIn A σ).mpr hσ) _ hT
  exact (specMap_comp_eq_iff_galHom K 𝒜 Ω σ x).mpr hfix

end Generic

/-! ### Composite: the infinite-orders converse for a group-object model -/

/-- **Infinite-orders converse for a model given as a group object** `𝒜` over the DVR `R`, with
the source law of the SAME group object: the orders are taken in the exact shape of the target's
set `{m | 0 < m ∧ IsUnit (m : R) ∧ Q m}`, and each order needs only the TARGET inertia condition
`PkgI2.InertiaTrivialOn (genericGrp K 𝒜) V m` at valuation subrings `V` of `Ω` containing `R`.
The Néron model property `hN` is an explicit (intermediate) hypothesis. -/
theorem abelianSchemePropertyBundle_of_grp_of_infinite_setOf
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (𝒜 : Grp (Over (Spec (CommRingCat.of R)))) [IsCommMonObj 𝒜.X]
    (hN : ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.NeronModelPropertyBundle R K 𝒜.X.hom)
    (hBK : ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle K
      (pullback.snd 𝒜.X.hom (specGenericFibreInclusion R K)))
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Q : ℕ → Prop) (hS : {m : ℕ | 0 < m ∧ IsUnit (m : R) ∧ Q m}.Infinite)
    (hQ : ∀ m : ℕ, 0 < m → IsUnit (m : R) → Q m →
      ∀ V : ValuationSubring Ω, (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ V) →
        PkgI2.InertiaTrivialOn (genericGrp K 𝒜) V m) :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle R 𝒜.X.hom :=
  ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_infinite_setOf_singleOrder_isAlgClosure
    K (ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp 𝒜)
    (ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp_commutative 𝒜) hN hBK Ω Q hS
    (fun m h0 hu hq => sourceHunr_of_inertiaTrivialOn K 𝒜 Ω m (hQ m h0 hu hq))

/-- **At the original data.** For the ORIGINAL field `K`, DVR `O`, prolongation `w` with the exact
comap condition, group object `A`, and a group-object model `𝒜` over `O` whose generic fibre
(`genericGrp K 𝒜`, the same object as in `PkgI2.HasGoodReduction`) is isomorphic to `A`: if the
EXACT target set `{m | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}` is infinite and
`𝒜` has the (explicit, intermediate) Néron model property, then `𝒜` is an abelian scheme (source
bundle). Uses H5 lane 2's `Valuation.inertiaTrivialOn_all_prolongations` (fixed `w` to every
valuation subring of `AlgebraicClosure K` containing `O`, including `⊤`) on the same `A`. -/
theorem abelianSchemePropertyBundle_of_targetOrders
    {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (CommRingCat.of K))))
    (𝒜 : Grp (Over (Spec (CommRingCat.of O)))) [IsCommMonObj 𝒜.X]
    (e : genericGrp K 𝒜 ≅ A)
    (hN : ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra.NeronModelPropertyBundle O K 𝒜.X.hom)
    (hBK : ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle K
      (pullback.snd 𝒜.X.hom (specGenericFibreInclusion O K)))
    (hS : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite) :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle O 𝒜.X.hom :=
  abelianSchemePropertyBundle_of_grp_of_infinite_setOf K 𝒜 hN hBK (AlgebraicClosure K)
    (fun m => PkgI2.InertiaTrivialOn A w m) hS
    (fun m _ _ hq V hV => inertiaTrivialOn_of_iso e V m
      (ZInQ.Contrib.CloudR2NOS.Valuation.inertiaTrivialOn_all_prolongations O w hw A m hq V
        -- `algebraMap O K̄ r = algebraMap K K̄ (algebraMap O K r)` holds definitionally
        (fun r => hV r)))

end ZInQ.Contrib.CloudR2NOS.SingleOrder.PkgBridge

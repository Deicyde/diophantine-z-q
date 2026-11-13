import Mathlib

/-!
# g0-product: the glue piece `ProductExists` (G17)

Check with `lake env lean scratch/g0-product/Product.lean`.

§1 copies, verbatim from `scratch/g0-split/Split.lean`, the definitions the piece depends on:
`PkgI3.AbVar` with `PkgI3.AbVar.dim` (Split.lean l. 2524-2543), `ZInQ.DefFaltings.AbVar` with
`ZInQ.DefFaltings.AbVar.dim` (l. 17798-17820), `G0Split.IsProductOf` (l. 19463) and
`G0Split.ProductExists` (l. 19570).

§2 proves, from Mathlib alone, that the fibre product `A ×_L Z` (Mathlib's cartesian monoidal
product `A.X ⊗ Z.X` in `Over (Spec L)`, whose underlying scheme is `pullback A.X.hom Z.X.hom`)
is a group scheme over `L` that is proper, smooth and geometrically integral, i.e. a
`ZInQ.DefFaltings.AbVar L`, and that `IsProductOf (A.X ⊗ Z.X) A.X Z.X` holds with the two
projections.

§3 proves `ProductExists` from one strictly smaller named Prop, `DimProductOverField`
(dimension of a product of schemes of finite type over a field, a textbook theorem).
-/

noncomputable section

/-! ## §1. Verbatim copies -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/-- An abelian variety over a field `K`: a group object in schemes over `Spec K` whose structure
morphism is proper, smooth and geometrically integral (Mumford §4, Milne 1986 §1). -/
structure AbVar (K : Type u) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

namespace AbVar

variable {K : Type u} [Field K]

/-- Commutativity is a Mathlib theorem (Stacks 0BFD), not an assumption. -/
instance (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

/-- The dimension of `A` (Krull dimension of the underlying space). -/
def dim (A : AbVar K) : WithBot ℕ∞ := topologicalKrullDim A.X.left

end AbVar

end PkgI3

namespace ZInQ.DefFaltings

section ModelsSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) An abelian variety over a field `K`: a group
object in schemes over `Spec K`, proper, smooth and geometrically integral. -/
structure AbVar (K : Type) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

/-- (copied from `ZInQKernel/HDecomp/Objects.lean`) The dimension of `A` (Krull dimension of the
underlying space). -/
noncomputable def AbVar.dim {K : Type} [Field K] (A : AbVar K) : WithBot ℕ∞ := topologicalKrullDim A.X.left

end ModelsSec

end ZInQ.DefFaltings

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.DefFaltings

/-- `P ≅ A × Z` as group schemes: homomorphisms `p₁ : P → A`, `p₂ : P → Z` with
`(p₁, p₂) : P → A × Z` an isomorphism. -/
def IsProductOf {K : Type} [Field K] (P A Z : Over (Spec (CommRingCat.of K))) [MonObj P]
    [MonObj A] [MonObj Z] : Prop :=
  ∃ (p₁ : P ⟶ A) (p₂ : P ⟶ Z), IsMonHom p₁ ∧ IsMonHom p₂ ∧ IsIso (lift p₁ p₂)

/-- **Missing piece 7 (definition-level glue; G17).** The product `A × Z` of abelian varieties is an
abelian variety `P` (proper, smooth, geometrically integral group scheme), with
`dim P = dim A + dim Z` (Mumford §4; STANDARD; geometric integrality of products is not in
Mathlib). -/
def ProductExists : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A Z : PkgI3.AbVar L),
    ∃ P : ZInQ.DefFaltings.AbVar L, IsProductOf P.X A.X Z.X ∧ P.dim = A.dim + Z.dim

end G0Split

/-! ## §2. The product is an abelian variety (proved, Mathlib only) -/

namespace G0Product

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Glue (proved).** Geometric integrality is stable under composition `X → Y → S` when the
first map is geometrically integral, flat and universally open and the second is geometrically
integral and locally of finite type. For a field `K` and `Spec K → S`, the base change
`X ×_S K = X ×_Y (Y ×_S K)` is integral by Mathlib's
`AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` applied over the
integral, locally noetherian scheme `Y ×_S K`. -/
theorem geometricallyIntegral_comp {X Y S : Scheme} (g : X ⟶ Y) (h : Y ⟶ S)
    [GeometricallyIntegral g] [Flat g] [UniversallyOpen g]
    [GeometricallyIntegral h] [LocallyOfFiniteType h] :
    GeometricallyIntegral (g ≫ h) := by
  refine ⟨fun K _ y Z fst snd hP => ?_⟩
  have : IsIntegral (pullback h y) := pullback_of_geometrically
    (GeometricallyIntegral.geometrically_isIntegral (f := h)) K y
  have : IsLocallyNoetherian (pullback h y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd h y)
  have hI : IsIntegral (pullback g (pullback.fst h y)) := inferInstance
  let e : Z ≅ pullback g (pullback.fst h y) :=
    hP.isoPullback ≪≫ (pullbackRightPullbackFstIso h y g).symm
  have : Nonempty Z := ⟨e.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

/-- **Glue (proved).** The fibre product `A ×_K Z` of two abelian varieties over a field `K`
(Mathlib's cartesian monoidal product `A.X ⊗ Z.X` in `Over (Spec K)`, with the product group
structure `GrpObj.tensorObj.instTensorObj`) is an abelian variety in the sense of
`ZInQ.DefFaltings.AbVar`: proper and smooth (composition and base change) and geometrically
integral (`geometricallyIntegral_comp`). -/
def prodAbVar {K : Type} [Field K] (A Z : PkgI3.AbVar K) : ZInQ.DefFaltings.AbVar K :=
  haveI : IsProper (A.X ⊗ Z.X).hom := by dsimp; infer_instance
  haveI : Smooth (A.X ⊗ Z.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral (A.X ⊗ Z.X).hom := by
    rw [Over.tensorObj_hom]; exact geometricallyIntegral_comp _ _
  { X := A.X ⊗ Z.X }

@[simp] lemma prodAbVar_X {K : Type} [Field K] (A Z : PkgI3.AbVar K) :
    (prodAbVar A Z).X = A.X ⊗ Z.X := rfl

/-- **Glue (proved).** `prodAbVar A Z` is the product of `A` and `Z` in the sense of
`G0Split.IsProductOf`, via the two projections (homomorphisms for the product group law;
`(fst, snd) = 𝟙`). -/
theorem isProductOf_prodAbVar {K : Type} [Field K] (A Z : PkgI3.AbVar K) :
    G0Split.IsProductOf (prodAbVar A Z).X A.X Z.X := by
  change G0Split.IsProductOf (A.X ⊗ Z.X) A.X Z.X
  exact ⟨fst A.X Z.X, snd A.X Z.X, inferInstance, inferInstance, by
    rw [lift_fst_snd]; infer_instance⟩

/-- The dimension of `prodAbVar A Z` is the Krull dimension of the fibre product scheme. -/
lemma prodAbVar_dim {K : Type} [Field K] (A Z : PkgI3.AbVar K) :
    (prodAbVar A Z).dim = topologicalKrullDim (pullback (C := Scheme) A.X.hom Z.X.hom) := rfl

end G0Product

/-! ## §3. `ProductExists` from the dimension formula -/

namespace G0Product

open CategoryTheory AlgebraicGeometry Limits

/-- **Glue, proved in §4-§5 (dimension of a product over a field).** For schemes `X`, `Y` of finite
type over a field `K`, `dim (X ×_K Y) = dim X + dim Y` (Krull dimensions of the underlying
spaces, in `WithBot ℕ∞`; both sides are `⊥` if `X` or `Y` is empty). Source: Stacks Project,
Varieties, Lemma 33.20.5 (Tag 0B2L?, UNVERIFIED number); Görtz-Wedhorn, *Algebraic Geometry I*,
Prop. 5.37 (UNVERIFIED number); for integral `X`, `Y` over an algebraically closed field,
Hartshorne II Ex. 3.20 / I Prop. 1.10 style transcendence-degree argument. STANDARD. -/
def DimProductOverField : Prop :=
  ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K))
    (g : Y ⟶ Spec (CommRingCat.of K)), LocallyOfFiniteType f → QuasiCompact f →
    LocallyOfFiniteType g → QuasiCompact g →
    topologicalKrullDim (pullback (C := Scheme) f g) = topologicalKrullDim X + topologicalKrullDim Y

/-- **G17, `ProductExists`, proved from `DimProductOverField`.** -/
theorem productExists_of_dimProduct (hD : DimProductOverField) : G0Split.ProductExists := by
  intro L _ _ A Z
  refine ⟨prodAbVar A Z, isProductOf_prodAbVar A Z, ?_⟩
  rw [prodAbVar_dim]
  exact hD L A.X.left Z.X.left A.X.hom Z.X.hom inferInstance inferInstance inferInstance
    inferInstance

end G0Product

#print axioms G0Product.productExists_of_dimProduct

/-! ## §4. `DimProductOverField` from the ring-level formula `DimTensorFG` (proved glue) -/

namespace G0Product

open Order

/-- **Glue (proved, topology).** If open embeddings `f i : Y i → X` cover `X` and `X` has a chain
of `n + 1` irreducible closed subsets, so does some `Y i`: pull the chain back along an `f i`
whose image meets the smallest member (a nonempty open subset of an irreducible set is dense,
so the pulled-back chain stays strict). -/
theorem exists_le_dim_of_cover {X : Type*} [TopologicalSpace X] {ι : Type*} {Y : ι → Type*}
    [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) (n : ℕ)
    (hn : (n : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ i, (n : WithBot ℕ∞) ≤ topologicalKrullDim (Y i) := by
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hn
  obtain ⟨x, hx⟩ := (l 0).isIrreducible'.nonempty
  obtain ⟨i, y, rfl⟩ := hcov x
  have hmem : ∀ k, f i y ∈ (l k : Set X) := fun k => (l.monotone (Fin.zero_le k)) hx
  let g : Fin (l.length + 1) → TopologicalSpace.IrreducibleCloseds (Y i) := fun k =>
    ⟨f i ⁻¹' l k, ⟨⟨y, hmem k⟩, (l k).isIrreducible'.2.preimage (hf i)⟩,
      (l k).isClosed'.preimage (hf i).continuous⟩
  refine ⟨i, Order.le_krullDim_iff.mpr ⟨{ length := l.length, toFun := g, step := fun k => ?_ }, hl⟩⟩
  have hlt : l k.castSucc < l k.succ := l.step k
  have hsub : (l k.castSucc : Set X) ⊆ l k.succ := SetLike.coe_subset_coe.mpr hlt.le
  have hle : g k.castSucc ≤ g k.succ := by
    rw [← SetLike.coe_subset_coe]
    exact fun z hz => hsub hz
  refine lt_of_le_not_ge hle (fun h => hlt.not_ge ?_)
  rw [← SetLike.coe_subset_coe]
  intro z hz
  have h1 := subset_closure_inter_of_isPreirreducible_of_isOpen (l k.succ).isIrreducible'.2
    (hf i).isOpen_range ⟨f i y, hmem k.succ, y, rfl⟩ hz
  refine closure_minimal ?_ (l k.castSucc).isClosed' h1
  rintro _ ⟨hw, w, rfl⟩
  exact (SetLike.coe_subset_coe.mpr h) (show w ∈ (g k.succ : Set (Y i)) from hw)

open CategoryTheory AlgebraicGeometry Limits

/-- **Glue (proved).** The scheme version of `exists_le_dim_of_cover` for an open cover. -/
theorem Scheme.exists_le_dim_of_openCover {X : Scheme} (𝒰 : X.OpenCover) (n : ℕ)
    (hn : (n : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ i, (n : WithBot ℕ∞) ≤ topologicalKrullDim (𝒰.X i) :=
  exists_le_dim_of_cover (fun i => ⇑(𝒰.f i)) (fun i => (𝒰.f i).isOpenEmbedding)
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩) n hn

/-- An open immersion does not increase dimension. -/
theorem dim_le_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y :=
  f.isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- `dim Spec R = dim R`. -/
theorem dim_Spec (R : CommRingCat) : topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R

/-- Isomorphic schemes have equal dimension. -/
theorem dim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

/-- `Spec R ×_{Spec K} Spec S = Spec (R ⊗_K S)` has dimension `dim (R ⊗_K S)`. -/
theorem dim_pullback_Spec (K : Type) [Field K] (R S : CommRingCat.{0})
    (φ : CommRingCat.of K ⟶ R) (ψ : CommRingCat.of K ⟶ S) :
    letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra
    topologicalKrullDim (pullback (C := Scheme) (Spec.map φ) (Spec.map ψ)) =
      ringKrullDim (TensorProduct K R S) := by
  let _ := φ.hom.toAlgebra; let _ := ψ.hom.toAlgebra
  exact (dim_eq_of_iso (pullbackSpecIso K R S)).trans (dim_Spec _)
/-- Order lemma in `WithBot ℕ∞`: `c ≤ d` if every natural number below `c` is below `d`. -/
theorem wb_le_of_forall_nat {c d : WithBot ℕ∞}
    (h : ∀ n : ℕ, (n : WithBot ℕ∞) ≤ c → (n : WithBot ℕ∞) ≤ d) : c ≤ d := by
  induction c using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe x =>
    induction x using ENat.recTopCoe with
    | top =>
      have : d = ⊤ := ENat.WithBot.eq_top_iff_forall_ge.mpr fun m => h m (by
        rw [← ENat.WithBot.coe_eq_natCast]; exact WithBot.coe_le_coe.mpr le_top)
      rw [this]; exact le_top
    | coe k => exact h k le_rfl

/-- Order lemma in `WithBot ℕ∞`: `a + b ≤ c` if `n + m ≤ c` whenever `n ≤ a`, `m ≤ b`. -/
theorem wb_add_le_of_forall {a b c : WithBot ℕ∞}
    (h : ∀ n m : ℕ, (n : WithBot ℕ∞) ≤ a → (m : WithBot ℕ∞) ≤ b →
      ((n + m : ℕ) : WithBot ℕ∞) ≤ c) : a + b ≤ c := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe x =>
  induction b using WithBot.recBotCoe with
  | bot => simp
  | coe y =>
  refine wb_le_of_forall_nat fun k hk => ?_
  rw [← WithBot.coe_add, ← ENat.WithBot.coe_eq_natCast, WithBot.coe_le_coe] at hk
  by_cases hkx : (k : ℕ∞) ≤ x
  · have := h k 0 (by rw [← ENat.WithBot.coe_eq_natCast]; exact WithBot.coe_le_coe.mpr hkx)
      (by rw [← ENat.WithBot.coe_eq_natCast]; exact WithBot.coe_le_coe.mpr (by simp))
    simpa using this
  · push Not at hkx
    obtain ⟨x0, rfl⟩ : ∃ x0 : ℕ, (x0 : ℕ∞) = x := ⟨x.toNat, ENat.natCast_toNat (ne_top_of_lt hkx)⟩
    have hx0 : x0 < k := by exact_mod_cast hkx
    have hm : ((k - x0 : ℕ) : ℕ∞) ≤ y := by
      rw [ENat.natCast_sub]
      exact tsub_le_iff_left.mpr hk
    have := h x0 (k - x0) le_rfl
      (by rw [← ENat.WithBot.coe_eq_natCast]; exact WithBot.coe_le_coe.mpr hm)
    rwa [Nat.add_sub_cancel' hx0.le] at this

/-- **Glue, proved below (`dimTensorFG`, §5): the dimension of a tensor product of finitely
generated algebras over a field.** For finitely generated algebras `R`, `S` over a field `K`,
`dim (R ⊗_K S) = dim R + dim S` (Krull dimensions in `WithBot ℕ∞`; both sides are `⊥` when
`R = 0` or `S = 0`). Source: Stacks Project, Algebra, Lemma 10.116.? (section "Dimension of
finite type algebras over fields", reprise; tag UNVERIFIED); classical via Noether
normalization: `R ⊗ S` is finite over `K[x₁..x_a, y₁..y_b]` (`a = dim R`, `b = dim S`),
injectively. STANDARD. Proved in §5 from Mathlib's Noether normalization
(`exists_integral_inj_algHom_of_fg`), `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`
and going up; the invariance of Krull dimension under integral injective extensions is proved
there (`ringKrullDim_eq_of_integral_injective`). -/
def DimTensorFG : Prop :=
  ∀ (K : Type) [Field K] (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S],
    Algebra.FiniteType K R → Algebra.FiniteType K S →
    ringKrullDim (TensorProduct K R S) = ringKrullDim R + ringKrullDim S

/-- **Glue (proved).** `DimProductOverField` from `DimTensorFG`: cover `X` and `Y` by affine
opens `Spec R_i`, `Spec S_j` (Mathlib's `affineOpenCover`); `X ×_K Y` is covered by the
`Spec R_i ×_K Spec S_j = Spec (R_i ⊗_K S_j)` (`Scheme.Pullback.openCoverOfLeftRight`,
`pullbackSpecIso`); each `R_i` is of finite type over `K` because `Spec R_i → Spec K` is locally
of finite type; dimensions of covers are suprema (`Scheme.exists_le_dim_of_openCover`). The
quasi-compactness hypotheses are not used. -/
theorem dimProductOverField_of_dimTensorFG (hT : DimTensorFG) : DimProductOverField := by
  intro K _ X Y f g hf _ hg _
  let 𝒱X := X.affineOpenCover
  let 𝒱Y := Y.affineOpenCover
  let 𝒲 := Scheme.Pullback.openCoverOfLeftRight 𝒱X.openCover 𝒱Y.openCover f g
  have key : ∀ (i : 𝒱X.I₀) (j : 𝒱Y.I₀),
      topologicalKrullDim (pullback (C := Scheme) (𝒱X.f i ≫ f) (𝒱Y.f j ≫ g)) =
      ringKrullDim (𝒱X.X i) + ringKrullDim (𝒱Y.X j) := by
    intro i j
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (𝒱X.f i ≫ f)
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (𝒱Y.f j ≫ g)
    have hφ' : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    have hψ' : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hφ' hψ'
    refine (dim_eq_of_iso (pullback.congrHom hφ.symm hψ.symm)).trans ?_
    refine (dim_pullback_Spec K _ _ φ ψ).trans ?_
    let _ := φ.hom.toAlgebra; let _ := ψ.hom.toAlgebra
    exact hT K _ _ hφ' hψ'
  apply le_antisymm
  · refine wb_le_of_forall_nat fun n hn => ?_
    obtain ⟨⟨i, j⟩, hij⟩ := Scheme.exists_le_dim_of_openCover 𝒲 n hn
    refine hij.trans ?_
    change topologicalKrullDim (pullback (C := Scheme) (𝒱X.f i ≫ f) (𝒱Y.f j ≫ g)) ≤ _
    refine (key i j).trans_le ?_
    have : IsOpenImmersion (𝒱X.f i) := 𝒱X.map_prop i
    have : IsOpenImmersion (𝒱Y.f j) := 𝒱Y.map_prop j
    exact add_le_add ((dim_Spec _).symm.trans_le (dim_le_of_isOpenImmersion (𝒱X.f i)))
      ((dim_Spec _).symm.trans_le (dim_le_of_isOpenImmersion (𝒱Y.f j)))
  · refine wb_add_le_of_forall fun n m hn hm => ?_
    obtain ⟨i, hi⟩ := Scheme.exists_le_dim_of_openCover 𝒱X.openCover n hn
    obtain ⟨j, hj⟩ := Scheme.exists_le_dim_of_openCover 𝒱Y.openCover m hm
    have : IsOpenImmersion (𝒲.f (i, j)) := 𝒲.map_prop (i, j)
    refine le_trans ?_ (dim_le_of_isOpenImmersion (𝒲.f (i, j)))
    change _ ≤ topologicalKrullDim (pullback (C := Scheme) (𝒱X.f i ≫ f) (𝒱Y.f j ≫ g))
    refine le_trans ?_ (key i j).ge
    rw [Nat.cast_add]
    exact add_le_add (hi.trans_eq (dim_Spec _)) (hj.trans_eq (dim_Spec _))

/-- **G17, `ProductExists`, proved from the ring-level textbook leaf `DimTensorFG`.** -/
theorem productExists_of_dimTensorFG (hT : DimTensorFG) : G0Split.ProductExists :=
  productExists_of_dimProduct (dimProductOverField_of_dimTensorFG hT)

end G0Product

/-! ## §5. `DimTensorFG` proved from Mathlib; `ProductExists` unconditionally -/

namespace G0Product

open TensorProduct

/-- **Glue (proved, commutative algebra).** Krull dimension is invariant under an injective
integral ring map `A → R`: `≤` by incomparability (`Ideal.IsIntegral.under_lt_under`), `≥` by
lying over and going up (`Ideal.exists_ideal_over_prime_of_isIntegral`,
`Ideal.exists_ltSeries_of_hasGoingUp`). -/
theorem ringKrullDim_eq_of_integral_injective {A R : Type*} [CommRing A] [CommRing R]
    (f : A →+* R) (hinj : Function.Injective f) (hint : f.IsIntegral) :
    ringKrullDim R = ringKrullDim A := by
  let _ := f.toAlgebra
  have : Algebra.IsIntegral A R := ⟨hint⟩
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A R)) ?_
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under (R := A) (I := p.asIdeal) (J := q.asIdeal) hpq
  · refine wb_le_of_forall_nat fun n hn => ?_
    obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hn
    obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (S := R) l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A R x = 0 := hx
        rw [show x = 0 from hinj (show f x = f 0 by rw [map_zero]; exact this)]
        exact zero_mem _)
    have : P.LiesOver l.head.asIdeal := ⟨hPo.symm⟩
    obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    exact Order.le_krullDim_iff.mpr ⟨L, hL.trans hl⟩

/-- **Glue (proved).** The tensor product `g ⊗ h` of integral algebra maps is integral. -/
theorem tensorMap_isIntegral {K A B R S : Type*} [CommRing K] [CommRing A] [CommRing B]
    [CommRing R] [CommRing S] [Algebra K A] [Algebra K B] [Algebra K R] [Algebra K S]
    (g : A →ₐ[K] R) (h : B →ₐ[K] S) (hg : g.IsIntegral) (hh : h.IsIntegral) :
    (Algebra.TensorProduct.map g h).toRingHom.IsIntegral := by
  set F := (Algebra.TensorProduct.map g h).toRingHom
  have hL : ∀ r : R, F.IsIntegralElem (r ⊗ₜ[K] (1 : S)) := by
    intro r
    have e : (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[K] S).comp g.toRingHom =
        F.comp Algebra.TensorProduct.includeLeftRingHom := by
      ext a; simp [F]
    have := (hg r).map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[K] S)
    rw [e] at this
    exact this.of_comp
  have hR : ∀ s : S, F.IsIntegralElem ((1 : R) ⊗ₜ[K] s) := by
    intro s
    have e : (Algebra.TensorProduct.includeRight : S →ₐ[K] R ⊗[K] S).toRingHom.comp
        h.toRingHom = F.comp (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom := by
      ext b; simp [F]
    have := (hh s).map (Algebra.TensorProduct.includeRight : S →ₐ[K] R ⊗[K] S).toRingHom
    rw [e] at this
    exact this.of_comp
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r s =>
    have : r ⊗ₜ[K] s = (r ⊗ₜ[K] (1:S)) * ((1:R) ⊗ₜ[K] s) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [this]; exact RingHom.IsIntegralElem.mul F (hL r) (hR s)
  | add x y hx hy => exact RingHom.IsIntegralElem.add F hx hy

/-- `dim K[X₀..X_{a-1}] = a` over a field (Mathlib). -/
theorem dim_mvPolynomial_fin (K : Type*) [Field K] (a : ℕ) :
    ringKrullDim (MvPolynomial (Fin a) K) = a := by
  simp [ringKrullDim_eq_zero_of_field]

/-- **`DimTensorFG`, proved.** Noether normalization (Mathlib's `exists_integral_inj_algHom_of_fg`)
gives injective integral `K[X₀..X_{a-1}] → R`, `K[Y₀..Y_{b-1}] → S`; their tensor product
`K[X] ⊗ K[Y] → R ⊗ S` is injective (flatness over a field) and integral, so
`dim (R ⊗ S) = dim (K[X] ⊗ K[Y]) = dim K[X][Y] = a + b = dim R + dim S`. The cases `R = 0`,
`S = 0` give `⊥ = ⊥`. -/
theorem dimTensorFG : DimTensorFG := by
  intro K _ R S _ _ _ _ hR hS
  by_cases hR0 : Subsingleton R
  · have : Subsingleton (R ⊗[K] S) := subsingleton_of_zero_eq_one (by
      rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : R) 0, zero_tmul])
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton, WithBot.bot_add]
  by_cases hS0 : Subsingleton S
  · have : Subsingleton (R ⊗[K] S) := subsingleton_of_zero_eq_one (by
      rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : S) 0, tmul_zero])
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton (R := S),
      WithBot.add_bot]
  rw [not_subsingleton_iff_nontrivial] at hR0 hS0
  obtain ⟨a, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K R
  obtain ⟨b, h, hhinj, hhint⟩ := exists_integral_inj_algHom_of_fg K S
  have dR : ringKrullDim R = a :=
    (ringKrullDim_eq_of_integral_injective g.toRingHom hginj hgint).trans (dim_mvPolynomial_fin K a)
  have dS : ringKrullDim S = b :=
    (ringKrullDim_eq_of_integral_injective h.toRingHom hhinj hhint).trans (dim_mvPolynomial_fin K b)
  have hFinj : Function.Injective (Algebra.TensorProduct.map g h) :=
    TensorProduct.map_injective_of_flat_flat g.toLinearMap h.toLinearMap hginj hhinj
  have dT : ringKrullDim (R ⊗[K] S) =
      ringKrullDim (MvPolynomial (Fin a) K ⊗[K] MvPolynomial (Fin b) K) :=
    ringKrullDim_eq_of_integral_injective _ hFinj (tensorMap_isIntegral g h hgint hhint)
  have dP : ringKrullDim (MvPolynomial (Fin a) K ⊗[K] MvPolynomial (Fin b) K) = a + b := by
    rw [ringKrullDim_eq_of_ringEquiv
      (MvPolynomial.algebraTensorAlgEquiv (σ := Fin b) K (MvPolynomial (Fin a) K)).toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, dim_mvPolynomial_fin]
    simp
  rw [dT, dP, dR, dS]
/-- **G17, `ProductExists` (`G0Split.ProductExists`, verbatim statement), proved with no
hypotheses**, from Mathlib only. -/
theorem productExists : G0Split.ProductExists :=
  productExists_of_dimTensorFG dimTensorFG

end G0Product

#print axioms G0Product.productExists

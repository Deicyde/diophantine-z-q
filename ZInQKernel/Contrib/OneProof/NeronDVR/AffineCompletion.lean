import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.QuasiAffine
import ZInQKernel.Contrib.OneProof.NeronDVR.StableOpen
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing

/-!
# Affine neighborhoods for stable-open descent

An affine open of a normal, locally Noetherian scheme which contains all
codimension-one points outside the generic fibre is recovered by completing
its generic fibre. The extension of morphisms to affine targets across
codimension at least two proves this without constructing the boundary divisor.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace NeronDVR

noncomputable section

universe u

/-- Completion of the generic part of an affine open adds no points when the
affine open contains the codimension-at-most-one points off the generic part. -/
theorem openCompletion_le_affine_of_codimOne
    {X X₀ : Scheme.{u}} [IsLocallyNoetherian X] [X.IsSeparated]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (i : X₀ ⟶ X) [IsOpenImmersion i] [IsDominant i]
    (U : X.Opens) (hU : IsAffineOpen U)
    (hcodim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 →
      x ∈ U ∨ x ∈ Set.range i) :
    openCompletion i (i ⁻¹ᵁ U) ≤ U := by
  let W := openCompletion i (i ⁻¹ᵁ U)
  let V := W.ι ⁻¹ᵁ U
  have hWU : ∀ x : X₀, i x ∈ W → i x ∈ U := by
    intro x hx
    have h := preimage_openCompletion i (i ⁻¹ᵁ U)
    change x ∈ i ⁻¹ᵁ W at hx
    rw [h] at hx
    exact hx
  have hWV : ∀ x : W.toScheme, ringKrullDim (W.toScheme.presheaf.stalk x) ≤ 1 → x ∈ V := by
    intro x hx
    have he := (W.stalkIso x).commRingCatIsoToRingEquiv.ringKrullDim
    have hx' : ringKrullDim (X.presheaf.stalk x.1) ≤ 1 := he ▸ hx
    rcases hcodim x.1 hx' with hmem | ⟨y, hy⟩
    · exact hmem
    · change x.1 ∈ U
      exact hy ▸ hWU y (hy ▸ x.2)
  let e (x : W.toScheme) := (W.stalkIso x).commRingCatIsoToRingEquiv
  have hW (x : W.toScheme) : IsDomain (W.toScheme.presheaf.stalk x) ∧
      IsIntegrallyClosed (W.toScheme.presheaf.stalk x) := by
    have : IsDomain (X.presheaf.stalk x.1) := (hX x.1).1
    have : IsIntegrallyClosed (X.presheaf.stalk x.1) := (hX x.1).2
    exact ⟨(e x).toMulEquiv.isDomain_iff.mpr ‹_›, IsIntegrallyClosed.of_equiv (e x).symm⟩
  have : IsAffine U := hU
  let g := W.ι.resLE U V le_rfl
  obtain ⟨f, hf, -⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.existsUnique_extension_to_affine_of_isIntegrallyClosed_stalk
      hW V hWV g
  have hV : IsDominant V.ι := by
    rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
    have hd : Dense (W.ι ⁻¹' Set.range i) := by
      rw [dense_iff_closure_eq,
        ← W.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage W.ι.continuous,
        i.denseRange.closure_range, Set.preimage_univ]
    refine hd.mono ?_
    rintro x ⟨y, hy⟩
    change i y = x.1 at hy
    change x.1 ∈ U
    exact hy ▸ hWU y (hy ▸ x.2)
  have : ∀ x : W.toScheme, _root_.IsReduced (W.toScheme.presheaf.stalk x) := fun x =>
    let : IsDomain (W.toScheme.presheaf.stalk x) := (hW x).1
    inferInstance
  have : IsReduced W.toScheme := isReduced_of_isReduced_stalk _
  have hfac : f ≫ U.ι = W.ι := by
    apply ext_of_isDominant V.ι
    rw [← Category.assoc, hf, Scheme.Hom.resLE_comp_ι]
  intro x hx
  have h : (f ⟨x, hx⟩).1 = x :=
    congrArg (fun k : W.toScheme ⟶ X => k ⟨x, hx⟩) hfac
  exact h ▸ (f ⟨x, hx⟩).2


/-- A point of codimension at most one outside the generic fibre of a flat
scheme over a DVR is a generic point of its fibre. -/
theorem fibreGeneric_of_codimOne
    {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    (x : X) (hx : f x ≠ (⊥ : PrimeSpectrum R)) (hcodim : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    ∀ y : X, y ⤳ x → f y = f x → y = x := by
  intro y hy hfy
  by_contra hne
  have hbot : (⊥ : PrimeSpectrum R) ⤳ f y :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨z, hz, hfz⟩ := Flat.generalizingMap f hbot
  have hyz : y < z := by
    refine lt_iff_le_not_ge.mpr ⟨hz, fun h => ?_⟩
    exact hx (hfy.symm.trans ((congrArg f ((show y ⤳ z from h).antisymm hz).eq).trans hfz))
  have hxy : x < y := by
    refine lt_iff_le_not_ge.mpr ⟨hy, fun h => ?_⟩
    exact hne (hy.antisymm (show x ⤳ y from h)).eq
  have hcx : Order.coheight x ≤ (1 : ENat) := by
    rw [ringKrullDim_stalk_eq_coheight] at hcodim
    exact WithBot.coe_le_coe.mp hcodim
  have hcy := (Order.coheight_le_coe_iff (x := x) (n := 1)).mp hcx y hxy
  have hcz := (Order.coheight_le_coe_iff (x := y) (n := 0)).mp (Order.le_of_lt_succ hcy)
  exact (not_lt_zero) (hcz z hyz)

/-- A smooth separated scheme of finite type over a DVR has an affine open
containing the generic points of every fibre and equal to the completion of
its own generic part. -/
theorem exists_affine_open_eq_openCompletion
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X₀ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    [IsSeparated f] [QuasiCompact f] (i : X₀ ⟶ X) [IsOpenImmersion i] [IsDominant i]
    (hi : Set.range i = f ⁻¹' {(⊥ : PrimeSpectrum R)}) :
    ∃ U : X.Opens, IsAffineOpen U ∧ openCompletion i (i ⁻¹ᵁ U) = U ∧
      ∀ x : X, (∀ y : X, y ⤳ x → f y = f x → y = x) → x ∈ U := by
  obtain ⟨U, hU, hgen⟩ :=
    ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let hnormal := ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R f
  refine ⟨U, hU, le_antisymm (openCompletion_le_affine_of_codimOne hnormal i U hU ?_)
    ((le_openCompletion_iff i _ _).mpr le_rfl), hgen⟩
  intro x hx
  by_cases hg : f x = (⊥ : PrimeSpectrum R)
  · right
    rw [hi]
    exact hg
  · exact Or.inl (hgen x (fibreGeneric_of_codimOne f x hg hx))


/-- For a Noetherian open subscheme, points in the closure of the image of a
closed subset are specializations of points of that closed subset. -/
theorem exists_specializes_of_mem_closure_image
    {X X₀ : Scheme.{u}} [NoetherianSpace X₀] (i : X₀ ⟶ X)
    {Z : Set X₀} (hZ : IsClosed Z) {x : X} (hx : x ∈ closure (i '' Z)) :
    ∃ y ∈ Z, i y ⤳ x := by
  classical
  let C : Closeds X₀ := ⟨Z, hZ⟩
  obtain ⟨s, hs, hc⟩ := NoetherianSpace.exists_finset_irreducible C
  have hZ' : Z = ⋃ k ∈ s, (k : Set X₀) := by
    change (C : Set X₀) = _
    rw [hc, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
    rfl
  rw [hZ', Set.image_iUnion₂, s.closure_biUnion] at hx
  obtain ⟨k, hk, hx⟩ := Set.mem_iUnion₂.mp hx
  let y := (hs ⟨k, hk⟩).genericPoint
  have hy : IsGenericPoint y (k : Set X₀) := (hs ⟨k, hk⟩).isGenericPoint_genericPoint k.2
  refine ⟨y, ?_, ?_⟩
  · rw [hZ']; exact Set.mem_iUnion₂.mpr ⟨k, hk, hy.mem⟩
  · rw [← hy.def, closure_image_closure i.continuous, Set.image_singleton] at hx
    exact specializes_iff_mem_closure.mpr hx

/-- An open containing the generic points of the generic fibre completes to an
open containing every point of codimension at most one off the generic fibre. -/
theorem mem_openCompletion_of_coheight_le_one
    {X X₀ : Scheme.{u}} [NoetherianSpace X₀] (i : X₀ ⟶ X) [IsOpenImmersion i]
    (V : X₀.Opens) (hV : ∀ y : X₀, IsMax y → y ∈ V)
    (x : X) (hx : x ∉ Set.range i) (hcodim : Order.coheight x ≤ 1) :
    x ∈ openCompletion i V := by
  change x ∉ closure (i '' (V : Set X₀)ᶜ)
  intro hc
  obtain ⟨y, hy, hyx⟩ := exists_specializes_of_mem_closure_image i V.isOpen.isClosed_compl hc
  have hxy : x < i y := by
    refine lt_iff_le_not_ge.mpr ⟨hyx, fun h => ?_⟩
    exact hx ⟨y, (hyx.antisymm (show x ⤳ i y from h)).eq⟩
  have hd : Order.coheight (i y) < (1 : ENat) :=
    (Order.coheight_le_coe_iff (x := x) (n := 1)).mp hcodim _ hxy
  rw [coheight_eq_of_isOpenImmersion i] at hd
  have hzero : Order.coheight y = 0 := le_antisymm (Order.le_of_lt_succ hd) bot_le
  exact hy (hV y (Order.coheight_eq_zero.mp hzero))


/-- A flat morphism to the spectrum of a domain has dense generic fibre. -/
theorem isDominant_of_generic_range
    {R : Type u} [CommRing R] [IsDomain R] {X X₀ : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] (i : X₀ ⟶ X)
    (hi : Set.range i = f ⁻¹' {(⊥ : PrimeSpectrum R)}) : IsDominant i := by
  refine ⟨fun x => ?_⟩
  have hbot : (⊥ : PrimeSpectrum R) ⤳ f x :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y, hyx, hfy⟩ := Flat.generalizingMap f hbot
  have hiy : y ∈ Set.range i := by rw [hi]; exact hfy
  exact closure_mono (Set.singleton_subset_iff.mpr hiy)
    (specializes_iff_mem_closure.mp hyx)

/-- Taking the generic completion of a generic-fibre open that contains its
generic points preserves the generic points of each fibre of a smooth DVR
scheme. -/
theorem fibreGeneric_mem_openCompletion
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X₀ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (i : X₀ ⟶ X) [IsOpenImmersion i] [NoetherianSpace X₀]
    (hi : Set.range i = f ⁻¹' {(⊥ : PrimeSpectrum R)})
    (V : X₀.Opens) (hV : ∀ y : X₀, IsMax y → y ∈ V)
    (x : X) (hx : ∀ y : X, y ⤳ x → f y = f x → y = x) :
    x ∈ openCompletion i V := by
  by_cases hxi : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hxi
    have hy : IsMax y := by
      intro z hz
      have hfe (a : X₀) : f (i a) = (⊥ : PrimeSpectrum R) := by
        have hm : i a ∈ Set.range i := Set.mem_range_self a
        rw [hi] at hm
        exact hm
      have he := hx (i z) ((show z ⤳ y from hz).map i.continuous) ((hfe z).trans (hfe y).symm)
      rw [i.isOpenEmbedding.injective he]
    change y ∈ i ⁻¹ᵁ openCompletion i V
    rw [preimage_openCompletion]
    exact hV y hy
  · have hfp : f x ≠ (⊥ : PrimeSpectrum R) := fun he => hxi (hi.symm ▸
      (show x ∈ f ⁻¹' {(⊥ : PrimeSpectrum R)} from he))
    have hm : (f x : PrimeSpectrum R).asIdeal ≠ ⊥ := fun he =>
      hfp (PrimeSpectrum.ext_iff.mpr he)
    have hmax : (f x : PrimeSpectrum R).asIdeal.IsMaximal :=
      Ideal.IsPrime.isMaximal_of_ne_bot (f x : PrimeSpectrum R).isPrime hm
    have hc : f x = IsLocalRing.closedPoint R := by
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
    obtain ⟨hdom, hdvr⟩ :=
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes
        R f x hc (fun y hy hyf => hx y hy (hyf.trans hc.symm))
    have hcd := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk x)
    rw [ringKrullDim_stalk_eq_coheight] at hcd
    exact mem_openCompletion_of_coheight_le_one i V hV x hxi
      (WithBot.coe_le_coe.mp hcd.le)

private theorem isMax_of_isMax_image
    {X Y : Scheme.{u}} (r : X ⟶ Y) [LocallyQuasiFinite r]
    {x : X} (hx : IsMax (r x)) : IsMax x := by
  intro y hy
  have hxy := (show y ⤳ x from hy).map r.continuous
  have he : r y = r x := (hxy.antisymm (hx hxy)).eq
  rw [(r.isDiscrete_preimage_singleton (r x)).eq_of_specializes hy he rfl]

private theorem isMax_image_of_isMax
    {X Y : Scheme.{u}} (r : X ⟶ Y) [Flat r] {x : X} (hx : IsMax x) :
    IsMax (r x) := by
  intro y hy
  obtain ⟨x', hx', rfl⟩ := Flat.generalizingMap r (show y ⤳ r x from hy)
  exact (hx hx').map r.continuous

/-- A compatible finite flat map on the generic fibre yields an invariant
quasi-affine open containing the generic points of every fibre. This is the
reduction in Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.5, case (b). -/
theorem exists_invariant_quasiAffine_open
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {S T A : Scheme.{u}} {p : Spec (CommRingCat.of R) ⟶ S} [UniversallyOpen p]
    {N : Over (Spec (CommRingCat.of R))} [Smooth N.hom] [QuasiCompact N.hom]
    [IsSeparated N.hom] (d : Over.DescentDatum p N) (j : T ⟶ S) [IsOpenImmersion j]
    (r : pullback (N.hom ≫ p) j ⟶ A) (hr : d.CompatibleOnOpen j r)
    [IsFinite r] [Flat r]
    (hi : Set.range (pullback.fst (N.hom ≫ p) j) = N.hom ⁻¹' {(⊥ : PrimeSpectrum R)}) :
    ∃ U : N.left.Opens, d.IsInvariant U ∧ U.toScheme.IsQuasiAffine ∧
      ∀ x : N.left, (∀ y : N.left, y ⤳ x → N.hom y = N.hom x → y = x) → x ∈ U := by
  let f := N.hom
  let i := pullback.fst (N.hom ≫ p) j
  have : IsDominant i := isDominant_of_generic_range N.hom i hi
  have : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  have : IsNoetherian N.left := {}
  have : NoetherianSpace ↥(pullback (N.hom ≫ p) j) := i.isOpenEmbedding.isInducing.noetherianSpace
  obtain ⟨Q, hQ, hcomp, hgen⟩ := exists_affine_open_eq_openCompletion f i hi
  let C : Set ↥(pullback (N.hom ≫ p) j) := (↑(i ⁻¹ᵁ Q) : Set ↥(pullback (N.hom ≫ p) j))ᶜ
  let V : A.Opens := ⟨(r '' C)ᶜ, (r.isClosedMap C (i ⁻¹ᵁ Q).isOpen.isClosed_compl).isOpen_compl⟩
  let U := openCompletion i (r ⁻¹ᵁ V)
  have hUQ : U ≤ Q := by
    rw [← hcomp]
    apply (le_openCompletion_iff i _ _).mpr
    rw [preimage_openCompletion]
    intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hV (x : ↥(pullback (N.hom ≫ p) j)) (hx : IsMax x) : x ∈ r ⁻¹ᵁ V := by
    rintro ⟨y, hy, hyx⟩
    have hmax : IsMax y := isMax_of_isMax_image r
      (hyx.symm ▸ isMax_image_of_isMax r hx : IsMax (r y))
    have hmax' : IsMax (i y) := by
      rw [← Order.coheight_eq_zero, coheight_eq_of_isOpenImmersion i]
      exact Order.coheight_eq_zero.mpr hmax
    exact hy (hgen (i y) (fun z hz _ => (hz.antisymm (hmax' hz)).eq))
  have : IsAffine Q := hQ
  have : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have hqa : U.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion (N.left.homOfLE hUQ)
  refine ⟨U, d.isInvariant_openCompletion j r hr V, hqa, ?_⟩
  exact fibreGeneric_mem_openCompletion f i hi _ hV


open ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing.L4DenseAssembly in
/-- A smooth separated scheme of finite type over a DVR has finitely many
generic points of fibres. -/
theorem finite_fibreGeneric
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    [IsSeparated f] [QuasiCompact f] :
    {x : X | ∀ y : X, y ⤳ x → f y = f x → y = x}.Finite := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  refine ((finite_setOf_fibreMax_closed f).union
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents)).subset ?_
  intro x hx
  by_cases hc : f x = IsLocalRing.closedPoint R
  · exact Or.inl ⟨hx, hc⟩
  · right
    let C : irreducibleComponents X := ⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩
    let y := genericPoints.ofComponent C
    have hy : y.1 ⤳ x := (genericPoints.isGenericPoint_ofComponent C).specializes
      mem_irreducibleComponent
    exact (eq_of_specializes_of_fibreMax_of_ne f hx hc y.1 hy) ▸ y.2

end

end NeronDVR

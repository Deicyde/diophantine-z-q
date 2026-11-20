import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.LocalRing.Etale
import ZInQKernel.Contrib.AbVarBC.Mul
import ZInQKernel.Contrib.CloudR2Poincare.L1.Translation
import ZInQKernel.Contrib.OneProof.NeronDVR.AffineCompletion
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.CanonicalSection
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.RelativeCartierPullback
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.Tensor
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorPower

/-!
# Ampleness from symmetric translates of a Cartier divisor

The last step of BLR §6.4, Proposition 2 turns the square isomorphisms into
sections whose affine nonvanishing opens cover the scheme.
-/

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open scoped AlgebraicGeometry.Scheme.Modules CategoryTheory.MonObj

namespace NeronDVR

open ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Smooth
  (exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing)

noncomputable section

variable {X : Scheme.{0}}

/-- The sum of the two translates of an effective Cartier divisor in the
theorem of the square, written as a product of its defining ideals. -/
def symmetricTranslate (D : X.IdealSheafData) (g : X ≅ X) : X.IdealSheafData :=
  D.comap g.hom * D.comap g.inv

private theorem symmetricTranslate_invertible (D : X.IdealSheafData) (hD : D.IsInvertible)
    (g : X ≅ X) : (symmetricTranslate D g).IsInvertible :=
  (hD.comap_of_flat g.hom).mul_effectiveCartier (hD.comap_of_flat g.inv)

/-- A symmetric translate is avoided exactly where both translates of the
original divisor are avoided. -/
theorem symmetricTranslate_compl (D : X.IdealSheafData) (g : X ≅ X) :
    (symmetricTranslate D g).support.compl =
      (g.hom ⁻¹ᵁ D.support.compl) ⊓ (g.inv ⁻¹ᵁ D.support.compl) := by
  ext x
  simp [symmetricTranslate]

private theorem symmetricTranslate_square_of_picard (D : X.IdealSheafData)
    (hD : D.IsInvertible) (g : X ≅ X)
    (hSquare : letI := hD.isInvertible_dual_toModules
      let L := Scheme.Pic.mk D.toModulesᵛ
      Scheme.Pic.map g.hom L * Scheme.Pic.map g.inv L = L ^ 2) :
    Nonempty ((symmetricTranslate D g).toModulesᵛ ≅ D.toModulesᵛ.tensorPow 2) := by
  let I := D.comap g.hom
  let J := D.comap g.inv
  let L := D.toModulesᵛ
  have hI : I.IsInvertible := hD.comap_of_flat g.hom
  have hJ : J.IsInvertible := hD.comap_of_flat g.inv
  have hIJ : (I * J).IsInvertible := hI.mul_effectiveCartier hJ
  have := hI.isInvertible_toModules
  have := hJ.isInvertible_toModules
  have := hIJ.isInvertible_toModules
  have : L.IsInvertible := hD.isInvertible_dual_toModules
  have hmap (a : X ⟶ X) [IsIso a] :
      letI := (hD.comap_of_flat a).isInvertible_dual_toModules
      Scheme.Pic.map a (Scheme.Pic.mk L) = Scheme.Pic.mk (D.comap a).toModulesᵛ := by
    have := (hD.comap_of_flat a).isInvertible_dual_toModules
    rw [Scheme.Pic.map_mk]
    exact (Scheme.Pic.mk_eq_mk_iff _ _).mpr
      (hD.nonempty_pullback_dual_toModules_iso a (hD.comap_of_flat a))
  have hpow : Scheme.Pic.mk (L.tensorPow 2) = (Scheme.Pic.mk L) ^ 2 := by
    rw [pow_two, ← Scheme.Pic.mk_tensorObj]
    exact (Scheme.Pic.mk_eq_mk_iff _ _).mpr ⟨Iso.refl L ⊗ᵢ ρ_ L⟩
  change Nonempty ((I * J).toModulesᵛ ≅ L.tensorPow 2)
  apply (Scheme.Pic.mk_eq_mk_iff _ _).mp
  rw [Scheme.Pic.mk_dual, Scheme.Pic.mk_toModules_mul hI hJ, mul_inv,
    ← Scheme.Pic.mk_dual, ← Scheme.Pic.mk_dual, ← hmap g.hom, ← hmap g.inv, hpow]
  exact hSquare

/-- Symmetric translation gives an affine nonvanishing neighborhood at each
point, using sections of a single power of the original line bundle. -/
theorem exists_affine_nonvanishing_of_symmetricTranslate_cover [X.IsSeparated]
    (D : X.IdealSheafData) (hD : D.IsInvertible) (hU : IsAffineOpen D.support.compl)
    {I : Type*} (g : I → (X ≅ X))
    (hSquare : letI := hD.isInvertible_dual_toModules
      let L := Scheme.Pic.mk D.toModulesᵛ
      ∀ i, Scheme.Pic.map (g i).hom L * Scheme.Pic.map (g i).inv L = L ^ 2)
    (hCover : ∀ x : X, ∃ i, x ∈ (symmetricTranslate D (g i)).support.compl) :
    letI := hD.isInvertible_dual_toModules
    ∀ x : X, ∃ s : 𝟙_ X.Modules ⟶ D.toModulesᵛ.tensorPow 2,
      x ∈ s.zeroLocus.support.compl ∧ IsAffineOpen s.zeroLocus.support.compl := by
  let := hD.isInvertible_dual_toModules
  intro x
  obtain ⟨i, hi⟩ := hCover x
  obtain ⟨square⟩ := symmetricTranslate_square_of_picard D hD (g i) (hSquare i)
  obtain ⟨s, hs⟩ := (symmetricTranslate_invertible D hD (g i)).exists_zeroLocus_eq_of_iso
    square
  refine ⟨s, ?_, ?_⟩
  · rw [hs]
    exact hi
  · rw [hs, symmetricTranslate_compl]
    exact (hU.preimage (g i).hom).inf (hU.preimage (g i).inv)

/-- Over a strictly henselian DVR, every open of a smooth scheme which meets the
special fibre contains the closed point of a section. This is the section-lifting
step in BLR §6.4, Proposition 2. -/
theorem exists_section_in_open_of_strictHenselianDVR
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] (U : X.Opens)
    {x : X} (hx : f x = IsLocalRing.closedPoint R) (hxU : x ∈ U) :
    ∃ a : Spec (CommRingCat.of R) ⟶ X, a ≫ f = 𝟙 _ ∧ a (IsLocalRing.closedPoint R) ∈ U := by
  obtain ⟨R', _, _, _, _, _, _, _, _, _, a, _, ha, haU⟩ :=
    exists_finite_etale_dvr_specMap_comp_eq_apply_closedPoint_mem_of_henselianLocalRing f U x hx hxU
  have hres : Algebra.adjoin (IsLocalRing.ResidueField R)
      {IsLocalRing.residue R' (0 : R')} = ⊤ := by
    apply eq_top_iff.mpr
    intro y _
    obtain ⟨b, rfl⟩ := IsSepClosed.algebraMap_surjective
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R') y
    exact Subalgebra.algebraMap_mem _ b
  have hadj : Algebra.adjoin R ({0} : Set R') = ⊤ :=
    (IsLocalRing.adjoin_residue_eq_top_iff_adjoin_eq_top (0 : R')).mp hres
  have hb : Algebra.adjoin R ({0} : Set R') ≤ ⊥ := Algebra.adjoin_le (by simp)
  have hsurj : Function.Surjective (algebraMap R R') := by
    intro b
    have hh : b ∈ (⊤ : Subalgebra R R') := by simp
    rw [← hadj] at hh
    exact Algebra.mem_bot.mp (hb hh)
  let s := Spec.map (CommRingCat.ofHom (algebraMap R R'))
  have : IsIso s := isIso_SpecMap_iff.mpr ⟨FaithfulSMul.algebraMap_injective _ _, hsurj⟩
  have hsClosed : s (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (algebraMap R R')
  have hsInv : inv s (IsLocalRing.closedPoint R) = IsLocalRing.closedPoint R' := by
    calc
      _ = inv s (s (IsLocalRing.closedPoint R')) := congrArg (fun z : Spec (CommRingCat.of R) =>
        inv s z) hsClosed.symm
      _ = _ := congrArg (fun f : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R') =>
        f (IsLocalRing.closedPoint R')) (IsIso.hom_inv_id s)
  refine ⟨inv s ≫ a, ?_, ?_⟩
  · rw [Category.assoc, ha]
    exact IsIso.inv_hom_id s
  · change a (inv s (IsLocalRing.closedPoint R)) ∈ U
    rw [hsInv]
    exact haU

set_option backward.isDefEq.respectTransparency false in
/-- A nonempty open of the integral generic fibre contains the generic point
of a section over a strictly henselian DVR. The point used to lift the section
is generic in a component of the special fibre. -/
theorem exists_section_in_generic_open_of_strictHenselianDVR
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    {X₀ : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (i : X₀ ⟶ X) [IsOpenImmersion i] [NoetherianSpace X₀] [IrreducibleSpace X₀]
    (hi : Set.range i = f ⁻¹' {(⊥ : PrimeSpectrum R)})
    (V : X₀.Opens) (hV : (V : Set X₀).Nonempty) (x : X)
    (hs : f x = IsLocalRing.closedPoint R)
    (hx : ∀ y, y ⤳ x → f y = f x → y = x) :
    ∃ (a : Spec (CommRingCat.of R) ⟶ X), a ≫ f = 𝟙 _ ∧
      ∃ y ∈ V, i y = a (⊥ : PrimeSpectrum R) := by
  let W := openCompletion i V
  have hre : ∀ y : X₀, IsMax y → y ∈ V := by
    intro y hy
    have hgen : genericPoint X₀ ∈ V :=
      (genericPoint_spec X₀).mem_open_set_iff V.isOpen |>.mpr (by simpa using hV)
    have h₁ : genericPoint X₀ ⤳ y := (genericPoint_spec X₀).specializes trivial
    have h₂ : y ⤳ genericPoint X₀ := hy h₁
    rwa [(h₂.antisymm h₁).eq]
  have hxW : x ∈ W := fibreGeneric_mem_openCompletion f i hi V hre x hx
  obtain ⟨a, ha, haW⟩ := exists_section_in_open_of_strictHenselianDVR f W hs hxW
  let generic : Spec (CommRingCat.of R) := (⊥ : PrimeSpectrum R)
  have hηc : generic ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  have hηW : a generic ∈ W := (hηc.map a.continuous).mem_open W.isOpen haW
  have hη : f (a generic) = generic :=
    congrArg (fun g : Spec (CommRingCat.of R) ⟶ _ => g generic) ha
  have hrange : a generic ∈ Set.range i := hi.symm ▸ hη
  obtain ⟨y, hy⟩ := hrange
  refine ⟨a, ha, y, ?_, hy⟩
  have hyW : y ∈ i ⁻¹ᵁ W := by
    change i y ∈ W
    rwa [hy]
  simpa [W] using hyW

open ZInQ.Contrib.CloudR2Poincare

private theorem translate_comp {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (a b : 𝟙_ (Over S) ⟶ G) :
    L1.translate G a ≫ L1.translate G b = L1.translate G (b * a) := by
  simp only [L1.translate, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]
  exact (mul_assoc _ _ _).symm

/-- Translation by a section of a group scheme, with inverse given by the
inverse section. -/
def leftTranslationIso {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (a : 𝟙_ (Over S) ⟶ G) : G ≅ G where
  hom := L1.translate G a
  inv := L1.translate G a⁻¹
  hom_inv_id := by rw [translate_comp, inv_mul_cancel, L1.translate_one]
  inv_hom_id := by rw [translate_comp, mul_inv_cancel, L1.translate_one]

/-- Along a finite morphism from an irreducible scheme, the entire inverse
image of some nonempty open lies in a prescribed nonempty open. This is used
to descend the translation conditions from the residue field of a point. -/
theorem exists_nonempty_open_preimage_le_of_finite
    {Y : Scheme.{0}} [IrreducibleSpace X] (f : X ⟶ Y) [IsFinite f]
    (U : X.Opens) (hne : (U : Set X).Nonempty) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ f ⁻¹ᵁ V ≤ U := by
  let closed : Set Y := f '' (U : Set X)ᶜ
  have hclosed : IsClosed closed := f.isClosedMap _ U.isOpen.isClosed_compl
  let V : Y.Opens := ⟨closedᶜ, hclosed.isOpen_compl⟩
  have hgen : genericPoint X ∈ U := by
    apply (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr
    simpa using hne
  refine ⟨V, ⟨f (genericPoint X), ?_⟩, ?_⟩
  · rintro ⟨z, hz, heq⟩
    obtain rfl : z = genericPoint X := by
      by_contra h
      exact (ZInQ.Contrib.AbVarBC.MulRigidity.ne_of_specializes_of_lqf f
        ((genericPoint_spec X).specializes trivial) (Ne.symm h)) heq.symm
    exact hz hgen
  · intro z hz
    by_contra hzu
    exact hz ⟨z, hzu, rfl⟩

section Orbit

variable {S : Scheme.{0}} {H G T : Over S} [GrpObj G] [GrpObj H]
  (i : H ⟶ G) (x : T ⟶ G)

/-- The orbit map of a point with respect to a subgroup of a group scheme. -/
def leftOrbit : H ⊗ T ⟶ G :=
  (fst H T ≫ i) * (snd H T ≫ x)

/-- The open selecting parameters whose action and inverse action both land
in a prescribed open descends to a nonempty open under a finite projection. -/
theorem exists_nonempty_open_of_finite_orbit_parameter [IrreducibleSpace (H ⊗ T).left]
    {Y : Scheme.{0}} (p : (H ⊗ T).left ⟶ Y) [IsFinite p] (U : G.left.Opens)
    (hU : ((leftOrbit i x).left ⁻¹ᵁ U : Set (H ⊗ T).left).Nonempty) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧
      ∀ y : (H ⊗ T).left, p y ∈ V →
        (leftOrbit i x).left y ∈ U ∧
          (leftOrbit i x).left (((GrpObj.inv : H ⟶ H) ⊗ₘ 𝟙 T).left y) ∈ U := by
  let w : (H ⊗ T).left ⟶ (H ⊗ T).left := ((GrpObj.inv : H ⟶ H) ⊗ₘ 𝟙 T).left
  have : IsIso w := inferInstanceAs
    (IsIso ((Over.forget S).map ((GrpObj.inv : H ⟶ H) ⊗ₘ 𝟙 T)))
  let W : (H ⊗ T).left.Opens := (leftOrbit i x).left ⁻¹ᵁ U
  have hW' : (w ⁻¹ᵁ W : Set (H ⊗ T).left).Nonempty :=
    hU.preimage w.surjective
  have hW : ((W ⊓ w ⁻¹ᵁ W : (H ⊗ T).left.Opens) : Set (H ⊗ T).left).Nonempty :=
    nonempty_preirreducible_inter W.isOpen (w ⁻¹ᵁ W).isOpen hU hW'
  obtain ⟨V, hV, hp⟩ := exists_nonempty_open_preimage_le_of_finite p (W ⊓ w ⁻¹ᵁ W) hW
  exact ⟨V, hV, fun y hy => hp hy⟩

omit [GrpObj H] in
private theorem orbit_section (a : 𝟙_ (Over S) ⟶ H) :
    lift (toUnit T ≫ a) (𝟙 T) ≫ leftOrbit i x = x ≫ L1.translate G (a ≫ i) := by
  simp [leftOrbit, L1.translate, MonObj.comp_mul, Category.assoc]

end Orbit

private def rightOrbitIso {S : Scheme.{0}} {G T : Over S} [GrpObj G]
    (x : T ⟶ G) : G ⊗ T ≅ G ⊗ T where
  hom := lift (fst G T * (snd G T ≫ x)) (snd G T)
  inv := lift (fst G T * ((snd G T ≫ x ≫ GrpObj.inv))) (snd G T)
  hom_inv_id := by
    have hCancel : (snd G T ≫ x) * (snd G T ≫ x ≫ GrpObj.inv) = 1 := by
      simpa only [Category.assoc, Hom.mul_def, Hom.one_def] using GrpObj.lift_comp_inv_right (snd G T ≫ x)
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.comp_mul, _root_.mul_assoc, hCancel]
  inv_hom_id := by
    have hCancel : (snd G T ≫ x ≫ GrpObj.inv) * (snd G T ≫ x) = 1 := by
      simpa only [Category.assoc, Hom.mul_def, Hom.one_def] using GrpObj.lift_comp_inv_left (snd G T ≫ x)
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.comp_mul, _root_.mul_assoc, hCancel]

private theorem whiskerRight_isOpenImmersion {S : Scheme.{0}} {H G T : Over S}
    (i : H ⟶ G) [IsOpenImmersion i.left] : IsOpenImmersion (i ▷ T).left := by
  have hg : IsPullback (snd G T).left (fst G T).left T.hom G.hom :=
    (IsPullback.of_hasPullback G.hom T.hom).flip
  have hh : IsPullback (snd H T).left (fst H T).left T.hom (i.left ≫ G.hom) := by
    rw [Over.w i]
    exact (IsPullback.of_hasPullback H.hom T.hom).flip
  have hh' : IsPullback ((i ▷ T).left ≫ (snd G T).left) (fst H T).left
      T.hom (i.left ≫ G.hom) := by
    simpa using hh
  have hi : IsPullback (i ▷ T).left (fst H T).left (fst G T).left i.left := by
    exact IsPullback.of_right hh' (by simp) hg
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hi.flip inferInstance

private theorem isFibreGeneric_of_fibreι_isMax {X Y : Scheme.{0}} (f : X ⟶ Y)
    (s : Y) {x : f.fiber s} (hx : IsMax x) :
    ∀ z, z ⤳ f.fiberι s x → f z = f (f.fiberι s x) → z = f.fiberι s x := by
  intro z hz hbase
  have hs : f (f.fiberι s x) = s := by
    have hh : f.fiberι s x ∈ Set.range (f.fiberι s) := ⟨_, rfl⟩
    rwa [f.range_fiberι] at hh
  have hz' : z ∈ Set.range (f.fiberι s) := by
    rw [f.range_fiberι, Set.mem_preimage, Set.mem_singleton_iff]
    exact hbase.trans hs
  obtain ⟨z, rfl⟩ := hz'
  have hzX : z ⤳ x := (f.fiberι s).isEmbedding.isInducing.specializes_iff.mp hz
  exact congrArg (fun z => f.fiberι s z) (hzX.antisymm (hx hzX)).eq

/-- A fibre-dense open meets the orbit of every field-valued point under a geometrically
integral open subgroup. -/
theorem leftOrbit_nonempty_of_contains_fibre_generics {S : Scheme.{0}} {H G : Over S}
    [GrpObj H] [GrpObj G] [GeometricallyIntegral H.hom]
    (i : H ⟶ G) [IsOpenImmersion i.left] (U : G.left.Opens)
    (hU : ∀ y : G.left, (∀ z, z ⤳ y → G.hom z = G.hom y → z = y) → y ∈ U)
    (F : Type) [Field F] (t : Spec (CommRingCat.of F) ⟶ S)
    (x : Over.mk t ⟶ G) : ((leftOrbit i x).left ⁻¹ᵁ U : Set (H ⊗ Over.mk t).left).Nonempty := by
  let T := Over.mk t
  change ((leftOrbit i x).left ⁻¹ᵁ U : Set (H ⊗ T).left).Nonempty
  let s := t (IsLocalRing.closedPoint F)
  let q := Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo t))
  have hq : q ≫ S.fromSpecResidueField s = T.hom :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField F S t
  have hqFlat : Flat q := by
    rw [Flat.SpecMap_iff]
    let : Algebra (S.residueField s) F := (Scheme.descResidueField (Scheme.stalkClosedPointTo t)).hom.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  let e := pullbackLeftPullbackSndIso G.hom (S.fromSpecResidueField s) q
  let k : (G ⊗ T).left ≅ pullback (G.hom.fiberToSpecResidueField s) q :=
    (pullback.congrHom rfl hq.symm) ≪≫ e.symm
  let p : (H ⊗ T).left ⟶ G.hom.fiber s :=
    (i ▷ T).left ≫ (rightOrbitIso x).hom.left ≫ k.hom ≫
      pullback.fst (G.hom.fiberToSpecResidueField s) q
  have : IsOpenImmersion (i ▷ T).left := whiskerRight_isOpenImmersion i
  have : IsIso (rightOrbitIso x).hom.left := inferInstanceAs
    (IsIso ((Over.forget S).mapIso (rightOrbitIso x)).hom)
  have : Flat p := by
    dsimp only [p]
    infer_instance
  have hp : p ≫ G.hom.fiberι s = (leftOrbit i x).left := by
    have hk : k.hom ≫ pullback.fst _ _ ≫ G.hom.fiberι s = (fst G T).left := by
      change ((pullback.congrHom rfl hq.symm).hom ≫ e.inv) ≫
        pullback.fst (pullback.snd G.hom (S.fromSpecResidueField s)) q ≫
          pullback.fst G.hom (S.fromSpecResidueField s) = _
      rw [Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
      simp [pullback.congrHom]
    have hi : (i ▷ T) ≫ (rightOrbitIso x).hom ≫ fst G T = leftOrbit i x := by
      change (i ▷ T) ≫ lift (fst G T * (snd G T ≫ x)) (snd G T) ≫ fst G T = _
      rw [lift_fst, MonObj.comp_mul, ← Category.assoc, whiskerRight_fst, whiskerRight_snd]
      rfl
    simpa [p, hk] using congrArg (fun f : H ⊗ T ⟶ G => f.left) hi
  have : IsIntegral (H ⊗ T).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback H.hom t)
  let y := genericPoint (H ⊗ T).left
  have hy : IsMax (p y) := by
    intro z hz
    obtain ⟨y', hy', rfl⟩ := Flat.generalizingMap p (show z ⤳ p y from hz)
    exact ((genericPoint_spec _).specializes trivial : y ⤳ y').map p.continuous
  refine ⟨y, ?_⟩
  change (leftOrbit i x).left y ∈ U
  rw [← hp, Scheme.Hom.comp_apply]
  exact hU _ (isFibreGeneric_of_fibreι_isMax G.hom s hy)


set_option backward.isDefEq.respectTransparency false in
/-- Simultaneous inverse-translation conditions give a global translating
section when sections meet every nonempty open of the parameter fibre. -/
theorem exists_symmetricTranslate_of_fibre_parameter
    {S Y : Scheme.{0}} {H G T : Over S} [GrpObj H] [GrpObj G]
    (i : H ⟶ G) [IsMonHom i] (x : T ⟶ G) (z : T.left)
    (s : S) (hz : T.hom z = s) (p : (H ⊗ T).left ⟶ Y)
    [IsFinite p] [IrreducibleSpace (H ⊗ T).left]
    (j : Y ⟶ H.left) (hj : Function.Injective j) (hp : p ≫ j = (fst H T).left)
    (U : G.left.Opens) (hU : ((leftOrbit i x).left ⁻¹ᵁ U : Set (H ⊗ T).left).Nonempty)
    (hsection : ∀ V : Y.Opens, (V : Set Y).Nonempty →
      ∃ (a : 𝟙_ (Over S) ⟶ H) (y : Y), y ∈ V ∧ j y = a.left s) :
    ∃ a : 𝟙_ (Over S) ⟶ H,
      (leftTranslationIso G (a ≫ i)).hom.left (x.left z) ∈ U ∧
        (leftTranslationIso G (a ≫ i)).inv.left (x.left z) ∈ U := by
  obtain ⟨V, hne, hV⟩ := exists_nonempty_open_of_finite_orbit_parameter i x p U hU
  obtain ⟨a, y, hy, hyj⟩ := hsection V hne
  let l : T ⟶ H ⊗ T := lift (toUnit T ≫ a) (𝟙 T)
  have hl : l.left ≫ p ≫ j = T.hom ≫ a.left := by
    rw [hp, ← Over.comp_left, lift_fst, Over.comp_left, Over.toUnit_left]
  have hval : j (p (l.left z)) = a.left s := by
    change (l.left ≫ p ≫ j) z = a.left s
    rw [hl]
    exact congrArg (fun w => a.left w) hz
  have hmem : p (l.left z) ∈ V := by
    rw [hj (hval.trans hyj.symm)]
    exact hy
  obtain ⟨hfwd, hinv⟩ := hV _ hmem
  have hfwd' : l ≫ leftOrbit i x = x ≫ (leftTranslationIso G (a ≫ i)).hom :=
    orbit_section i x a
  have hinv' : l ≫ ((GrpObj.inv : H ⟶ H) ⊗ₘ 𝟙 T) ≫ leftOrbit i x =
      x ≫ (leftTranslationIso G (a ≫ i)).inv := by
    calc
      _ = lift (toUnit T ≫ a⁻¹) (𝟙 T) ≫ leftOrbit i x := by
        simp only [l, lift_map_assoc, Hom.inv_def, Category.assoc, Category.comp_id]
      _ = x ≫ L1.translate G (a⁻¹ ≫ i) := orbit_section i x a⁻¹
      _ = _ := by rw [GrpObj.inv_comp]; rfl
  refine ⟨a, ?_, ?_⟩
  · change (x ≫ (leftTranslationIso G (a ≫ i)).hom).left z ∈ U
    rw [← hfwd']
    exact hfwd
  · change (x ≫ (leftTranslationIso G (a ≫ i)).inv).left z ∈ U
    rw [← hinv']
    exact hinv

set_option backward.isDefEq.respectTransparency false in
/-- The inverse-translation condition over the special fibre lifts to a
section of the translating subgroup over a strictly henselian DVR. -/
theorem exists_symmetricTranslate_on_special_fibre
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    {H G T : Over (Spec (CommRingCat.of R))} [GrpObj H] [GrpObj G] [Smooth H.hom]
    (i : H ⟶ G) [IsMonHom i] (x : T ⟶ G) (z : T.left)
    (hz : T.hom z = IsLocalRing.closedPoint R)
    (p : (H ⊗ T).left ⟶ H.hom.fiber (IsLocalRing.closedPoint R))
    [IsFinite p] [IrreducibleSpace (H ⊗ T).left]
    (hp : p ≫ H.hom.fiberι (IsLocalRing.closedPoint R) = (fst H T).left)
    (U : G.left.Opens) (hU : ((leftOrbit i x).left ⁻¹ᵁ U : Set (H ⊗ T).left).Nonempty) :
    ∃ a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ H,
      (leftTranslationIso G (a ≫ i)).hom.left (x.left z) ∈ U ∧
        (leftTranslationIso G (a ≫ i)).inv.left (x.left z) ∈ U := by
  let s : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  let j := H.hom.fiberι s
  refine exists_symmetricTranslate_of_fibre_parameter i x z s hz p j
    j.isEmbedding.injective hp U hU ?_
  intro V hV
  obtain ⟨y, hy⟩ := hV
  obtain ⟨E, hE, hEV⟩ := j.isEmbedding.isInducing.isOpen_iff.mp V.isOpen
  let W : H.left.Opens := ⟨E, hE⟩
  have hyW : j y ∈ W := by
    change y ∈ j ⁻¹' E
    rwa [hEV]
  have hys : H.hom (j y) = s := by
    have hym : j y ∈ Set.range j := ⟨y, rfl⟩
    rwa [H.hom.range_fiberι] at hym
  obtain ⟨a₀, ha₀, haW⟩ := exists_section_in_open_of_strictHenselianDVR H.hom W hys hyW
  let a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ H := Over.homMk a₀ ha₀
  have has : H.hom (a₀ s) = s := congrArg (fun g : Spec (CommRingCat.of R) ⟶ _ => g s) ha₀
  have hr : a₀ s ∈ Set.range j := (H.hom.range_fiberι s).symm ▸ has
  obtain ⟨v, hv⟩ := hr
  refine ⟨a, v, ?_, hv⟩
  change v ∈ (V : Set _)
  rw [← hEV]
  change j v ∈ W
  rwa [hv]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse-translation condition over the integral generic fibre lifts
to a section of the translating subgroup over a strictly henselian DVR. -/
theorem exists_symmetricTranslate_on_generic_fibre
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    {Y : Scheme.{0}} {H G T : Over (Spec (CommRingCat.of R))}
    [GrpObj H] [GrpObj G] [Smooth H.hom]
    (i : H ⟶ G) [IsMonHom i] (x : T ⟶ G) (z : T.left)
    (hz : T.hom z = (⊥ : PrimeSpectrum R))
    (j : Y ⟶ H.left) [IsOpenImmersion j] [NoetherianSpace Y] [IrreducibleSpace Y]
    (hj : Set.range j = H.hom ⁻¹' {(⊥ : PrimeSpectrum R)})
    (w : H.left) (hw : H.hom w = IsLocalRing.closedPoint R)
    (hgen : ∀ v, v ⤳ w → H.hom v = H.hom w → v = w)
    (p : (H ⊗ T).left ⟶ Y) [IsFinite p] [IrreducibleSpace (H ⊗ T).left]
    (hp : p ≫ j = (fst H T).left)
    (U : G.left.Opens) (hU : ((leftOrbit i x).left ⁻¹ᵁ U : Set (H ⊗ T).left).Nonempty) :
    ∃ a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ H,
      (leftTranslationIso G (a ≫ i)).hom.left (x.left z) ∈ U ∧
        (leftTranslationIso G (a ≫ i)).inv.left (x.left z) ∈ U := by
  refine exists_symmetricTranslate_of_fibre_parameter i x z _ hz p j
    j.isOpenEmbedding.injective hp U hU ?_
  intro V hV
  obtain ⟨a, ha, y, hy, hya⟩ :=
    exists_section_in_generic_open_of_strictHenselianDVR H.hom j hj V hV w hw hgen
  exact ⟨Over.homMk a ha, y, hy, hya⟩

set_option backward.isDefEq.respectTransparency false in
/-- Symmetric translates of an open meeting every geometric orbit cover the
group over a strictly henselian DVR. The translating subgroup has geometrically
integral fibres. -/
theorem symmetricTranslation_cover_of_orbits
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    {H G : Over (Spec (CommRingCat.of R))} [GrpObj H] [GrpObj G]
    [Smooth H.hom] [GeometricallyIntegral H.hom] [QuasiCompact H.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsOpenImmersion (H.hom.fiberι (⊥ : PrimeSpectrum R))]
    (i : H ⟶ G) [IsMonHom i] (U : G.left.Opens)
    (horbit : ∀ (F : Type) [Field F] (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R))
      (x : Over.mk t ⟶ G), ((leftOrbit i x).left ⁻¹ᵁ U : Set (H ⊗ Over.mk t).left).Nonempty) :
    ∀ y : G.left, ∃ a : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ H,
      (leftTranslationIso G (a ≫ i)).hom.left y ∈ U ∧
        (leftTranslationIso G (a ≫ i)).inv.left y ∈ U := by
  let S := Spec (CommRingCat.of R)
  have translateOnFibre (s : S) :
      ∀ {T : Over S} (x : T ⟶ G) (z : T.left), T.hom z = s →
        ∀ (p : (H ⊗ T).left ⟶ H.hom.fiber s) [IsFinite p] [IrreducibleSpace (H ⊗ T).left],
          p ≫ H.hom.fiberι s = (fst H T).left →
          ((leftOrbit i x).left ⁻¹ᵁ U : Set (H ⊗ T).left).Nonempty →
          ∃ a : 𝟙_ (Over S) ⟶ H,
            (leftTranslationIso G (a ≫ i)).hom.left (x.left z) ∈ U ∧
              (leftTranslationIso G (a ≫ i)).inv.left (x.left z) ∈ U := by
    intro T
    by_cases hs : s = (⊥ : PrimeSpectrum R)
    · subst s
      intro x z htz p _ _ hp hU
      let s₁ : S := IsLocalRing.closedPoint R
      let w := H.hom.fiberι s₁ (genericPoint (H.hom.fiber s₁))
      have hw : H.hom w = s₁ := by
        have hw' : w ∈ Set.range (H.hom.fiberι s₁) := ⟨_, rfl⟩
        rwa [H.hom.range_fiberι] at hw'
      have hgen : ∀ v, v ⤳ w → H.hom v = H.hom w → v = w := by
        intro v hv hvs
        have hv' : v ∈ Set.range (H.hom.fiberι s₁) := by
          rw [H.hom.range_fiberι, Set.mem_preimage, Set.mem_singleton_iff]
          exact hvs.trans hw
        obtain ⟨v', rfl⟩ := hv'
        have hvG : v' ⤳ genericPoint (H.hom.fiber s₁) :=
          (H.hom.fiberι s₁).isEmbedding.isInducing.specializes_iff.mp hv
        have hGv : genericPoint (H.hom.fiber s₁) ⤳ v' :=
          (genericPoint_spec _).specializes trivial
        exact congrArg (fun v' => H.hom.fiberι s₁ v') (hvG.antisymm hGv).eq
      have : IsLocallyNoetherian (H.hom.fiber (⊥ : PrimeSpectrum R)) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.snd H.hom ((Spec (CommRingCat.of R)).fromSpecResidueField
            (⊥ : PrimeSpectrum R)))
      have : CompactSpace (H.hom.fiber (⊥ : PrimeSpectrum R)) := inferInstance
      have : IsNoetherian (H.hom.fiber (⊥ : PrimeSpectrum R)) := {}
      exact exists_symmetricTranslate_on_generic_fibre i x z htz _ (H.hom.range_fiberι _)
        w hw hgen p hp U hU
    · have hne : s.asIdeal ≠ ⊥ := fun h => hs (PrimeSpectrum.ext h)
      have hm : s.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot s.isPrime hne
      have he : s = IsLocalRing.closedPoint R :=
        PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
      subst s
      intro x z htz p _ _ hp hU
      exact exists_symmetricTranslate_on_special_fibre i x z htz p hp U hU
  have hclosed (s : S) (u : G.hom.fiber s) (hu : IsClosed ({u} : Set (G.hom.fiber s))) :
      ∃ a : 𝟙_ (Over S) ⟶ H,
        (leftTranslationIso G (a ≫ i)).hom.left (G.hom.fiberι s u) ∈ U ∧
          (leftTranslationIso G (a ≫ i)).inv.left (G.hom.fiberι s u) ∈ U := by
    let Gs := G.hom.fiber s
    let q := Gs.fromSpecResidueField u
    let φ := q ≫ G.hom.fiberToSpecResidueField s
    let t := φ ≫ S.fromSpecResidueField s
    let T := Over.mk t
    let x : T ⟶ G := Over.homMk (q ≫ G.hom.fiberι s) (by
      change (q ≫ G.hom.fiberι s) ≫ G.hom = (q ≫ G.hom.fiberToSpecResidueField s) ≫
        S.fromSpecResidueField s
      rw [Category.assoc, Scheme.Hom.fiber_fac, Category.assoc])
    let z : T.left := IsLocalRing.closedPoint (Gs.residueField u)
    have htz : T.hom z = s := S.fromSpecResidueField_apply s _
    have hxz : x.left z = G.hom.fiberι s u := by
      change G.hom.fiberι s (q z) = _
      rw [Gs.fromSpecResidueField_apply]
    have : LocallyOfFiniteType q := isClosed_singleton_iff_locallyOfFiniteType.mp hu
    have : LocallyOfFiniteType (G.hom.fiberToSpecResidueField s) :=
      show LocallyOfFiniteType (pullback.snd G.hom (S.fromSpecResidueField s)) from inferInstance
    have hφ : IsFinite φ :=
      isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr (by dsimp [φ]; infer_instance)
    let c := pullbackLeftPullbackSndIso H.hom (S.fromSpecResidueField s) φ
    let p : (H ⊗ T).left ⟶ H.hom.fiber s :=
      c.inv ≫ pullback.fst (H.hom.fiberToSpecResidueField s) φ
    have : IsFinite p := by
      have : IsFinite (pullback.fst (H.hom.fiberToSpecResidueField s) φ) := inferInstance
      dsimp only [p]
      infer_instance
    have hp : p ≫ H.hom.fiberι s = (fst H T).left :=
      (Category.assoc _ _ _).trans (pullbackLeftPullbackSndIso_inv_fst H.hom
        (S.fromSpecResidueField s) φ)
    have hInt : IsIntegral (H ⊗ T).left :=
      GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback H.hom t)
    have hU := horbit (Gs.residueField u) t x
    rw [← hxz]
    exact translateOnFibre s x z htz p hp hU
  intro y
  let s := G.hom y
  let y₀ := G.hom.asFiber y
  obtain ⟨u, hu, hcu⟩ := isClosed_closure.exists_closed_singleton
    (⟨y₀, subset_closure (Set.mem_singleton y₀)⟩ :
      (closure {y₀}).Nonempty)
  have hsp : y ⤳ G.hom.fiberι s u := by
    have hsp₀ : y₀ ⤳ u := specializes_iff_mem_closure.mpr hu
    simpa only [y₀, s, Scheme.Hom.fiberι_asFiber] using
      hsp₀.map (G.hom.fiberι s).continuous
  obtain ⟨a, ha, ha'⟩ := hclosed s u hcu
  refine ⟨a, ?_, ?_⟩
  · exact (hsp.map (leftTranslationIso G (a ≫ i)).hom.left.continuous).mem_open U.isOpen ha
  · exact (hsp.map (leftTranslationIso G (a ≫ i)).inv.left.continuous).mem_open U.isOpen ha'

end

end NeronDVR

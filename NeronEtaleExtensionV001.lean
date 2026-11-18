import NeronGenericFibreV001
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# An étale neighbourhood of an unramified coordinate field

Let `O` be a discrete valuation subring of a field `K`, let `Ω ⊇ K` be a field with a valuation
subring `w` lying over `O`, and let `M ⊆ Ω` be a finite separable subextension of `Ω / K`. Let
`B` be the integral closure of `O` in `M` and `𝔮 ⊆ B` the centre of `w` on `B`.

If `B` is unramified over `O` at `𝔮`, then there is `f ∈ B \ 𝔮` such that `B_f` is étale over `O`
(openness of the unramified locus, together with finiteness and freeness of `B` over `O`), `M` is
the base change `K ⊗_O B_f` (so `Spec M` is the generic fibre of `Spec B_f`), and `B_f` maps to
`w` over `O`. This is the arithmetic input that lets the Néron mapping property be applied to an
honest smooth (indeed étale) test scheme.
-/

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry Limits IsLocalRing
open scoped nonZeroDivisors

namespace NeronInvariantTorsion

section Ring

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
variable (O : ValuationSubring K) (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)

variable (M : IntermediateField K Ω) [Algebra O M] [IsScalarTower O K M]

include hw in
/-- Elements of `M` integral over `O` lie in `w`. -/
theorem integral_mem_w (b : integralClosure O M) : ((b : M) : Ω) ∈ w := by
  obtain ⟨p, hp, hpe⟩ := b.2
  have e : (algebraMap w Ω).comp (ιOw O w hw) = (algebraMap M Ω).comp (algebraMap O M) := by
    ext a
    change algebraMap K Ω (a : K) = ((algebraMap O M a : M) : Ω)
    rw [IsScalarTower.algebraMap_apply O K M]
    rfl
  have hint : IsIntegral w ((b : M) : Ω) := by
    refine ⟨p.map (ιOw O w hw), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, e]
    have h0 := Polynomial.hom_eval₂ p (algebraMap O M) (algebraMap M Ω) (b : M)
    rw [hpe, map_zero] at h0
    exact h0.symm
  have h := (integers_valuation w).mem_of_integral hint
  exact (w.valuation_le_one_iff _).mp h

/-- The inclusion of the integral closure of `O` in `M` into `w`. -/
def toW : integralClosure O M →+* w :=
  ((M.val.toRingHom).comp (integralClosure O M).toSubring.subtype).codRestrict w
    (fun b => integral_mem_w O w hw M b)

theorem toW_coe (b : integralClosure O M) : ((toW O w hw M b : w) : Ω) = ((b : M) : Ω) := rfl

/-- The centre of `w` on the integral closure of `O` in `M`. -/
def center : Ideal (integralClosure O M) :=
  (maximalIdeal w).comap (toW O w hw M)

instance center_isPrime : (center O w hw M).IsPrime :=
  Ideal.comap_isPrime _ _

theorem isUnit_toW_of_not_mem {f : integralClosure O M} (hf : f ∉ center O w hw M) :
    IsUnit (toW O w hw M f) := by
  by_contra h
  exact hf ((mem_maximalIdeal _).mpr h)

theorem ne_zero_of_not_mem {f : integralClosure O M} (hf : f ∉ center O w hw M) :
    ((f : M)) ≠ 0 := by
  intro h0
  have h1 : toW O w hw M f = 0 := by
    apply Subtype.ext
    rw [toW_coe, h0]
    rfl
  exact hf (by
    show toW O w hw M f ∈ maximalIdeal w
    rw [h1]; exact zero_mem _)

end Ring

section Etale

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
variable (O : ValuationSubring K) [IsDiscreteValuationRing O]
variable (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
variable (M : IntermediateField K Ω) [Algebra O M] [IsScalarTower O K M]
  [FiniteDimensional K M] [Algebra.IsSeparable K M]

instance integralClosure_finite : Module.Finite O (integralClosure O M) :=
  IsIntegralClosure.finite O K M (integralClosure O M)

instance faithfulSMul_O_M : FaithfulSMul O M := by
  rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq O K M]
  exact (algebraMap K M).injective.comp Subtype.val_injective

instance integralClosure_free : Module.Free O (integralClosure O M) :=
  IsIntegralClosure.module_free O K M (integralClosure O M)

instance integralClosure_finitePresentation :
    Algebra.FinitePresentation O (integralClosure O M) :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- **Étale neighbourhood.** If the integral closure `B` of `O` in `M` is unramified over `O` at
the centre of `w`, there is `f ∈ B` off the centre with `B_f` étale over `O`. -/
theorem exists_etale_away [Algebra.IsUnramifiedAt O (center O w hw M)] :
    ∃ f : integralClosure O M, f ∉ center O w hw M ∧
      Algebra.Etale O (Localization.Away f) := by
  haveI : Algebra.IsEtaleAt O (center O w hw M) :=
    Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat (center O w hw M)
  obtain ⟨f, hf, h⟩ := Algebra.exists_etale_of_isEtaleAt (R := O) (center O w hw M)
  exact ⟨f, hf, h⟩

end Etale

section Base

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
variable (O : ValuationSubring K)
variable (M : IntermediateField K Ω) [Algebra O M] [IsScalarTower O K M]
  [Algebra.IsAlgebraic K M]
variable (f : integralClosure O M) (hf : ((f : M)) ≠ 0)

/-- The algebra structure `B_f → M`. -/
def awayToM : Localization.Away f →+* M :=
  IsLocalization.Away.lift f (g := algebraMap (integralClosure O M) M) (isUnit_iff_ne_zero.mpr hf)

theorem awayToM_comp :
    (awayToM O M f hf).comp (algebraMap (integralClosure O M) (Localization.Away f)) =
      algebraMap (integralClosure O M) M :=
  IsLocalization.Away.lift_comp _ _

theorem awayToM_injective : Function.Injective (awayToM O M f hf) := by
  have hdom : IsDomain (integralClosure O M) := inferInstance
  have hinjB : Function.Injective (algebraMap (integralClosure O M) M) :=
    Subtype.val_injective
  have hf0 : f ≠ 0 := fun h0 => hf (by rw [h0]; rfl)
  have hinjC : Function.Injective
      (algebraMap (integralClosure O M) (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  unfold awayToM IsLocalization.Away.lift
  rw [IsLocalization.lift_injective_iff]
  intro x y
  exact ⟨fun h => congrArg _ (hinjC h), fun h => congrArg _ (hinjB h)⟩

/-- **`M` is the generic fibre of `B_f`**: `M` is the localization of `B_f` at the nonzero
elements of `O`. -/
theorem isLocalization_away :
    letI : Algebra (Localization.Away f) M := (awayToM O M f hf).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (Localization.Away f) O⁰) M := by
  let _ : Algebra (Localization.Away f) M := (awayToM O M f hf).toAlgebra
  have hB : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure O M) O⁰) M :=
    IsIntegralClosure.isLocalization O K M (integralClosure O M)
  have hcomp : ∀ b : integralClosure O M,
      algebraMap (Localization.Away f) M (algebraMap _ (Localization.Away f) b) =
        algebraMap (integralClosure O M) M b := fun b =>
    congrArg (fun φ : integralClosure O M →+* M => φ b) (awayToM_comp O M f hf)
  have hO : ∀ a : O, algebraMap (Localization.Away f) M (algebraMap O (Localization.Away f) a) =
      algebraMap O M a := by
    intro a
    rw [IsScalarTower.algebraMap_apply O (integralClosure O M) (Localization.Away f), hcomp]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩
    rw [hO]
    exact IsLocalization.map_units (M := Algebra.algebraMapSubmonoid (integralClosure O M) O⁰) M
      ⟨algebraMap O (integralClosure O M) a, a, ha, rfl⟩
  · intro z
    obtain ⟨⟨b, s⟩, hbs⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid (integralClosure O M) O⁰) z
    obtain ⟨_, a, ha, hs⟩ := s
    refine ⟨⟨algebraMap _ (Localization.Away f) b, ⟨algebraMap O (Localization.Away f) a,
      a, ha, rfl⟩⟩, ?_⟩
    simp only at hbs ⊢
    rw [hO, hcomp, ← hbs]
    congr 1
    rw [← hs]
    rfl
  · intro x y h
    exact ⟨1, by rw [awayToM_injective O M f hf h]⟩

end Base

section Neron

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
variable (O : ValuationSubring K) [IsDiscreteValuationRing O]
variable (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
variable (M : IntermediateField K Ω) [Algebra O M] [IsScalarTower O K M]
  [FiniteDimensional K M] [Algebra.IsSeparable K M]

/-- The structure map `O → B_f`, as a morphism of commutative rings. -/
def algOC (f : integralClosure O M) :
    CommRingCat.of O ⟶ CommRingCat.of (Localization.Away f) :=
  CommRingCat.ofHom (algebraMap O (Localization.Away f))

/-- The test scheme `Spec B_f` over `O`. -/
def testScheme (f : integralClosure O M) : Over (Spec (CommRingCat.of O)) :=
  Over.mk (Spec.map (algOC O M f))

theorem testScheme_smooth (f : integralClosure O M) (h : Algebra.Etale O (Localization.Away f)) :
    Smooth (testScheme O M f).hom := by
  haveI : Etale (Spec.map (algOC O M f)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr h
  show Smooth (Spec.map (algOC O M f))
  infer_instance

set_option maxHeartbeats 400000 in
/-- **Néron extension of unramified points.** Let `(N, e)` satisfy the Néron mapping property
over `O`. If the integral closure of `O` in the finite separable coordinate field `M` is
unramified at the centre of `w`, every point `x ∈ A(Ω)` coming from `y ∈ A(M)` is the generic
fibre of a `w`-section of `N`. The section is obtained by applying the mapping property to the
étale test scheme `Spec B_f` (whose generic fibre is `Spec M`) and restricting along
`Spec w → Spec B_f`. -/
theorem exists_section_of_unramified
    {A : PkgI3.AbVar K} {N : Over (Spec (CommRingCat.of O))}
    (e : (Over.pullback (jO O)).obj N ≅ A.X)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N => (Over.pullback (jO O)).map f ≫ e.hom)
    [Algebra.IsUnramifiedAt O (center O w hw M)]
    (y : A.Pt M) (x : A.Pt Ω)
    (hxy : Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ y.left = x.left) :
    ∃ (f : integralClosure O M) (_ : f ∉ center O w hw M)
      (_ : Algebra.Etale O (Localization.Away f)) (φ : testScheme O M f ⟶ N)
      (σ : specW O w hw ⟶ testScheme O M f), genericFibre O w hw e (σ ≫ φ) = x := by
  obtain ⟨f, hf, hEt⟩ := exists_etale_away O w hw M
  have hf0 := ne_zero_of_not_mem O w hw M hf
  letI : Algebra (Localization.Away f) M := (awayToM O M f hf0).toAlgebra
  have hBC : ∀ b : integralClosure O M,
      algebraMap (Localization.Away f) M (algebraMap _ (Localization.Away f) b) =
        algebraMap (integralClosure O M) M b := fun b =>
    congrArg (fun φ : integralClosure O M →+* M => φ b) (awayToM_comp O M f hf0)
  haveI : IsScalarTower O (Localization.Away f) M :=
      IsScalarTower.of_algebraMap_eq (R := O) (S := Localization.Away f) (A := M) (fun a => by
    rw [IsScalarTower.algebraMap_apply O (integralClosure O M) (Localization.Away f), hBC]
    rfl)
  haveI := isLocalization_away O M f hf0
  haveI : Algebra.IsPushout O (Localization.Away f) K M :=
    Algebra.isPushout_of_isLocalization O⁰ K (Localization.Away f) M
  have hPB := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout O (Localization.Away f) K M)
  have hPB' : IsPullback (Spec.map ((CommRingCat.ofHom (algebraMap (Localization.Away f) M) :
          CommRingCat.of (Localization.Away f) ⟶ CommRingCat.of M)))
      (Spec.map (CommRingCat.ofHom (algebraMap K M))) (testScheme O M f).hom (jO O) := hPB
  haveI : Smooth (testScheme O M f).hom := testScheme_smooth O M f hEt
  obtain ⟨iso, hfst, hsnd⟩ : ∃ i : Spec (CommRingCat.of M) ≅
      pullback (testScheme O M f).hom (jO O),
      i.hom ≫ pullback.fst _ _ = Spec.map ((CommRingCat.ofHom (algebraMap (Localization.Away f) M) :
          CommRingCat.of (Localization.Away f) ⟶ CommRingCat.of M))
      ∧ i.hom ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap K M)) :=
    ⟨hPB'.isoPullback, hPB'.isoPullback_hom_fst, hPB'.isoPullback_hom_snd⟩
  obtain ⟨y', hy'⟩ : ∃ y' : Spec (CommRingCat.of M) ⟶ A.X.left, y' = y.left := ⟨_, rfl⟩
  have hy : y' ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
    rw [hy']; exact Over.w y
  have hx : Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ y' = x.left := by rw [hy']; exact hxy
  obtain ⟨g, hgl⟩ : ∃ g : (Over.pullback (jO O)).obj (testScheme O M f) ⟶ A.X,
      g.left = iso.inv ≫ y' := ⟨Over.homMk (iso.inv ≫ y') (by
      calc (iso.inv ≫ y') ≫ A.X.hom = iso.inv ≫ (y' ≫ A.X.hom) := Category.assoc _ _ _
        _ = iso.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)) := congrArg (iso.inv ≫ ·) hy
        _ = iso.inv ≫ (iso.hom ≫ pullback.snd (testScheme O M f).hom (jO O)) :=
          congrArg (iso.inv ≫ ·) hsnd.symm
        _ = pullback.snd (testScheme O M f).hom (jO O) := Iso.inv_hom_id_assoc _ _), rfl⟩
  obtain ⟨φ, hφ⟩ := (hN (testScheme O M f)).2 g
  have hφ' : (Over.pullback (jO O)).map φ ≫ e.hom = g := hφ
  obtain ⟨lw, hlw⟩ : ∃ lw : Localization.Away f →+* w,
      lw.comp (algebraMap (integralClosure O M) (Localization.Away f)) = toW O w hw M :=
    ⟨IsLocalization.Away.lift f (isUnit_toW_of_not_mem O w hw M hf),
      IsLocalization.Away.lift_comp _ _⟩
  have hσeq : Spec.map (CommRingCat.ofHom lw) ≫ (testScheme O M f).hom = (specW O w hw).hom := by
    change Spec.map (CommRingCat.ofHom lw) ≫ Spec.map (algOC O M f) =
        Spec.map (CommRingCat.ofHom (ιOw O w hw))
    rw [← Spec.map_comp, algOC, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    rw [RingHom.comp_apply,
      IsScalarTower.algebraMap_apply O (integralClosure O M) (Localization.Away f)]
    change ((lw.comp (algebraMap (integralClosure O M) (Localization.Away f))) _ : Ω) = _
    rw [hlw, toW_coe]
    change ((algebraMap O M a : M) : Ω) = algebraMap K Ω (a : K)
    rw [IsScalarTower.algebraMap_apply O K M]
    rfl
  obtain ⟨σ, hσl⟩ : ∃ σ : specW O w hw ⟶ testScheme O M f,
      σ.left = Spec.map (CommRingCat.ofHom lw) := ⟨Over.homMk _ hσeq, rfl⟩
  refine ⟨f, hf, hEt, φ, σ, ?_⟩
  -- the scheme maps involved, with literal source and target objects
  obtain ⟨gp, hgp⟩ : ∃ gp : Spec (CommRingCat.of Ω) ⟶ pullback (specW O w hw).hom (jO O),
      gp = (genPt O w hw).left := ⟨_, rfl⟩
  obtain ⟨mσ, hmσ⟩ : ∃ mσ : pullback (specW O w hw).hom (jO O) ⟶
      pullback (testScheme O M f).hom (jO O), mσ = ((Over.pullback (jO O)).map σ).left :=
    ⟨_, rfl⟩
  have hgfst : gp ≫ pullback.fst (specW O w hw).hom (jO O) =
      Spec.map (CommRingCat.ofHom (algebraMap w Ω)) := by
    rw [hgp]; exact pullback.lift_fst _ _ _
  have hgsnd : gp ≫ pullback.snd (specW O w hw).hom (jO O) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
    rw [hgp]; exact pullback.lift_snd _ _ _
  have hσfst : mσ ≫ pullback.fst (testScheme O M f).hom (jO O) =
      pullback.fst (specW O w hw).hom (jO O) ≫ σ.left := by
    rw [hmσ]; exact pullback.lift_fst _ _ _
  have hσsnd : mσ ≫ pullback.snd (testScheme O M f).hom (jO O) =
      pullback.snd (specW O w hw).hom (jO O) := by
    rw [hmσ]; exact pullback.lift_snd _ _ _
  have hring : (algebraMap w Ω).comp lw =
      M.val.toRingHom.comp (algebraMap (Localization.Away f) M) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [RingHom.comp_assoc, RingHom.comp_assoc, hlw]
    ext b
    change ((toW O w hw M b : w) : Ω) = ((algebraMap (Localization.Away f) M
      (algebraMap (integralClosure O M) (Localization.Away f) b) : M) : Ω)
    rw [hBC]
    rfl
  have hringC : CommRingCat.ofHom lw ≫ CommRingCat.ofHom (algebraMap w Ω) =
      (CommRingCat.ofHom (algebraMap (Localization.Away f) M) :
          CommRingCat.of (Localization.Away f) ⟶ CommRingCat.of M) ≫
        CommRingCat.ofHom M.val.toRingHom := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]
  have hSpec : Spec.map (CommRingCat.ofHom (algebraMap w Ω)) ≫ σ.left =
      Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫
        Spec.map ((CommRingCat.ofHom (algebraMap (Localization.Away f) M) :
          CommRingCat.of (Localization.Away f) ⟶ CommRingCat.of M)) := by
    rw [hσl]
    exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map hringC).trans (Spec.map_comp _ _))
  have hSpecK : Spec.map (CommRingCat.ofHom (algebraMap K Ω)) =
      Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have key : gp ≫ mσ = Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ iso.hom := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (gp ≫ ·) hσfst).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ σ.left) hgfst).trans ?_
      refine hSpec.trans ?_
      refine (congrArg (Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ ·) hfst.symm).trans ?_
      exact (Category.assoc _ _ _).symm
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (gp ≫ ·) hσsnd).trans ?_
      refine hgsnd.trans ?_
      refine hSpecK.trans ?_
      refine (congrArg (Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ ·) hsnd.symm).trans ?_
      exact (Category.assoc _ _ _).symm
  have hgen : genericFibre O w hw e (σ ≫ φ) =
      genPt O w hw ≫ (Over.pullback (jO O)).map σ ≫ g := by
    rw [genericFibre, Functor.map_comp, Category.assoc, hφ']
  apply Over.OverMorphism.ext
  rw [hgen]
  have hleft : (genPt O w hw ≫ (Over.pullback (jO O)).map σ ≫ g).left =
      gp ≫ mσ ≫ g.left := by
    subst hgp
    subst hmσ
    rfl
  refine hleft.trans ?_
  refine (congrArg (fun t => gp ≫ mσ ≫ t) hgl).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (iso.inv ≫ y')) key).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ ·)
    (Iso.hom_inv_id_assoc iso y')).trans ?_
  exact hx

end Neron

end NeronInvariantTorsion

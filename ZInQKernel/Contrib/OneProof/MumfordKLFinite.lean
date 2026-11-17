import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.OneProof.PhiAmpleIsogeny
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocusTensor
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Endomorphism
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal

/-!
# `K(L)` is finite for ample `L` (Mumford §6, Application 1), proved (phi-ample)

For `A` an abelian variety over any field `K`, `L` ample, a representation `P` of `Pic_{A/K}` with identity
component `(B, j)` and the lift `λ_L : A → B` of `φ_L`, the kernel of `λ_L` has finitely many `K̄`-points
(`finite_ker_pts`). Mumford's argument, on irreducible closed subsets of the kernel: if `λ_L` vanishes on an
integral closed `Z ⊆ A`, then `(1 × i)^*Λ(L)` is classified by the constant map, so it is trivial (Kleiman 9.2.5,
the vendored normalized Picard functor); restricting along `z ↦ (−z, z)` gives `i^*L ⊗ i^*(−1)^*L ≅ 𝒪_Z`; both
factors are ample, so `Z` is affine; an integral affine proper `K`-scheme is a point.

Main results:
* `PhiAmple.phiAmpleIsogeny_of_phiSurjective : PicDict.MumfordPhiSurjectiveAC → T09Pic.PhiAmpleIsogeny`;
* `PhiAmple.mumfordKLFiniteSectionAC_of_open : T09Pic.PicRepresentableAbVar → T09Pic.PicZeroAbVar →
  PicFix.MumfordKLFiniteSectionAC` (pic-fix's printed leaf from L1 and L2, the fields beside it);
* `PhiAmple.mumfordKLFiniteAC_of_open` (the same for pic-dict's `MumfordKLFiniteAC`).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PhiAmple

open Scheme.Modules

section ZeroLocus

variable {X : Scheme.{0}}

/-- `D(ψ ≫ φ) ⊇ D(ψ) ∩ D(φ)`. -/
theorem notMem_support_comp {L M N : X.Modules} [L.IsInvertible] [M.IsInvertible] [N.IsInvertible]
    (ψ : L ⟶ M) (φ : M ⟶ N) {x : X} (h1 : x ∉ (Hom.zeroLocus ψ).support)
    (h2 : x ∉ (Hom.zeroLocus φ).support) : x ∉ (Hom.zeroLocus (ψ ≫ φ)).support := by
  obtain ⟨U, hxU, -, ⟨eM, hM⟩, eN, hN⟩ :=
    exists_isFreeGenerator₂ M N (TopologicalSpace.Opens.mem_top x)
  obtain ⟨V, hxV, hVU, eL, hL⟩ := exists_isFreeGenerator L hxU
  obtain ⟨b, hb⟩ := (hM.map hVU).exists_smul_eq (ψ.app V.1 eL)
  obtain ⟨c, hc⟩ := (hN.map hVU).exists_smul_eq
    (φ.app V.1 (M.presheaf.map (homOfLE hVU).op eM))
  have i1 := Hom.ideal_zeroLocus ψ V hL (hM.map hVU) hb.symm
  have i2 := Hom.ideal_zeroLocus φ V (hM.map hVU) (hN.map hVU) hc.symm
  have i3 := Hom.ideal_zeroLocus (ψ ≫ φ) V hL (hN.map hVU) (b := b * c) (by
    change φ.app V.1 (ψ.app V.1 eL) = _
    rw [← hb, Hom.app_smul, ← hc, mul_smul])
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV, i1, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton] at h1
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV, i2, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton] at h2
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxV, i3, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton, Scheme.basicOpen_mul]
  simp only [Set.mem_compl_iff, not_not] at h1 h2 ⊢
  exact ⟨h1, h2⟩

/-- An isomorphism vanishes nowhere. -/
theorem notMem_support_iso {M N : X.Modules} [M.IsInvertible] [N.IsInvertible] (e : M ≅ N) (x : X) :
    x ∉ (Hom.zeroLocus e.hom).support := by
  have h : Hom.zeroLocus e.hom = Hom.zeroLocus (𝟙 M) :=
    Hom.zeroLocus_eq_of_arrowIso _ _ (Arrow.isoMk (Iso.refl M) e.symm (by simp))
  rw [h]
  obtain ⟨U, hxU, -, eM, hM⟩ := exists_isFreeGenerator M (TopologicalSpace.Opens.mem_top x)
  have i1 := Hom.ideal_zeroLocus (𝟙 M) U hM hM (b := 1) (by simp)
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, i1, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton, Scheme.basicOpen_of_isUnit _ isUnit_one]
  simpa using hxU

/-- The zero scheme of `Q ◁ φ` is that of `φ`. -/
theorem zeroLocus_whiskerLeft {M N : X.Modules} [M.IsInvertible] [N.IsInvertible] (Q : X.Modules)
    [Q.IsInvertible] (φ : M ⟶ N) : Hom.zeroLocus (Q ◁ φ) = Hom.zeroLocus φ := by
  rw [← Hom.zeroLocus_whiskerRight φ Q]
  exact Hom.zeroLocus_eq_of_arrowIso _ _
    (Arrow.isoMk (β_ Q M) (β_ Q N) (BraidedCategory.braiding_naturality_right Q φ).symm)

/-- On a scheme whose global functions form a field, an endomorphism of `𝒪` that is nonzero at one point
vanishes nowhere. -/
theorem notMem_support_of_isField (hF : IsField Γ(X, ⊤)) (f : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) {x : X}
    (hx : x ∉ (Hom.zeroLocus f).support) (y : X) : y ∉ (Hom.zeroLocus f).support := by
  obtain ⟨g, rfl⟩ := exists_eq_smulHom (𝟙_ X.Modules) f
  by_cases hg : g = 0
  · subst hg
    exfalso
    apply hx
    rw [smulHom_zero, (Hom.zeroLocus_eq_bot_iff 0).2 rfl, Scheme.IdealSheafData.support_bot]
    trivial
  · obtain ⟨g', hg'⟩ := hF.mul_inv_cancel hg
    let e : 𝟙_ X.Modules ≅ 𝟙_ X.Modules :=
      ⟨smulHom _ g, smulHom _ g', by rw [← smulHom_mul, mul_comm, hg', smulHom_one],
        by rw [← smulHom_mul, hg', smulHom_one]⟩
    exact notMem_support_iso e y

end ZeroLocus

section Affine

variable {X : Scheme.{0}}

/-- Composing with an isomorphism does not change the zero scheme (any source). -/
theorem zeroLocus_comp_iso' {L M N : X.Modules} [L.IsInvertible] [M.IsInvertible] [N.IsInvertible]
    (s : L ⟶ M) (e : M ≅ N) : Hom.zeroLocus (s ≫ e.hom) = Hom.zeroLocus s :=
  (Hom.zeroLocus_eq_of_arrowIso s (s ≫ e.hom) (Arrow.isoMk (Iso.refl _) e (by simp))).symm

/-- **A scheme whose global functions form a field and which carries two ample classes with trivial
product is affine.** For `x`, sections `s` of `c^n` and `t` of `d^m` nonvanishing at `x`, with `D(s)` affine,
give the global function `u = s^{⊗m} ⊗ t^{⊗n}` (a section of `(cd)^{nm} = 𝒪`) nonvanishing at `x`, hence a unit;
so `D(s) ⊇ D(u) = X`. -/
theorem isAffine_of_ample_mul_eq_one [Nonempty X] (hF : IsField Γ(X, ⊤)) (c d : X.Pic)
    (hc : T09Pic.IsAmple X c) (hd : T09Pic.IsAmple X d) (hcd : c * d = 1) : IsAffine X := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨n, hn, s, hxs, haff⟩ := hc.2 x
  obtain ⟨m, hm, t, hxt, -⟩ := hd.2 x
  let Mc := (fromSkeleton X.Modules).obj c.val
  let Md := (fromSkeleton X.Modules).obj d.val
  let P := (Mc.tensorPow n).tensorPow m
  let Q := (Md.tensorPow m).tensorPow n
  let S : 𝟙_ X.Modules ⟶ P := Scheme.Modules.tensorPowSection s m
  let T : 𝟙_ X.Modules ⟶ Q := Scheme.Modules.tensorPowSection t n
  have hPQ : Scheme.Pic.mk (P ⊗ Q) = Scheme.Pic.mk (𝟙_ X.Modules) := by
    rw [Scheme.Pic.mk_tensorObj, PicFix.mk_tensorPow, PicFix.mk_tensorPow, PicFix.mk_tensorPow,
      PicFix.mk_tensorPow, Scheme.Pic.mk_fromSkeleton, Scheme.Pic.mk_fromSkeleton, ← pow_mul, ← pow_mul,
      mul_comm m n, ← mul_pow, hcd, one_pow]
    exact Scheme.Pic.one_eq_mk_unit
  obtain ⟨e⟩ := (Scheme.Pic.mk_eq_mk_iff _ _).1 hPQ
  let u : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules :=
    ((λ_ (𝟙_ X.Modules)).inv ≫ (𝟙_ X.Modules ◁ T)) ≫ ((S ▷ Q) ≫ e.hom)
  have hS : (Hom.zeroLocus ((S ▷ Q) ≫ e.hom)).support = (Hom.zeroLocus s).support := by
    rw [zeroLocus_comp_iso', Hom.zeroLocus_whiskerRight, PicFix.support_tensorPowSection _ hm]
  have hxs' : x ∉ (Hom.zeroLocus s).support := hxs
  have hxt' : x ∉ (Hom.zeroLocus t).support := hxt
  have hxu : x ∉ (Hom.zeroLocus u).support := by
    apply notMem_support_comp
    · apply notMem_support_comp
      · exact notMem_support_iso (λ_ (𝟙_ X.Modules)).symm x
      · rw [zeroLocus_whiskerLeft, PicFix.support_tensorPowSection _ hn]; exact hxt'
    · rw [hS]; exact hxs'
  have hsupp : (Hom.zeroLocus s).support = ⊥ := by
    rw [← hS]
    refine le_antisymm ?_ bot_le
    refine (Scheme.IdealSheafData.support_antitone (Hom.zeroLocus_comp_le
      ((λ_ (𝟙_ X.Modules)).inv ≫ (𝟙_ X.Modules ◁ T)) ((S ▷ Q) ≫ e.hom))).trans ?_
    intro y hy
    exact absurd hy (notMem_support_of_isField hF u hxu y)
  rw [hsupp] at haff
  have htop : (⊥ : TopologicalSpace.Closeds X).compl = ⊤ := by
    ext y; simp [TopologicalSpace.Closeds.compl]
  rw [htop] at haff
  have : IsAffine (⊤ : X.Opens).toScheme := haff
  exact IsAffine.of_isIso X.topIso.inv

/-- An affine scheme whose global functions form a field has one point. -/
theorem subsingleton_of_isAffine_of_isField [IsAffine X] (hF : IsField Γ(X, ⊤)) : Subsingleton X := by
  let _ := hF.toField
  have : Subsingleton (PrimeSpectrum Γ(X, ⊤)) := inferInstance
  refine ⟨fun a b => ?_⟩
  have h : X.isoSpec.hom a = X.isoSpec.hom b := Subsingleton.elim (α := PrimeSpectrum Γ(X, ⊤)) _ _
  simpa using congrArg X.isoSpec.inv h

end Affine

section Core

open T09Pic PkgI3 PkgI3.AbVar PicDict

variable {K : Type} [Field K] {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
  (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} {j : B.X ⟶ P}
  (hj : IsPicZero rep B j) {L : A.X.left.Pic} (hL : IsAmple A.X.left L) {lam : A.X ⟶ B.X}
  (hlam : lam ≫ j = phiL rep L)

include hj hL hlam in
/-- **Core of Mumford §6 Application 1.** An integral closed subscheme `Z ⊆ A` on which `λ_L` is constant
(equal to `0`) is a point: `(1 × i)^*Λ(L)` is classified by the constant map, so it is trivial (Kleiman 9.2.5,
the normalized Picard functor); restricting along `z ↦ (−z, z)` gives `i^*L ⊗ i^*(−1)^*L = 𝒪_Z`; both factors
are ample, so `Z` is affine, and an affine integral proper `K`-scheme is a point. -/
theorem subsingleton_of_lam_const (Zs : Scheme.{0}) [IsIntegral Zs] (i : Zs ⟶ A.X.left)
    [IsClosedImmersion i] (g : Zs ⟶ Spec (CommRingCat.of K))
    (hg : i ≫ lam.left = g ≫ η[B.X].left) : Subsingleton Zs := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  have hmon : IsMonHom j := hj.2.2
  have hw : i ≫ A.X.hom = g := by
    have h1 := congrArg (· ≫ B.X.hom) hg
    simp only [Category.assoc] at h1
    rw [Over.w lam] at h1
    rw [h1]
    have h2 : η[B.X].left ≫ B.X.hom = 𝟙 _ := Over.w η[B.X]
    rw [h2]
    exact Category.comp_id g
  let Zo : Over (Spec (CommRingCat.of K)) := Over.mk g
  let iO : Zo ⟶ A.X := Over.homMk i hw
  have h1 : iO ≫ lam = CartesianMonoidalCategory.toUnit Zo ≫ η[B.X] := by
    apply Over.OverMorphism.ext
    exact hg
  have h2 : iO ≫ phiL rep L = CartesianMonoidalCategory.toUnit Zo ≫ η[P] := by
    rw [← hlam, ← Category.assoc, h1, Category.assoc, IsMonHom.one_hom j]
  rw [phiL, comp_classify, ← homEquiv_symm_one rep] at h2
  -- `Λ(L)` restricted to `0 × A` is trivial
  have e0 : zT A A.X = (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.toUnit A.X ≫ η[A.X])
      (𝟙 A.X)).left := by
    apply pullback.hom_ext <;> simp
  have hμ0 : zT A A.X ≫ (μ[A.X]).left = 𝟙 _ := by
    rw [e0, ← Over.comp_left, MonObj.lift_comp_one_left]; rfl
  have hS0 : Scheme.Pic.map (A.X.hom ≫ η[A.X].left) L = 1 := by
    rw [Scheme.Pic.map_comp, Subsingleton.elim (α := (Spec (CommRingCat.of K)).Pic)
      (Scheme.Pic.map η[A.X].left L) 1, Scheme.Pic.map_one]
  have hz0 : Scheme.Pic.map (zT A A.X) (mumfordBundle A L) = 1 := by
    rw [mumfordBundle, ← Scheme.Pic.mapHom_apply]
    simp only [map_mul, map_inv, Scheme.Pic.mapHom_apply, ← Scheme.Pic.map_comp, hμ0,
      sectionBaseChange_fst, sectionBaseChange_snd, Scheme.Pic.map_id]
    rw [hS0]
    group
  have h4 : Scheme.Pic.map (zT A Zo)
      (Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom iO) (mumfordBundle A L)) = 1 := by
    rw [← Scheme.Pic.map_comp, sectionBaseChange_comp_baseChangeMap, Scheme.Pic.map_comp, hz0,
      Scheme.Pic.map_one]
  have h3 : (1 : (pullback A.X.hom Zo.hom).Pic) ∈ (Nrm A).obj (op Zo) := by
    change Scheme.Pic.map _ 1 = 1; exact Scheme.Pic.map_one _
  have h5' := Θ_inj (A := A) pushforwardUnitUniversal (T := Zo)
    (x := ⟨Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom iO) (mumfordBundle A L), h4⟩)
    (y := ⟨(1 : (pullback A.X.hom Zo.hom).Pic), h3⟩) (by
      rw [Θ_hom_app, Θ_hom_app]
      exact rep.homEquiv.symm.injective h2)
  have h5 : Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom iO) (mumfordBundle A L) = 1 :=
    congrArg Subtype.val h5'
  -- restriction along `z ↦ (−z, z)`
  have hι : ι[A.X].left ≫ A.X.hom = A.X.hom := Over.w ι[A.X]
  let s : Zs ⟶ pullback A.X.hom Zo.hom := pullback.lift (i ≫ ι[A.X].left) (𝟙 Zs) (by
    rw [Category.assoc, hι, hw, Category.id_comp]; rfl)
  have hσ : s ≫ JacobianChallenge.baseChangeMap A.X.hom iO =
      i ≫ (CartesianMonoidalCategory.lift ι[A.X] (𝟙 A.X)).left := by
    apply pullback.hom_ext <;> simp [s, JacobianChallenge.baseChangeMap, iO]
  have h6 : Scheme.Pic.map (i ≫ (CartesianMonoidalCategory.lift ι[A.X] (𝟙 A.X)).left)
      (mumfordBundle A L) = 1 := by
    rw [← hσ, Scheme.Pic.map_comp, h5, Scheme.Pic.map_one]
  have hμ : (CartesianMonoidalCategory.lift ι[A.X] (𝟙 A.X)).left ≫ (μ[A.X]).left =
      A.X.hom ≫ η[A.X].left := by
    rw [← Over.comp_left, GrpObj.left_inv]; rfl
  have hfst : (CartesianMonoidalCategory.lift ι[A.X] (𝟙 A.X)).left ≫ pullback.fst A.X.hom A.X.hom =
      ι[A.X].left := by simp
  have hsnd : (CartesianMonoidalCategory.lift ι[A.X] (𝟙 A.X)).left ≫ pullback.snd A.X.hom A.X.hom =
      𝟙 _ := by simp
  have hS : Scheme.Pic.map (i ≫ A.X.hom ≫ η[A.X].left) L = 1 := by
    rw [Scheme.Pic.map_comp, hS0, Scheme.Pic.map_one]
  have h7 : Scheme.Pic.map i L * Scheme.Pic.map (i ≫ ι[A.X].left) L = 1 := by
    rw [mumfordBundle, ← Scheme.Pic.mapHom_apply] at h6
    simp only [map_mul, map_inv, Scheme.Pic.mapHom_apply, ← Scheme.Pic.map_comp] at h6
    rw [Category.assoc, hμ, Category.assoc, hfst, Category.assoc, hsnd, Category.comp_id, hS,
      one_mul, ← mul_inv_rev, inv_eq_one] at h6
    exact h6
  -- both factors are ample
  haveI : CompactSpace A.X.left := hL.1
  haveI : CompactSpace Zs := i.isClosedEmbedding.compactSpace
  haveI : IsIso ι[A.X].left := (Over.forget _).map_isIso ι[A.X]
  have hc : IsAmple Zs (Scheme.Pic.map i L) := isAmple_pullback i L hL
  have hd : IsAmple Zs (Scheme.Pic.map (i ≫ ι[A.X].left) L) := by
    rw [Scheme.Pic.map_comp]
    exact isAmple_pullback i _ (isAmple_pullback ι[A.X].left L hL)
  -- `Γ(Z, 𝒪)` is a field
  haveI : UniversallyClosed g := by rw [← hw]; infer_instance
  have hF : IsField Γ(Zs, ⊤) := isField_of_universallyClosed K g
  haveI : IsAffine Zs := isAffine_of_ample_mul_eq_one hF _ _ hc hd h7
  exact subsingleton_of_isAffine_of_isField hF

end Core

section Finite

open T09Pic PkgI3 PkgI3.AbVar PicDict TopologicalSpace

variable {K : Type} [Field K]

/-- **`K(L)` is finite** (Mumford §6, Application 1, for every ample `L`, over any field): the kernel of
`λ_L` has finitely many `K̄`-points. The scheme-theoretic kernel `pullback λ_L 0` is noetherian and each of its
irreducible closed subsets is a point (`subsingleton_of_lam_const`), so it is a finite set of closed points. -/
theorem finite_ker_pts {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} {j : B.X ⟶ P}
    (hj : IsPicZero rep B j) {L : A.X.left.Pic} (hL : IsAmple A.X.left L) {lam : A.X ⟶ B.X}
    (hlam : lam ≫ j = phiL rep L) :
    {x : A.Pt (AlgebraicClosure K) | x ≫ lam = 1}.Finite := by
  have hηB : η[B.X].left ≫ B.X.hom = 𝟙 _ := Over.w η[B.X]
  haveI : IsClosedImmersion (η[B.X].left ≫ B.X.hom) := by rw [hηB]; infer_instance
  haveI : IsClosedImmersion η[B.X].left := IsClosedImmersion.of_comp η[B.X].left B.X.hom
  let p : pullback (C := Scheme.{0}) lam.left η[B.X].left ⟶ A.X.left := pullback.fst _ _
  haveI : IsClosedImmersion p := inferInstance
  haveI : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  haveI : CompactSpace A.X.left := hL.1
  haveI : IsNoetherian A.X.left := {}
  haveI : NoetherianSpace (pullback (C := Scheme.{0}) lam.left η[B.X].left) :=
    p.isClosedEmbedding.isInducing.noetherianSpace
  -- every irreducible closed subset of the kernel is a point
  have hirr : ∀ Z : Set (pullback (C := Scheme.{0}) lam.left η[B.X].left), IsClosed Z → IsIrreducible Z →
      Z.Subsingleton := by
    intro Z hZc hZi
    let Zc : Closeds (pullback (C := Scheme.{0}) lam.left η[B.X].left) := ⟨Z, hZc⟩
    let I := Scheme.IdealSheafData.vanishingIdeal Zc
    haveI : IsIntegral I.subscheme := Scheme.isIntegral_subscheme_vanishingIdeal Zc hZi
    have hsub := subsingleton_of_lam_const rep hj hL hlam I.subscheme (I.subschemeι ≫ p)
      (I.subschemeι ≫ pullback.snd _ _) (by simp [p, pullback.condition])
    have hr : Set.range I.subschemeι = Z := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact Scheme.IdealSheafData.coe_support_vanishingIdeal Zc
    rw [← hr]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [Subsingleton.elim a b]
  -- the kernel is a finite set
  have hfin : Finite (pullback (C := Scheme.{0}) lam.left η[B.X].left) := by
    let c : pullback (C := Scheme.{0}) lam.left η[B.X].left → irreducibleComponents (pullback (C := Scheme.{0}) lam.left η[B.X].left) :=
      fun k => ⟨irreducibleComponent k, irreducibleComponent_mem_irreducibleComponents k⟩
    have hinj : Function.Injective c := by
      intro a b h
      have h' : irreducibleComponent a = irreducibleComponent b := congrArg Subtype.val h
      exact hirr _ isClosed_irreducibleComponent isIrreducible_irreducibleComponent
        mem_irreducibleComponent (h' ▸ mem_irreducibleComponent)
    haveI : Finite (irreducibleComponents (pullback (C := Scheme.{0}) lam.left η[B.X].left)) :=
      NoetherianSpace.finite_irreducibleComponents.to_subtype
    exact Finite.of_injective c hinj
  -- its points are closed
  have hcl : ∀ k, IsClosed {p k} := by
    intro k
    have h1 : closure {k} = ({k} : Set (pullback (C := Scheme.{0}) lam.left η[B.X].left)) :=
      (hirr _ isClosed_closure isIrreducible_singleton.closure).eq_singleton_of_mem
        (subset_closure rfl)
    have : IsClosed ({k} : Set (pullback (C := Scheme.{0}) lam.left η[B.X].left)) := by
      rw [← h1]; exact isClosed_closure
    rw [← Set.image_singleton]
    exact p.isClosedEmbedding.isClosedMap _ this
  -- the `K̄`-points of the kernel lie over its finitely many points
  refine (Set.finite_iUnion (fun k => finite_pts_over (B := A) (p k) (hcl k))).subset ?_
  intro x hx
  have hx' : x.left ≫ lam.left = (ptK K).hom ≫ η[B.X].left := congrArg (fun f => f.left) hx
  refine Set.mem_iUnion.2 ⟨pullback.lift x.left (ptK K).hom hx' (IsLocalRing.closedPoint _), ?_⟩
  show x.left _ = p _
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst]

/-- **Main result.** `φ_L` is an isogeny for every ample `L` (the field `phiAmpleIsogeny`), from Mumford §8 Thm 1
alone: finiteness of `K(L)` is now proved (`finite_ker_pts`), so `MumfordKLFiniteSectionAC` is not needed. -/
theorem phiAmpleIsogeny_of_phiSurjective (h8 : MumfordPhiSurjectiveAC) : PhiAmpleIsogeny := by
  have hsub := picZeroPtsTranslInv_of_leaves pushforwardUnitUniversal geomIntegralProd
  have h8' := mumfordPhiSurjective_of_ac h8
  intro K _ A P rep B j hj L hL lam hlam
  obtain ⟨lam', hlam'⟩ := exists_hom_comp_eq_phiL rep hj L
  have hjm : Mono j := by
    haveI : IsOpenImmersion j.left := hj.1
    exact (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  have he : lam = lam'.hom := by rw [← cancel_mono j, hlam, hlam']
  subst he
  refine ⟨finiteOfFiniteKerPts K A B lam' (finite_ker_pts rep hj hL hlam), ?_⟩
  apply surjective_of_forall_pt
  intro y
  obtain ⟨x, hx⟩ := h8' K A _ (ampleBaseChangeAlgClosure K A L hL) _ (hsub K A P rep B j hj y)
  exact ⟨x, picClass_injective rep hj (by rw [picClass_phiL rep L lam'.hom hlam x, hx])⟩

end Finite

section KPoints

open T09Pic PkgI3 PkgI3.AbVar PicDict

variable {k : Type} [Field k]

/-- `X ◁ x ≫ μ = pr₁ ≫ t_x` for a `k`-point `x`. -/
lemma whisker_mu_kpt {X : AbVar k} (x : AC.Kpt X) :
    (X.X ◁ x) ≫ μ[X.X] = CartesianMonoidalCategory.fst X.X _ ≫ AC.tr x := by
  simp only [AC.tr, CartesianMonoidalCategory.comp_lift_assoc, Category.comp_id]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp only [CartesianMonoidalCategory.whiskerLeft_snd, CartesianMonoidalCategory.lift_snd]
    rw [← Category.assoc]
    congr 1
    exact CartesianMonoidalCategory.toUnit_unique _ _

/-- **`Λ(L)` restricted along a `k`-point `x`** is `φ_L(x)` (transported to `X ×_k k`). -/
theorem map_mumfordBundle_kpt {X : AbVar k} (c : X.X.left.Pic) (x : AC.Kpt X) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap X.X.hom x) (mumfordBundle X c) =
      Scheme.Pic.map (pullback.fst X.X.hom (𝟙_ (Over (Spec (CommRingCat.of k)))).hom) (AC.phi c x) := by
  have e : JacobianChallenge.baseChangeMap X.X.hom x = (X.X ◁ x).left := by
    apply pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]
  have hμ : JacobianChallenge.baseChangeMap X.X.hom x ≫ (μ[X.X]).left =
      pullback.fst X.X.hom (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ (AC.tr x).left := by
    rw [e, ← Over.comp_left, whisker_mu_kpt]
    simp
  have hfst : JacobianChallenge.baseChangeMap X.X.hom x ≫ pullback.fst X.X.hom X.X.hom =
      pullback.fst X.X.hom (𝟙_ (Over (Spec (CommRingCat.of k)))).hom := pullback.lift_fst _ _ _
  have hsnd : JacobianChallenge.baseChangeMap X.X.hom x ≫ pullback.snd X.X.hom X.X.hom =
      pullback.snd _ _ ≫ x.left := pullback.lift_snd _ _ _
  have hS : Scheme.Pic.map x.left c = 1 :=
    Subsingleton.elim (α := (Spec (CommRingCat.of k)).Pic) _ _
  rw [mumfordBundle, ← Scheme.Pic.mapHom_apply]
  simp only [map_mul, map_inv, Scheme.Pic.mapHom_apply, ← Scheme.Pic.map_comp, hμ, hsnd, hfst]
  rw [Scheme.Pic.map_comp (pullback.snd _ _) x.left, hS, Scheme.Pic.map_one, Scheme.Pic.map_comp]
  simp only [AC.phi, inv_one, mul_one]
  rw [Scheme.Pic.map_mul]
  congr 1
  rw [eq_comm, eq_inv_iff_mul_eq_one, ← Scheme.Pic.map_mul, inv_mul_cancel, Scheme.Pic.map_one]

/-- **`K(L)` is finite for every ample `L`** (pic-dict's `MumfordKLFiniteAC`, Mumford §6 Application 1), from
the Picard scheme (L1) and `Pic⁰` (L2): a `k`-point of `K(L)` lies in `ker λ_L`, and `X(k) ↪ X(k̄)`. -/
theorem mumfordKLFiniteAC_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) :
    MumfordKLFiniteAC := by
  intro k _ _ X c₀ hc₀
  obtain ⟨P, ⟨rep⟩⟩ := h1 k X
  obtain ⟨B, j, hj⟩ := h2 k X P rep
  obtain ⟨lam, hlam⟩ := exists_hom_comp_eq_phiL rep hj c₀
  letI := picardFunctorCommGrpObj X.X.hom rep
  have hmon : IsMonHom j := hj.2.2
  have hjm : Mono j := by
    haveI : IsOpenImmersion j.left := hj.1
    exact (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  have hF := finite_ker_pts rep hj hc₀ hlam
  let u : ptK k ⟶ 𝟙_ (Over (Spec (CommRingCat.of k))) := CartesianMonoidalCategory.toUnit _
  haveI : Epi u := by
    haveI : Epi u.left := by
      haveI : Surjective u.left := ⟨fun _ => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
      haveI : Flat u.left := by
        change Flat (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
        rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom]
        exact RingHom.flat_algebraMap_iff.mpr inferInstance
      exact Flat.epi_of_flat_of_surjective u.left
    exact (Over.forget _).epi_of_epi_map this
  refine (hF.preimage (f := fun x : AC.Kpt X => u ≫ x) fun a _ b _ h => cancel_epi u |>.1 h).subset ?_
  intro x hx
  change AC.phi c₀ x = 1 at hx
  change (u ≫ x) ≫ lam.hom = 1
  have hx1 : x ≫ lam.hom = CartesianMonoidalCategory.toUnit _ ≫ η[B.X] := by
    rw [← cancel_mono j, Category.assoc, hlam, phiL, comp_classify, map_mumfordBundle_kpt, hx,
      Scheme.Pic.map_one, homEquiv_symm_one rep, Category.assoc, IsMonHom.one_hom j]
  rw [Category.assoc, hx1, ← Category.assoc, CartesianMonoidalCategory.toUnit_unique (u ≫ _)
    (CartesianMonoidalCategory.toUnit _)]
  rfl

/-- **pic-fix's printed leaf `MumfordKLFiniteSectionAC` is a theorem** given L1 and L2 (both fields of the
bundle that carries it). -/
theorem mumfordKLFiniteSectionAC_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) :
    PicFix.MumfordKLFiniteSectionAC :=
  fun k _ _ X c₀ hc₀ _ => mumfordKLFiniteAC_of_open h1 h2 k X c₀ hc₀

end KPoints

end PhiAmple

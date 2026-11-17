import ZInQKernel.Contrib.OneProof.PrintedStableHeight
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint
import ZInQKernel.OneProof.H.TailZ19

/-! # semiab-descend: `SemiAbelianDescendsPerfect` from Chevalley's structure theorem over a perfect field

height-fix left one glue Prop, `ZInQ.HeightFix.SemiAbelianDescendsPerfect` (descent of semi-abelian identity
components from `k̄` to a perfect field `k`; `PrintedStableHeight.lean`). This file proves it, statement unchanged
and for **every** perfect field, from one new leaf:

* **LEAF `ChevalleyPerfect`** (§9): Chevalley's structure theorem over a perfect field (existence and uniqueness of
  the normal smooth connected affine subgroup `H` with `G/H` an abelian variety), with `G/H` read as a faithfully
  flat homomorphism onto an abelian variety with scheme-theoretic kernel `H`.

Everything else is proved here (no `sorry`, standard axioms):

* §1 Yoneda on affine test schemes: a morphism over `S` bijective on points with values in affine schemes is an
  isomorphism (`isIso_of_bijective_affine`); §2 affine `K`-schemes are `Spec` of `K`-algebras;
* §3-§4 a kernel that is a split torus in the functor of points (`(Rˣ)^r ≅ ker`, natural in `K`-algebras, as in
  `HasSemiAbelianIdentityComponent`) is `Spec K[x₁^{±1}, …, x_r^{±1}]`, hence smooth, connected and affine
  (`isSmoothConnAffineKer_of_torus`);
* §5 a faithfully flat homomorphism with smooth kernel onto a smooth group has smooth source (shear square
  `U ×_B U ≅ U × ker π` and Mathlib's flat descent of smoothness; `smooth_of_smoothKer`);
* §6 an open subgroup scheme of a group locally of finite type over an algebraically closed field is closed
  (Jacobson property, rational points and translations; `isClosed_range_openSubgroup`);
* §7 the identity component `G⁰` of a group scheme of finite type over a field is an open subgroup (Stacks 04KV,
  proved in the tree as `geomConnOfRationalPoint_proof`);
* §8 smooth connected affine kernels stay so after a field extension;
* §9 the assembly `semiAbelianDescendsPerfect_of_chevalley`: `G⁰` over `k`; `(G⁰)_{k̄}` equals the given open
  subgroup `U'` of `G_{k̄}` (both are clopen-connected); `U'` is smooth (§3, §5), so `G⁰` is smooth (descent along
  `Spec k̄ → Spec k`); Chevalley over `k` gives `π : G⁰ → B`; uniqueness over `k̄` identifies the kernel of
  `π_{k̄}` with the given torus.
* §10 the fields `bostLowerBound`, `gaudronRemondThm14` (and the optional `javanpeykarBound`, `pazukiCor13Upper`)
  from height-fix's printed leaves and `ChevalleyPerfect`, with no glue.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open DictModels.RaynaudOr ZInQ.HeightSplit

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.SemiAbDescend

/-! ## §1. Points over affine schemes determine morphisms -/

section Yoneda

variable {S : Scheme.{0}}

/-- The affine open cover of `T.left`. -/
abbrev cov (T : Over S) : T.left.OpenCover := T.left.affineOpenCover.openCover

/-- The pieces of the affine open cover of `T.left`, as objects over `S`. -/
abbrev coverObj (T : Over S) (x : (cov T).I₀) : Over S :=
  Over.mk ((cov T).f x ≫ T.hom)

/-- The inclusion of a cover piece. -/
abbrev coverMap (T : Over S) (x : (cov T).I₀) : coverObj T x ⟶ T :=
  Over.homMk ((cov T).f x) rfl

theorem isAffine_coverObj (T : Over S) (x : (cov T).I₀) : IsAffine (coverObj T x).left := by
  change IsAffine (Spec _); infer_instance

/-- Injectivity on all test objects from injectivity on affine ones. -/
theorem injective_of_affine {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ T : Over S, IsAffine T.left → Function.Injective (fun a : T ⟶ X => a ≫ f))
    (T : Over S) : Function.Injective (fun a : T ⟶ X => a ≫ f) := by
  intro a b hab
  simp only at hab
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (cov T) _ _ fun x => ?_
  have := h (coverObj T x) (isAffine_coverObj T x) (a₁ := coverMap T x ≫ a) (a₂ := coverMap T x ≫ b)
    (by simp only [Category.assoc, hab])
  exact congrArg CommaMorphism.left this

/-- **Yoneda on affine test objects**: a morphism over `S` that is bijective on points with values in
affine schemes is an isomorphism. -/
theorem isIso_of_bijective_affine {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ T : Over S, IsAffine T.left → Function.Bijective (fun a : T ⟶ X => a ≫ f)) :
    IsIso f := by
  have hinj := injective_of_affine f (fun T hT => (h T hT).1)
  choose a ha using fun x => (h (coverObj Y x) (isAffine_coverObj Y x)).2 (coverMap Y x)
  have ha' : ∀ x, a x ≫ f = coverMap Y x := ha
  have hcompat : ∀ x y : (cov Y).I₀, pullback.fst ((cov Y).f x) ((cov Y).f y) ≫ (a x).left =
      pullback.snd ((cov Y).f x) ((cov Y).f y) ≫ (a y).left := by
    intro x y
    let P : Over S := Over.mk (pullback.fst ((cov Y).f x) ((cov Y).f y) ≫ (cov Y).f x ≫ Y.hom)
    let p1 : P ⟶ coverObj Y x := Over.homMk (pullback.fst ((cov Y).f x) ((cov Y).f y)) rfl
    let p2 : P ⟶ coverObj Y y := Over.homMk (pullback.snd ((cov Y).f x) ((cov Y).f y)) (by
      simp only [P, coverObj, Over.mk_hom]
      rw [pullback.condition_assoc])
    have := hinj P (a₁ := p1 ≫ a x) (a₂ := p2 ≫ a y) (by
      simp only [Category.assoc, ha']
      apply Over.OverMorphism.ext
      simp only [Over.comp_left, Over.homMk_left, p1, p2]
      exact pullback.condition)
    exact congrArg CommaMorphism.left this
  let gl : Y.left ⟶ X.left := (cov Y).glueMorphisms (fun x => (a x).left) hcompat
  have hgl : ∀ x, (cov Y).f x ≫ gl = (a x).left := fun x => (cov Y).ι_glueMorphisms _ hcompat x
  have hw : gl ≫ X.hom = Y.hom := by
    refine Scheme.Cover.hom_ext (cov Y) _ _ fun x => ?_
    rw [← Category.assoc, hgl, Over.w]
    rfl
  let g : Y ⟶ X := Over.homMk gl hw
  have hgf : g ≫ f = 𝟙 Y := by
    apply Over.OverMorphism.ext
    refine Scheme.Cover.hom_ext (cov Y) _ _ fun x => ?_
    simp only [Over.comp_left, Over.homMk_left, Over.id_left, Category.comp_id, g]
    rw [← Category.assoc, hgl, ← Over.comp_left, ha']
    rfl
  have hfg : f ≫ g = 𝟙 X := hinj X (a₁ := f ≫ g) (a₂ := 𝟙 X) (by
    simp only [Category.assoc, hgf, Category.comp_id, Category.id_comp])
  exact ⟨g, hfg, hgf⟩

end Yoneda

/-! ## §2. Affine schemes over `K` are `Spec` of `K`-algebras -/

section AlgPt

variable {K : Type} [Field K]

/-- Every morphism between `Spec`s of `K`-algebras over `K` is `Spec` of a `K`-algebra map. -/
theorem exists_algPtMap {R S : Type} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (f : algPt K R ⟶ algPt K S) : ∃ ψ : S →ₐ[K] R, f = algPtMap ψ := by
  obtain ⟨ψ0, hψ0⟩ : ∃ ψ0 : CommRingCat.of S ⟶ CommRingCat.of R, Spec.map ψ0 = f.left :=
    ⟨Spec.preimage f.left, Spec.map_preimage _⟩
  have hw : f.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K S)) =
      Spec.map (CommRingCat.ofHom (algebraMap K R)) := Over.w f
  have hc : CommRingCat.ofHom (algebraMap K S) ≫ ψ0 = CommRingCat.ofHom (algebraMap K R) :=
    Spec.map_injective (by rw [Spec.map_comp, hψ0]; exact hw)
  refine ⟨{ ψ0.hom with commutes' := fun c => ?_ }, ?_⟩
  · have := congrArg (fun g => g.hom c) hc
    simpa using this
  · apply Over.OverMorphism.ext
    simp only [algPtMap]
    rw [← hψ0]
    rfl

/-- An affine scheme over `K` is isomorphic over `K` to `Spec` of a `K`-algebra. -/
theorem exists_iso_algPt (T : Over (Spec (CommRingCat.of K))) [IsAffine T.left] :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra K R), Nonempty (T ≅ algPt K R) := by
  let ψ : CommRingCat.of K ⟶ Γ(T.left, ⊤) := Spec.preimage (T.left.isoSpec.inv ≫ T.hom)
  letI : Algebra K Γ(T.left, ⊤) := ψ.hom.toAlgebra
  refine ⟨Γ(T.left, ⊤), inferInstance, this, ⟨Over.isoMk T.left.isoSpec ?_⟩⟩
  have h1 : Spec.map ψ = T.left.isoSpec.inv ≫ T.hom := Spec.map_preimage _
  show T.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.hom) = T.hom
  change T.left.isoSpec.hom ≫ Spec.map ψ = T.hom
  rw [h1, Iso.hom_inv_id_assoc]

/-- Bijectivity on all affine points from bijectivity on `Spec` of `K`-algebras. -/
theorem bijective_affine_of_algPt {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y)
    (h : ∀ (R : Type) [CommRing R] [Algebra K R],
      Function.Bijective (fun a : algPt K R ⟶ X => a ≫ f))
    (T : Over (Spec (CommRingCat.of K))) (hT : IsAffine T.left) :
    Function.Bijective (fun a : T ⟶ X => a ≫ f) := by
  obtain ⟨R, _, _, ⟨i⟩⟩ := exists_iso_algPt T
  have e1 : (T ⟶ X) ≃ (algPt K R ⟶ X) := (i.homCongr (Iso.refl X))
  have e2 : (T ⟶ Y) ≃ (algPt K R ⟶ Y) := (i.homCongr (Iso.refl Y))
  have hcomm : (fun a : T ⟶ X => a ≫ f) =
      (i.homCongr (Iso.refl Y)).symm ∘ (fun a : algPt K R ⟶ X => a ≫ f) ∘ (i.homCongr (Iso.refl X)) := by
    funext a
    simp [Iso.homCongr]
  rw [hcomm]
  exact (Equiv.bijective _).comp ((h R).comp (Equiv.bijective _))

end AlgPt


/-! ## §3. A kernel that is a split torus in the functor of points is `Spec K[x^{±1}]` -/

section Torus

variable {K : Type} [Field K]

/-- The coordinate ring `K[x₁^{±1}, …, x_r^{±1}]` of the split torus `𝔾_m^r`. -/
abbrev TorusRing (K : Type) [Field K] (r : ℕ) : Type :=
  Localization.Away (∏ i : Fin r, MvPolynomial.X i : MvPolynomial (Fin r) K)

theorem isUnit_X {r : ℕ} (i : Fin r) :
    IsUnit (algebraMap (MvPolynomial (Fin r) K) (TorusRing K r) (MvPolynomial.X i)) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := TorusRing K r)
    (∏ i : Fin r, MvPolynomial.X i : MvPolynomial (Fin r) K)
  exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))) hu

/-- The universal point `(x₁, …, x_r)` of `𝔾_m^r`. -/
def tUniv (r : ℕ) : Fin r → (TorusRing K r)ˣ := fun i => (isUnit_X i).unit

/-- The `K`-algebra map `K[x^{±1}] → R`, `xᵢ ↦ tᵢ`. -/
def torusLift {r : ℕ} {R : Type} [CommRing R] [Algebra K R] (t : Fin r → Rˣ) :
    TorusRing K r →ₐ[K] R :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (∏ i : Fin r, MvPolynomial.X i :
      MvPolynomial (Fin r) K)) (f := MvPolynomial.aeval (fun i => (t i : R))) (by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow, map_prod, MvPolynomial.aeval_X]
    have : (∏ i, (t i : R)) = ((∏ i, t i : Rˣ) : R) := by simp [Units.coe_prod]
    rw [this]
    exact IsUnit.pow n (Units.isUnit _))

theorem torusLift_tUniv {r : ℕ} {R : Type} [CommRing R] [Algebra K R] (t : Fin r → Rˣ) (i : Fin r) :
    torusLift t ((tUniv r i : (TorusRing K r)ˣ) : TorusRing K r) = t i := by
  simp only [tUniv, IsUnit.unit_spec, torusLift, IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_eq]
  simp

theorem algHom_ext_torus {r : ℕ} {R : Type} [CommRing R] [Algebra K R]
    (ψ₁ ψ₂ : TorusRing K r →ₐ[K] R)
    (h : ∀ i, ψ₁ ((tUniv r i : (TorusRing K r)ˣ) : TorusRing K r) =
      ψ₂ ((tUniv r i : (TorusRing K r)ˣ) : TorusRing K r)) : ψ₁ = ψ₂ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (∏ i : Fin r, MvPolynomial.X i :
    MvPolynomial (Fin r) K))
  apply MvPolynomial.algHom_ext
  intro i
  show ψ₁ (algebraMap _ _ (MvPolynomial.X i)) = ψ₂ (algebraMap _ _ (MvPolynomial.X i))
  simpa [tUniv] using h i

end Torus

/-! ## §4. Kernels -/

section Ker

variable {K : Type} [Field K]

/-- The scheme-theoretic kernel of `π : G → B` (fibre product with the unit section of `B`). -/
abbrev kerObj {G B : Over (Spec (CommRingCat.of K))} [GrpObj B] (π : G ⟶ B) :
    Over (Spec (CommRingCat.of K)) :=
  pullback π η[B]

/-- The kernel is a smooth connected affine `K`-scheme. -/
def IsSmoothConnAffineKer {G B : Over (Spec (CommRingCat.of K))} [GrpObj B] (π : G ⟶ B) : Prop :=
  Smooth (kerObj π).hom ∧ IsAffine (kerObj π).left ∧ ConnectedSpace (kerObj π).left

instance (r : ℕ) : IsDomain (TorusRing K r) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
    (Finset.prod_ne_zero_iff.mpr fun i _ => MvPolynomial.X_ne_zero i))

theorem smooth_algPt_torus (r : ℕ) : Smooth (algPt K (TorusRing K r)).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (TorusRing K r))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change RingHom.Smooth (algebraMap K (TorusRing K r))
  rw [RingHom.smooth_algebraMap]
  haveI : Algebra.Smooth K (MvPolynomial (Fin r) K) := inferInstance
  haveI : Algebra.Smooth (MvPolynomial (Fin r) K) (TorusRing K r) := inferInstance
  exact Algebra.Smooth.comp K (MvPolynomial (Fin r) K) (TorusRing K r)

/-- **A kernel that is a split torus in the functor of points is smooth, connected and affine**: it is
`Spec K[x₁^{±1}, …, x_r^{±1}]` (Yoneda on affine test schemes). -/
theorem isSmoothConnAffineKer_of_torus {U B : Over (Spec (CommRingCat.of K))} [GrpObj U] [GrpObj B]
    (π : U ⟶ B) (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra K R], (Fin r → Rˣ) →* (algPt K R ⟶ U))
    (he_inj : ∀ (R : Type) [CommRing R] [Algebra K R], Function.Injective (e R))
    (he_ker : ∀ (R : Type) [CommRing R] [Algebra K R] (u : algPt K R ⟶ U), u ≫ π = 1 ↔ u ∈ (e R).range)
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
      (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t) :
    IsSmoothConnAffineKer π := by
  let L := TorusRing K r
  have hk : e L (tUniv r) ≫ π = toUnit _ ≫ η[B] := by
    rw [(he_ker L _).mpr ⟨tUniv r, rfl⟩]; rfl
  let j : algPt K L ⟶ kerObj π := pullback.lift (e L (tUniv r)) (toUnit _) hk
  have hj1 : j ≫ pullback.fst π η[B] = e L (tUniv r) := pullback.lift_fst _ _ _
  have hmap : ∀ (R : Type) [CommRing R] [Algebra K R] (ψ : L →ₐ[K] R),
      algPtMap ψ ≫ e L (tUniv r) = e R (fun i => Units.map (ψ : L →* R) (tUniv r i)) :=
    fun R _ _ ψ => (he_nat L R ψ (tUniv r)).symm
  have hbij : ∀ (R : Type) [CommRing R] [Algebra K R],
      Function.Bijective (fun a : algPt K R ⟶ algPt K L => a ≫ j) := by
    intro R _ _
    constructor
    · intro a₁ a₂ h
      simp only at h
      obtain ⟨ψ₁, rfl⟩ := exists_algPtMap a₁
      obtain ⟨ψ₂, rfl⟩ := exists_algPtMap a₂
      have h2 := congrArg (· ≫ pullback.fst π η[B]) h
      simp only [Category.assoc, hj1, hmap] at h2
      have h3 := he_inj R h2
      rw [algHom_ext_torus ψ₁ ψ₂ fun i => by
        have := congrArg (fun t => ((t i : Rˣ) : R)) h3
        simpa using this]
    · intro b
      have hb : (b ≫ pullback.fst π η[B]) ≫ π = 1 := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        rw [toUnit_unique (b ≫ pullback.snd π η[B]) (toUnit _)]
        rfl
      obtain ⟨t, ht⟩ := (he_ker R _).mp hb
      refine ⟨algPtMap (torusLift t), ?_⟩
      apply pullback.hom_ext
      · simp only [Category.assoc, hj1, hmap]
        rw [← ht]
        congr 1
        funext i
        ext
        exact torusLift_tUniv t i
      · exact toUnit_unique _ _
  haveI : IsIso j := isIso_of_bijective_affine j (bijective_affine_of_algPt j hbij)
  let E := asIso j
  have hw : (kerObj π).hom = E.inv.left ≫ (algPt K L).hom := (Over.w E.inv).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hw]
    haveI := smooth_algPt_torus (K := K) r
    infer_instance
  · change IsAffine (kerObj π).left
    haveI : IsAffine (algPt K L).left := by change IsAffine (Spec _); infer_instance
    exact IsAffine.of_isIso E.inv.left
  · haveI : ConnectedSpace (algPt K L).left := by
      change ConnectedSpace (Spec (CommRingCat.of L)); infer_instance
    haveI : IsIso E.hom.left := by change IsIso ((Over.forget _).map E.hom); infer_instance
    exact (E.hom.left.surjective).connectedSpace E.hom.left.continuous

end Ker

/-! ## §5. A faithfully flat homomorphism with smooth kernel onto a smooth group has smooth source -/

section Shear

variable {K : Type} [Field K]

/-- The shear square `U × ker π ⇉ U` (`(u, t) ↦ u` and `(u, t) ↦ u t`) is a pullback of `π` along `π`. -/
theorem isPullback_shear {U B : Over (Spec (CommRingCat.of K))} [GrpObj U] [GrpObj B] (π : U ⟶ B)
    [IsMonHom π] :
    IsPullback (fst U (kerObj π)) (fst U (kerObj π) * (snd U (kerObj π) ≫ pullback.fst π η[B]))
      π π := by
  set ιk := pullback.fst π η[B]
  have hιk : ιk ≫ π = 1 := by
    rw [pullback.condition, toUnit_unique (pullback.snd π η[B]) (toUnit _)]; rfl
  have hcomm : fst U (kerObj π) ≫ π = (fst U (kerObj π) * (snd U (kerObj π) ≫ ιk)) ≫ π := by
    rw [MonObj.mul_comp, Category.assoc, hιk, MonObj.comp_one, _root_.mul_one]
  refine ⟨⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk hcomm (fun c => lift c.fst
      (pullback.lift (c.fst⁻¹ * c.snd) (toUnit _) ?_)) ?_ ?_ ?_⟩⟩
  · rw [MonObj.mul_comp, GrpObj.inv_comp, c.condition, _root_.inv_mul_cancel]; rfl
  · intro c; simp
  · intro c
    rw [MonObj.comp_mul, lift_fst, ← Category.assoc, lift_snd, pullback.lift_fst, _root_.mul_inv_cancel_left]
  · intro c m h1 h2
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]; exact h1
    · rw [lift_snd]
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        rw [MonObj.comp_mul, h1] at h2
        rw [← h2, Category.assoc, _root_.inv_mul_cancel_left]
      · exact toUnit_unique _ _

/-- **Smoothness of an extension**: if `π : U → B` is a faithfully flat quasi-compact homomorphism onto a smooth
`K`-group with smooth kernel, then `U` is smooth (flat descent of smoothness along `π`, through the shear
isomorphism `U ×_B U ≅ U × ker π`). -/
theorem smooth_of_smoothKer {U B : Over (Spec (CommRingCat.of K))} [GrpObj U] [GrpObj B] (π : U ⟶ B)
    [IsMonHom π] (hfl : Flat π.left) (hsu : Surjective π.left) (hqc : QuasiCompact π.left)
    [Smooth B.hom] (hK : Smooth (kerObj π).hom) : Smooth U.hom := by
  have hP := (isPullback_shear π).map (Over.forget _)
  have hfst : Smooth ((Over.forget _).map (fst U (kerObj π))) := by
    change Smooth (pullback.fst U.hom (kerObj π).hom)
    infer_instance
  have hπ : Smooth π.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hP ⟨⟨hsu, hfl⟩, hqc⟩ hfst
  rw [← Over.w π]
  infer_instance

end Shear

/-! ## §6. Open subgroups of group schemes over an algebraically closed field are closed -/

section OpenSubgroup

variable {K : Type} [Field K]

local notation "𝟙K" => 𝟙_ (Over (Spec (CommRingCat.of K)))

instance subsingleton_unitLeft : Subsingleton (𝟙K).left :=
  inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))

/-- A `K`-point of `X` whose image lies in an open subscheme factors through it. -/
theorem factor_point {X Y : Over (Spec (CommRingCat.of K))} (i : Y ⟶ X) [IsOpenImmersion i.left]
    (a : 𝟙K ⟶ X) (s : (𝟙K).left) (ha : a.left s ∈ Set.range i.left) :
    ∃ a' : 𝟙K ⟶ Y, a' ≫ i = a := by
  have hr : Set.range a.left ⊆ Set.range i.left := by
    rintro _ ⟨s', rfl⟩; rwa [Subsingleton.elim s' s]
  refine ⟨Over.homMk (IsOpenImmersion.lift i.left a.left hr) ?_, ?_⟩
  · have : Y.hom = i.left ≫ X.hom := (Over.w i).symm
    rw [this, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w a
  · apply Over.OverMorphism.ext
    simp [IsOpenImmersion.lift_fac]

/-- Left translation by a `K`-point. -/
def transl {X : Over (Spec (CommRingCat.of K))} [GrpObj X] (s : 𝟙K ⟶ X) : X ⟶ X :=
  (toUnit X ≫ s) * 𝟙 X

theorem comp_transl {X : Over (Spec (CommRingCat.of K))} [GrpObj X] (s : 𝟙K ⟶ X) {T : Over _}
    (a : T ⟶ X) : a ≫ transl s = (toUnit T ≫ s) * a := by
  rw [transl, MonObj.comp_mul, ← Category.assoc, toUnit_unique (a ≫ toUnit X) (toUnit T),
    Category.comp_id]

theorem transl_comp_transl {X : Over (Spec (CommRingCat.of K))} [GrpObj X] (s t : 𝟙K ⟶ X) :
    transl s ≫ transl t = transl (t * s) := by
  rw [comp_transl, transl, transl, ← _root_.mul_assoc, ← MonObj.comp_mul]

theorem transl_one {X : Over (Spec (CommRingCat.of K))} [GrpObj X] : transl (1 : 𝟙K ⟶ X) = 𝟙 X := by
  rw [transl, MonObj.comp_one, _root_.one_mul]

theorem point_comp_transl {X : Over (Spec (CommRingCat.of K))} [GrpObj X] (s a : 𝟙K ⟶ X) :
    a ≫ transl s = s * a := by
  rw [comp_transl, toUnit_unique (toUnit 𝟙K) (𝟙 _), Category.id_comp]

/-- **An open subgroup scheme of a group scheme locally of finite type over an algebraically closed field is
closed** (SGA 3 VI_A 0.5-type statement). Proof: a closed point `x` outside `U` is a `K`-point `s`, and
`s · U` is an open neighbourhood of `x` disjoint from `U` (if it met `U`, it would meet it in a `K`-point, and
`s ∈ U(K)`); closed points are dense in every closed set (Jacobson). -/
theorem isClosed_range_openSubgroup [IsAlgClosed K] {X Y : Over (Spec (CommRingCat.of K))} [GrpObj X]
    [GrpObj Y] [LocallyOfFiniteType X.hom] (i : Y ⟶ X) [IsOpenImmersion i.left] [IsMonHom i] :
    IsClosed (Set.range i.left) := by
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  set O := Set.range i.left with hOdef
  have hO : IsOpen O := i.left.isOpenEmbedding.isOpen_range
  let pt : (𝟙K).left := (default : Spec (CommRingCat.of K))
  -- the `K`-point at a closed point
  have hpt : ∀ x : X.left, IsClosed {x} → ∃ a : 𝟙K ⟶ X, a.left pt = x := by
    intro x hx
    refine ⟨Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp _ _ _), ?_⟩
    exact pointOfClosedPoint_apply _ _ _ _
  have hmem : ∀ a : 𝟙K ⟶ X, a.left pt ∈ O ↔ ∃ a' : 𝟙K ⟶ Y, a' ≫ i = a := by
    intro a
    refine ⟨factor_point i a pt, ?_⟩
    rintro ⟨a', rfl⟩
    exact ⟨a'.left pt, rfl⟩
  have key : ∀ x ∈ closedPoints X.left, x ∉ O → ∃ V : Set X.left, IsOpen V ∧ x ∈ V ∧ Disjoint V O := by
    intro x hx hxO
    obtain ⟨s, rfl⟩ := hpt x hx
    have hinv : IsIso (transl s) :=
      ⟨transl s⁻¹, by rw [transl_comp_transl, _root_.inv_mul_cancel, transl_one],
        by rw [transl_comp_transl, _root_.mul_inv_cancel, transl_one]⟩
    haveI : IsIso (transl s).left := by
      change IsIso ((Over.forget _).map (transl s)); infer_instance
    refine ⟨(transl s).left '' O, (transl s).left.isOpenEmbedding.isOpenMap _ hO, ?_, ?_⟩
    · refine ⟨(η[X] : 𝟙K ⟶ X).left pt, ?_, ?_⟩
      · rw [hmem]; exact ⟨η[Y], IsMonHom.one_hom i⟩
      · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, point_comp_transl]
        rw [show (η[X] : 𝟙K ⟶ X) = 1 from (toUnit_unique (toUnit 𝟙K) (𝟙 _) ▸ (Category.id_comp _)).symm,
          _root_.mul_one]
    · rw [Set.disjoint_iff]
      rintro y ⟨⟨z, hz, rfl⟩, hyO⟩
      -- a closed point in the nonempty open `sU ∩ U`
      have hVo : IsOpen ((transl s).left '' O ∩ O) :=
        ((transl s).left.isOpenEmbedding.isOpenMap _ hO).inter hO
      obtain ⟨y', ⟨⟨z', hz', rfl⟩, hy'O⟩, hy'c⟩ :=
        nonempty_inter_closedPoints
          (show ((transl s).left '' O ∩ O).Nonempty from ⟨_, ⟨z, hz, rfl⟩, hyO⟩) hVo.isLocallyClosed
      obtain ⟨t, ht⟩ := hpt _ hy'c
      obtain ⟨t', ht'⟩ := (hmem t).mp (ht ▸ hy'O)
      have hz'' : (t ≫ transl s⁻¹).left pt = z' := by
        rw [Over.comp_left, Scheme.Hom.comp_apply, ht, ← Scheme.Hom.comp_apply, ← Over.comp_left,
          transl_comp_transl, _root_.inv_mul_cancel, transl_one]
        rfl
      rw [point_comp_transl] at hz''
      obtain ⟨u', hu'⟩ := (hmem (s⁻¹ * t)).mp (hz'' ▸ hz')
      apply hxO
      rw [hmem]
      refine ⟨t' * u'⁻¹, ?_⟩
      rw [MonObj.mul_comp, GrpObj.inv_comp, ht', hu', _root_.mul_inv_rev, _root_.inv_inv,
        _root_.mul_inv_cancel_left]
  -- conclude with the Jacobson property
  rw [← isOpen_compl_iff]
  have hD : IsClosed (Oᶜ \ interior Oᶜ) := hO.isClosed_compl.inter isOpen_interior.isClosed_compl
  have hDe : Oᶜ \ interior Oᶜ = ∅ := by
    by_contra hne
    obtain ⟨x, ⟨hxO, hxi⟩, hxc⟩ := nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.mpr hne)
      hD.isLocallyClosed
    obtain ⟨V, hV, hxV, hVO⟩ := key x hxc hxO
    exact hxi (interior_maximal (fun v hv => Set.disjoint_left.mp hVO hv) hV hxV)
  rw [← interior_eq_iff_isOpen]
  exact (interior_subset).antisymm (Set.sdiff_eq_empty.mp hDe)

end OpenSubgroup

/-! ## §7. The identity component of a group scheme of finite type over a field -/

section IdComp

open CToPrinted OpenSub

/-- `G⁰` is closed under the group law, for `G` locally of finite type and quasi-compact over a noetherian base,
once it is open (the proof of TailZ19's `idCompSubgroup_of`, with openness as a hypothesis instead of SGA 3
VI_B 3.10). -/
theorem isSubgroupOpen_of_isOpen (hG : AVGlue.GeomConnOfRationalPoint) {k : Type} [Field k]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (hW : IsOpen (idCompSet G)) :
    IsSubgroupOpen G ⟨idCompSet G, hW⟩ := by
  let S := Spec (CommRingCat.of k)
  let W : G.left.Opens := ⟨idCompSet G, hW⟩
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : IsNoetherian G.left := {}
  let f0 : W.toScheme ⟶ S := W.ι ≫ G.hom
  haveI : GeometricallyConnected f0 := geomConnected_idComp hG G W rfl
  let e := (η[G] : 𝟙_ (Over S) ⟶ G).left
  have he : ∀ s, G.hom (e s) = s := by
    intro s
    rw [← Scheme.Hom.comp_apply, Over.w]
    rfl
  refine ⟨fun s => idCompSet_one G s, ?_, ?_⟩
  · intro z hz1 hz2
    let s := G.hom (pullback.fst G.hom G.hom z)
    let m := pullback.map f0 f0 G.hom G.hom W.ι W.ι (𝟙 _) (by simp [f0]) (by simp [f0])
    let f00 := pullback.snd f0 f0 ≫ f0
    haveI : GeometricallyConnected f00 := GeometricallyConnected.comp _ _
    have hc : _root_.IsConnected (f00 ⁻¹' {s}) := f00.isConnected_preimage_singleton s
    have hm : ∀ v, G.hom (pullback.fst G.hom G.hom (m v)) = f00 v := by
      intro v
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition,
        ← Category.assoc, pullback.lift_snd, Category.assoc]
    let μl := (μ[G] : G ⊗ G ⟶ G).left
    have hμ : ∀ w : (G ⊗ G).left, G.hom (μl w) = G.hom (pullback.fst G.hom G.hom w) := by
      intro w
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun h => h w) (congrArg (fun k => k.base) (Over.w (μ[G] : G ⊗ G ⟶ G)))
    let P := μl '' (m '' (f00 ⁻¹' {s}))
    have hP : _root_.IsPreconnected P :=
      (hc.isPreconnected.image _ m.continuous.continuousOn).image _ μl.continuous.continuousOn
    have hPsub : P ⊆ G.hom ⁻¹' {s} := by
      rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      show G.hom (μl (m v)) = s
      rw [hμ, hm]
      exact hv
    -- `e(s) ∈ P`
    have hη : Set.range e ⊆ Set.range W.ι := by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact idCompSet_one G t
    let eW : S ⟶ W.toScheme := IsOpenImmersion.lift W.ι e hη
    have heW : eW ≫ W.ι = e := IsOpenImmersion.lift_fac _ _ _
    let v0 : S ⟶ pullback f0 f0 := pullback.lift eW eW rfl
    have hv0 : v0 ≫ m = (lift (η[G]) (η[G]) : 𝟙_ (Over S) ⟶ G ⊗ G).left := by
      apply pullback.hom_ext
      · simp [v0, m, heW, e]
      · simp [v0, m, heW, e]
    have hlift : lift (η[G]) (η[G]) ≫ μ[G] = (η[G] : 𝟙_ (Over S) ⟶ G) := by
      have := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over S))) (η[G] : 𝟙_ (Over S) ⟶ G)
      rwa [Category.id_comp] at this
    have hes : e s ∈ P := by
      refine ⟨m (v0 s), ⟨v0 s, ?_, rfl⟩, ?_⟩
      · show f00 (v0 s) = s
        have hlf : (lift (η[G]) (η[G]) : 𝟙_ (Over S) ⟶ G ⊗ G).left ≫ pullback.fst G.hom G.hom = e := by
          have h0 := congrArg CommaMorphism.left
            (CartesianMonoidalCategory.lift_fst (η[G] : 𝟙_ (Over S) ⟶ G) (η[G] : 𝟙_ (Over S) ⟶ G))
          exact h0
        rw [← hm, ← Scheme.Hom.comp_apply v0 m, hv0]
        show G.hom (pullback.fst G.hom G.hom
          ((lift (η[G]) (η[G]) : 𝟙_ (Over S) ⟶ G ⊗ G).left s)) = s
        rw [← Scheme.Hom.comp_apply (lift (η[G]) (η[G]) : 𝟙_ (Over S) ⟶ G ⊗ G).left
          (pullback.fst G.hom G.hom), hlf]
        exact he s
      · show μl (m (v0 s)) = e s
        rw [← Scheme.Hom.comp_apply v0 m, hv0, ← Scheme.Hom.comp_apply, ← Over.comp_left, hlift]
    -- `z ∈ m '' (f00⁻¹ {s})`
    have hz : z ∈ Set.range m := by
      rw [Scheme.Pullback.range_map]
      refine ⟨?_, ?_⟩
      · show pullback.fst G.hom G.hom z ∈ Set.range W.ι
        rw [Scheme.Opens.range_ι]; exact hz1
      · show pullback.snd G.hom G.hom z ∈ Set.range W.ι
        rw [Scheme.Opens.range_ι]; exact hz2
    obtain ⟨v, rfl⟩ := hz
    have hzP : μl (m v) ∈ P := ⟨m v, ⟨v, (hm v).symm, rfl⟩, rfl⟩
    have := hP.subset_connectedComponentIn hes hPsub hzP
    show μl (m v) ∈ connectedComponentIn (G.hom ⁻¹' {G.hom (μl (m v))}) (e (G.hom (μl (m v))))
    rw [hμ]
    exact this
  · intro x hx
    let ιl := (GrpObj.inv : G ⟶ G).left
    have hι : ∀ y, G.hom (ιl y) = G.hom y := by
      intro y
      rw [← Scheme.Hom.comp_apply, Over.w]
    let C := connectedComponentIn (G.hom ⁻¹' {G.hom x}) (e (G.hom x))
    have hC : _root_.IsPreconnected (ιl '' C) :=
      isPreconnected_connectedComponentIn.image _ ιl.continuous.continuousOn
    have hsub : ιl '' C ⊆ G.hom ⁻¹' {G.hom x} := by
      rintro _ ⟨y, hy, rfl⟩
      show G.hom (ιl y) = G.hom x
      rw [hι]
      exact connectedComponentIn_subset (G.hom ⁻¹' {G.hom x}) _ hy
    have hes : e (G.hom x) ∈ ιl '' C := by
      refine ⟨e (G.hom x), mem_connectedComponentIn (he _), ?_⟩
      show ιl (e (G.hom x)) = e (G.hom x)
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.one_inv]
    have := hC.subset_connectedComponentIn hes hsub ⟨x, hx, rfl⟩
    show ιl x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom (ιl x)}) (e (G.hom (ιl x)))
    rw [hι]
    exact this

variable {k : Type} [Field k]

theorem idCompSet_eq_cc (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (s : Spec (CommRingCat.of k)) :
    idCompSet G = connectedComponent ((η[G] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G).left s) := by
  ext x
  have h1 : G.hom.base ⁻¹' {G.hom.base x} = Set.univ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have h2 : G.hom.base x = s := Subsingleton.elim _ _
  show x ∈ connectedComponentIn (G.hom.base ⁻¹' {G.hom.base x}) _ ↔ _
  rw [h1, connectedComponentIn_univ, h2]

variable (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]

theorem isOpen_idCompSet : IsOpen (idCompSet G) := by
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : IsNoetherian G.left := {}
  rw [idCompSet_eq_cc G default]
  exact AVGlue.isOpen_connectedComponent_of_noetherian _

theorem isClosed_idCompSet : IsClosed (idCompSet G) := by
  rw [idCompSet_eq_cc G default]; exact isClosed_connectedComponent

/-- `G⁰`, as an open of `G`. -/
abbrev W0 : G.left.Opens := ⟨idCompSet G, isOpen_idCompSet G⟩

theorem isSubgroupOpen_W0 (hG : AVGlue.GeomConnOfRationalPoint) : IsSubgroupOpen G (W0 G) :=
  isSubgroupOpen_of_isOpen hG G (isOpen_idCompSet G)

theorem connectedSpace_W0 : ConnectedSpace (W0 G).toScheme := by
  have hc : _root_.IsConnected (idCompSet G) := by
    rw [idCompSet_eq_cc G default]; exact isConnected_connectedComponent
  have himg : (W0 G).ι '' Set.univ = idCompSet G := by
    rw [Set.image_univ, Scheme.Opens.range_ι]; rfl
  rw [← himg] at hc
  exact connectedSpace_iff_univ.mpr
    ⟨hc.1.of_image, ((W0 G).ι.isOpenEmbedding.isInducing.isPreconnected_image).mp hc.2⟩

end IdComp

/-! ## §8. The kernel commutes with base change -/

section KerBC

variable {k k' : Type} [Field k] [Field k'] (φ : k →+* k')

/-- **Smooth connected affine kernels stay so after a field extension** (connectedness from Stacks 04KV). -/
theorem isSmoothConnAffineKer_bc (hG : AVGlue.GeomConnOfRationalPoint)
    {U B : Over (Spec (CommRingCat.of k))} [GrpObj U] [GrpObj B] (π : U ⟶ B) [IsMonHom π]
    (h : IsSmoothConnAffineKer π) :
    letI : GrpObj ((Over.pullback (sφ φ)).obj B) := Functor.grpObjObj
    IsSmoothConnAffineKer ((Over.pullback (sφ φ)).map π) := by
  letI : GrpObj ((Over.pullback (sφ φ)).obj B) := Functor.grpObjObj
  obtain ⟨hs, ha, hc⟩ := h
  let F := Over.pullback (sφ φ)
  have h1 : IsPullback (F.map (pullback.fst π η[B])) (F.map (pullback.snd π η[B])) (F.map π)
      (F.map η[B]) := (IsPullback.of_hasPullback π η[B]).map F
  have h2 : IsPullback (F.map (pullback.fst π η[B])) (toUnit (F.obj (kerObj π))) (F.map π)
      η[F.obj B] := by
    refine IsPullback.of_iso h1 (Iso.refl _) (Iso.refl _) (Functor.Monoidal.εIso F).symm (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp
    · exact toUnit_unique _ _
    · simp
    · change F.map η[B] ≫ 𝟙 _ = (Functor.Monoidal.εIso F).inv ≫ (Functor.LaxMonoidal.ε F ≫ F.map η[B])
      rw [Category.comp_id, ← Functor.Monoidal.εIso_hom, Iso.inv_hom_id_assoc]
  let E : F.obj (kerObj π) ≅ kerObj (F.map π) := h2.isoPullback
  -- properties of `F.obj (kerObj π) = kerObj π ×_k k'`
  haveI := hs
  haveI := ha
  have hsF : Smooth (F.obj (kerObj π)).hom := by
    change Smooth (pullback.snd (kerObj π).hom (sφ φ)); infer_instance
  have haF : IsAffine (F.obj (kerObj π)).left := by
    change IsAffine (pullback (kerObj π).hom (sφ φ))
    haveI : IsAffineHom (pullback.snd (kerObj π).hom (sφ φ)) := inferInstance
    exact isAffine_of_isAffineHom (pullback.snd (kerObj π).hom (sφ φ))
  have hcF : ConnectedSpace (F.obj (kerObj π)).left := by
    let sec : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ kerObj π :=
      pullback.lift η[U] (𝟙 _) (by rw [IsMonHom.one_hom π, Category.id_comp])
    have hsec : sec.left ≫ (kerObj π).hom = 𝟙 _ := Over.w sec
    have hgc : GeometricallyConnected (kerObj π).hom :=
      hG k (kerObj π).left (kerObj π).hom sec.left hsec inferInstance inferInstance hc
    exact hgc.geometrically_connectedSpace (sφ φ)
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hw : (kerObj (F.map π)).hom = E.inv.left ≫ (F.obj (kerObj π)).hom := (Over.w E.inv).symm
  haveI : IsIso E.hom.left := by change IsIso ((Over.forget _).map E.hom); infer_instance
  haveI : IsIso E.inv.left := by change IsIso ((Over.forget _).map E.inv); infer_instance
  refine ⟨?_, ?_, ?_⟩
  · rw [hw]; infer_instance
  · exact IsAffine.of_isIso E.inv.left
  · exact (E.hom.left.surjective).connectedSpace E.hom.left.continuous

end KerBC

/-! ## §9. The leaf, and the glue Prop from it -/

section Leaf

variable {k : Type} [Field k]

/-- `π : G → B` presents the abelian variety `B` as a quotient `G/H` by a smooth connected affine normal subgroup
`H`: `π` is a faithfully flat homomorphism whose scheme-theoretic kernel `H` is smooth, connected and affine. -/
def IsChevalleyQuotient {G : Over (Spec (CommRingCat.of k))} [GrpObj G] (B : PkgI3.AbVar k)
    (π : G ⟶ B.X) : Prop :=
  IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧ IsSmoothConnAffineKer π

end Leaf

/-- **LEAF `ChevalleyPerfect`** (Chevalley's structure theorem for algebraic groups over a perfect field;
B. Conrad, "A modern proof of Chevalley's theorem on algebraic groups", J. Ramanujan Math. Soc. 17 (2002), 1-18,
Thm. 1.1; J. S. Milne, *Algebraic Groups* (Cambridge, 2017), Thm. 8.27; originally Chevalley (1960) and Rosenlicht
(1956). Theorem numbers recalled without network: UNVERIFIED.)

*Printed* (as recalled): let `G` be a smooth connected group scheme of finite type over a perfect field `k`. There
is a unique normal smooth connected affine closed subgroup `H ⊆ G` such that `G/H` is an abelian variety.

*Lean form*, for `G` smooth (`Smooth G.hom`, which includes locally of finite presentation), quasi-compact (so of
finite type) and connected over a perfect field `k`:
* existence: an abelian variety `B` (`PkgI3.AbVar`: proper, smooth, geometrically integral group scheme) and a
  faithfully flat homomorphism `π : G → B` whose scheme-theoretic kernel `ker π = G ×_B Spec k` (`kerObj`) is
  smooth, connected and affine (`IsChevalleyQuotient`);
* uniqueness: two such presentations `π₁, π₂` have the same kernel, on points with values in every `k`-scheme `T`.

*Reading*: "`G/H` is an abelian variety" is read as "there is a faithfully flat homomorphism from `G` onto an
abelian variety with kernel `H`". This is how quotients are defined (Milne, *Algebraic Groups*, §5.c: a quotient
map is a faithfully flat homomorphism, and its target is `G/ker`; SGA 3 VI_A 3.2-5.4; UNVERIFIED numbers): the
quotient map `G → G/H` is faithfully flat with kernel `H`, and conversely a faithfully flat `π : G → B` with kernel
`H` identifies `B` with `G/H`. Under this reading the existence clause is the existence half of the print, and the
uniqueness clause is the uniqueness half (`ker π₁ = H₁ = H₂ = ker π₂`, here only on points). It is never stronger
than the print. Commutativity of `G` is not assumed (Chevalley does not need it). -/
def ChevalleyPerfect : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
    Smooth G.hom → QuasiCompact G.hom → ConnectedSpace G.left →
    (∃ (B : PkgI3.AbVar k) (π : G ⟶ B.X), IsChevalleyQuotient B π) ∧
    ∀ (B₁ B₂ : PkgI3.AbVar k) (π₁ : G ⟶ B₁.X) (π₂ : G ⟶ B₂.X),
      IsChevalleyQuotient B₁ π₁ → IsChevalleyQuotient B₂ π₂ →
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G), x ≫ π₁ = 1 ↔ x ≫ π₂ = 1

theorem isMonHom_of_comp_mono {C : Type*} [Category C] [CartesianMonoidalCategory C] {A B D : C}
    [MonObj A] [MonObj B] [MonObj D] (f : A ⟶ B) (m : B ⟶ D) [Mono m] [IsMonHom m] [IsMonHom (f ≫ m)] :
    IsMonHom f where
  one_hom := by
    rw [← cancel_mono m, Category.assoc, IsMonHom.one_hom (f ≫ m), IsMonHom.one_hom m]
  mul_hom := by
    rw [← cancel_mono m, Category.assoc, IsMonHom.mul_hom (f ≫ m), Category.assoc, IsMonHom.mul_hom m,
      ← Category.assoc, tensorHom_comp_tensorHom]

open CToPrinted in
/-- **`SemiAbelianDescendsPerfect` from Chevalley's theorem over a perfect field.** -/
theorem semiAbelianDescendsPerfect_of_chevalley (hC : ChevalleyPerfect) :
    ZInQ.HeightFix.SemiAbelianDescendsPerfect := by
  intro k _ _ G _ _ _ hbar
  have hG : AVGlue.GeomConnOfRationalPoint := geomConnOfRationalPoint_proof
  let φ := φbar k
  let F := Over.pullback (sφ φ)
  letI : GrpObj (F.obj G) := Functor.grpObjObj
  obtain ⟨U', _, inc', hoi', hmh', hcon', B', π', hπm', hfl', hsu', r, e', he_inj', he_ker', he_nat'⟩ :=
    hbar
  haveI := hoi'
  haveI : LocallyOfFiniteType (F.obj G).hom := by
    change LocallyOfFiniteType (pullback.snd G.hom (sφ φ)); infer_instance
  haveI : QuasiCompact (F.obj G).hom := by
    change QuasiCompact (pullback.snd G.hom (sφ φ)); infer_instance
  -- (a) `G⁰` over `k`
  have hW := isSubgroupOpen_W0 G hG
  letI : GrpObj (OpenSub.G0 (W0 G)) := OpenSub.grpG0 hW
  have hinc : IsMonHom (OpenSub.incl (W0 G)) := OpenSub.isMonHom_incl hW
  let U := OpenSub.G0 (W0 G)
  let incl : U ⟶ G := OpenSub.incl (W0 G)
  haveI : IsOpenImmersion incl.left := inferInstanceAs (IsOpenImmersion (W0 G).ι)
  haveI : LocallyOfFiniteType ((W0 G).ι ≫ G.hom) := inferInstance
  haveI : QuasiCompact ((W0 G).ι ≫ G.hom) := quasiCompact_of_openImm incl
  haveI : LocallyOfFiniteType U.hom := inferInstanceAs (LocallyOfFiniteType ((W0 G).ι ≫ G.hom))
  haveI : QuasiCompact U.hom := inferInstanceAs (QuasiCompact ((W0 G).ι ≫ G.hom))
  have hconnU : ConnectedSpace U.left := connectedSpace_W0 G
  letI : GrpObj (F.obj U) := Functor.grpObjObj
  have hconnFU : ConnectedSpace (F.obj U).left :=
    connectedSpace_pullback_idComp hG G (W0 G) rfl (AlgebraicClosure k) (sφ φ)
  haveI : QuasiCompact (F.obj U).hom := by
    change QuasiCompact (pullback.snd U.hom (sφ φ)); infer_instance
  -- (b) `U' = (G⁰)_{k̄}` inside `G_{k̄}`
  let p := pullback.fst G.hom (sφ φ)
  have hsq := pbmap_isPullback (sφ φ) U G incl
  haveI hFinc : IsOpenImmersion (F.map incl).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq (inferInstanceAs (IsOpenImmersion (W0 G).ι))
  have hrangeU : Set.range (F.map incl).left = p ⁻¹' (idCompSet G) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      show p ((F.map incl).left y) ∈ idCompSet G
      rw [← Scheme.Hom.comp_apply, ← hsq.w, Scheme.Hom.comp_apply]
      have : incl.left (pullback.fst U.hom (sφ φ) y) ∈ Set.range (W0 G).ι := ⟨_, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    · intro hx
      have hx' : p x ∈ Set.range (W0 G).ι := by rw [Scheme.Opens.range_ι]; exact hx
      obtain ⟨u, hu⟩ := hx'
      obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := incl.left) (g := p) u x hu
      refine ⟨hsq.isoPullback.inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_snd, hz2]
  let pt : (𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure k))))).left :=
    (default : Spec (CommRingCat.of (AlgebraicClosure k)))
  let ebar := (η[F.obj G] : 𝟙_ _ ⟶ F.obj G).left pt
  have he1 : ebar ∈ Set.range inc'.left :=
    ⟨(η[U'] : 𝟙_ _ ⟶ U').left pt, by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsMonHom.one_hom inc']⟩
  have he2 : ebar ∈ p ⁻¹' idCompSet G := by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, unit_bc_fst, Scheme.Hom.comp_apply]
    exact idCompSet_one G _
  have hclo : IsClopen (p ⁻¹' idCompSet G) :=
    ⟨(isClosed_idCompSet G).preimage p.continuous, (isOpen_idCompSet G).preimage p.continuous⟩
  have hsub1 : Set.range inc'.left ⊆ p ⁻¹' idCompSet G :=
    (isConnected_range inc'.left.continuous).isPreconnected.subset_isClopen hclo ⟨ebar, he1, he2⟩
  have hR'clo : IsClopen (Set.range inc'.left) :=
    ⟨isClosed_range_openSubgroup inc', inc'.left.isOpenEmbedding.isOpen_range⟩
  have hpre : _root_.IsPreconnected (p ⁻¹' idCompSet G) := by
    rw [← hrangeU]; exact (isConnected_range (F.map incl).left.continuous).isPreconnected
  have hsub2 : p ⁻¹' idCompSet G ⊆ Set.range inc'.left :=
    hpre.subset_isClopen hR'clo ⟨ebar, he2, he1⟩
  have heq : Set.range (F.map incl).left = Set.range inc'.left := by
    rw [hrangeU]; exact hsub2.antisymm hsub1
  let isoS := IsOpenImmersion.isoOfRangeEq (F.map incl).left inc'.left heq
  have hfac : isoS.hom ≫ inc'.left = (F.map incl).left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let φU : F.obj U ≅ U' := Over.isoMk isoS (by
    have h1 : U'.hom = inc'.left ≫ (F.obj G).hom := (Over.w inc').symm
    rw [h1, ← Category.assoc, hfac]; exact Over.w (F.map incl))
  have hφU : φU.hom ≫ inc' = F.map incl := by
    apply Over.OverMorphism.ext; exact hfac
  haveI : Mono inc' := ⟨fun g h hgh => Over.OverMorphism.ext ((cancel_mono inc'.left).mp
    (by simpa using congrArg CommaMorphism.left hgh))⟩
  haveI : IsMonHom (φU.hom ≫ inc') := by rw [hφU]; infer_instance
  haveI : IsMonHom φU.hom := isMonHom_of_comp_mono φU.hom inc'
  haveI : IsMonHom (φU.inv ≫ φU.hom) := by rw [Iso.inv_hom_id]; infer_instance
  haveI : IsMonHom φU.inv := isMonHom_of_comp_mono φU.inv φU.hom
  -- (c) the kernels of `π'` and of `φU ≫ π'` are split tori
  have hkerπ' := isSmoothConnAffineKer_of_torus π' r e' he_inj' he_ker' he_nat'
  let e2 : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ F.obj U) :=
    fun R _ _ => (IsMonHom.monoidHom φU.inv (algPt _ R)).comp (e' R)
  have he2_apply : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] (t : Fin r → Rˣ),
      e2 R t = e' R t ≫ φU.inv := fun _ _ _ _ => rfl
  have he_inj2 : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      Function.Injective (e2 R) := by
    intro R _ _ t₁ t₂ h
    rw [he2_apply, he2_apply] at h
    exact he_inj' R ((cancel_mono φU.inv).mp h)
  have he_ker2 : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R]
      (u : algPt (AlgebraicClosure k) R ⟶ F.obj U), u ≫ (φU.hom ≫ π') = 1 ↔ u ∈ (e2 R).range := by
    intro R _ _ u
    rw [← Category.assoc, he_ker' R (u ≫ φU.hom)]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by rw [he2_apply, ht, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, by rw [he2_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩
  have he_nat2 : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
      [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
      e2 S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e2 R t := by
    intro R S _ _ _ _ f t
    rw [he2_apply, he2_apply, he_nat', Category.assoc]
  have hker2 := isSmoothConnAffineKer_of_torus (φU.hom ≫ π') r e2 he_inj2 he_ker2 he_nat2
  -- (d) smoothness: `U'`, `(G⁰)_{k̄}`, `G⁰`
  haveI : LocallyOfFiniteType U'.hom := by rw [← Over.w inc']; infer_instance
  haveI : QuasiCompact U'.hom := quasiCompact_of_openImm inc'
  haveI : IsLocallyNoetherian U'.left := LocallyOfFiniteType.isLocallyNoetherian U'.hom
  haveI : CompactSpace U'.left := QuasiCompact.compactSpace_of_compactSpace U'.hom
  haveI : IsNoetherian U'.left := {}
  have hsmU' : Smooth U'.hom := smooth_of_smoothKer π' hfl' hsu' inferInstance hkerπ'.1
  have hsmFU : Smooth (F.obj U).hom := by
    rw [← Over.w φU.hom]
    haveI : IsIso φU.hom.left := by change IsIso ((Over.forget _).map φU.hom); infer_instance
    infer_instance
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (sφ φ) :=
    ⟨⟨⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩, inferInstance⟩, inferInstance⟩
  have hsmU : Smooth U.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := U.hom) (g := sφ φ) hQ hsmFU
  -- (e) Chevalley over `k`, and uniqueness over `k̄`
  obtain ⟨⟨B, π, hπm, hπfl, hπsu, hπker⟩, -⟩ := hC k U hsmU inferInstance hconnU
  haveI := hπm
  letI : GrpObj (F.obj B.X) := Functor.grpObjObj
  let Bk : PkgI3.AbVar (AlgebraicClosure k) :=
    { X := F.obj B.X
      grp := Functor.grpObjObj
      proper := by change IsProper (pullback.snd B.X.hom (sφ φ)); infer_instance
      smooth := by change Smooth (pullback.snd B.X.hom (sφ φ)); infer_instance
      geomInt := by change GeometricallyIntegral (pullback.snd B.X.hom (sφ φ)); infer_instance }
  have hq1 : IsChevalleyQuotient Bk (F.map π) :=
    ⟨inferInstanceAs (IsMonHom (F.map π)),
      MorphismProperty.of_isPullback (P := @Flat) (pbmap_isPullback _ _ _ π) hπfl,
      MorphismProperty.of_isPullback (P := @Surjective) (pbmap_isPullback _ _ _ π) hπsu,
      isSmoothConnAffineKer_bc φ hG π hπker⟩
  haveI : IsIso φU.hom.left := by change IsIso ((Over.forget _).map φU.hom); infer_instance
  have hq2 : IsChevalleyQuotient B' (φU.hom ≫ π') := by
    refine ⟨inferInstance, ?_, ?_, hker2⟩
    · haveI := hfl'; change Flat (φU.hom.left ≫ π'.left); infer_instance
    · haveI := hsu'; change Surjective (φU.hom.left ≫ π'.left); infer_instance
  have huniq := (hC (AlgebraicClosure k) (F.obj U) hsmFU inferInstance hconnFU).2 Bk B' (F.map π)
    (φU.hom ≫ π') hq1 hq2
  -- (f) assemble
  refine ⟨U, inferInstance, incl, inferInstanceAs (IsOpenImmersion (W0 G).ι), hinc, hconnU, B, π, hπm,
    hπfl, hπsu, r, fun R _ _ => (Φ φ U R).toMonoidHom.comp (e2 R), ?_, ?_, ?_⟩
  · intro R _ _
    exact (Φ φ U R).injective.comp (he_inj2 R)
  · intro R _ _ u
    letI := algK φ R
    have h1 : u ≫ π = 1 ↔ (Φ φ U R).symm u ≫ F.map π = 1 := by
      constructor
      · intro h
        apply (Φ φ B.X R).injective
        rw [Φ_comp, MulEquiv.apply_symm_apply, h, map_one]
      · intro h
        have := congrArg (Φ φ B.X R) h
        rwa [Φ_comp, MulEquiv.apply_symm_apply, map_one] at this
    rw [h1, huniq, he_ker2]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by simp [ht]⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply] at ht
      rw [← ht, MulEquiv.symm_apply_apply]
  · intro R S _ _ _ _ f t
    letI := algK φ R
    letI := algK φ S
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [he_nat2 R S f t, Φ_natural]

/-! ## §10. The fields, with no glue -/

section Fields

open ZInQ.HeightFix

/-- **The field `bostLowerBound`** from height-fix's printed leaf, the two textbook fields for T35 and the leaf
`ChevalleyPerfect` (the glue `SemiAbelianDescendsPerfect` is proved). -/
theorem bostLowerBound_of_printed_chevalley (hB : BostLowerBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hMT : AvSplit.MumfordTorsionAlgClosed)
    (hC : ChevalleyPerfect) : ZInQ.HeightSplit.BostLowerBound :=
  bostLowerBound_of_printed hB hUL hMT (semiAbelianDescendsPerfect_of_chevalley hC)

/-- **The field `gaudronRemondThm14`**, likewise. -/
theorem gaudronRemondThm14_of_printed_chevalley (hGR : GaudronRemondThm14Printed)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hMT : AvSplit.MumfordTorsionAlgClosed)
    (hC : ChevalleyPerfect) : ZInQ.HeightSplit.GaudronRemondThm14 :=
  gaudronRemondThm14_of_printed hGR hUL hMT (semiAbelianDescendsPerfect_of_chevalley hC)

/-- The optional field `javanpeykarBound`, likewise. -/
theorem javanpeykarBound_of_printed_chevalley (hJ : JavanpeykarBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hMT : AvSplit.MumfordTorsionAlgClosed)
    (hC : ChevalleyPerfect) : ZInQ.HeightSplit.JavanpeykarBound :=
  javanpeykarBound_of_printed hJ hUL hMT (semiAbelianDescendsPerfect_of_chevalley hC)

/-- The optional field `pazukiCor13Upper`, likewise. -/
theorem pazukiCor13Upper_of_printed_chevalley (hP : PazukiCor13UpperPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hMT : AvSplit.MumfordTorsionAlgClosed)
    (hC : ChevalleyPerfect) : ZInQ.HeightSplit.PazukiCor13Upper :=
  pazukiCor13Upper_of_printed hP hUL hMT (semiAbelianDescendsPerfect_of_chevalley hC)

/-- The printed stable height is the kernel's, with `ChevalleyPerfect` in place of the glue. -/
theorem isPrintedStableHeight_iff_chevalley (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hGC : AVGlue.GeomConnOfRationalPoint) (hC : ChevalleyPerfect) {K : Type} [Field K]
    [NumberField K] (A : PkgI3.AbVar K) (x : ℝ) :
    IsPrintedStableHeight A x ↔ ZInQ.HeightSplit.IsStableFaltingsHeight A x :=
  isPrintedStableHeight_iff hT35 hGC (semiAbelianDescendsPerfect_of_chevalley hC) A x

end Fields

end ZInQ.SemiAbDescend


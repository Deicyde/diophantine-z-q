import ZInQKernel.Contrib.OneProof.FaltingsDict2SplitTorus
import ZInQKernel.Contrib.OneProof.FaltingsDict
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Kernel
import Mathlib.AlgebraicGeometry.Group.Abelian

/-! The scheme kernel and its geometric identification with the split torus. -/

noncomputable section

namespace ZInQ.FaltingsRestate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open DictModels.RaynaudOr ZInQ.HeightSplit ZInQ.SemiAbDescend
open ZInQ.Contrib.MilneQuasiInverse.Kernel

set_option linter.style.haveILetI false

variable {k : Type} [Field k]

local notation "Sch" => Over (Spec (CommRingCat.of k))

/-- The scheme kernel is the fibre product with the unit section, with
the group structure obtained from its group valued functor of points. -/
abbrev torusKernel {G B : Sch} [GrpObj G] [GrpObj B] (π : G ⟶ B) [IsMonHom π] :
    Grp Sch :=
  kernelGrp π

/-- The inclusion of the kernel in the source. -/
abbrev torusKernelι {G B : Sch} [GrpObj G] [GrpObj B] (π : G ⟶ B) [IsMonHom π] :
    (torusKernel π).X ⟶ G :=
  kernelInclusion π

/-- The fibre product that defines the kernel. -/
theorem torusKernel_isPullback {G B : Sch} [GrpObj G] [GrpObj B]
    (π : G ⟶ B) [IsMonHom π] :
    IsPullback (torusKernelι π) (toUnit (torusKernel π).X) π η[B] := by
  have h : pullback.snd π η[B] = toUnit (torusKernel π).X := Subsingleton.elim _ _
  rw [← h]
  exact IsPullback.of_hasPullback π η[B]

/-- The unit section is closed over a field, so the kernel inclusion is closed. -/
theorem torusKernel_isClosedImmersion {G B : Sch} [GrpObj G] [GrpObj B]
    (π : G ⟶ B) [IsMonHom π] :
    IsClosedImmersion (torusKernelι π).left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (kernel_isPullback π).flip inferInstance

/-- On every test scheme, the represented points of the fibre product are
the group kernel of postcomposition with the quotient. -/
def torusKernel_points {G B : Sch} [GrpObj G] [GrpObj B]
    (π : G ⟶ B) [IsMonHom π] (X : Sch) :
    letI : GrpObj (torusKernel π).X := (torusKernel π).grp
    (X ⟶ (torusKernel π).X) ≃* (pointsMap π X).ker :=
  kernelPointsMulEquiv π X

/-- Equality is detected by affine test schemes, since the source has an affine open cover. -/
private theorem hom_ext_of_algPt {X Y : Sch} {f g : X ⟶ Y}
    (h : ∀ (R : Type) [CommRing R] [Algebra k R] (p : algPt k R ⟶ X), p ≫ f = p ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (cov X) _ _ fun x => ?_
  letI := isAffine_coverObj X x
  obtain ⟨R, _, _, ⟨a⟩⟩ := exists_iso_algPt (coverObj X x)
  have he := h R (a.inv ≫ coverMap X x)
  rw [Category.assoc, Category.assoc, cancel_epi] at he
  exact congrArg CommaMorphism.left he

/-- A natural monoid map from tuples of units to a represented kernel
determines a group scheme isomorphism, by evaluating at the universal tuple. -/
private theorem torusIso_of_points {P G B : Sch} [GrpObj P] [GrpObj G] [GrpObj B]
    (i : P ⟶ G) [IsMonHom i] [Mono i] (π : G ⟶ B)
    (hi : i ≫ π = 1)
    (liftKernel : ∀ {X : Sch} (u : X ⟶ G), u ≫ π = 1 → ∃ v : X ⟶ P, v ≫ i = u)
    (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra k R],
      (Fin r → Rˣ) →* (algPt k R ⟶ G))
    (he : ∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R))
    (hk : ∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ G),
      u ≫ π = 1 ↔ u ∈ (e R).range)
    (hn : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
      (f : R →ₐ[k] S) (t : Fin r → Rˣ),
      e S (fun j => Units.map (f : R →* S) (t j)) = algPtMap f ≫ e R t) :
    Nonempty (Grp.mk (splitTorus k r) ≅ Grp.mk P) := by
  let A := TorusRing k r
  let M := splitTorus k r
  let u : Fin r → Aˣ := splitTorusPoints A (𝟙 M)
  obtain ⟨m, hm⟩ := liftKernel (X := M) (e A u) ((hk A _).mpr ⟨u, rfl⟩)
  have formula (R : Type) [CommRing R] [Algebra k R] (x : algPt k R ⟶ M) :
      x ≫ m ≫ i = e R (splitTorusPoints R x) := by
    obtain ⟨f, hx⟩ := exists_algPtMap (K := k) (R := R) (S := A) x
    calc
      x ≫ m ≫ i = x ≫ e A u := congrArg (x ≫ ·) hm
      _ = algPtMap f ≫ e A u := congrArg (fun (z : algPt k R ⟶ M) => z ≫ e A u) hx
      _ = e R (fun j => Units.map (f : A →* R) (u j)) := (hn A R f u).symm
      _ = e R (splitTorusPoints R x) := by
        rw [← splitTorusPoints_natural (p := 𝟙 M)]
        have hx' : algPtMap (k := k) f ≫ 𝟙 M = x := (Category.comp_id _).trans hx.symm
        exact congrArg (fun z : algPt k R ⟶ M => e R (splitTorusPoints R z)) hx'
  have mOne (R : Type) [CommRing R] [Algebra k R] :
      (1 : algPt k R ⟶ M) ≫ m = 1 :=
    (cancel_mono i).mp (by rw [Category.assoc, formula, map_one, map_one, MonObj.one_comp])
  have mMul (R : Type) [CommRing R] [Algebra k R] (x y : algPt k R ⟶ M) :
      (x * y) ≫ m = (x ≫ m) * (y ≫ m) :=
    (cancel_mono i).mp (by
      rw [Category.assoc, formula, map_mul, map_mul, MonObj.mul_comp]
      simp only [Category.assoc, formula])
  haveI : IsMonHom m := by
    constructor
    · apply hom_ext_of_algPt
      intro R _ _ x
      simp only [← Category.assoc, MonObj.one_eq_one, MonObj.comp_one]
      exact mOne R
    · apply hom_ext_of_algPt
      intro R _ _ x
      simp only [← Category.assoc, MonObj.mul_eq_mul, MonObj.comp_mul]
      simpa only [tensorHom_fst, tensorHom_snd, Category.assoc] using mMul R
        (x ≫ fst M M) (x ≫ snd M M)
  haveI : IsIso m := isIso_of_bijective_affine m (bijective_affine_of_algPt m (fun R _ _ => by
    constructor
    · intro x y hxy
      have eq := congrArg (fun z => z ≫ i) hxy
      simp only [Category.assoc, formula] at eq
      exact (splitTorusPoints R).injective (he R eq)
    · intro v
      obtain ⟨t, ht⟩ := (hk R (v ≫ i)).mp (by rw [Category.assoc, hi, MonObj.comp_one])
      refine ⟨(splitTorusPoints R).symm t, (cancel_mono i).mp ?_⟩
      rw [Category.assoc, formula, MulEquiv.apply_symm_apply, ht]))
  exact ⟨Grp.mkIso' (asIso m)⟩

/-- An extension of an abelian variety by a torus as group schemes. The
quotient is faithfully flat, the inclusion is a closed immersion and the
pullback of the unit section, and the kernel is geometrically split. -/
def HasTorusExtensionScheme (G : Sch) [GrpObj G] : Prop :=
  ∃ (B : PkgI3.AbVar k) (π : G ⟶ B.X) (_ : IsMonHom π),
    Flat π.left ∧ Surjective π.left ∧
      ∃ (T : Grp Sch) (i : T.X ⟶ G) (_ : IsMonHom i),
        IsClosedImmersion i.left ∧ IsPullback i (toUnit T.X) π η[B.X] ∧
        ∃ r : ℕ, Nonempty
          (Grp.mk (splitTorus (AlgebraicClosure k) r) ≅
            (Over.pullback (sφ (φbar k))).mapGrp.obj T)

/-- The pointwise torus extension on the whole group gives a faithfully
flat quotient whose scheme kernel is a torus. -/
theorem hasTorusExtensionScheme_of_hasTorusExtension
    (G : Sch) [GrpObj G] (h : HasTorusExtension G) : HasTorusExtensionScheme G := by
  obtain ⟨B, π, hπ, hf, hs, r, e, he, hk, hn⟩ := h
  letI := hπ
  let φ := φbar k
  let F := Over.pullback (sφ φ)
  let T := torusKernel π
  letI : GrpObj T.X := T.grp
  haveI : IsMonHom (torusKernelι π) := kernelInclusion_isMonHom π
  letI : GrpObj (F.obj G) := Functor.grpObjObj
  letI : GrpObj (F.obj B.X) := Functor.grpObjObj
  letI : GrpObj (F.obj T.X) := Functor.grpObjObj
  refine ⟨B, π, hπ, hf, hs, T, torusKernelι π, inferInstance,
    torusKernel_isClosedImmersion π, torusKernel_isPullback π, r, ?_⟩
  let p := (torusKernel_isPullback π).map F
  have hunit : F.map η[B.X] = 1 := by rw [MonObj.one_eq_one, Functor.map_one]
  haveI : Mono (F.map (torusKernelι π)) := p.mono_fst_of_mono
  have hi : F.map (torusKernelι π) ≫ F.map π = 1 := by rw [p.w, hunit, MonObj.comp_one]
  let E (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] :
      (Fin r → Rˣ) →* (algPt (AlgebraicClosure k) R ⟶ F.obj G) :=
    letI := algK φ R
    (Φ φ G R).symm.toMonoidHom.comp (e R)
  refine torusIso_of_points (F.map (torusKernelι π)) (F.map π) hi ?_ r E ?_ ?_ ?_
  · intro X u hu
    let v : X ⟶ F.obj (𝟙_ Sch) := toUnit X ≫ Functor.LaxMonoidal.ε F
    exact ⟨p.lift u v (by rw [hu, hunit, MonObj.comp_one]), p.lift_fst _ _ _⟩
  · intro R _ _
    exact (Φ φ G R).symm.injective.comp (he R)
  · intro R _ _ u
    letI := algK φ R
    rw [← (Φ φ B.X R).injective.eq_iff, Φ_comp, map_one, hk]
    change (∃ a, e R a = Φ φ G R u) ↔ ∃ a, (Φ φ G R).symm (e R a) = u
    simp only [MulEquiv.symm_apply_eq]
  · intro R S _ _ _ _ f t
    letI := algK φ R
    letI := algK φ S
    apply (Φ φ G S).injective
    rw [Φ_natural]
    change Φ φ G S ((Φ φ G S).symm (e S _)) = _ ≫ Φ φ G R ((Φ φ G R).symm (e R t))
    simpa only [MulEquiv.apply_symm_apply] using hn R S f t

end ZInQ.FaltingsRestate

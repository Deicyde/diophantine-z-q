import ZInQKernel.OneProof.H.TailZ23
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.RepresentableGroup
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Field
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.QuasiProjective
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist
import ZInQKernel.Contrib.FrobChain.Rigidity
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Invertible
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.CoordinateCover
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Embedding
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Relative
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ClearDenominators
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.GlobalSection
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Morphisms.ImmersionAffine
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Group
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocusFunctorial

/-! # OneProof H, leaf-fold14 (2/2): the t09-pic fold, `OpenAddedLeaves13` and `sixContactMin_of_open18`

t09-pic (docs/research/t09-pic.md; `scratch/t09-pic/Pic.lean`, copied below as namespace `T09Pic` without its §0 (a
verbatim copy of the field's type, checked there by `rfl`), the six-way split of L4 and the `#print` lines) proves the
added field `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` (GLUE; Mumford §§6, 8, 20, 23) from four printed
leaves over the vendored relative Picard functor (`ZInQKernel/Contrib/CloudW07JacobiansCurves/`):
* L1 `T09Pic.PicRepresentableAbVar` (Grothendieck–Murre–Oort representability),
* L2 `T09Pic.PicZeroAbVar` (`Pic⁰` is an abelian variety),
* L3 `T09Pic.PhiAmpleIsogeny` (`φ_L` is an isogeny for ample `L`),
* L4 `T09Pic.WeilPairingMumford` (the properties of Mumford's `ē_n`, pinned to the genuine `weilScalar`),
by `T09Pic.t09SymmIsogenyExists_of_four` (very ample ⇒ ample is proved there). `OpenAddedLeaves13` is
`OpenAddedLeaves12` with the field replaced by the four leaves; `sixContactMin_of_open18` calls
`sixContactMin_of_open17`. docs/research/leaf-fold14.md lists the fields. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace T09Pic

open PkgI3 PkgI3.AbVar

variable {K : Type} [Field K]

/-! ## §1. Genuine definitions -/

/-- **The Mumford bundle** `Λ(L) = m^*L ⊗ p₁^*L⁻¹ ⊗ p₂^*L⁻¹` on `A ×_K A` (Mumford, *Abelian
varieties*, §8, (iv); UNVERIFIED numbering). -/
def mumfordBundle (A : AbVar K) (L : A.X.left.Pic) : (pullback A.X.hom A.X.hom).Pic :=
  (show (pullback A.X.hom A.X.hom).Pic from Scheme.Pic.map (μ[A.X]).left L) * (Scheme.Pic.map (pullback.fst A.X.hom A.X.hom) L)⁻¹ *
    (Scheme.Pic.map (pullback.snd A.X.hom A.X.hom) L)⁻¹

/-- **`φ_L : A → Pic_{A/K}`**: the morphism classifying the family `Λ(L)` on `A ×_K A` over the
second factor, through a representation of the Picard functor (Yoneda). On points,
`φ_L(x) = [t_x^*L ⊗ L⁻¹]` (Mumford §8). -/
def phiL {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (L : A.X.left.Pic) : A.X ⟶ P :=
  rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op A.X) (mumfordBundle A L))

/-- **The identity component** of a group scheme `G` over `K`: the connected component of the
identity point (the image of the unit section `Spec K → G`). -/
def identityComponent (G : Over (Spec (CommRingCat.of K))) [GrpObj G] : Set G.left :=
  {x | ∃ s : (𝟙_ (Over (Spec (CommRingCat.of K)))).left, x ∈ connectedComponent (η[G].left s)}

/-- **`(B, ι)` is the identity component `Pic⁰` of the Picard scheme `P`** (`P` represents the Picard
functor of `A` through `rep`, with its group law `picardFunctorCommGrpObj`): `ι : B → P` is an open
immersion onto the identity component and a homomorphism. This pins `(B, ι)` down up to unique
isomorphism. -/
def IsPicZero {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P) : Prop :=
  letI := picardFunctorCommGrpObj A.X.hom rep
  IsOpenImmersion j.left ∧ Set.range j.left = identityComponent P ∧ IsMonHom j

/-- **Very ample** (relative to `K`, finitely many coordinates): `L ≅ i^*𝒪(1)` for an immersion
`i : A → ℙ^N_K` over `K` (EGA II 4.4.2, Hartshorne II §7; UNVERIFIED numbering). Very ample implies
ample (Hartshorne II Thm 7.6; UNVERIFIED). -/
def IsVeryAmple (A : AbVar K) (L : A.X.left.Pic) : Prop :=
  ∃ (N : Type) (_ : Finite N) (i : A.X.left ⟶ ℙ(N; Spec (CommRingCat.of K))),
    IsImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = A.X.hom ∧
    L = Scheme.Pic.map i (Scheme.Pic.mk (ProjectiveSpace.twist N (Spec (CommRingCat.of K)) 1))

/-! ## §2. Glue (proved) -/

/-- **Every abelian variety over `K` has a very ample class** (proved from the vendored
`GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral`). -/
theorem exists_isVeryAmple (A : AbVar K) : ∃ L, IsVeryAmple A L := by
  obtain ⟨N, hN, i, hi, hover⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral A.X
  exact ⟨_, N, hN, i, hi, hover, rfl⟩


/-- Precomposition with `f : T' ⟶ T` classifies the pulled-back class (Yoneda + naturality of the
sheafification map). -/
lemma comp_classify {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {T T' : Over (Spec (CommRingCat.of K))}
    (f : T' ⟶ T) (c : (pullback A.X.hom T.hom).Pic) :
    f ≫ rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op T) c) =
      rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op T')
        (Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom f) c)) := by
  rw [rep.comp_homEquiv_symm]
  congr 1
  exact ((toPicardFunctor A.X.hom).naturality_apply f.op c).symm

/-- `Λ(L)` restricted to `A × {0}` is trivial. -/
lemma mumfordBundle_restrict_zero (A : AbVar K) (L : A.X.left.Pic) :
    Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom η[A.X]) (mumfordBundle A L) = 1 := by
  have h1 : JacobianChallenge.baseChangeMap A.X.hom η[A.X] = (A.X ◁ η[A.X]).left := by
    apply pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]
  have hμ : JacobianChallenge.baseChangeMap A.X.hom η[A.X] ≫ (μ[A.X]).left =
      JacobianChallenge.baseChangeMap A.X.hom η[A.X] ≫ pullback.fst A.X.hom A.X.hom := by
    rw [h1, ← Over.comp_left, MonObj.mul_one]
    simp
  have hsnd : JacobianChallenge.baseChangeMap A.X.hom η[A.X] ≫ pullback.snd A.X.hom A.X.hom =
      pullback.snd _ _ ≫ η[A.X].left := pullback.lift_snd _ _ _
  have hS : Scheme.Pic.map η[A.X].left L = 1 :=
    Subsingleton.elim (α := (Spec (CommRingCat.of K)).Pic) _ _
  rw [mumfordBundle, ← Scheme.Pic.mapHom_apply]
  simp only [map_mul, map_inv, Scheme.Pic.mapHom_apply, ← Scheme.Pic.map_comp, hμ, hsnd]
  rw [Scheme.Pic.map_comp (pullback.snd _ _) η[A.X].left, hS, Scheme.Pic.map_one]
  simp

/-- **`φ_L(0) = 0`**: `η_A ≫ φ_L = η_P` for the group law of the Picard scheme. -/
lemma eta_comp_phiL {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (L : A.X.left.Pic) :
    letI := picardFunctorCommGrpObj A.X.hom rep
    η[A.X] ≫ phiL rep L = η[P] := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  rw [phiL, comp_classify, mumfordBundle_restrict_zero]
  have h := (picardClassifyingHom A.X.hom rep (𝟙_ _)).map_one
  rw [picardClassifyingHom_apply] at h
  rw [h, show (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P) = CartesianMonoidalCategory.toUnit _ ≫ η from rfl]
  simp


/-- **`φ_L` factors through `Pic⁰` by a homomorphism** `λ_L : A → B`: `A` is connected and
`φ_L(0) = 0` (so the image lies in the identity component), `ι` is an open immersion onto it, and
the lift preserves `0`, hence is a homomorphism by rigidity
(`MulRigidity.isMonHom_of_geometricallyIntegral`, Mumford §4 Cor. 1). -/
theorem exists_hom_comp_eq_phiL {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} {j : B.X ⟶ P}
    (hj : IsPicZero rep B j) (L : A.X.left.Pic) :
    ∃ lam : Hom A B, lam.hom ≫ j = phiL rep L := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  obtain ⟨hopen, hrange, hmon⟩ := hj
  have h0 := eta_comp_phiL rep L
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  have hsub : Set.range (phiL rep L).left ⊆ Set.range j.left := by
    rw [hrange]
    rintro _ ⟨a, rfl⟩
    refine ⟨A.X.hom a, ?_⟩
    have he : η[P].left (A.X.hom a) = (phiL rep L).left (η[A.X].left (A.X.hom a)) := by
      rw [← h0]; rfl
    rw [he]
    exact (isPreconnected_range (phiL rep L).left.continuous).subset_connectedComponent
      ⟨_, rfl⟩ ⟨a, rfl⟩
  let l : A.X.left ⟶ B.X.left := IsOpenImmersion.lift j.left (phiL rep L).left hsub
  have hl : l ≫ j.left = (phiL rep L).left := IsOpenImmersion.lift_fac _ _ _
  have hw : l ≫ B.X.hom = A.X.hom := by
    rw [← Over.w j, ← Category.assoc, hl, Over.w]
  let lam : A.X ⟶ B.X := Over.homMk l hw
  have hlam : lam ≫ j = phiL rep L := Over.OverMorphism.ext hl
  have hη : η[A.X] ≫ lam = η[B.X] := by
    apply Over.OverMorphism.ext
    apply (cancel_mono j.left).1
    rw [Over.comp_left, Category.assoc]
    change η[A.X].left ≫ lam.left ≫ j.left = η[B.X].left ≫ j.left
    rw [← Over.comp_left, hlam, ← Over.comp_left, h0, ← Over.comp_left _ _ _ η[B.X] j, IsMonHom.one_hom]
  have : IsMonHom lam := MulRigidity.isMonHom_of_geometricallyIntegral A.X B.X lam hη
  exact ⟨Hom.mk' lam, hlam⟩


/-! ## §2b. The dual morphism `f^∨` on the Picard scheme and on `Pic⁰` (genuine, proved) -/

/-- `f × id_T : A ×_K T → A' ×_K T`. -/
abbrev famMap {A A' : AbVar K} (f : A.X ⟶ A'.X) (T : Over (Spec (CommRingCat.of K))) :
    pullback A.X.hom T.hom ⟶ pullback A'.X.hom T.hom :=
  pullback.map _ _ _ _ f.left (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- Pull-back of families along `f × id`: `Pic(A'_T) → Pic(A_T)`, natural in `T`. -/
def picPresheafMap {A A' : AbVar K} (f : A.X ⟶ A'.X) :
    picardPresheaf A'.X.hom ⟶ picardPresheaf A.X.hom where
  app T := TypeCat.ofHom (Scheme.Pic.map (famMap f T.unop))
  naturality T T' φ := by
    ext c
    change Scheme.Pic.map (famMap f T'.unop)
        (Scheme.Pic.map (JacobianChallenge.baseChangeMap A'.X.hom φ.unop) c) =
      Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom φ.unop)
        (Scheme.Pic.map (famMap f T.unop) c)
    have e : famMap f T'.unop ≫ JacobianChallenge.baseChangeMap A'.X.hom φ.unop =
        JacobianChallenge.baseChangeMap A.X.hom φ.unop ≫ famMap f T.unop := by
      apply pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap]
    exact (Scheme.Pic.map_comp _ _ (show (pullback A'.X.hom T.unop.hom).Pic from c)).symm.trans
      ((congrArg (fun g => Scheme.Pic.map g (show (pullback A'.X.hom T.unop.hom).Pic from c)) e).trans
        (Scheme.Pic.map_comp _ _ _))

/-- The sheafified pull-back `f^* : Pic_{A/K} → Pic_{A/K}`. -/
def dualSheafMap {A : AbVar K} (f : A.X ⟶ A.X) :
    (picardFunctor A.X.hom).obj ⟶ (picardFunctor A.X.hom).obj :=
  sheafifyMap (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (picPresheafMap f)

lemma toPicardFunctor_comp_dualSheafMap {A : AbVar K} (f : A.X ⟶ A.X) :
    toPicardFunctor A.X.hom ≫ dualSheafMap f = picPresheafMap f ≫ toPicardFunctor A.X.hom :=
  (toSheafify_naturality (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (picPresheafMap f)).symm

/-- **The dual morphism on the Picard scheme**, `f^∨ : P → P` for `f : A → A` (Yoneda applied to
`f^* : Pic_{A/K} → Pic_{A/K}`, the sheafified pull-back of families; Mumford §8). -/
def dualP {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (f : A.X ⟶ A.X) : P ⟶ P :=
  rep.homEquiv.symm ((dualSheafMap f).app (op P) (rep.homEquiv (𝟙 P)))

lemma comp_dualP {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (f : A.X ⟶ A.X)
    {T : Over (Spec (CommRingCat.of K))} (g : T ⟶ P) :
    g ≫ dualP rep f = rep.homEquiv.symm ((dualSheafMap f).app (op T) (rep.homEquiv g)) := by
  rw [dualP, rep.comp_homEquiv_symm]
  congr 1
  rw [← NatTrans.naturality_apply, ← rep.homEquiv_comp, Category.comp_id]

/-- `f^∨(0) = 0`. -/
lemma eta_comp_dualP {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (f : A.X ⟶ A.X) :
    letI := picardFunctorCommGrpObj A.X.hom rep
    η[P] ≫ dualP rep f = η[P] := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  have h := (picardClassifyingHom A.X.hom rep (𝟙_ _)).map_one
  rw [picardClassifyingHom_apply,
    show (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P) = CartesianMonoidalCategory.toUnit _ ≫ η
      from rfl] at h
  simp only [CartesianMonoidalCategory.toUnit_unique (CartesianMonoidalCategory.toUnit _) (𝟙 _),
    Category.id_comp] at h
  rw [comp_dualP, ← h, Equiv.apply_symm_apply]
  congr 1
  have := congrArg (fun τ => τ.app (op (𝟙_ (Over (Spec (CommRingCat.of K)))))
    (1 : (pullback A.X.hom (𝟙_ (Over (Spec (CommRingCat.of K)))).hom).Pic))
    (toPicardFunctor_comp_dualSheafMap f)
  simp only [NatTrans.comp_app] at this
  exact this.trans (congrArg _ (Scheme.Pic.map_one _))

/-- **The dual endomorphism on `Pic⁰`**: `f^∨` restricts to `B = Pic⁰` (B is connected and
`f^∨(0) = 0`), as a homomorphism (rigidity). -/
theorem exists_dual_on_picZero {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} {j : B.X ⟶ P}
    (hj : IsPicZero rep B j) (f : A.X ⟶ A.X) :
    ∃ fv : End B, fv.hom ≫ j = j ≫ dualP rep f := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  obtain ⟨hopen, hrange, hmon⟩ := hj
  have h0 := eta_comp_dualP rep f
  haveI : IsIntegral B.X.left := GeometricallyIntegral.isIntegral_of_subsingleton B.X.hom
  have hjη : η[B.X] ≫ j = η[P] := IsMonHom.one_hom j
  have h2 : η[B.X] ≫ j ≫ dualP rep f = η[P] := by rw [← Category.assoc, hjη, h0]
  have hsub : Set.range (j ≫ dualP rep f).left ⊆ Set.range j.left := by
    rw [hrange]
    rintro _ ⟨b, rfl⟩
    refine ⟨B.X.hom b, ?_⟩
    have he : η[P].left (B.X.hom b) = (j ≫ dualP rep f).left (η[B.X].left (B.X.hom b)) := by
      rw [← h2]; rfl
    rw [he]
    exact (isPreconnected_range (j ≫ dualP rep f).left.continuous).subset_connectedComponent
      ⟨_, rfl⟩ ⟨b, rfl⟩
  let l : B.X.left ⟶ B.X.left := IsOpenImmersion.lift j.left (j ≫ dualP rep f).left hsub
  have hl : l ≫ j.left = (j ≫ dualP rep f).left := IsOpenImmersion.lift_fac _ _ _
  have hw : l ≫ B.X.hom = B.X.hom :=
    calc l ≫ B.X.hom = l ≫ j.left ≫ P.hom := by rw [Over.w j]
      _ = (j ≫ dualP rep f).left ≫ P.hom := by rw [← Category.assoc, hl]
      _ = B.X.hom := Over.w _
  let fv : B.X ⟶ B.X := Over.homMk l hw
  have hfv : fv ≫ j = j ≫ dualP rep f := Over.OverMorphism.ext hl
  have hη : η[B.X] ≫ fv = η[B.X] := by
    apply Over.OverMorphism.ext
    apply (cancel_mono j.left).1
    rw [Over.comp_left, Category.assoc]
    change η[B.X].left ≫ fv.left ≫ j.left = η[B.X].left ≫ j.left
    rw [← Over.comp_left, hfv, ← Over.comp_left, ← Category.assoc, hjη, h0,
      ← Over.comp_left _ _ _ η[B.X] j, hjη]
  have : IsMonHom fv := MulRigidity.isMonHom_of_geometricallyIntegral B.X B.X fv hη
  exact ⟨Hom.mk' fv, hfv⟩

/-! ## §3. Leaves (printed statements over the genuine objects of §1) -/

section Leaves

open HDec.WeilPairing

/-- **LEAF L1 (representability of the Picard functor).** For an abelian variety `A` over a field `K`
the relative Picard fppf sheaf `Pic_{A/K}` is representable. Published: Murre (1964) and Oort (1962)
for `X` proper over a field; Grothendieck, FGA Exp. 232, Thm 3.1, and Kleiman, *The Picard scheme*
(FGA Explained, 2005), Thm 9.4.8 (with Thm 9.2.5: since `𝒪_K = f_*𝒪_A` universally and `A` has the
section `0`, the Zariski, étale and fppf sheaves all equal `T ↦ Pic(A_T)/Pic(T)`), for `X` projective with geometrically integral fibres — abelian
varieties are projective (Mumford §6, Application 1; cf. the vendored
`GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral`). UNVERIFIED
numbering. Statement copied from `scratch/c-to-printed2/T09Roadmap.lean`. -/
def PicRepresentableAbVar : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K),
    ∃ P : Over (Spec (CommRingCat.of K)), Nonempty ((picardFunctor A.X.hom).obj.RepresentableBy P)

/-- **LEAF L2 (`Pic⁰_{A/K}` is an abelian variety).** The identity component of the Picard scheme
of an abelian variety is open, and with the induced group law it is an abelian variety (the dual
abelian variety `Â`). Published: Mumford, *Abelian varieties*, §13 (`Â = Pic⁰` is an abelian
variety of dimension `g`, reduced: §13 Cor. 3 / Thm 1) over `K̄`; Kleiman, *The Picard scheme*,
Prop. 9.5.3 (`Pic⁰` open and closed, of finite type) and Prop. 9.5.1 (compatible with field
extension), so smoothness, properness and geometric integrality descend to `K`; the identity
component of a group scheme locally of finite type over a field is geometrically connected
(SGA 3, VI_A 2.4; Stacks Tag 0B7R); Milne, *Abelian varieties* (1986), §9-10. UNVERIFIED numbering. Stated over every representation `rep`; it is
invariant under the unique isomorphism of representing objects. -/
def PicZeroAbVar : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P),
    ∃ (B : AbVar K) (j : B.X ⟶ P), IsPicZero rep B j

/-- **LEAF L3 (`φ_L` is an isogeny for ample `L`).** If `L` is (very) ample, `λ_L : A → Pic⁰`
(the map with `λ_L ≫ ι = φ_L`) is finite and surjective. Published: Mumford §6, Application 1
(`L = 𝒪(D)`, `D` effective, ample `⇒ K(L) = ker φ_L` finite; for general ample `L` use
`K(L) ⊆ K(L^m)` with `L^m` effective, and proper + quasi-finite `⇒` finite) and §8, Thm 1 (`φ_L`
surjective onto `Â`, `Â ≅ A/K(L)`);
very ample `⇒` ample (Hartshorne II, Thm 7.6 / EGA II 4.5.10); over a non-closed `K`, finiteness and
surjectivity descend from `K̄` (fpqc descent, EGA IV 2.6.4 / 2.7.1). UNVERIFIED numbering. Quantified
over every `(B, ι)` with `IsPicZero` (unique up to unique isomorphism) and every lift `λ`. -/
def PhiVeryAmpleIsogeny : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j → ∀ L : A.X.left.Pic, IsVeryAmple A L →
      ∀ lam : A.X ⟶ B.X, lam ≫ j = phiL rep L → IsIsogenyMor lam

/-- **LEAF L4 (Mumford's Weil pairing `ē_n : A[n] × Â[n] → μ_n` at `Â = Pic⁰`).** There are pairings
`e_n : A[n] × Pic⁰[n] → μ_n` (on `K̄`-points) which, for `n ≥ 1` invertible in `K`, are perfect,
`G_K`-equivariant (`e_n` is defined over `K`), compatible (`e_{mn}(x, y) = e_n(m x, y)` for
`y ∈ Â[n]`), under which every endomorphism `f` of `A` has an adjoint on `Pic⁰` (its dual `f^∨`:
`e_n(x, f^∨ y) = e_n(f x, y)`), and with `e_n(x, φ_L(x)) = 1` for very ample `L`. Published:
Mumford §20 (definition of `ē_n` and its properties: bilinear, perfect, `e_{nm}(x, y) = e_n(mx, y)`,
`e_n(x, f^∨ y) = e_n(f x, y)`, there for isogenies; for every homomorphism: Milne 1986, Lemma 16.2(c),
or reduce via the isogeny `f + [N]`, `(f + [N])^∨ = f^∨ + [N]`, and bilinearity) and §23
(`e^L_n(x, y) := ē_n(x, φ_L(y))` is skew-symmetric with `e^L_n(x, x) = 1`, for every `L`); Galois equivariance: Milne, *Abelian varieties* (1986), §16 (`e_n` is defined
over `K`). UNVERIFIED numbering. The pairing is existential (Mumford's `ē_n` witnesses it), so this is
a consequence of the printed statements, never stronger. -/
def WeilPairingPicZero : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j →
    ∃ e : ∀ n : ℕ, Pairing A B n,
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsPerfect (e n)) ∧
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → HDec.WeilPairing.IsGalEquivariant (e n)) ∧
      (∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
        ∀ (x : tors A (m * n)) (y : tors B n),
          (e (m * n) x (torsIncl B (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val) ∧
      (∀ f : End A, ∃ fv : End B, ∀ n : ℕ, 0 < n → (n : K) ≠ 0 →
        ∀ x y, e n x (torsMap fv n y) = e n (torsMap f n x) y) ∧
      (∀ L : A.X.left.Pic, IsVeryAmple A L → ∀ lam : Hom A B, lam.hom ≫ j = phiL rep L →
        ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x : tors A n, e n x (torsMap lam n x) = 0)

/-- **Ample** (Stacks, *Properties of schemes*, Def. 28.26.1, Tag 01PS; EGA II 4.5.3; UNVERIFIED
numbering): `X` is quasi-compact and every point lies in an affine `X_s = {s ≠ 0}` for some global
section `s` of some `L^{⊗n}`, `n ≥ 1` (`X_s` = complement of the support of the zero locus of `s`,
vendored `Scheme.Modules.Hom.zeroLocus`). -/
def IsAmple (X : Scheme.{0}) (L : X.Pic) : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ (n : ℕ) (_ : 0 < n)
    (s : 𝟙_ X.Modules ⟶ ((fromSkeleton X.Modules).obj L.val).tensorPow n),
    x ∈ (Scheme.Modules.Hom.zeroLocus s).support.compl ∧
      IsAffineOpen (Scheme.Modules.Hom.zeroLocus s).support.compl

/-- **LEAF L0 (very ample ⇒ ample).** EGA II 4.5.10 (very ample relative to an affine base ⇒ ample,
in the EGA/Stacks sense used by `IsAmple`); Stacks, *Morphisms*, section "Ample and very ample
sheaves" (Tags 01VM-01VS); Hartshorne II Thm 7.6 (with ampleness defined by global generation, which
agrees with `IsAmple` on Noetherian schemes, EGA II 4.5.2). UNVERIFIED numbering. -/
def VeryAmpleIsAmple : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : A.X.left.Pic), IsVeryAmple A L → IsAmple A.X.left L

/-- **LEAF L3, printed form (`φ_L` is an isogeny for ample `L`).** As `PhiVeryAmpleIsogeny`, for every
ample `L` (Mumford §6 Application 1 and §8 Thm 1; UNVERIFIED numbering). -/
def PhiAmpleIsogeny : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j → ∀ L : A.X.left.Pic, IsAmple A.X.left L →
      ∀ lam : A.X ⟶ B.X, lam ≫ j = phiL rep L → IsIsogenyMor lam

/-- **LEAF L4, printed form.** As `WeilPairingPicZero`, with the *genuine* dual `f^∨` (any lift
`fv : Pic⁰ → Pic⁰` of `dualP rep f`; it exists by `exists_dual_on_picZero` and is unique since `ι` is
a monomorphism) in `ē_n(x, f^∨ y) = ē_n(f x, y)` (Mumford §20, (5)), and `ē_n(x, φ_L(x)) = 1` for
every ample `L` (Mumford §23). UNVERIFIED numbering. -/
def WeilPairingPicZeroPrinted : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j →
    ∃ e : ∀ n : ℕ, Pairing A B n,
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsPerfect (e n)) ∧
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → HDec.WeilPairing.IsGalEquivariant (e n)) ∧
      (∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
        ∀ (x : tors A (m * n)) (y : tors B n),
          (e (m * n) x (torsIncl B (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val) ∧
      (∀ (f : End A) (fv : End B), fv.hom ≫ j = j ≫ dualP rep f.hom → ∀ n : ℕ, 0 < n →
        (n : K) ≠ 0 → ∀ x y, e n x (torsMap fv n y) = e n (torsMap f n x) y) ∧
      (∀ L : A.X.left.Pic, IsAmple A.X.left L → ∀ lam : Hom A B, lam.hom ≫ j = phiL rep L →
        ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x : tors A n, e n x (torsMap lam n x) = 0)

end Leaves

/-- Glue: the printed L3 and L0 give L3 for very ample classes. -/
theorem phiVeryAmpleIsogeny_of_printed (h0 : VeryAmpleIsAmple) (h3 : PhiAmpleIsogeny) :
    PhiVeryAmpleIsogeny := fun K _ A P rep B j hj L hL lam hlam =>
  h3 K A P rep B j hj L (h0 K A L hL) lam hlam

/-- Glue: the printed L4 (genuine `f^∨`, ample `L`) and L0 give L4. -/
theorem weilPairingPicZero_of_printed (h0 : VeryAmpleIsAmple) (h4 : WeilPairingPicZeroPrinted) :
    WeilPairingPicZero := by
  intro K _ A P rep B j hj
  obtain ⟨e, hperf, hgal, hcompat, hdual, halt⟩ := h4 K A P rep B j hj
  refine ⟨e, hperf, hgal, hcompat, fun f => ?_, fun L hL => halt L (h0 K A L hL)⟩
  obtain ⟨fv, hfv⟩ := exists_dual_on_picZero rep hj f.hom
  exact ⟨fv, hdual f fv hfv⟩

/-! ## §4. `t09SymmIsogenyExists` from the four leaves -/

/-- **Main result.** The field `t09SymmIsogenyExists` follows from the four printed leaves L1-L4 over
the genuine Picard functor; the glue (existence of a very ample class, `φ_L(0) = 0`, `φ_L` lands in
`Pic⁰`, the lift is a homomorphism) is proved above. -/
theorem t09SymmIsogenyExists_of_leaves (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar)
    (h3 : PhiVeryAmpleIsogeny) (h4 : WeilPairingPicZero) :
    HDec.WeilPairing.T09_SymmIsogenyExists := by
  intro K _ A
  obtain ⟨P, ⟨rep⟩⟩ := h1 K A
  obtain ⟨B, j, hj⟩ := h2 K A P rep
  obtain ⟨L, hL⟩ := exists_isVeryAmple A
  obtain ⟨lam, hlam⟩ := exists_hom_comp_eq_phiL rep hj L
  obtain ⟨e, hperf, hgal, hcompat, hdual, halt⟩ := h4 K A P rep B j hj
  exact ⟨{ D := { dual := B, e := e, perfect := hperf, galois := hgal, compat := hcompat,
                  dualEnd := hdual }
           lam := lam
           isogeny := h3 K A P rep B j hj L hL lam.hom hlam
           symm := fun n hn hnK x => by
             rw [HDec.WeilPairing.weil_apply]
             exact halt L hL lam hlam n hn hnK x }⟩

/-! ## §5. Non-vacuity of `IsAmple` -/

/-- Over an algebraically closed field every abelian variety has an ample class in the sense of
`IsAmple` (from the vendored `GrpObj.hasAmpleFamily_of_smooth_of_irreducibleSpace`, `n = 1`). A check
that `IsAmple` is not inert, so `VeryAmpleIsAmple` is not refuted by the definition. -/
theorem exists_isAmple_of_isAlgClosed [IsAlgClosed K] (A : AbVar K) : ∃ L, IsAmple A.X.left L := by
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  obtain ⟨M, hM, I, hI, s, haff, hcov⟩ :=
    GrpObj.hasAmpleFamily_of_smooth_of_irreducibleSpace (baseField := K) A.X
  letI := hM
  haveI : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  let N := (fromSkeleton A.X.left.Modules).obj (Scheme.Pic.mk M).val
  let e : M ≅ N.tensorPow 1 := (Scheme.Pic.mkIso M).symm ≪≫ (ρ_ N).symm
  refine ⟨Scheme.Pic.mk M, inferInstance, fun x => ?_⟩
  have hx : x ∈ ⨆ i, (Scheme.Modules.Hom.zeroLocus (s i)).support.compl := by
    rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hz : Scheme.Modules.Hom.zeroLocus (s i ≫ e.hom) = Scheme.Modules.Hom.zeroLocus (s i) :=
    Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso (s i ≫ e.hom) (s i)
      (Arrow.isoMk (Iso.refl _) e.symm (by simp))
  exact ⟨1, one_pos, s i ≫ e.hom, by rw [hz]; exact hi, by rw [hz]; exact haff i⟩

/-! ## §5b. Very ample ⇒ ample (proved; removes leaf L0) -/

section VeryAmple

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An invertible `E` with sections `σ_k` whose nonvanishing loci are affine and cover `X` is
ample (`n = 1`). -/
theorem isAmple_mk_of_sections {X : Scheme.{0}} [CompactSpace X] (E : X.Modules) [E.IsInvertible]
    {I : Type} (σ : I → (𝟙_ X.Modules ⟶ E))
    (haff : ∀ k, IsAffineOpen (Scheme.Modules.Hom.zeroLocus (σ k)).support.compl)
    (hcov : ∀ x, ∃ k, x ∈ (Scheme.Modules.Hom.zeroLocus (σ k)).support.compl) :
    IsAmple X (Scheme.Pic.mk E) := by
  let F := (fromSkeleton X.Modules).obj (Scheme.Pic.mk E).val
  let e : E ≅ F.tensorPow 1 := (Scheme.Pic.mkIso E).symm ≪≫ (ρ_ F).symm
  refine ⟨inferInstance, fun x => ?_⟩
  obtain ⟨k, hk⟩ := hcov x
  have hz : Scheme.Modules.Hom.zeroLocus (σ k ≫ e.hom) = Scheme.Modules.Hom.zeroLocus (σ k) :=
    Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso (σ k ≫ e.hom) (σ k)
      (Arrow.isoMk (Iso.refl _) e.symm (by simp))
  exact ⟨1, one_pos, σ k ≫ e.hom, by rw [hz]; exact hk, by rw [hz]; exact haff k⟩

variable {X : Scheme.{0}} {N : Type} {S : Scheme.{0}}

/-- the pulled-back coordinate section `i^*Xₖ` of `i^*𝒪(1)` -/
def coordSection (i : X ⟶ ℙ(N; S)) (k : N) :
    𝟙_ X.Modules ⟶ (Scheme.Modules.pullback i).obj (ProjectiveSpace.twist N S 1) :=
  Scheme.Modules.homOfGlobalSection _
    (Scheme.Modules.pullbackSection i (ProjectiveSpace.twistOneSection N S k))

/-- **`X_{i^*Xₖ} = i⁻¹ D₊(Xₖ)`.** -/
theorem compl_support_zeroLocus_coordSection (i : X ⟶ ℙ(N; S)) (k : N) :
    (Scheme.Modules.Hom.zeroLocus (coordSection i k)).support.compl =
      i ⁻¹ᵁ ProjectiveSpace.standardOpen N S k := by
  ext x
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((ProjectiveSpace.iSup_standardOpen N S).ge (Set.mem_univ (i x)))
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := i ⁻¹ᵁ ProjectiveSpace.standardOpen N S j) hj
  let E := (Scheme.Modules.pullback i).obj (ProjectiveSpace.twist N S 1)
  have heV := ProjectiveSpace.isFreeGenerator_pullbackSection_twistOneSection i j
  have heU := heV.map hWV
  have hform := ProjectiveSpace.pullbackSection_twistOneSection_map_eq_smul i k j
  have key := Scheme.Modules.basicOpen_coeff_eq (coordSection i k) ⟨W, hW⟩ heU
  let c : Γ(X, i ⁻¹ᵁ ProjectiveSpace.standardOpen N S j) :=
    i.app (ProjectiveSpace.standardOpen N S j) ((ProjectiveSpace.toIntegralModel N S).app
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule N (ULift.{0} ℤ)) (MvPolynomial.X j))
      (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{0} ℤ) j k)))
  have h1 : (coordSection i k).app W (Scheme.Modules.unitSectionsEquiv W 1) =
      E.presheaf.map (homOfLE hWV).op (E.presheaf.map (homOfLE (i.preimage_mono le_top)).op
        (Scheme.Modules.pullbackSection i (ProjectiveSpace.twistOneSection N S k))) := by
    refine (Scheme.Modules.homOfGlobalSection_app_one _ _ W).trans ?_
    exact (Scheme.Modules.presheaf_map_map_apply _ _ _).symm
  have hσ : (coordSection i k).app W (Scheme.Modules.unitSectionsEquiv W 1) =
      X.presheaf.map (homOfLE hWV).op c • E.presheaf.map (homOfLE hWV).op
        (E.presheaf.map (homOfLE (i.preimage_mono le_top)).op
          (Scheme.Modules.pullbackSection i (ProjectiveSpace.twistOneSection N S j))) := by
    rw [h1]
    erw [hform]
    exact Scheme.Modules.map_smul _ _ _ _
  have hcoeff : heU.coeff ((coordSection i k).app W (Scheme.Modules.unitSectionsEquiv W 1)) =
      X.presheaf.map (homOfLE hWV).op c :=
    heU.smul_left_injective (by
      show heU.coeff _ • _ = _ • _
      rw [heU.coeff_smul]
      exact hσ)
  rw [hcoeff] at key
  erw [Scheme.basicOpen_res] at key
  have hX (m : N) : MvPolynomial.X m ∈ MvPolynomial.homogeneousSubmodule N (ULift.{0} ℤ) 1 :=
    MvPolynomial.X_mem_homogeneousSubmodule_one _ m
  have hr : (Proj (MvPolynomial.homogeneousSubmodule N (ULift.{0} ℤ))).basicOpen
      (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{0} ℤ) j k)) =
      Proj.basicOpen _ (MvPolynomial.X j) ⊓ Proj.basicOpen _ (MvPolynomial.X k) :=
    Proj.basicOpen_ratio (MvPolynomial.homogeneousSubmodule N (ULift.{0} ℤ)) one_pos (hX j) (hX k)
  have hc : X.basicOpen c = i ⁻¹ᵁ (ProjectiveSpace.toIntegralModel N S ⁻¹ᵁ
      (Proj.basicOpen _ (MvPolynomial.X j) ⊓ Proj.basicOpen _ (MvPolynomial.X k))) := by
    rw [← hr, Scheme.preimage_basicOpen, Scheme.preimage_basicOpen]
    rfl
  rw [hc] at key
  constructor
  · intro h
    have hm : x ∈ W ⊓ (Scheme.Modules.Hom.zeroLocus (coordSection i k)).support.compl := ⟨hxW, h⟩
    rw [← key] at hm
    exact hm.2.2
  · intro h
    have hm : x ∈ W ⊓ i ⁻¹ᵁ (ProjectiveSpace.toIntegralModel N S ⁻¹ᵁ
        (Proj.basicOpen _ (MvPolynomial.X j) ⊓ Proj.basicOpen _ (MvPolynomial.X k))) := ⟨hxW, hj, h⟩
    rw [key] at hm
    exact hm.2

/-- **The pull-back of `𝒪(1)` along an immersion with closed image is ample** (proved): the sections
`i^*Xₖ` have nonvanishing loci `i⁻¹ D₊(Xₖ)`, affine since `D₊(Xₖ)` is affine and `i` is a closed
immersion onto its image, and they cover. -/
theorem isAmple_of_isImmersion [CompactSpace X] [Finite N] [IsAffine S] (i : X ⟶ ℙ(N; S))
    [IsImmersion i] (hcl : IsClosed (Set.range i)) :
    IsAmple X (Scheme.Pic.map i (Scheme.Pic.mk (ProjectiveSpace.twist N S 1))) := by
  rw [Scheme.Pic.map_mk]
  refine isAmple_mk_of_sections _ (coordSection i) (fun k => ?_) (fun x => ?_)
  · rw [compl_support_zeroLocus_coordSection]
    refine i.isAffineOpen_preimage_of_le_coborderRange
      (ProjectiveSpace.isAffineOpen_standardOpen N S k) ?_
    intro y _
    change y ∈ coborder (Set.range i)
    rw [coborder_eq_univ_iff.mpr hcl]
    trivial
  · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((ProjectiveSpace.iSup_standardOpen N S).ge (Set.mem_univ (i x)))
    exact ⟨k, by rw [compl_support_zeroLocus_coordSection]; exact hk⟩

end VeryAmple

/-- **L0 is a theorem**: a very ample class on an abelian variety is ample (`i` is proper, since
`A` is proper over `K` and `ℙ^N_K` is separated, so its image is closed). -/
theorem veryAmpleIsAmple : VeryAmpleIsAmple := by
  intro K _ A L hL
  obtain ⟨N, hN, i, hi, hover, rfl⟩ := hL
  haveI : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  haveI : IsProper (i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
    rw [hover]; infer_instance
  haveI : IsProper i := IsProper.of_comp i (ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
  exact isAmple_of_isImmersion i i.isClosedMap.isClosed_range

/-! ## §6. Mumford's `ē_n` as a genuine definition, and the leaf in fully genuine form -/

/-- `Spec K̄` as a `K`-scheme. -/
abbrev ptK (K : Type) [Field K] : Over (Spec (CommRingCat.of K)) :=
  ptObj (K := K) (AlgebraicClosure K)

/-- **Translation by `x ∈ A(K̄)` on `A_K̄`**, as a `K`-morphism `A ×_K K̄ → A ×_K K̄`,
`(a, s) ↦ (a + x(s), s)` (`t_x`, Mumford §2). -/
def transl {A : AbVar K} (x : A.Pt (AlgebraicClosure K)) : A.X ⊗ ptK K ⟶ A.X ⊗ ptK K :=
  CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _ ≫ x) ≫ μ[A.X])
    (CartesianMonoidalCategory.snd _ _)

/-- **Multiplication by `n` on `A_K̄`** (`n_A = id^n` in the group of `K`-endomorphisms of the
scheme, base-changed to `K̄`). -/
def mulN (A : AbVar K) (n : ℕ) : A.X ⊗ ptK K ⟶ A.X ⊗ ptK K :=
  ((𝟙 A.X) ^ n) ▷ ptK K

/-- **The class `M_y ∈ Pic(A_K̄)` of a point `y ∈ Pic⁰(K̄)`**: a class whose image in
`Pic_{A/K}(K̄)` is the point `y ≫ ι` (exists by Kleiman Thm 9.2.5, `A` having a section; unique since
`Pic(K̄) = 1`). Defined by choice (`1` if no such class existed). -/
def picClass {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} (j : B.X ⟶ P)
    (y : B.Pt (AlgebraicClosure K)) : (pullback A.X.hom (ptK K).hom).Pic := by
  classical
  exact if h : ∃ c, (toPicardFunctor A.X.hom).app (op (ptK K)) c = rep.homEquiv (y ≫ j)
    then h.choose else 1

/-- **Mumford's `ē_n(x, y)`, genuine** (Mumford §20 via the descent description of §§12, 15; the
explicit formula as in Milne 1986 §16; UNVERIFIED numbering): for `y ∈ Pic⁰[n](K̄)` with class `M`, choose `ψ : 𝒪 ≅ n_A^*M` (exists: Mumford
§8 (iv)); for `x ∈ A[n](K̄)`, `n_A ∘ t_x = n_A`, so `t_x^*ψ` is a second trivialization and
`t_x^*ψ ∘ ψ⁻¹ ∈ Aut(𝒪_{A_K̄}) = Γ(A_K̄, 𝒪)^× = K̄^×` is the value (independent of the choices). Defined
by choice; `1` if a condition fails (it never does for `x ∈ A[n]`, `y ∈ Pic⁰[n]`). -/
def weilScalar {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} (j : B.X ⟶ P) (n : ℕ)
    (x : A.Pt (AlgebraicClosure K)) (y : B.Pt (AlgebraicClosure K)) :
    Γ(pullback A.X.hom (ptK K).hom, ⊤) := by
  classical
  let X := pullback A.X.hom (ptK K).hom
  let t : X ⟶ X := (transl x).left
  let m : X ⟶ X := (mulN A n).left
  let M : X.Modules := (fromSkeleton X.Modules).obj (picClass rep j y).val
  exact if h : t ≫ m = m then
    if hψ : Nonempty (Scheme.Modules.unit X ≅ (Scheme.Modules.pullback m).obj M) then
      Scheme.Modules.unitHomAddEquiv (Scheme.Modules.unit X)
        ((Scheme.Modules.pullbackObjUnitIso t).inv ≫ (Scheme.Modules.pullback t).map hψ.some.hom ≫
          (Scheme.Modules.pullbackComp t m).hom.app M ≫
            (Scheme.Modules.pullbackCongr h).hom.app M ≫ hψ.some.inv)
    else 1
  else 1

/-- `K̄ → Γ(A_K̄, 𝒪)` (constants; a bijection, vendored
`bijective_appTop_of_isProper_of_geometricallyIntegral`). -/
def constK (A : AbVar K) : AlgebraicClosure K →+* Γ(pullback A.X.hom (ptK K).hom, ⊤) :=
  (pullback.snd A.X.hom (ptK K).hom).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure K))).inv.hom

/-- **`n_A ∘ t_x = n_A` for `x ∈ A[n](K̄)`** (proved): the first condition in `weilScalar` holds on
`n`-torsion. -/
theorem transl_comp_mulN {A : AbVar K} {n : ℕ} (x : A.Pt (AlgebraicClosure K)) (hx : x ^ n = 1) :
    transl x ≫ mulN A n = mulN A n := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [transl, mulN, Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
      CartesianMonoidalCategory.lift_fst_assoc]
    simp only [MonObj.comp_pow, Category.comp_id]
    rw [← CategoryTheory.Hom.mul_def, mul_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, mul_one]
  · simp [transl, mulN]

/-- The same on the underlying schemes `A_K̄`, for `x ∈ A[n]`. -/
theorem transl_left_comp_mulN_left {A : AbVar K} {n : ℕ} (x : HDec.WeilPairing.tors A n) :
    (transl (Additive.toMul (x : HDec.WeilPairing.P A))).left ≫ (mulN A n).left =
      (mulN A n).left := by
  rw [← Over.comp_left, transl_comp_mulN]
  have := x.2
  change n • (x : HDec.WeilPairing.P A) = 0 at this
  rw [← toMul_nsmul, this]
  rfl

/-- **LEAF L5 (points of `Pic_{A/K}` over `K̄` are line bundles on `A_K̄`).** Kleiman, *The Picard
scheme*, Thm 9.2.5 (`𝒪_K = f_*𝒪_A` universally and `f` has a section, so
`Pic(A_T)/Pic(T) ≅ Pic_{(A/K)(fppf)}(T)`), at `T = Spec K̄` where `Pic(T) = 1`; UNVERIFIED numbering.
Not used by the main theorems; it makes `picClass` the genuine class (no default branch). -/
def PicPointsAlgClosed : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K),
    Function.Bijective ((toPicardFunctor A.X.hom).app (op (ptK K)))

/-- **LEAF L6 (`n_A^*M ≅ 𝒪` for `M ∈ Pic⁰[n]`).** Mumford §8 (iv) (`n_A^*M ≅ M^n` for `M ∈ Pic⁰`)
with `M^n ≅ 𝒪` for `y ∈ Pic⁰[n]` (the group law of `Pic` is `⊗`, vendored
`homEquiv_symm_toPicardFunctor_mul`); Mumford's `Pic⁰ = {L : t_x^*L ≅ L ∀ x}` is the set of
`K̄`-points of the identity component by Mumford §8 Thm 1 and §13, Kleiman §9.5; true for every `n`
(for `n = 0`, `0_A^*M` comes from `Pic(K̄) = 1`); UNVERIFIED numbering. Not used by the main theorems; with
`transl_left_comp_mulN_left` it removes every default branch of `weilScalar` (`weilScalar_spec`). -/
def MulNTrivialPicZero : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j → ∀ (n : ℕ) (y : HDec.WeilPairing.tors B n),
      Nonempty (Scheme.Modules.unit (pullback A.X.hom (ptK K).hom) ≅
        (Scheme.Modules.pullback (mulN A n).left).obj
          ((fromSkeleton (pullback A.X.hom (ptK K).hom).Modules).obj
            (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))).val))

/-- **`weilScalar` is Mumford's formula** on `A[n] × Pic⁰[n]` (no default branch), given L6:
`ē_n(x, y) = t_x^*ψ ∘ ψ⁻¹` for any trivialization `ψ : 𝒪 ≅ n_A^*M_y`. -/
theorem weilScalar_spec (h6 : MulNTrivialPicZero) {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} {j : B.X ⟶ P}
    (hj : IsPicZero rep B j) {n : ℕ} (x : HDec.WeilPairing.tors A n)
    (y : HDec.WeilPairing.tors B n) :
    ∃ ψ : Scheme.Modules.unit (pullback A.X.hom (ptK K).hom) ≅
        (Scheme.Modules.pullback (mulN A n).left).obj
          ((fromSkeleton (pullback A.X.hom (ptK K).hom).Modules).obj
            (picClass rep j (Additive.toMul (y : HDec.WeilPairing.P B))).val),
      weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
          (Additive.toMul (y : HDec.WeilPairing.P B)) =
        Scheme.Modules.unitHomAddEquiv (Scheme.Modules.unit _)
          ((Scheme.Modules.pullbackObjUnitIso (transl (Additive.toMul (x : HDec.WeilPairing.P A))).left).inv ≫
            (Scheme.Modules.pullback (transl (Additive.toMul (x : HDec.WeilPairing.P A))).left).map ψ.hom ≫
            (Scheme.Modules.pullbackComp _ _).hom.app _ ≫
            (Scheme.Modules.pullbackCongr (transl_left_comp_mulN_left x)).hom.app _ ≫ ψ.inv) := by
  have hψ := h6 K A P rep B j hj n y
  refine ⟨hψ.some, ?_⟩
  unfold weilScalar
  rw [dite_eq_left (transl_left_comp_mulN_left x)]
  exact dite_eq_left hψ

section LeafMumford

open HDec.WeilPairing

/-- **LEAF L4, fully genuine form (Mumford's `ē_n`).** As `WeilPairingPicZeroPrinted`, with the
pairing pinned to Mumford's genuine `ē_n` (`weilScalar`): its values, as constants of
`Γ(A_K̄, 𝒪)`, are `weilScalar`. Published: Mumford §20 and §23 (the properties), Kleiman Thm 9.2.5
(points of `Pic⁰` over `K̄` are line bundles on `A_K̄`), Mumford §8 (iv) (`n_A^*M ≅ 𝒪` for
`M ∈ Pic⁰[n]`), `Γ(A_K̄, 𝒪) = K̄`; UNVERIFIED numbering. Every clause is invariant under
`e ↦ -e`, so the leaf holds whichever sign convention for `ē_n` (`t_x^*ψ ψ⁻¹` or its inverse). -/
def WeilPairingMumford : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j →
    ∃ e : ∀ n : ℕ, Pairing A B n,
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsPerfect (e n)) ∧
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → HDec.WeilPairing.IsGalEquivariant (e n)) ∧
      (∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
        ∀ (x : tors A (m * n)) (y : tors B n),
          (e (m * n) x (torsIncl B (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val) ∧
      (∀ (f : End A) (fv : End B), fv.hom ≫ j = j ≫ dualP rep f.hom → ∀ n : ℕ, 0 < n →
        (n : K) ≠ 0 → ∀ x y, e n x (torsMap fv n y) = e n (torsMap f n x) y) ∧
      (∀ L : A.X.left.Pic, IsAmple A.X.left L → ∀ lam : Hom A B, lam.hom ≫ j = phiL rep L →
        ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x : tors A n, e n x (torsMap lam n x) = 0) ∧
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ (x : tors A n) (y : tors B n),
        constK A ((e n x y).val : AlgebraicClosure K) =
          weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A))
            (Additive.toMul (y : HDec.WeilPairing.P B)))

end LeafMumford

/-- The fully genuine L4 implies the printed L4 (forget the identification with `weilScalar`). -/
theorem weilPairingPicZeroPrinted_of_mumford (h : WeilPairingMumford) : WeilPairingPicZeroPrinted := by
  intro K _ A P rep B j hj
  obtain ⟨e, h1, h2, h3, h4, h5, -⟩ := h K A P rep B j hj
  exact ⟨e, h1, h2, h3, h4, h5⟩

/-- **Main result, fully genuine form.** -/
theorem t09SymmIsogenyExists_of_mumford (h0 : VeryAmpleIsAmple) (h1 : PicRepresentableAbVar)
    (h2 : PicZeroAbVar) (h3 : PhiAmpleIsogeny) (h4 : WeilPairingMumford) :
    HDec.WeilPairing.T09_SymmIsogenyExists :=
  t09SymmIsogenyExists_of_leaves h1 h2 (phiVeryAmpleIsogeny_of_printed h0 h3)
    (weilPairingPicZero_of_printed h0 (weilPairingPicZeroPrinted_of_mumford h4))

/-- **Main result, four printed leaves.** L0 is proved (`veryAmpleIsAmple`), so the field follows from
L1 (Picard representability), L2 (`Pic⁰` is an abelian variety), L3 (`φ_L` isogeny for ample `L`) and
L4 (Mumford's genuine `ē_n`). -/
theorem t09SymmIsogenyExists_of_four (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar)
    (h3 : PhiAmpleIsogeny) (h4 : WeilPairingMumford) : HDec.WeilPairing.T09_SymmIsogenyExists :=
  t09SymmIsogenyExists_of_mumford veryAmpleIsAmple h1 h2 h3 h4

/-- **Main result, printed form.** `t09SymmIsogenyExists` from the five printed leaves
L0 (very ample ⇒ ample), L1 (Picard representability), L2 (`Pic⁰` is an abelian variety),
L3 (`φ_L` isogeny for ample `L`), L4 (Mumford's `ē_n` with the genuine `f^∨`). -/
theorem t09SymmIsogenyExists_of_printed (h0 : VeryAmpleIsAmple) (h1 : PicRepresentableAbVar)
    (h2 : PicZeroAbVar) (h3 : PhiAmpleIsogeny) (h4 : WeilPairingPicZeroPrinted) :
    HDec.WeilPairing.T09_SymmIsogenyExists :=
  t09SymmIsogenyExists_of_leaves h1 h2 (phiVeryAmpleIsogeny_of_printed h0 h3)
    (weilPairingPicZero_of_printed h0 h4)

end T09Pic

namespace HDec

namespace HSyn

/-! ## The bundle -/

/-- **The added leaves still open** (leaf-fold14, t09-pic fold): x6-fold's `OpenAddedLeaves12` without
`t09SymmIsogenyExists` (t09-pic's `T09Pic.t09SymmIsogenyExists_of_four`), with its four printed leaves added.
17 fields. -/
structure OpenAddedLeaves13 : Prop where
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  qmCentralizerCMC : QMSplit.Aut.QMCentralizerCMC
  tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants
  axSenTate : _root_.ZInQ.Contrib.HodgeSplit.AxSenTate
  milneIsogenyQuasiInverse : _root_.AvSplit.MilneIsogenyQuasiInverse
  shimuraTaniyamaQbar : G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar
  egaIV_8_10_5_xii : _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii
  shimuraGoodReductionNoGuard : CurveSplitGR.ShimuraGoodReductionNoGuard
  /-- qm-split, H-87/H-88: the valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16,
  Thm 2.20; Rankin Thm 4.1.4). -/
  valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
  /-- qm-split, H-87/H-88: `ι(𝒪¹)` is cocompact Fuchsian with covolume `2π/3` (Shimura 1971 Prop. 9.2;
  Shimizu 1965). -/
  shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
  /-- shimura-glue, printed form, on abelian schemes (route-a-fold): Deligne's theorem on the connected
  components of a Shimura variety for `G = B^×` at level `K₃` on one fine witness `Y₃` (Deligne, Sém. Bourbaki
  389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.1.3, 2.6.3; locators UNVERIFIED). -/
  deligneComponentsY3PrintedAb : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb
  /-- x6-glue (shimura-glue), printed form (on abelian schemes): Deligne's theorem on the connected components of a
  Shimura variety (Sém. Bourbaki 389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.6.3; locators UNVERIFIED) for
  `G = B^×` at level `𝒪̂^×` on one canonical coarse witness `X₆` (the double coset is computed in Lean). -/
  deligneComponentsX6PrintedAb : _root_.ShimuraGlue.DeligneComponentsX6PrintedAb
  /-- x6-glue (shimura-split), textbook, weakened: for a proper `X → Spec k`, `char k = 0`, connectedness of
  `X ×_k k̄` gives geometric connectedness (EGA IV 4.5; Stacks 0389; locators UNVERIFIED). -/
  geomConnOfAlgClosure : QMSplit.Moduli.GeomConnOfAlgClosure
  /-- t09-pic, L1, printed form: the relative Picard fppf sheaf of an abelian variety over a field is representable
  (Murre 1964, Oort 1962; FGA Exp. 232 Thm 3.1; Kleiman, *The Picard scheme*, Thm 9.4.8 with 9.2.5; locators
  UNVERIFIED). With the next three replaces `t09SymmIsogenyExists`. -/
  picRepresentableAbVar : _root_.T09Pic.PicRepresentableAbVar
  /-- t09-pic, L2, printed form: for every representation of `Pic_{A/K}`, its identity component with the induced
  group law is an abelian variety (`IsPicZero`; Mumford §13, Kleiman 9.5.1 and 9.5.3, SGA 3 VI_A 2.4; locators
  UNVERIFIED). -/
  picZeroAbVar : _root_.T09Pic.PicZeroAbVar
  /-- t09-pic, L3, printed form: for ample `L`, the lift `λ_L : A → Pic⁰` of `φ_L` is an isogeny (Mumford §6
  Application 1 and §8 Thm 1; locators UNVERIFIED). -/
  phiAmpleIsogeny : _root_.T09Pic.PhiAmpleIsogeny
  /-- t09-pic, L4, printed form (single leaf): there is a pairing `A[n] × Pic⁰[n] → μ_n`, `n` invertible in `K`, with
  the values of Mumford's `ē_n` (`weilScalar`), perfect, Galois-equivariant, compatible in `n`, adjoint for the
  genuine dual `f^∨`, and trivial on `(x, λ_L x)` for ample `L` (Mumford §20 and §23; Milne 1986 §16; locators
  UNVERIFIED). -/
  weilPairingMumford : _root_.T09Pic.WeilPairingMumford

/-! ## From the new bundle to x6-fold's -/

/-- x6-fold's added-leaf bundle from leaf-fold14's: `t09SymmIsogenyExists` from t09-pic's four printed leaves. -/
theorem addedLeaves12_of_open13 (l : OpenAddedLeaves13) : OpenAddedLeaves12 where
  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := _root_.T09Pic.t09SymmIsogenyExists_of_four l.picRepresentableAbVar l.picZeroAbVar
    l.phiAmpleIsogeny l.weilPairingMumford
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  shimuraTaniyamaQbar := l.shimuraTaniyamaQbar
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  shimuraGoodReductionNoGuard := l.shimuraGoodReductionNoGuard
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  deligneComponentsY3PrintedAb := l.deligneComponentsY3PrintedAb
  deligneComponentsX6PrintedAb := l.deligneComponentsX6PrintedAb
  geomConnOfAlgClosure := l.geomConnOfAlgClosure

/-- **G0 with only the open leaves and the open glue** (leaf-fold14; no `sorry`, standard axioms).
`ZInQ.SixContactMin` from `OpenResearchLeaves14` (35), `OpenTextbookLeaves10` (15), `OpenAddedLeaves13` (17) and
`OpenGlue7` (1). -/
theorem sixContactMin_of_open18 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves13)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) : ZInQ.SixContactMin :=
  sixContactMin_of_open17 r t (addedLeaves12_of_open13 l) g hYu hθ

end HSyn

end HDec

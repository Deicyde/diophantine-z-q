import ZInQKernel.Contrib.OneProof.PicZeroAbVarCharZero
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.NormalizedSheaf
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.RepresentableGroup

/-!
# Kleiman 9.5.4 over Kleiman's own Picard functor (kleiman-section)

`PicFix.KleimanPicZeroProper` (`Contrib/OneProof/PicZeroAbVar.lean`) quantifies over schemes representing the tree's
`picardFunctor X.hom`, the fppf sheafification of `T ↦ Pic(X ×_K T)` with no quotient. Kleiman, *The Picard scheme*
(FGA Explained, Ch. 9), Def. 9.2.2, sheafifies `T ↦ Pic(X_T)/Pic(T)` (numbering UNVERIFIED). This file:

* defines Kleiman's functor `kleimanPicardPresheafGrp f : T ↦ Pic(X ×_S T) ⧸ Pic(T)` (a presheaf of groups),
  its fppf sheafification `kleimanPicardSheaf f`, and the group law `kleimanPicardGrpObj` of a representing scheme
  (built exactly as the tree's `picardFunctorCommGrpObj`);
* proves `picardFunctorIsoKleiman f : picardFunctor f ≅ kleimanPicardSheaf f` for **every** `f : X ⟶ S`, with no
  section: the quotient map `Pic(X_T) → Pic(X_T)/Pic(T)` is surjective, and it is locally injective because a class
  of `Pic(T)` is trivial on a Zariski cover of `T` (`Pic.exists_map_iota_eq_one`), so it is locally bijective and
  becomes an isomorphism after fppf sheafification;
* proves that the identity points (hence the identity components) of the two group laws on a representing scheme
  agree (`eta_repKleiman`, `identityComponent_repKleiman`);
* states Kleiman 9.5.4 over Kleiman's functor in two forms: `KleimanPicZeroProperQ` (the hypotheses of
  `PicFix.KleimanPicZeroProper`) and `KleimanPicZeroProperPrinted` (weakest reading: additionally `X` geometrically
  integral, projective over `K` and with a `K`-point), and proves
  `kleimanPicZeroProper_of_Q : KleimanPicZeroProperQ → PicFix.KleimanPicZeroProper` (the autofold) and
  `picZeroAbVar0_of_printed : PicLocFinType → IdentityComponentLFT → KleimanPicZeroProperPrinted → PicZeroAbVar0`
  (the hand fold; abelian varieties are geometrically integral, have the identity point and are projective by
  `T09Pic.exists_isVeryAmple`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory

namespace KleimanSection

open Scheme

variable {X S : Scheme.{u}}

/-- The image of `Pic(T)` in `Pic(X ×_S T)` under pullback along the projection. -/
abbrev picBase (f : X ⟶ S) (T : Over S) : Subgroup (pullback f T.hom).Pic :=
  (Pic.mapHom (pullback.snd f T.hom)).range

lemma map_baseChangeMap_map_snd (f : X ⟶ S) {T T' : Over S} (φ : T' ⟶ T) (M : T.left.Pic) :
    Pic.map (JacobianChallenge.baseChangeMap f φ) (Pic.map (pullback.snd f T.hom) M) =
      Pic.map (pullback.snd f T'.hom) (Pic.map φ.left M) := by
  rw [← Pic.map_comp, ← Pic.map_comp, pullback.lift_snd]

/-- **Kleiman's relative Picard functor** (Kleiman, *The Picard scheme*, Def. 9.2.2; UNVERIFIED numbering) as a
presheaf of groups: `T ↦ Pic(X ×_S T) / Pic(T)`. -/
def kleimanPicardPresheafGrp (f : X ⟶ S) : (Over S)ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj T := GrpCat.of ((pullback f T.unop.hom).Pic ⧸ picBase f T.unop)
  map φ := GrpCat.ofHom (QuotientGroup.map _ _ (Pic.mapHom (JacobianChallenge.baseChangeMap f φ.unop)) (by
    rintro _ ⟨M, rfl⟩
    exact ⟨Pic.map φ.unop.left M, (map_baseChangeMap_map_snd f φ.unop M).symm⟩))
  map_id T := by
    refine GrpCat.hom_ext (QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ ?_))
    change (QuotientGroup.mk (Pic.map (JacobianChallenge.baseChangeMap f (𝟙 T).unop) x) :
      (pullback f T.unop.hom).Pic ⧸ picBase f T.unop) = QuotientGroup.mk x
    rw [unop_id, JacobianChallenge.baseChangeMap_id, Pic.map_id]
  map_comp φ ψ := by
    refine GrpCat.hom_ext (QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x ↦ ?_))
    change (QuotientGroup.mk (Pic.map (JacobianChallenge.baseChangeMap f (φ ≫ ψ).unop) x) : _ ⧸ _) =
      QuotientGroup.mk (Pic.map (JacobianChallenge.baseChangeMap f ψ.unop)
        (Pic.map (JacobianChallenge.baseChangeMap f φ.unop) x))
    rw [unop_comp, JacobianChallenge.baseChangeMap_comp, Pic.map_comp]

/-- Kleiman's relative Picard functor `T ↦ Pic(X_T)/Pic(T)` as a presheaf of sets. -/
abbrev kleimanPicardPresheaf (f : X ⟶ S) : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  kleimanPicardPresheafGrp f ⋙ forget GrpCat

/-- **Kleiman's `Pic_{(X/S)(fppf)}`**: the fppf sheafification of `T ↦ Pic(X_T)/Pic(T)` (Kleiman, *The Picard
scheme*, Def. 9.2.2; UNVERIFIED numbering). -/
def kleimanPicardSheaf (f : X ⟶ S) : Sheaf (fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (fppfTopology.over S) (Type (u + 1))).obj (kleimanPicardPresheaf f)

/-- The quotient map `Pic(X_T) → Pic(X_T)/Pic(T)`, as a morphism of presheaves of groups. -/
def quotGrp (f : X ⟶ S) : picardPresheafGrp f ⟶ kleimanPicardPresheafGrp f where
  app T := GrpCat.ofHom (QuotientGroup.mk' (picBase f T.unop))
  naturality T T' φ := by
    refine GrpCat.hom_ext (MonoidHom.ext fun x ↦ ?_)
    rfl

/-- The quotient map as a morphism of presheaves of sets, out of `picardPresheaf`. -/
def quot (f : X ⟶ S) : picardPresheaf f ⟶ kleimanPicardPresheaf f :=
  Functor.whiskerRight (quotGrp f) (forget GrpCat)

instance isLocallySurjective_quot (f : X ⟶ S) :
    Presheaf.IsLocallySurjective (fppfTopology.over S) (quot f) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun T y ↦ by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := picBase f T.unop) y
    exact ⟨x, rfl⟩

instance isLocallyInjective_quot (f : X ⟶ S) :
    Presheaf.IsLocallyInjective (fppfTopology.over S) (quot f) where
  equalizerSieve_mem {T} x y h := by
    change (pullback f T.unop.hom).Pic at x y
    have h' : (QuotientGroup.mk x : (pullback f T.unop.hom).Pic ⧸ picBase f T.unop) = QuotientGroup.mk y := h
    obtain ⟨M, hM⟩ := QuotientGroup.eq.mp h'
    have hy : y = x * Pic.map (pullback.snd f T.unop.hom) M := by
      rw [show Pic.map (pullback.snd f T.unop.hom) M = x⁻¹ * y from hM, mul_inv_cancel_left]
    choose cover membership triv using fun point : T.unop.left ↦ Pic.exists_map_iota_eq_one M point
    rw [GrothendieckTopology.mem_over_iff]
    refine fppfTopology.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck
      (R := Presieve.ofArrows (fun point ↦ (cover point).toScheme) (fun point ↦ (cover point).ι)) ?_)
    · rw [Sieve.generate_le_iff]
      rintro _ _ ⟨point⟩
      rw [Sieve.overEquiv_iff]
      let restriction : Over.mk ((cover point).ι ≫ T.unop.hom) ⟶ T.unop := Over.homMk (cover point).ι
      change Pic.map (JacobianChallenge.baseChangeMap f restriction) x =
        Pic.map (JacobianChallenge.baseChangeMap f restriction) y
      rw [hy, Pic.map_mul, map_baseChangeMap_map_snd]
      change _ = _ * Pic.map _ (Pic.map (cover point).ι M)
      rw [triv point, Pic.map_one, mul_one]
    · rw [fppfPrecoverage, ofArrows_mem_precoverage_iff]
      exact ⟨fun point ↦ ⟨point, ⟨point, membership point⟩, rfl⟩,
        fun point ↦ ⟨inferInstance, inferInstance⟩⟩

instance isIso_presheafToSheaf_map_quot (f : X ⟶ S) :
    IsIso ((presheafToSheaf (fppfTopology.over S) (Type (u + 1))).map (quot f)) :=
  ((fppfTopology.over S).W_iff _).mp ((fppfTopology.over S).W_of_isLocallyBijective _)

/-- **Comparison (no section needed).** The tree's `picardFunctor f` (the fppf sheafification of
`T ↦ Pic(X_T)`) is isomorphic to Kleiman's `Pic_{(X/S)(fppf)}` (the fppf sheafification of
`T ↦ Pic(X_T)/Pic(T)`), by the sheafified quotient map. -/
def picardFunctorIsoKleiman (f : X ⟶ S) : picardFunctor f ≅ kleimanPicardSheaf f :=
  asIso ((presheafToSheaf (fppfTopology.over S) (Type (u + 1))).map (quot f))


/-- The group law of a scheme representing Kleiman's `Pic_{(X/S)(fppf)}`, induced from the quotient groups
`Pic(X_T)/Pic(T)` (the same construction as the tree's `picardFunctorCommGrpObj`). -/
@[instance_reducible]
def kleimanPicardGrpObj (f : X ⟶ S) {P : Over S} (rep : (kleimanPicardSheaf f).obj.RepresentableBy P) :
    GrpObj P :=
  GrpObj.ofRepresentableBySheafify (fppfTopology.over S) (kleimanPicardPresheafGrp f) P rep

/-- A representation of the tree's `picardFunctor` is a representation of Kleiman's sheaf. -/
def repKleiman (f : X ⟶ S) {P : Over S} (rep : (picardFunctor f).obj.RepresentableBy P) :
    (kleimanPicardSheaf f).obj.RepresentableBy P :=
  rep.ofIso ((sheafToPresheaf _ _).mapIso (picardFunctorIsoKleiman f))

/-- A representation of Kleiman's sheaf is a representation of the tree's `picardFunctor`. -/
def repTree (f : X ⟶ S) {P : Over S} (rep : (kleimanPicardSheaf f).obj.RepresentableBy P) :
    (picardFunctor f).obj.RepresentableBy P :=
  rep.ofIso ((sheafToPresheaf _ _).mapIso (picardFunctorIsoKleiman f).symm)

open scoped MonObj in
/-- The identity points agree: the class of the trivial bundle maps to the class of the trivial bundle. -/
lemma eta_repKleiman (f : X ⟶ S) {P : Over S} (rep : (picardFunctor f).obj.RepresentableBy P) :
    (letI := kleimanPicardGrpObj f (repKleiman f rep); η[P]) =
      (letI := picardFunctorCommGrpObj f rep; η[P]) := by
  change (repKleiman f rep).homEquiv.symm
      ((toSheafify (fppfTopology.over S) (kleimanPicardPresheaf f)).app _
        (1 : (pullback f (𝟙_ (Over S)).hom).Pic ⧸ picBase f (𝟙_ (Over S)))) =
    rep.homEquiv.symm ((toSheafify (fppfTopology.over S) (picardPresheaf f)).app _
      (1 : (pullback f (𝟙_ (Over S)).hom).Pic))
  rw [Equiv.symm_apply_eq]
  change _ = ((presheafToSheaf (fppfTopology.over S) (Type (u + 1))).map (quot f)).hom.app _
    (rep.homEquiv (rep.homEquiv.symm ((toSheafify (fppfTopology.over S) (picardPresheaf f)).app _
      (1 : (pullback f (𝟙_ (Over S)).hom).Pic))))
  rw [Equiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom (congr_app (toSheafify_naturality (fppfTopology.over S) (quot f))
    (op (𝟙_ (Over S)))) (1 : (pullback f (𝟙_ (Over S)).hom).Pic)


/-! ## The leaves and the derivations -/

open T09Pic PkgI3 PkgI3.AbVar PicDict PicFix

/-- The identity components of the two group laws on a representing scheme agree. -/
lemma identityComponent_repKleiman {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P : Over (Spec (CommRingCat.of K))} (rep : (picardFunctor X.hom).obj.RepresentableBy P) :
    (letI := kleimanPicardGrpObj X.hom (repKleiman X.hom rep); identityComponent P) =
      (letI := picardFunctorCommGrpObj X.hom rep; identityComponent P) := by
  unfold identityComponent
  rw [eta_repKleiman]

/-- **LEAF (printed form, proper reading).** Kleiman, *The Picard scheme* (FGA Explained, Ch. 9), Thm 9.5.4: for `X`
proper and geometrically normal over a field `K`, the identity component `Pic⁰_{X/K}` of the Picard scheme is
proper. Here `Pic_{X/K}` is any scheme representing Kleiman's `Pic_{(X/K)(fppf)}`, the fppf sheafification of
`T ↦ Pic(X_T)/Pic(T)` (Def. 9.2.2), with its induced group law, and `V` any open on the identity component; both are
unique up to unique isomorphism, so the print's existence statements become quantifiers. Numbering UNVERIFIED; reading
risks: the print may assume `X` projective, and may represent the étale sheaf (see `KleimanPicZeroProperPrinted`). -/
def KleimanPicZeroProperQ : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))), IsProper X.hom →
    geometrically IsNormalScheme X.hom →
    ∀ (P : Over (Spec (CommRingCat.of K))) (rep : (kleimanPicardSheaf X.hom).obj.RepresentableBy P)
      (V : P.left.Opens),
      letI := kleimanPicardGrpObj X.hom rep
      (V : Set P.left) = identityComponent P → IsProper (V.ι ≫ P.hom)

/-- **The autofold**: `PicFix.KleimanPicZeroProper` (stated over the tree's `picardFunctor`) from Kleiman 9.5.4 over
Kleiman's functor, by `picardFunctorIsoKleiman` (no section needed). -/
theorem kleimanPicZeroProper_of_Q (h : KleimanPicZeroProperQ) : PicFix.KleimanPicZeroProper := by
  intro K _ X hX hN P rep V hV
  refine h K X hX hN P (repKleiman X.hom rep) V ?_
  rw [identityComponent_repKleiman]
  exact hV

/-- **LEAF (printed form, weakest reading).** Kleiman, *The Picard scheme* (FGA Explained, Ch. 9), Thm 9.5.4
(numbering UNVERIFIED), restricted to `X` that are moreover geometrically integral, projective over `K` (proper with an
immersion into `ℙ^N_K` over `K`, hence a closed immersion) and have a `K`-point `σ`: then the identity component of
any scheme representing Kleiman's `Pic_{(X/K)(fppf)}` (the fppf sheafification of `T ↦ Pic(X_T)/Pic(T)`, Def. 9.2.2)
is proper. It is a consequence of the print under each reading: if the print assumes projective, the hypotheses here
include it, and "proper" is weaker than "projective"; if the print's `Pic_{X/K}` represents the étale sheaf, then by
Kleiman Thm 9.2.5 (a section and `𝒪_K = f_*𝒪_X` universally, which holds for `X` proper and geometrically integral)
`T ↦ Pic(X_T)/Pic(T)` is already an fppf sheaf, so the étale and fppf sheafifications coincide (numbers UNVERIFIED). -/
def KleimanPicZeroProperPrinted : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))), IsProper X.hom →
    GeometricallyIntegral X.hom → geometrically IsNormalScheme X.hom →
    (∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of K))),
      IsImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = X.hom) →
    (∃ σ : Spec (CommRingCat.of K) ⟶ X.left, σ ≫ X.hom = 𝟙 _) →
    ∀ (P : Over (Spec (CommRingCat.of K))) (rep : (kleimanPicardSheaf X.hom).obj.RepresentableBy P)
      (V : P.left.Opens),
      letI := kleimanPicardGrpObj X.hom rep
      (V : Set P.left) = identityComponent P → IsProper (V.ι ≫ P.hom)

/-- The weakest-reading form is a consequence of the proper-reading form. -/
theorem kleimanPicZeroProperPrinted_of_Q (h : KleimanPicZeroProperQ) : KleimanPicZeroProperPrinted :=
  fun K _ X hX _ hN _ _ => h K X hX hN

open scoped MonObj in
/-- `PicZeroProperAt K` (the abelian-variety instance) from the weakest-reading form: an abelian variety is proper,
geometrically integral, smooth (hence geometrically normal), projective (`T09Pic.exists_isVeryAmple`) and has the
identity point. -/
theorem picZeroProperAt_of_printed (h : KleimanPicZeroProperPrinted) (K : Type) [Field K] :
    PicZeroChar0.PicZeroProperAt K := by
  intro A P rep V hV
  obtain ⟨L, N, hN, i, hi, hover, -⟩ := exists_isVeryAmple A
  refine h K A.X inferInstance inferInstance (geometricallyNormal_of_smooth A.X.hom) ⟨N, hN, i, hi, hover⟩
    ⟨η[A.X].left, Over.w η[A.X]⟩ P (repKleiman A.X.hom rep) V ?_
  rw [identityComponent_repKleiman]
  exact hV

/-- **The hand fold's consumer**: `PicZeroChar0.PicZeroAbVar0` from `PicLocFinType`, `IdentityComponentLFT` (both
proved in `Contrib/OneProof`) and `KleimanPicZeroProperPrinted`, with Cartier's theorem proved. Same argument as
`PicZeroChar0.picZeroAbVar0_of_leaves`. -/
theorem picZeroAbVar0_of_printed (h1 : PicLocFinType) (h2 : IdentityComponentLFT)
    (h3 : KleimanPicZeroProperPrinted) : PicZeroChar0.PicZeroAbVar0 := fun K _ _ =>
  PicZeroChar0.picZeroAbVarAt_of h1 h2 K
    (PicZeroChar0.picZeroSmoothAt_charZero ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof h1 K)
    (picZeroProperAt_of_printed h3 K)

end KleimanSection

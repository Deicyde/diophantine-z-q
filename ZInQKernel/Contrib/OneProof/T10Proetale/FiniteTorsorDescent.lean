import ZInQKernel.Contrib.OneProof.T10Proetale.AffineLocalLifts
import ZInQKernel.Contrib.OneProof.T10Proetale.LocalRepresentatives
import ZInQKernel.Contrib.OneProof.T10Proetale.MapDescentDatum
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Comma.Over.DescentRepresentable
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.AffineLocal
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.Gluing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# The split lift torsor and its descent datum

The local pointwise representations of the lift sheaf form a representation
on the slice of the small site. On a quasi-compact separated base, a single
affine cover carries the overlap datum and effective descent gives a finite
étale scheme representing the lift sheaf.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace ZInQ.Manuscript.T10Proetale

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Scheme.{0}} {B : Type} [TopologicalSpace B] [DiscreteTopology B]
  [AddCommGroup B] [IsTopologicalAddGroup B]

private abbrev coeffPresentation := injectivePresentation (continuousCoefficients X B)

private abbrev quotientSections (X : Scheme.{0}) (B : Type)
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B] :=
  (coeffPresentation (X := X) (B := B)).X₃.obj.obj (op (T10Etale.terminalProEt X))

private abbrev liftPsh (s : quotientSections X B) :=
  (liftSheaf (S := coeffPresentation) (T10Etale.isTerminalProEt X) s).obj

set_option backward.isDefEq.respectTransparency false in
theorem splitProjection_etale (V : Scheme.{0}) : Etale (splitProjection V B) :=
  IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ => inferInstance)

set_option backward.isDefEq.respectTransparency false in
theorem splitProjection_finite (V : Scheme.{0}) [IsAffine V] [Finite B] :
    IsFinite (splitProjection V B) := by
  let e : V ≅ Spec Γ(V, ⊤) := V.isoSpec
  let E : (∐ fun _ : B => V) ≅ (∐ fun _ : B => Spec Γ(V, ⊤)) :=
    Limits.Sigma.mapIso fun _ : B => e
  have h : splitProjection V B ≫ e.hom =
      E.hom ≫ splitProjection (Spec Γ(V, ⊤)) B := by
    apply Limits.Sigma.hom_ext
    intro i
    simp [splitProjection, E]
  have := splitProjection_spec_finite (I := B) Γ(V, ⊤)
  have hh : IsFinite (E.hom ≫ splitProjection (Spec Γ(V, ⊤)) B) := inferInstance
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsFinite) (splitProjection V B)
    e.hom).mp (h.symm ▸ hh)

private abbrev splitSite (V : X.ProEt) : X.ProEt :=
  have : Etale (splitProjection V.left B) := splitProjection_etale (B := B) V.left
  .mk (splitProjection V.left B ≫ V.hom)

private def splitSiteMap (V : X.ProEt) : splitSite (B := B) V ⟶ V :=
  MorphismProperty.Over.homMk (splitProjection V.left B) rfl

set_option backward.isDefEq.respectTransparency false in
private def splitSliceHomEquiv {V : X.ProEt} (W : Over V) :
    (W ⟶ Over.mk (splitSiteMap (B := B) V)) ≃
      {r : W.left.left ⟶ (∐ fun _ : B => V.left) //
        r ≫ splitProjection V.left B = W.hom.left} where
  toFun f := ⟨f.left.left, by
    have h := congrArg (proUnderlying X).map (Over.w f)
    rw [Functor.map_comp] at h
    exact h⟩
  invFun r :=
    Over.homMk (MorphismProperty.Over.homMk r.val (by
      change r.val ≫ splitProjection V.left B ≫ V.hom = W.left.hom
      rw [← Category.assoc, r.2]
      exact ((Scheme.ProEt.forget X).map W.hom).w)) (by
        apply (proUnderlying X).map_injective
        exact r.2)
  left_inv f := Over.OverMorphism.ext ((proUnderlying X).map_injective rfl)
  right_inv _ := rfl

private theorem localLiftSections_congr (s : quotientSections X B) {V W : X.ProEt}
    (x : (liftPsh s).obj (op V)) {f g : W ⟶ V} (e : f = g)
    (p : { r : W.left ⟶ (∐ fun _ : B => V.left) // r ≫ splitProjection V.left B = f.left }) :
    localLiftSections s x f p =
      localLiftSections s x g ⟨p.val, p.property.trans (congrArg (proUnderlying X).map e)⟩ := by
  subst g
  rfl

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- A chosen lift gives a representation of the actual lift sheaf on the slice. -/
def liftSheafRepresentableOnSlice (s : quotientSections X B) {V : X.ProEt}
    (x : (liftPsh s).obj (op V)) :
    ((Over.forget V).op ⋙ liftPsh s).RepresentableBy (Over.mk (splitSiteMap (B := B) V)) where
  homEquiv {W} := (splitSliceHomEquiv W).trans (localLiftSections s x W.hom)
  homEquiv_comp {W W'} f g := by
    let r := splitSliceHomEquiv W' g
    let e : f.left ≫ W'.hom = W.hom := Over.w f
    let r' : { q : W.left.left ⟶ (∐ fun _ : B => V.left) //
        q ≫ splitProjection V.left B = (f.left ≫ W'.hom).left } :=
      ⟨f.left.left ≫ r.val, by
        rw [Category.assoc, r.property]
        rfl⟩
    change localLiftSections s x W.hom (splitSliceHomEquiv W (f ≫ g)) =
      (liftPsh s).map f.left.op (localLiftSections s x W'.hom r)
    have h := localLiftSections_restrict s x W'.hom f.left r
    change (liftPsh s).map f.left.op (localLiftSections s x W'.hom r) =
      localLiftSections s x (f.left ≫ W'.hom) r' at h
    rw [h, localLiftSections_congr s x e r']
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-compact test object has a single affine pro-étale cover with a section
of the lift sheaf. -/
theorem liftSheaf_affineCover (s : quotientSections X B) (U : X.ProEt) [CompactSpace U.left] :
    ∃ (V : X.ProEt) (p : V ⟶ U), IsAffine V.left ∧ WeaklyEtale ((proUnderlying X).map p) ∧
      Surjective ((proUnderlying X).map p) ∧ Nonempty ((liftPsh s).obj (op V)) := by
  obtain ⟨V, p, hv, hp, hsurj, x, hx⟩ := affineCover_lift_of_compactSpace coeffPresentation.g
    (sectionAt (T10Etale.isTerminalProEt X) s U)
    (liftSheaf_locallyNonempty _ s (injectivePresentation_shortExact (continuousCoefficients X B)) U)
  refine ⟨V, p, hv, hp, hsurj, ⟨⟨x, ?_⟩⟩⟩
  change coeffPresentation.g.hom.app (op V) x = sectionAt (T10Etale.isTerminalProEt X) s V
  rw [hx, ← Functor.map_comp_apply, ← op_comp,
    (T10Etale.isTerminalProEt X).hom_ext (p ≫ (T10Etale.isTerminalProEt X).from U)
      ((T10Etale.isTerminalProEt X).from V)]

/-- The split scheme carries the canonical descent datum from the lift sheaf. -/
def liftSheafDescentDatum (s : quotientSections X B) {U V : X.ProEt}
    (p : V ⟶ U) (x : (liftPsh s).obj (op V)) :
    Over.DescentDatum p (Over.mk (splitSiteMap (B := B) V)) :=
  Functor.RepresentableBy.overDescentDatum
    (presheaf := (Over.forget U).op ⋙ liftPsh s) (liftSheafRepresentableOnSlice s x)

private theorem affineOverSeparated {U V : Scheme.{0}} [IsAffine V]
    {S : Scheme.{0}} [IsAffine S] (g : U ⟶ S) [IsSeparated g] (p : V ⟶ U) :
    IsAffineHom p := by
  have : IsAffineHom (p ≫ g) := inferInstance
  exact IsAffineHom.of_comp p g

private theorem isInvariant_preimage {U V : Scheme.{0}} {p : V ⟶ U} {R : Over V}
    (d : Over.DescentDatum p R) (O : U.Opens) : d.IsInvariant ((R.hom ≫ p) ⁻¹ᵁ O) := by
  intro T u v h q hq
  rintro y ⟨x, rfl⟩
  have hs := hq ⟨x, rfl⟩
  have h₁ : (d.transport u v h q).left ≫ R.hom ≫ p = v ≫ p := by
    rw [← Category.assoc, Over.w]
    rfl
  have h₂ : q.left ≫ R.hom ≫ p = u ≫ p := by
    rw [← Category.assoc, Over.w]
    rfl
  change (R.hom ≫ p) ((d.transport u v h q).left x) ∈ O
  change (R.hom ≫ p) (q.left x) ∈ O at hs
  rw [← Scheme.Hom.comp_apply, h₁, ← h, ← h₂]
  exact hs

set_option backward.isDefEq.respectTransparency false in
private theorem isEffective_of_affineMap {U V : Scheme.{0}} {p : V ⟶ U}
    [IsAffineHom p] [Flat p] [Surjective p] {R : Over V} [IsAffineHom R.hom]
    (d : Over.DescentDatum p R) : d.IsEffective := by
  apply d.isEffective_of_forall_exists_mem
  intro x
  obtain ⟨O, hO, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show (R.hom ≫ p) x ∈ (⊤ : U.Opens) from trivial)
  refine ⟨(R.hom ≫ p) ⁻¹ᵁ O, isInvariant_preimage d O, hx, ?_⟩
  exact d.isEffective_restrict_of_isAffineOpen (isInvariant_preimage d O)
    (hO.preimage (R.hom ≫ p)) hO le_rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical split lift datum has finite étale effective descent in schemes
over a base separated over an affine scheme. The compatibility is with the
datum of the actual lift sheaf on the small site. -/
theorem liftSheaf_finiteEtaleDescent [Finite B]
    (s : quotientSections X B) {U V : X.ProEt} {S : Scheme.{0}} [IsAffine S]
    (g : U.left ⟶ S) [IsSeparated g] [IsAffine V.left]
    (p : V ⟶ U) [Surjective ((proUnderlying X).map p)]
    (x : (liftPsh s).obj (op V)) :
    ∃ (D : Over U.left) (k : (∐ fun _ : B => V.left) ⟶ D.left),
      IsFinite D.hom ∧ Etale D.hom ∧ Surjective D.hom ∧
      IsPullback k (splitProjection V.left B) D.hom ((proUnderlying X).map p) ∧
      ∀ {T : X.ProEt} (u v : T ⟶ V) (e : u ≫ p = v ≫ p)
        (q : Over.mk u ⟶ Over.mk (splitSiteMap (B := B) V)),
        (proUnderlying X).map ((liftSheafDescentDatum s p x).transport u v e q).left ≫ k =
          (proUnderlying X).map q.left ≫ k := by
  let F := proUnderlying X
  have : WeaklyEtale (F.map p ≫ U.hom) := by
    have h : F.map p ≫ U.hom = V.hom := ((Scheme.ProEt.forget X).map p).w
    rw [h]
    infer_instance
  have : WeaklyEtale (F.map p) := WeaklyEtale.of_comp _ U.hom
  have : Flat (F.map p) := inferInstance
  have : IsAffine (F.obj V) := ‹IsAffine V.left›
  have : IsAffineHom (F.map p) := affineOverSeparated (V := F.obj V) g (F.map p)
  have : QuasiCompact (F.map p) := inferInstance
  let d := liftSheafDescentDatum s p x
  let d' := mapDescentDatum F d
  have : IsFinite ((Over.post F).obj (Over.mk (splitSiteMap (B := B) V))).hom :=
    splitProjection_finite (B := B) V.left
  obtain ⟨D, k, hk, hinv⟩ := isEffective_of_affineMap d'
  have := splitProjection_surjective (I := B) V.left
  have : Surjective (k ≫ D.hom) := hk.w.symm ▸
    inferInstanceAs (Surjective (splitProjection V.left B ≫ F.map p))
  have hp : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (F.map p) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hfin := AlgebraicGeometry.IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  refine ⟨D, k,
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsFinite) hk.flip hp
      (splitProjection_finite (B := B) V.left),
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale) hk.flip hp
      (splitProjection_etale (B := B) V.left), Surjective.of_comp k D.hom, hk, ?_⟩
  intro T u v e q
  let eq := (F.map_comp u p).symm.trans
    ((congrArg F.map e).trans (F.map_comp v p))
  have h := hinv (F.map u) (F.map v) eq ((Over.post F).map q)
  rw [mapDescentDatum_transport_image] at h
  exact h

private theorem proPullbackCover {U V : X.ProEt} (p : V ⟶ U)
    [WeaklyEtale ((proUnderlying X).map p)] [Surjective ((proUnderlying X).map p)]
    [QuasiCompact ((proUnderlying X).map p)] (W : Over U) :
    Sieve.generate (Presieve.singleton (pullback.fst W.hom p)) ∈
      Scheme.ProEt.topology X W.left := by
  let F := proUnderlying X
  have h := F.map_isPullback (IsPullback.of_hasPullback W.hom p)
  let : WeaklyEtale (F.map (pullback.fst W.hom p)) :=
    MorphismProperty.of_isPullback (P := @WeaklyEtale) h.flip inferInstance
  let : Surjective (F.map (pullback.fst W.hom p)) :=
    MorphismProperty.of_isPullback (P := @Surjective) h.flip inferInstance
  let : QuasiCompact (F.map (pullback.fst W.hom p)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) h.flip inferInstance
  exact proSingletonCover _

private theorem liftCover_epi {U V : X.ProEt} (p : V ⟶ U)
    [WeaklyEtale ((proUnderlying X).map p)] [Surjective ((proUnderlying X).map p)]
    [QuasiCompact ((proUnderlying X).map p)] (W : Over U) :
    Epi (pullback.fst W.hom p) := by
  let F := proUnderlying X
  have h := F.map_isPullback (IsPullback.of_hasPullback W.hom p)
  let : Flat (F.map (pullback.fst W.hom p)) :=
    MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  let : Surjective (F.map (pullback.fst W.hom p)) :=
    MorphismProperty.of_isPullback (P := @Surjective) h.flip inferInstance
  let := Flat.epi_of_flat_of_surjective (F.map (pullback.fst W.hom p))
  exact Functor.epi_of_epi_map F (f := pullback.fst W.hom p) inferInstance

open Functor.RepresentableBy in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
/-- On a quasi-compact object separated over an affine scheme, the degree-one
lift sheaf on the slice is represented by a finite étale cover. -/
theorem liftSheaf_finiteEtaleRepresentable [Finite B] (s : quotientSections X B)
    (U : X.ProEt) {S : Scheme.{0}} [IsAffine S] (g : U.left ⟶ S)
    [CompactSpace U.left] [IsSeparated g] :
    ∃ (D : X.ProEt) (d : D ⟶ U), IsFinite ((proUnderlying X).map d) ∧
      Etale ((proUnderlying X).map d) ∧ Surjective ((proUnderlying X).map d) ∧
      Nonempty (((Over.forget U).op ⋙ liftPsh s).RepresentableBy (Over.mk d)) := by
  obtain ⟨V, p, ha, hwe, hsurj, ⟨x⟩⟩ := liftSheaf_affineCover s U
  let F := proUnderlying X
  have : IsAffine (F.obj V) := ha
  have : IsAffineHom (F.map p) := affineOverSeparated (V := F.obj V) g (F.map p)
  have : QuasiCompact (F.map p) := inferInstance
  obtain ⟨D', k', hfin, het, hs, hk, hinv⟩ := liftSheaf_finiteEtaleDescent s g p x
  let D : X.ProEt := .mk (D'.hom ≫ U.hom)
  let d : D ⟶ U := MorphismProperty.Over.homMk D'.hom rfl
  let k : splitSite (B := B) V ⟶ D := MorphismProperty.Over.homMk k' (by
    change k' ≫ D'.hom ≫ U.hom = splitProjection V.left B ≫ V.hom
    have h := ((Scheme.ProEt.forget X).map p).w
    rw [← Category.assoc, hk.w, Category.assoc]
    exact congrArg (splitProjection V.left B ≫ ·) h)
  have hk' : IsPullback k (splitSiteMap (B := B) V) d p :=
    IsPullback.of_map_of_faithful F hk
  let r : ((Over.map p).op ⋙ (Over.forget U).op ⋙ liftPsh s).RepresentableBy
      (Over.mk (splitSiteMap (B := B) V)) := liftSheafRepresentableOnSlice s x
  refine ⟨D, d, hfin, het, hs, r.nonempty_representableBy_of_descent k hk' ?_ (liftCover_epi p) ?_ ?_⟩
  · intro T u v e q
    apply F.map_injective
    rw [Functor.map_comp, Functor.map_comp]
    change F.map ((liftSheafDescentDatum s p x).transport u v e q).left ≫ k' = F.map q.left ≫ k'
    exact hinv u v e q
  · intro W q hq
    let J := Scheme.ProEt.topology X
    have h := (Presieve.isSheafFor_iff_generate _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) (yoneda.obj D) _
        (proPullbackCover p W))
    refine (Presieve.isSheafFor_singleton.mp h q ?_).exists
    intro Z v w eq
    let t := pullback.lift v w eq
    have ht := congrArg (t ≫ ·) hq
    change v ≫ q = w ≫ q
    simpa only [← Category.assoc, t, pullback.lift_fst, pullback.lift_snd] using ht
  · intro W
    let J := Scheme.ProEt.topology X
    let P := (J.overPullback (Type 1) U).obj
      (liftSheaf (S := coeffPresentation) (T10Etale.isTerminalProEt X) s)
    apply (Presieve.isSheafFor_iff_generate _).mpr
    change Presieve.IsSheafFor P.obj _
    refine ((isSheaf_iff_isSheaf_of_type _ _).mp P.property) _ ?_
    rw [J.mem_over_iff, Sieve.overEquiv_generate,
      ← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve,
      Presieve.map_singleton]
    exact proPullbackCover p W

set_option backward.isDefEq.respectTransparency false in
/-- A quotient section's lift sheaf on the whole small site of a quasi-compact
scheme separated over an affine scheme is represented by a finite étale
surjection. -/
theorem liftSheaf_globalRepresentable [Finite B] (s : quotientSections X B)
    {S : Scheme.{0}} [IsAffine S] (g : X ⟶ S) [CompactSpace X] [IsSeparated g] :
    ∃ D : X.ProEt, IsFinite D.hom ∧ Etale D.hom ∧ Surjective D.hom ∧
      Nonempty ((liftPsh s).RepresentableBy D) := by
  let T := T10Etale.terminalProEt X
  let hT := T10Etale.isTerminalProEt X
  have : CompactSpace T.left := ‹CompactSpace X›
  have : IsSeparated (g : T.left ⟶ S) := ‹IsSeparated g›
  obtain ⟨D, d, hf, he, hs, ⟨r⟩⟩ := liftSheaf_finiteEtaleRepresentable s T g
  have h : (proUnderlying X).map d = D.hom := by
    have hw := ((Scheme.ProEt.forget X).map d).w
    change (proUnderlying X).map d ≫ 𝟙 X = D.hom at hw
    exact (Category.comp_id _).symm.trans hw
  refine ⟨D, h ▸ hf, h ▸ he, h ▸ hs, ⟨?_⟩⟩
  let e (W : X.ProEt) : (W ⟶ D) ≃ (Over.mk (hT.from W) ⟶ Over.mk d) :=
    { toFun := fun f => Over.homMk f (hT.hom_ext _ _)
      invFun := fun f => f.left
      left_inv := fun _ => rfl
      right_inv := fun _ => Over.OverMorphism.ext rfl }
  refine { homEquiv := fun {W} => (e W).trans r.homEquiv, homEquiv_comp := ?_ }
  intro W W' f k
  exact r.homEquiv_comp
    (Over.homMk (U := Over.mk (hT.from W)) (V := Over.mk (hT.from W')) f (hT.hom_ext _ _))
    (e W' k)

set_option backward.isDefEq.respectTransparency false in
/-- Each actual finite pro-étale degree-one class has a quotient-section
representative whose lift sheaf is a finite étale cover. The class vanishes
exactly when this cover has a section. -/
theorem proFiniteH1_representable (ℓ n : ℕ) [Fact ℓ.Prime] (a : ProFiniteH X ℓ n 1)
    {S : Scheme.{0}} [IsAffine S] (g : X ⟶ S) [CompactSpace X] [IsSeparated g] :
    ∃ (s : quotientSections X (ZMod (ℓ ^ n))) (D : X.ProEt),
      classOfSection (T10Etale.isTerminalProEt X) (continuousCoefficients X (ZMod (ℓ ^ n))) s = a ∧
      IsFinite D.hom ∧ Etale D.hom ∧ Surjective D.hom ∧
      Nonempty ((liftPsh s).RepresentableBy D) ∧
      (a = 0 ↔ ∃ f : X ⟶ D.left, f ≫ D.hom = 𝟙 X) := by
  let T := T10Etale.terminalProEt X
  let hT := T10Etale.isTerminalProEt X
  let F := continuousCoefficients X (ZMod (ℓ ^ n))
  obtain ⟨s, hs⟩ := classOfSection_surjective hT F a
  obtain ⟨D, hf, he, hsur, ⟨r⟩⟩ := liftSheaf_globalRepresentable s g
  refine ⟨s, D, hs, hf, he, hsur, ⟨r⟩, ?_⟩
  rw [← hs, classOfSection_eq_zero_iff]
  have hS : sectionAt (S := injectivePresentation F) hT s T = s := by
    have h : hT.from T = 𝟙 T := hT.hom_ext _ _
    change (injectivePresentation F).X₃.obj.map (hT.from T).op s = s
    rw [h, op_id, Functor.map_id_apply]
  have H : Nonempty (sectionLifts (S := injectivePresentation F) s) ↔
      Nonempty ((liftPsh s).obj (op T)) := by
    change Nonempty (sectionLifts (S := injectivePresentation F) s) ↔
      Nonempty (sectionLifts (S := injectivePresentation F) (sectionAt hT s T))
    rw [hS]
  refine H.trans ((Equiv.nonempty_congr r.homEquiv.symm).trans ?_)
  exact ⟨fun ⟨f⟩ => ⟨f.left, ((Scheme.ProEt.forget X).map f).w⟩,
    fun ⟨f, h⟩ => ⟨MorphismProperty.Over.homMk f h⟩⟩

set_option backward.isDefEq.respectTransparency false in
private def pullbackSliceHomEquivOfTerminal {T D : X.ProEt} (hT : IsTerminal T) (W : Over D) :
    (W ⟶ Over.mk (pullback.snd (hT.from D) (hT.from D))) ≃ (W.left ⟶ D) where
  toFun f := f.left ≫ pullback.fst _ _
  invFun f := Over.homMk (pullback.lift f W.hom (hT.hom_ext _ _)) (pullback.lift_snd ..)
  left_inv f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst ..
    · exact (pullback.lift_snd ..).trans (Over.w f).symm
  right_inv f := pullback.lift_fst ..

set_option backward.isDefEq.respectTransparency false in
/-- The representing cover splits on pullback to itself, using the lift
corresponding to its identity map. This is the geometric trivialization
of the actual sheaf, on the small site's slice over the cover. -/
def liftSheaf_selfPullbackSplits (s : quotientSections X B) {D : X.ProEt}
    (r : (liftPsh s).RepresentableBy D) :
    Over.mk (pullback.snd ((T10Etale.isTerminalProEt X).from D)
      ((T10Etale.isTerminalProEt X).from D)) ≅
        Over.mk (splitSiteMap (B := B) D) := by
  let hT := T10Etale.isTerminalProEt X
  let p := hT.from D
  change Over.mk (pullback.snd p p) ≅ Over.mk (splitSiteMap (B := B) D)
  let r' : ((Over.forget D).op ⋙ liftPsh s).RepresentableBy (Over.mk (pullback.snd p p)) :=
    { homEquiv := fun {W} => (pullbackSliceHomEquivOfTerminal hT W).trans r.homEquiv
      homEquiv_comp := by
        intro W W' f q
        change r.homEquiv ((f.left ≫ q.left) ≫ pullback.fst p p) =
          (liftPsh s).map f.left.op (r.homEquiv (q.left ≫ pullback.fst p p))
        rw [Category.assoc, r.homEquiv_comp] }
  exact r'.uniqueUpToIso (liftSheafRepresentableOnSlice s (r.homEquiv (𝟙 D)))

end
end ZInQ.Manuscript.T10Proetale

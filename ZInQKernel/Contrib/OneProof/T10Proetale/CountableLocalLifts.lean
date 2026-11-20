import ZInQKernel.Contrib.OneProof.T10Proetale.AffineWeaklyEtaleLimits
import ZInQKernel.Contrib.OneProof.T10Proetale.AffineLocalLifts

/-!
# Countable products of pro-étale epimorphisms

Successively lift one more coordinate over an affine cover of the preceding
stage. The limit cover maps to each stage, so that all the lifts can be read on
that one cover. This applies to the actual small pro-étale site.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

variable {X : Scheme.{0}}

private abbrev J := Scheme.ProEt.topology X

private abbrev ASh := Sheaf (J (X := X)) Ab.{1}

private structure LiftStep {U : X.ProEt} {F G : ASh (X := X)}
    (f : F ⟶ G) (s : G.obj.obj (op U)) where
  V : X.ProEt
  p : V ⟶ U
  affine : IsAffine V.left
  weaklyEtale : WeaklyEtale ((proUnderlying X).map p)
  surjective : Surjective ((proUnderlying X).map p)
  lifts : (Presheaf.imageSieve f.hom s) p

private def chooseLiftStep {U : X.ProEt} [IsAffine U.left] {F G : ASh (X := X)}
    (f : F ⟶ G) (s : G.obj.obj (op U)) [Sheaf.IsLocallySurjective f] :
    LiftStep f s :=
  let h := affineCover_lift f s (Presheaf.imageSieve_mem _ _ _)
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2.1, h.choose_spec.choose_spec.2.2.1,
    h.choose_spec.choose_spec.2.2.2⟩

section Tower

variable {T : X.ProEt} [IsAffine T.left] {F G : ℕ → ASh (X := X)}
    (f : ∀ n, F n ⟶ G n) [∀ n, Sheaf.IsLocallySurjective (f n)]
    (s : ∀ n, (G n).obj.obj (op T))

private def liftTower : ℕ → Σ U : X.ProEt, {_p : U ⟶ T // IsAffine U.left}
  | 0 => ⟨T, ⟨𝟙 _, inferInstance⟩⟩
  | n + 1 =>
    let stage := liftTower n
    let : IsAffine stage.1.left := stage.2.2
    let step := chooseLiftStep (f n) ((G n).obj.map stage.2.1.op (s n))
    ⟨step.V, ⟨step.p ≫ stage.2.1, step.affine⟩⟩

private def liftTowerStep (n : ℕ) :
    LiftStep (f n) ((G n).obj.map (liftTower f s n).2.1.op (s n)) :=
  let : IsAffine (liftTower f s n).1.left := (liftTower f s n).2.2
  chooseLiftStep (f n) ((G n).obj.map (liftTower f s n).2.1.op (s n))

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- On an affine object, countably many local lifting problems can be solved on
one affine weakly étale covering map. -/
theorem countable_affineCover_lifts :
    ∃ (V : X.ProEt) (a : V ⟶ T), IsAffine V.left ∧ WeaklyEtale ((proUnderlying X).map a) ∧
      Surjective ((proUnderlying X).map a) ∧ ∀ n, (Presheaf.imageSieve (f n).hom (s n)) a := by
  let t := liftTower f s
  let b (n : ℕ) : (t (n + 1)).1 ⟶ (t n).1 := (liftTowerStep f s n).p
  let p (n : ℕ) : (t n).1 ⟶ T := (t n).2.1
  let U (n : ℕ) : Scheme := (t n).1.left
  let (n : ℕ) : IsAffine (U n) := (t n).2.2
  let k (n : ℕ) : U (n + 1) ⟶ U n := (proUnderlying X).map (b n)
  obtain ⟨c, hc, hw, hs⟩ := affineSequenceLimitCover k
    (fun n => (liftTowerStep f s n).weaklyEtale) (fun n => (liftTowerStep f s n).surjective)
  let L := c.pt
  let p₀ : L ⟶ T.left := c.π.app (op 0)
  let : WeaklyEtale p₀ := hw
  let V := Scheme.ProEt.mk (p₀ ≫ T.hom)
  let a : V ⟶ T := MorphismProperty.Over.homMk p₀ rfl
  have hp (n : ℕ) : c.π.app (op n) ≫ (proUnderlying X).map (p n) = p₀ := by
    induction n with
    | zero =>
      change p₀ ≫ 𝟙 T.left = p₀
      exact Category.comp_id _
    | succ n ih =>
      have heq := c.w (homOfLE (Nat.le_succ n)).op
      rw [Functor.ofOpSequence_map_homOfLE_succ] at heq
      change c.π.app (op (n + 1)) ≫ k n = c.π.app (op n) at heq
      change c.π.app (op (n + 1)) ≫ (proUnderlying X).map (b n ≫ p n) = p₀
      rw [Functor.map_comp, ← Category.assoc, heq, ih]
  let q (n : ℕ) : V ⟶ (t n).1 :=
    MorphismProperty.Over.homMk (c.π.app (op n)) (by
      have h := ((Scheme.ProEt.forget X).map (p n)).w
      change (proUnderlying X).map (p n) ≫ T.hom = (t n).1.hom at h
      change c.π.app (op n) ≫ (t n).1.hom = p₀ ≫ T.hom
      rw [← h, ← Category.assoc, hp])
  have hq (n : ℕ) : q n ≫ p n = a := by
    apply (proUnderlying X).map_injective
    rw [Functor.map_comp]
    exact hp n
  refine ⟨V, a, hc, hw, hs, ?_⟩
  intro n
  have h := (liftTowerStep f s n).lifts
  change (Presheaf.imageSieve (f n).hom ((G n).obj.map (p n).op (s n))) (b n) at h
  rw [← Presheaf.pullback_imageSieve] at h
  have h' : (Presheaf.imageSieve (f n).hom (s n)) (p (n + 1)) := h
  exact hq (n + 1) ▸ (Presheaf.imageSieve (f n).hom (s n)).downward_closed h' (q (n + 1))

end Tower

private def sectionType (U : X.ProEt) : ASh (X := X) ⥤ Type 1 :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U) ⋙ forget Ab.{1}

private instance sectionType_preservesLimits (U : X.ProEt) :
    PreservesLimitsOfShape (Discrete ℕ) (sectionType U) := by
  delta sectionType
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem product_section_lifts {F G : ℕ → ASh (X := X)} (f : ∀ n, F n ⟶ G n)
    {U V : X.ProEt} (a : V ⟶ U) (s : (∏ᶜ G).obj.obj (op U))
    (ha : ∀ n, (Presheaf.imageSieve (f n).hom ((Pi.π G n).hom.app (op U) s)) a) :
    (Presheaf.imageSieve (Limits.Pi.map f).hom s) a := by
  choose z hz using ha
  let E := sectionType V
  let lhF := isLimitFanMkObjOfIsLimit E F (Pi.π F) (productIsProduct F)
  let lhG := isLimitFanMkObjOfIsLimit E G (Pi.π G) (productIsProduct G)
  let c : Fan (fun n => E.obj (F n)) := Fan.mk PUnit (fun n => ↾fun _ => z n)
  let y : (∏ᶜ F).obj.obj (op V) := lhF.lift c PUnit.unit
  have hy (n : ℕ) : (Pi.π F n).hom.app (op V) y = z n :=
    ConcreteCategory.congr_hom (lhF.fac c ⟨n⟩) PUnit.unit
  refine ⟨y, ?_⟩
  let w := (Limits.Pi.map f).hom.app (op V) y
  let v := (∏ᶜ G).obj.map a.op s
  change w = v
  suffices h : (↾fun _ : PUnit => w) = (↾fun _ : PUnit => v) from
    ConcreteCategory.congr_hom h PUnit.unit
  apply lhG.hom_ext
  intro ⟨n⟩
  apply ConcreteCategory.hom_ext
  intro u
  change (Pi.π G n).hom.app (op V) w = (Pi.π G n).hom.app (op V) v
  have eq := congrArg (fun g : ∏ᶜ F ⟶ G n => g.hom.app (op V) y) (Limits.Pi.map_π f n)
  change (Pi.π G n).hom.app (op V) w = (f n).hom.app (op V) ((Pi.π F n).hom.app (op V) y) at eq
  rw [eq, hy, hz]
  exact (NatTrans.naturality_apply (Pi.π G n).hom a.op s).symm

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Countable products of epimorphisms of abelian sheaves on the small pro-étale site
are epimorphisms. -/
theorem proProduct_epi {F G : ℕ → ASh (X := X)} (f : ∀ n, F n ⟶ G n)
    [∀ n, Epi (f n)] : Epi (Limits.Pi.map f) := by
  apply (Sheaf.isLocallySurjective_iff_epi' Ab.{1} (Limits.Pi.map f)).mp
  let (n : ℕ) : Sheaf.IsLocallySurjective (f n) :=
    (Sheaf.isLocallySurjective_iff_epi' Ab.{1} _).mpr inferInstance
  constructor
  intro U s
  let R := Presheaf.imageSieve (Limits.Pi.map f).hom s
  have ha (T : X.ProEt) [IsAffine T.left] (g : T ⟶ U) :
      R.pullback g ∈ J (X := X) T := by
    let t := (∏ᶜ G).obj.map g.op s
    obtain ⟨V, a, hV, hwe, hsurj, hl⟩ :=
      countable_affineCover_lifts f (fun n => (Pi.π G n).hom.app (op T) t)
    let : IsAffine V.left := hV
    let : WeaklyEtale ((proUnderlying X).map a) := hwe
    let : Surjective ((proUnderlying X).map a) := hsurj
    let : QuasiCompact ((proUnderlying X).map a) :=
      inferInstanceAs (QuasiCompact (show V.left ⟶ T.left from (proUnderlying X).map a))
    refine (J (X := X)).superset_covering (Sieve.generate_le_iff _ _ |>.mpr ?_)
      (proSingletonCover a)
    rintro _ _ ⟨⟩
    rw [show R.pullback g = Presheaf.imageSieve (Limits.Pi.map f).hom t from
      Presheaf.pullback_imageSieve (Limits.Pi.map f).hom s g]
    exact product_section_lifts f a t hl
  let C := U.left.affineOpenCover
  let T (i : C.I₀) : X.ProEt := .mk (C.f i ≫ U.hom)
  let e (i : C.I₀) : T i ⟶ U := MorphismProperty.Over.homMk (C.f i) rfl
  have hC : Sieve.ofArrows T e ∈ J (X := X) U := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [Scheme.ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    apply Scheme.zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale)
    change C.openCover.presieve₀ ∈ _
    exact C.openCover.mem₀
  refine (J (X := X)).transitive hC R ?_
  rintro T' a ⟨_, b, c, ⟨i⟩, rfl⟩
  have : IsAffine (T i).left := inferInstanceAs (IsAffine (Spec (C.X i)))
  rw [Sieve.pullback_comp]
  exact (J (X := X)).pullback_stable b (ha (T i) (e i))

end
end ZInQ.Manuscript.T10Proetale

import ZInQKernel.Contrib.OneProof.FaltingsDVR.EtaleSections
import ZInQKernel.Contrib.OneProof.FaltingsDVR.EtalePower
import ZInQKernel.Contrib.NeronC.NMPInjective
import ZInQKernel.Contrib.CloudB3W17bReduced.Port.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.BaseChange

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace SmoothGroup

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
  [Field K] [Algebra R K] [IsFractionRing R K]

abbrev genericMap (R K : Type) [CommRing R] [Field K] [Algebra R K] :
    Spec (.of K) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K))

set_option backward.isDefEq.respectTransparency false in
/-- A morphism between étale schemes over a strictly henselian DVR that is
monic on the generic fibre is injective on points of the special fibre. -/
theorem injective_on_closed_of_generic_mono
    {X Y : Over (Spec (.of R))} [Etale X.hom] [Etale Y.hom] [IsSeparated X.hom]
    (u : X ⟶ Y) [Mono ((Over.pullback (genericMap R K)).map u)] :
    Set.InjOn u.left (X.hom ⁻¹' {IsLocalRing.closedPoint R}) := by
  intro x hx y hy h
  obtain ⟨a, ha, hax⟩ := exists_section_over_closed_of_etale X.hom x hx
  obtain ⟨b, hb, hby⟩ := exists_section_over_closed_of_etale X.hom y hy
  let S := Spec (.of R)
  let I : Over S := 𝟙_ (Over S)
  let secA : I ⟶ X := Over.homMk a ha
  let secB : I ⟶ X := Over.homMk b hb
  have hau : (a ≫ u.left) ≫ Y.hom = 𝟙 _ := by rw [Category.assoc, Over.w, ha]
  have hbu : (b ≫ u.left) ≫ Y.hom = 𝟙 _ := by rw [Category.assoc, Over.w, hb]
  have hab : a ≫ u.left = b ≫ u.left := by
    apply section_eq_of_closed_eq Y.hom hau hbu
    simp only [Scheme.Hom.comp_apply, hax, hby, h]
  have hcomp : secA ≫ u = secB ≫ u := Over.OverMorphism.ext hab
  let j := genericMap R K
  let F := Over.pullback j
  have : Mono (F.map u) := ‹Mono ((Over.pullback (genericMap R K)).map u)›
  have hmap : F.map secA ≫ F.map u = F.map secB ≫ F.map u := by
    rw [← Functor.map_comp, ← Functor.map_comp, hcomp]
  have : IsSchemeTheoreticallyDominant j :=
    ZInQ.Contrib.NeronC.isSchemeTheoreticallyDominant_spec_map _
      (IsFractionRing.injective R K)
  have : QuasiCompact j := by dsimp [j, genericMap]; infer_instance
  have : Flat I.hom := show Flat (𝟙 S) from inferInstance
  have hsec : secA = secB := ZInQ.Contrib.NeronC.pullback_map_injective j I X
    ((cancel_mono (F.map u)).mp hmap)
  have hab' : a = b := congrArg CommaMorphism.left hsec
  rw [← hax, hab', hby]

section Torsion

set_option linter.unusedSectionVars false

variable {A B : Over (Spec (.of R))} [GrpObj A] [GrpObj B]

/-- The scheme-theoretic kernel of multiplication. -/
abbrev torsion (A : Over (Spec (.of R))) [GrpObj A] (m : ℕ) : Over (Spec (.of R)) :=
  Over.mk (pullback.snd (𝟙 A ^ m : A ⟶ A).left η[A].left)

private theorem torsion_condition (A : Over (Spec (.of R))) [GrpObj A] (m : ℕ) :
    pullback.fst (𝟙 A ^ m : A ⟶ A).left η[A].left ≫ (𝟙 A ^ m : A ⟶ A).left =
      (torsion A m).hom ≫ η[A].left := pullback.condition

/-- The inclusion of the scheme-theoretic multiplication kernel. -/
def torsionInclusion (A : Over (Spec (.of R))) [GrpObj A] (m : ℕ) :
    torsion A m ⟶ A := Over.homMk (pullback.fst _ _) (by
  change pullback.fst (𝟙 A ^ m : A ⟶ A).left η[A].left ≫ A.hom = (torsion A m).hom
  rw [← Over.w (𝟙 A ^ m : A ⟶ A), ← Category.assoc, torsion_condition,
    Category.assoc, Over.w η[A]]
  exact Category.comp_id _)

private theorem pow_natural (c : A ⟶ B) [IsMonHom c] (m : ℕ) :
    (𝟙 A ^ m : A ⟶ A).left ≫ c.left = c.left ≫ (𝟙 B ^ m : B ⟶ B).left := by
  have h : (𝟙 A ^ m : A ⟶ A) ≫ c = c ≫ (𝟙 B ^ m : B ⟶ B) := by
    rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  exact congrArg CommaMorphism.left h

private theorem one_natural (c : A ⟶ B) [IsMonHom c] :
    η[A].left ≫ c.left = η[B].left :=
  congrArg CommaMorphism.left (IsMonHom.one_hom c)

def torsionMap (c : A ⟶ B) [IsMonHom c] (m : ℕ) : torsion A m ⟶ torsion B m := by
  have hc : ((torsionInclusion A m).left ≫ c.left) ≫ (𝟙 B ^ m : B ⟶ B).left =
      (torsion A m).hom ≫ η[B].left := by
    rw [Category.assoc, ← pow_natural c m, ← Category.assoc]
    change (pullback.fst (𝟙 A ^ m : A ⟶ A).left η[A].left ≫
      (𝟙 A ^ m : A ⟶ A).left) ≫ c.left = _
    rw [torsion_condition, Category.assoc, one_natural c]
  exact Over.homMk (pullback.lift _ _ hc) (pullback.lift_snd _ _ _)

theorem torsionMap_inclusion (c : A ⟶ B) [IsMonHom c] (m : ℕ) :
    torsionMap c m ≫ torsionInclusion B m = torsionInclusion A m ≫ c := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

private theorem isClosedImmersion_torsionInclusion [IsSeparated A.hom] (m : ℕ) :
    IsClosedImmersion (torsionInclusion A m).left := by
  have : IsClosedImmersion η[A].left := by
    have : IsClosedImmersion (η[A].left ≫ A.hom) := by
      rw [Over.w]
      exact inferInstanceAs (IsClosedImmersion (𝟙 (Spec (.of R))))
    exact IsClosedImmersion.of_comp η[A].left A.hom
  change IsClosedImmersion (pullback.fst (𝟙 A ^ m : A ⟶ A).left η[A].left)
  infer_instance

private theorem etale_torsion [IsCommMonObj A] [Smooth A.hom]
    (m : ℕ) (hm : IsUnit (m : R)) : Etale (torsion A m).hom := by
  have := etale_pow A m hm
  change Etale (pullback.snd (𝟙 A ^ m : A ⟶ A).left η[A].left)
  infer_instance

/-- A comparison which is monic on the generic fibre is injective on
prime-to-residue-characteristic torsion in the special fibre. -/
theorem torsionMap_injective_special [IsSeparated A.hom] [IsCommMonObj A] [Smooth A.hom]
    [IsCommMonObj B] [Smooth B.hom]
    (c : A ⟶ B) [IsMonHom c] [Mono ((Over.pullback (genericMap R K)).map c)]
    (m : ℕ) (hm : IsUnit (m : R)) :
    Set.InjOn (torsionMap c m).left ((torsion A m).hom ⁻¹' {IsLocalRing.closedPoint R}) := by
  have : Etale (torsion A m).hom := etale_torsion m hm
  have : Etale (torsion B m).hom := etale_torsion m hm
  have : IsClosedImmersion (torsionInclusion A m).left := isClosedImmersion_torsionInclusion m
  have : IsSeparated (torsion A m).hom := by
    rw [← Over.w (torsionInclusion A m)]
    infer_instance
  have : Mono (torsionInclusion A m) := by
    constructor
    intro T a b h
    apply Over.OverMorphism.ext
    exact (cancel_mono (torsionInclusion A m).left).mp (congrArg CommaMorphism.left h)
  let F := Over.pullback (genericMap R K)
  have : Mono (F.map c) := ‹Mono ((Over.pullback (genericMap R K)).map c)›
  have : Mono (F.map (torsionMap c m) ≫ F.map (torsionInclusion B m)) := by
    rw [← Functor.map_comp, torsionMap_inclusion, Functor.map_comp]
    infer_instance
  have : Mono (F.map (torsionMap c m)) := mono_of_mono _ (F.map (torsionInclusion B m))
  exact injective_on_closed_of_generic_mono (K := K) (torsionMap c m)


/-- The residue-field point of the base, viewed in the slice. -/
abbrev residueObject (R : Type) [CommRing R] [IsLocalRing R] :
    Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))

private theorem fieldHom_ext {k : Type} [Field k] {d : Spec (.of k) ⟶ Spec (.of R)}
    [UniversallyInjective d] {X : Over (Spec (.of R))} [Etale X.hom]
    {a b : Over.mk d ⟶ X} (h : a.left (IsLocalRing.closedPoint k) =
      b.left (IsLocalRing.closedPoint k)) : a = b := by
  let P := pullback X.hom d
  let g : P ⟶ Spec (.of k) := pullback.snd _ _
  let a' : Spec (.of k) ⟶ P := pullback.lift a.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w a)
  let b' : Spec (.of k) ⟶ P := pullback.lift b.left (𝟙 _) (by rw [Category.id_comp]; exact Over.w b)
  have : UniversallyInjective (pullback.fst X.hom d) :=
    UniversallyInjective.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback X.hom d).flip inferInstance
  have ha' : a' ≫ pullback.fst X.hom d = a.left := pullback.lift_fst _ _ _
  have hb' : b' ≫ pullback.fst X.hom d = b.left := pullback.lift_fst _ _ _
  have hg : Etale g := show Etale (pullback.snd X.hom d) from inferInstance
  have h' : a' = b' := by
    apply section_eq_of_closed_eq g (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
    apply (pullback.fst X.hom d).injective
    let eval := fun (f : Spec (.of k) ⟶ X.left) => f (IsLocalRing.closedPoint k)
    exact (congrArg eval ha').trans (h.trans (congrArg eval hb').symm)
  exact Over.OverMorphism.ext (by rw [← ha', ← hb', h'])

private def torsionLift {P : Over (Spec (.of R))} (a : P ⟶ A) (m : ℕ) (ha : a ^ m = 1) :
    P ⟶ torsion A m := by
  have h : a ≫ (𝟙 A ^ m : A ⟶ A) = toUnit P ≫ η[A] := by
    rw [MonObj.comp_pow, Category.comp_id, ha, Hom.one_def]
  have hl : a.left ≫ (𝟙 A ^ m : A ⟶ A).left = P.hom ≫ η[A].left :=
    congrArg CommaMorphism.left h
  exact Over.homMk (pullback.lift a.left P.hom hl)
    (pullback.lift_snd _ _ _)

private theorem torsionLift_inclusion {P : Over (Spec (.of R))} (a : P ⟶ A) (m : ℕ) (ha : a ^ m = 1) :
    torsionLift a m ha ≫ torsionInclusion A m = a :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

/-- A homomorphism that is generically monic has no nontrivial special-fibre
torsion points in its kernel at any order invertible on a strictly henselian DVR. -/
theorem field_torsion_kernel_trivial
    [IsSeparated A.hom] [IsCommMonObj A] [Smooth A.hom]
    [IsSeparated B.hom] [IsCommMonObj B] [Smooth B.hom]
    (c : A ⟶ B) [IsMonHom c] [Mono ((Over.pullback (genericMap R K)).map c)]
    {k : Type} [Field k] (d : Spec (.of k) ⟶ Spec (.of R)) [UniversallyInjective d]
    (hd : d (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R)
    (a : Over.mk d ⟶ A) (m : ℕ) (hm : IsUnit (m : R))
    (ha : a ^ m = 1) (hc : a ≫ c = 1) : a = 1 := by
  let z : Spec (.of k) := IsLocalRing.closedPoint k
  let u := torsionLift a m ha
  let v := torsionLift (1 : Over.mk d ⟶ A) m (one_pow m)
  let t := torsionMap c m
  have : IsClosedImmersion (torsionInclusion B m).left := isClosedImmersion_torsionInclusion m
  have hu : u ≫ t ≫ torsionInclusion B m = 1 := by
    rw [torsionMap_inclusion, ← Category.assoc, torsionLift_inclusion]
    exact hc
  have hv : v ≫ t ≫ torsionInclusion B m = 1 := by
    rw [torsionMap_inclusion, ← Category.assoc, torsionLift_inclusion, MonObj.one_comp]
  have htv : u ≫ t = v ≫ t := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (torsionInclusion B m).left).mp
    have h : (u ≫ t) ≫ torsionInclusion B m = (v ≫ t) ≫ torsionInclusion B m := by
      simpa only [Category.assoc] using hu.trans hv.symm
    exact congrArg CommaMorphism.left h
  have ff : ∀ w : Over.mk d ⟶ torsion A m,
      (torsion A m).hom (w.left z) = IsLocalRing.closedPoint R := by
    intro w
    change (w.left ≫ (torsion A m).hom) z = _
    rw [Over.w]
    exact hd
  have hpts : u.left z = v.left z :=
    torsionMap_injective_special (K := K) c m hm (ff u) (ff v)
      (congrArg (fun w : Over.mk d ⟶ torsion B m => w.left z) htv)
  have : Etale (torsion A m).hom := etale_torsion m hm
  have huv : u = v := fieldHom_ext hpts
  rw [← torsionLift_inclusion a m ha, show torsionLift a m ha = v from huv, torsionLift_inclusion]


/-- The special-fibre kernel remains free of prime-to-residue-characteristic
torsion after passage to the algebraic closure of the residue field. -/
theorem algebraicClosure_residue_torsion_kernel_trivial
    [IsSeparated A.hom] [IsCommMonObj A] [Smooth A.hom]
    [IsSeparated B.hom] [IsCommMonObj B] [Smooth B.hom]
    (c : A ⟶ B) [IsMonHom c] [Mono ((Over.pullback (genericMap R K)).map c)]
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) L]
    (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField R) L)) ≫
      (residueObject R).hom) ⟶ A) (m : ℕ) (hm : IsUnit (m : R))
    (ha : a ^ m = 1) (hc : a ≫ c = 1) : a = 1 := by
  let k := IsLocalRing.ResidueField R
  let t : Spec (.of L) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let d := (residueObject R).hom
  have : UniversallyInjective t :=
    universallyInjective_specMap_of_isPurelyInseparable k L
  have : IsClosedImmersion d := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (IsLocalRing.residue R)) IsLocalRing.residue_surjective
  have : UniversallyInjective (t ≫ d) :=
    MorphismProperty.comp_mem @UniversallyInjective t d inferInstance inferInstance
  have hd : (t ≫ d) (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint R := by
    have ht : t (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint k :=
      Subsingleton.elim (α := Spec (.of k)) _ _
    change d (t (IsLocalRing.closedPoint L)) = _
    rw [ht]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  exact field_torsion_kernel_trivial (K := K) c (t ≫ d) hd a m hm ha hc

end Torsion

end SmoothGroup

import ZInQKernel.Contrib.OneProof.SZThm33.ToricTorsionDensity
import ZInQKernel.Contrib.OneProof.SZThm33.AbelianTorsionDominance

/-! A subgroup covering all ℓ-power torsion of a split semiabelian group
has dense image. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace Topology
open ZInQ.HeightSplit ZInQ.SemiAbDescend ZInQ.FaltingsRestate
open scoped BigOperators

set_option linter.style.haveILetI false
set_option maxHeartbeats 1800000

namespace SZRaynaud

variable {k : Type} [Field k] [IsAlgClosed k]

/-- The values of a naturally parametrized torus on ℓ-power torsion lie in
a closed subset only if all values of that torus lie in the subset. -/
theorem torus_parameter_mem_of_primary_mem
    {U : (Over (Spec (CommRingCat.of k)))} [GrpObj U] {r ℓ : ℕ} (hr : 1 < ℓ) (hℓ : (ℓ : k) ≠ 0)
    (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U))
    (hn : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
      (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)
    {C : Set U.left} (hC : IsClosed C)
    (h : ∀ t : Fin r → kˣ, (∃ n : ℕ, t ^ ℓ ^ n = 1) →
      (e k t).left (IsLocalRing.closedPoint k) ∈ C)
    (t : Fin r → kˣ) : (e k t).left (IsLocalRing.closedPoint k) ∈ C := by
  let u := e (TorusRing k r) (tUniv r)
  let f (t : Fin r → kˣ) :=
    Spec.map (CommRingCat.ofHom (torusLift (K := k) t).toRingHom) (IsLocalRing.closedPoint k)
  have he (t : Fin r → kˣ) : u.left (f t) = (e k t).left (IsLocalRing.closedPoint k) := by
    have hu : algPtMap (torusLift (K := k) t) ≫ u = e k t := by
      rw [← hn]
      congr 1
      funext i
      apply Units.ext
      exact torusLift_tUniv t i
    exact congrArg (fun a : (algPt k k) ⟶ U => a.left (IsLocalRing.closedPoint k)) hu
  have hd := denseRange_torus_primary_points (k := k) (r := r) hr hℓ
  let D := u.left ⁻¹' C
  have hD : IsClosed D := hC.preimage u.left.continuous
  have hrD : Set.range (fun t : CommGroup.primaryComponent (Fin r → kˣ) ℓ => f t.1) ⊆ D := by
    rintro _ ⟨t, rfl⟩
    change u.left (f t.1) ∈ C
    rw [he]
    exact h t.1 (CommGroup.mem_primaryComponent.mp t.2)
  have hDall : Set.univ ⊆ D := hd.closure_eq ▸ closure_minimal hrD hD
  have ht : u.left (f t) ∈ C := hDall (Set.mem_univ (f t))
  rwa [he] at ht

private def algPtUnitIso : algPt k k ≅ (𝟙_ (Over (Spec (CommRingCat.of k)))) :=
  Over.isoMk (Iso.refl _) (by simp [algPt])

private theorem surjective_mapGroupPoint_of_dominant
    {X Y : (Over (Spec (CommRingCat.of k)))} [GrpObj X] [GrpObj Y] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] (f : X ⟶ Y) [IsMonHom f] [QuasiCompact f.left] [IsDominant f.left] :
    Function.Surjective (mapGroupPoint (P := (algPt k k)) f) := by
  intro y
  obtain ⟨x, hx⟩ := surjective_points_of_dominant_group_hom f (algPtUnitIso.inv ≫ y)
  refine ⟨algPtUnitIso.hom ≫ x, ?_⟩
  change (algPtUnitIso.hom ≫ x) ≫ f = y
  rw [Category.assoc, show x ≫ f = algPtUnitIso.inv ≫ y from hx,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

private theorem exists_algPt_preimage_of_in_range
    {X Y : (Over (Spec (CommRingCat.of k)))} (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (y : (algPt k k) ⟶ Y) (hy : y.left (IsLocalRing.closedPoint k) ∈ Set.range f.left) :
    ∃ x : (algPt k k) ⟶ X, x ≫ f = y := by
  let b := algPtUnitIso.inv ≫ y
  obtain ⟨a, ha⟩ := exists_point_preimage_of_in_range f b (by
    have h : b.left (IsLocalRing.closedPoint k) = y.left (IsLocalRing.closedPoint k) := rfl
    rwa [h])
  refine ⟨algPtUnitIso.hom ≫ a, ?_⟩
  rw [Category.assoc, ha]
  exact Iso.hom_inv_id_assoc _ _

private theorem tuple_pow_surjective {r : ℕ} (m : ℕ) (hm : 0 < m) :
    Function.Surjective (fun x : Fin r → kˣ => x ^ m) := by
  intro x
  have h (i : Fin r) : ∃ y : kˣ, y ^ m = x i := by
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (x i : k) hm
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at ha
      exact (x i).ne_zero ha.symm
    exact ⟨Units.mk0 a ha0, Units.ext ha⟩
  choose y hy using h
  exact ⟨y, funext hy⟩

/-- For a surjective map with a split torus kernel, every point of the
abelian quotient killed by (m) is the image of a point killed by (m). -/
theorem lift_torsion_of_splitTorus_kernel
    {U : (Over (Spec (CommRingCat.of k)))} [GrpObj U] [IsCommMonObj U]
    (B : PkgI3.AbVar k) (π : U ⟶ B.X) [IsMonHom π]
    [LocallyOfFiniteType π.left] [Surjective π.left]
    {r : ℕ} (e : (Fin r → kˣ) →* ((algPt k k) ⟶ U))
    (hk : ∀ u : (algPt k k) ⟶ U, u ≫ π = 1 ↔ u ∈ e.range)
    {m : ℕ} (hm : 0 < m) (y : (algPt k k) ⟶ B.X) (hy : y ^ m = 1) :
    ∃ x : (algPt k k) ⟶ U, x ^ m = 1 ∧ x ≫ π = y := by
  let f := mapGroupPoint (P := (algPt k k)) π
  obtain ⟨x, hx⟩ := surjective_mapGroupPoint π y
  have hxK : x ^ m ∈ e.range := (hk _).mp (by
    change f (x ^ m) = 1
    rw [map_pow, show f x = y from hx, hy])
  obtain ⟨a, ha⟩ := hxK
  obtain ⟨b, hb⟩ := tuple_pow_surjective m hm a
  refine ⟨x / e b, ?_, ?_⟩
  · change b ^ m = a at hb
    rw [div_pow, ← map_pow, hb, ha, div_self']
  · change f (x / e b) = y
    rw [map_div, hx, show f (e b) = 1 from (hk _).mpr ⟨b, rfl⟩, div_one]

variable {ℓ : ℕ} [Fact ℓ.Prime]

set_option backward.isDefEq.respectTransparency false in
/-- A homomorphism into a split semiabelian group is dominant if every
ℓ-power torsion point of the target is in its image. -/
theorem dominant_of_splitSemiabelian_primary_torsion
    {X U : (Over (Spec (CommRingCat.of k)))} [GrpObj X] [GrpObj U] [IsCommMonObj U]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (f : X ⟶ U) [IsMonHom f] [QuasiCompact f.left]
    (B : PkgI3.AbVar k) (b : ℕ) (hb : B.dim = (b : WithBot ℕ∞))
    (π : U ⟶ B.X) [IsMonHom π] [Surjective π.left]
    (hℓ : (ℓ : k) ≠ 0) {r : ℕ}
    (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U))
    (hk : ∀ u : (algPt k k) ⟶ U, u ≫ π = 1 ↔ u ∈ (e k).range)
    (hn : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (a : R →ₐ[k] S)
      (t : Fin r → Rˣ), e S (fun i => Units.map (a : R →* S) (t i)) = algPtMap a ≫ e R t)
    (ht : ∀ (n : ℕ) (x : (algPt k k) ⟶ U), x ^ ℓ ^ n = 1 →
      x ∈ (mapGroupPoint (P := (algPt k k)) f).range) :
    IsDominant f.left := by
  obtain ⟨G, hG, i, hiM, hi, q, hqM, hqD, hqC, hfi⟩ := exists_group_scheme_image f
  letI : GrpObj G := hG
  haveI : IsMonHom i := hiM
  haveI : IsClosedImmersion i.left := hi
  haveI : IsDominant q.left := hqD
  haveI : LocallyOfFiniteType G.hom := by rw [← Over.w i]; infer_instance
  haveI : LocallyOfFiniteType π.left := by
    haveI : LocallyOfFiniteType (π.left ≫ B.X.hom) := by
      rw [Over.w π]
      infer_instance
    exact locallyOfFiniteType_of_comp π.left B.X.hom
  haveI : QuasiCompact G.hom := by rw [← Over.w i]; infer_instance
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : IsNoetherian G.left := {}
  haveI : QuasiCompact (i ≫ π).left := inferInstance
  have hti (n : ℕ) (x : (algPt k k) ⟶ U) (hx : x ^ ℓ ^ n = 1) :
      x ∈ (mapGroupPoint (P := (algPt k k)) i).range := by
    obtain ⟨a, ha⟩ := ht n x hx
    exact ⟨a ≫ q, (Category.assoc _ _ _).trans (congrArg (a ≫ ·) hfi |>.trans ha)⟩
  obtain ⟨Z, hZG, j, hjM, hj, p, hpM, hpD, hpC, hfac⟩ :=
    exists_group_scheme_image (i ≫ π)
  letI : GrpObj Z := hZG
  haveI : IsMonHom j := hjM
  haveI : IsClosedImmersion j.left := hj
  haveI : IsDominant p.left := hpD
  have hsurj : Function.Surjective j.left := by
    apply surjective_closedGroup_of_primary_torsion B b hb hℓ Z j
    intro n y hy
    obtain ⟨x, hx, hxy⟩ := lift_torsion_of_splitTorus_kernel B π (e k) hk
      (pow_pos (Fact.out : ℓ.Prime).pos n) y hy
    obtain ⟨z, hz⟩ := hti n x hx
    refine ⟨z ≫ p, ?_⟩
    change (z ≫ p) ≫ j = y
    rw [Category.assoc, hfac, ← Category.assoc, show z ≫ i = x from hz, hxy]
  haveI : Surjective j.left := ⟨hsurj⟩
  haveI : IsDominant (i ≫ π).left := by
    rw [← hfac]
    change IsDominant (p.left ≫ j.left)
    infer_instance
  have htor (t : Fin r → kˣ) : (e k t).left (IsLocalRing.closedPoint k) ∈ Set.range i.left := by
    apply torus_parameter_mem_of_primary_mem (Fact.out : ℓ.Prime).one_lt hℓ e hn
      i.left.isClosedEmbedding.isClosed_range
    intro a ha
    obtain ⟨n, hpow⟩ := ha
    obtain ⟨x, hx⟩ := hti n (e k a) (by rw [← map_pow, hpow, map_one])
    refine ⟨x.left (IsLocalRing.closedPoint k), ?_⟩
    exact congrArg (fun y : (algPt k k) ⟶ U => y.left (IsLocalRing.closedPoint k)) hx
  suffices hS : Function.Surjective i.left by
    haveI : Surjective i.left := ⟨hS⟩
    rw [← hfi]
    change IsDominant (q.left ≫ i.left)
    infer_instance
  have hPts : Function.Surjective (mapGroupPoint (P := (algPt k k)) i) := by
    intro x
    obtain ⟨z, hz⟩ := surjective_mapGroupPoint_of_dominant (i ≫ π) (x ≫ π)
    change z ≫ i ≫ π = x ≫ π at hz
    have hxK : x / (z ≫ i) ∈ (e k).range := (hk _).mp (by
      let g := mapGroupPoint (P := (algPt k k)) π
      change g (x / (z ≫ i)) = 1
      rw [map_div, show g (z ≫ i) = g x from Category.assoc _ _ _ |>.trans hz, div_self'])
    obtain ⟨t, ht⟩ := hxK
    obtain ⟨a, ha⟩ := exists_algPt_preimage_of_in_range i (e k t) (htor t)
    refine ⟨a * z, ?_⟩
    change (a * z) ≫ i = x
    rw [MonObj.mul_comp, ha, ht, div_mul_cancel]
  haveI : JacobsonSpace U.left := LocallyOfFiniteType.jacobsonSpace U.hom
  have hc : closedPoints U.left ⊆ Set.range i.left := by
    intro x hx
    let y : (algPt k k) ⟶ U := Over.homMk (pointOfClosedPoint U.hom x hx)
      ((pointOfClosedPoint_comp U.hom x hx).trans (by simp [algPt]))
    obtain ⟨z, hz⟩ := hPts y
    refine ⟨z.left (IsLocalRing.closedPoint k), ?_⟩
    exact (congrArg (fun a : (algPt k k) ⟶ U => a.left (IsLocalRing.closedPoint k)) hz).trans
      (pointOfClosedPoint_apply U.hom x hx _)
  have hcov := closure_minimal hc i.left.isClosedEmbedding.isClosed_range
  rw [closure_closedPoints] at hcov
  exact fun x => hcov (Set.mem_univ x)

/-- Surjectivity on rational Tate modules suffices for dominance on a split
semiabelian target, because each target torsion point lifts to a Tate tower. -/
theorem dominant_of_splitSemiabelian_rationalTate_surjective
    {X U : (Over (Spec (CommRingCat.of k)))} [GrpObj X] [GrpObj U] [IsCommMonObj X] [IsCommMonObj U]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (f : X ⟶ U) [IsMonHom f] [QuasiCompact f.left]
    (B : PkgI3.AbVar k) (b : ℕ) (hb : B.dim = (b : WithBot ℕ∞))
    (π : U ⟶ B.X) [IsMonHom π] [Surjective π.left]
    (hℓ : (ℓ : k) ≠ 0) {r : ℕ}
    (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U))
    (he : Function.Injective (e k))
    (hk : ∀ u : (algPt k k) ⟶ U, u ≫ π = 1 ↔ u ∈ (e k).range)
    (hn : ∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (a : R →ₐ[k] S)
      (t : Fin r → Rˣ), e S (fun i => Units.map (a : R →* S) (t i)) = algPtMap a ≫ e R t)
    (hs : Function.Surjective ((PkgI3.Tate.map (ℓ := ℓ)
      (mapGroupPoint (P := (algPt k k)) f).toAdditive).baseChange ℚ_[ℓ])) :
    IsDominant f.left := by
  haveI : LocallyOfFiniteType π.left := by
    haveI : LocallyOfFiniteType (π.left ≫ B.X.hom) := by
      rw [Over.w π]
      infer_instance
    exact locallyOfFiniteType_of_comp π.left B.X.hom
  apply dominant_of_splitSemiabelian_primary_torsion f B b hb π hℓ e hk hn
  intro n x hx
  obtain ⟨t, ht⟩ := tate_level_surjective_of_counts (ℓ := ℓ) (2 * b + r)
    (card_torsion_semiabelian U B π r b hb hℓ (e k) he hk) n (Additive.ofMul x) hx
  obtain ⟨y, hy⟩ := mem_range_of_coord_of_rationalTate_surjective
    (mapGroupPoint (P := (algPt k k)) f).toAdditive hs t n
  exact ⟨Additive.toMul y, congrArg Additive.toMul (hy.trans ht)⟩

#print axioms torus_parameter_mem_of_primary_mem
#print axioms dominant_of_splitSemiabelian_primary_torsion
#print axioms dominant_of_splitSemiabelian_rationalTate_surjective

end SZRaynaud

import NeronEtale.TateFiniteIndexV002
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.JacobsonSpace

/-!
# Open subgroups of finite type group schemes over an algebraically closed field

`k` algebraically closed, `G` a commutative group scheme over `k`, locally of finite type and
quasi-compact, `inc : U → G` an open immersion which is a homomorphism of group schemes (for
instance the identity component). Points are the original point objects
`PkgI3.AbVar.ptObj k = (Spec k → Spec k)`.

* `finiteIndex_pt_range`: `U(k)` has finite index in `G(k)`. Translates of `U` by rational points
  are open and nonempty; two of them meet only if the points lie in one coset of `U(k)` (a common
  point may be taken closed since `G` is Jacobson, and closed points are rational by the
  Nullstellensatz); `G` is a Noetherian space, so there are finitely many cosets.
* `isCommMonObj_of_mono'`: `U` is commutative (monomorphic homomorphism into commutative `G`).
* `tate_open_subgroup_bijective`, `tateOpenSubgroupEquiv`: `T_ℓ(U(k)) → T_ℓ(G(k))` is bijective
  for EVERY prime `ℓ` (no coprimality with `[G(k) : U(k)]`), from the general finite-index
  theorem of `NeronEtale.TateFiniteIndexV002`.
* `range_coord_open_subgroup`: the level-`n` coordinates of `T_ℓ(G(k))` are the images of the
  level-`n` coordinates of `T_ℓ(U(k))`; `range_coord_eq_torsion_of_root`: these are all of
  `M[ℓⁿ]` when `M` has compatible `ℓ`-th roots of its `ℓ`-power torsion; combined in
  `range_coord_open_subgroup_eq_image_torsion` (that root property of `U(k)` is a hypothesis
  here, not proved).
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace FiniteIndexTate

/-! ## Rational points and translations -/

/-- Rational points: `Spec k → Spec k`, definitionally the original point object
`PkgI3.AbVar.ptObj k` (`pt_eq_ptObj`). -/
abbrev pt (k : Type) [Field k] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)))

theorem pt_eq_ptObj (k : Type) [Field k] : pt k = PkgI3.AbVar.ptObj (K := k) k := rfl

variable {k : Type} [Field k]

theorem pt_hom : (pt k).hom = 𝟙 (Spec (CommRingCat.of k)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- The point object is the monoidal unit. -/
def ptUnitIso (k : Type) [Field k] : pt k ≅ 𝟙_ (Over (Spec (CommRingCat.of k))) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 (Spec (CommRingCat.of k)) ≫ 𝟙 (Spec (CommRingCat.of k)) = (pt k).hom
    rw [Category.comp_id, pt_hom])

section Translation

variable (G : Over (Spec (CommRingCat.of k))) [GrpObj G]

/-- A rational point as a point of the unit object. -/
def ptE (g : pt k ⟶ G) : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G := (ptUnitIso k).inv ≫ g

theorem ptE_mul (g h : pt k ⟶ G) : ptE G (g * h) = ptE G g * ptE G h := MonObj.comp_mul _ _ _

theorem ptE_one : ptE G (1 : pt k ⟶ G) = 1 := MonObj.comp_one _

/-- Left translation of `G` by a rational point. -/
def transl (g : pt k ⟶ G) : G ⟶ G := (toUnit G ≫ ptE G g) * 𝟙 G

theorem comp_transl {X : Over (Spec (CommRingCat.of k))} (x : X ⟶ G) (g : pt k ⟶ G) :
    x ≫ transl G g = (toUnit X ≫ ptE G g) * x := by
  rw [transl, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id]

theorem pt_comp_transl (z g : pt k ⟶ G) : z ≫ transl G g = g * z := by
  rw [comp_transl, toUnit_unique (toUnit (pt k)) (ptUnitIso k).hom]
  have h : (ptUnitIso k).hom ≫ ptE G g = g := by
    simp only [ptE, Iso.hom_inv_id_assoc]
  rw [h]

theorem transl_comp_transl (g h : pt k ⟶ G) : transl G g ≫ transl G h = transl G (h * g) := by
  rw [comp_transl]
  simp only [transl]
  rw [← _root_.mul_assoc, ← MonObj.comp_mul, ← ptE_mul]

theorem transl_one : transl G (1 : pt k ⟶ G) = 𝟙 G := by
  rw [transl, ptE_one, MonObj.comp_one, _root_.one_mul]

instance transl_isIso (g : pt k ⟶ G) : IsIso (transl G g) :=
  ⟨⟨transl G g⁻¹, by rw [transl_comp_transl, inv_mul_cancel, transl_one],
    by rw [transl_comp_transl, mul_inv_cancel, transl_one]⟩⟩

instance transl_left_isIso (g : pt k ⟶ G) : IsIso (transl G g).left :=
  (inferInstance : IsIso ((Over.forget _).map (transl G g)))

end Translation

/-! ## Finite index -/

section Index

variable [IsAlgClosed k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
  [LocallyOfFiniteType G.hom]
  {U : Over (Spec (CommRingCat.of k))} [GrpObj U] (inc : U ⟶ G) [IsOpenImmersion inc.left]
  [IsMonHom inc]

/-- A rational point lying in a translate of `U` comes from a rational point of `U`. -/
theorem exists_preimage_transl (g : pt k ⟶ G) (zl : Spec (CommRingCat.of k) ⟶ G.left)
    (hzl : zl ≫ G.hom = (pt k).hom) (p : G.left) (hp : ∀ a, zl a = p)
    (hpg : p ∈ Set.range (inc.left ≫ (transl G g).left)) :
    ∃ a : pt k ⟶ U, (a ≫ inc) ≫ transl G g = Over.homMk zl hzl := by
  have H' : Set.range zl ⊆ Set.range (inc.left ≫ (transl G g).left) := by
    rintro _ ⟨c, rfl⟩
    rw [hp c]
    exact hpg
  let wl := IsOpenImmersion.lift (inc.left ≫ (transl G g).left) zl H'
  have hw : wl ≫ inc.left ≫ (transl G g).left = zl := IsOpenImmersion.lift_fac _ _ _
  have h1 : (inc.left ≫ (transl G g).left) ≫ G.hom = U.hom := by
    rw [Category.assoc, Over.w (transl G g), Over.w inc]
  have hwU : wl ≫ U.hom = (pt k).hom := by
    rw [← h1, ← Category.assoc, hw, hzl]
  refine ⟨Over.homMk wl hwU, ?_⟩
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.homMk_left]
  rw [Category.assoc]
  exact hw

/-- Two translates of `U` meet only along one coset of `U(k)`. -/
theorem exists_of_meet (g h : pt k ⟶ G)
    (hne : (Set.range (inc.left ≫ (transl G g).left) ∩
      Set.range (inc.left ≫ (transl G h).left)).Nonempty) :
    ∃ a b : pt k ⟶ U, g * (a ≫ inc) = h * (b ≫ inc) := by
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  have ho : ∀ g : pt k ⟶ G, IsOpen (Set.range (inc.left ≫ (transl G g).left)) := fun g =>
    IsOpenImmersion.isOpen_range _
  obtain ⟨p, ⟨hpg, hph⟩, hpc⟩ :=
    nonempty_inter_closedPoints hne ((ho g).inter (ho h)).isLocallyClosed
  let zl : Spec (CommRingCat.of k) ⟶ G.left := pointOfClosedPoint G.hom p hpc
  have hzl : zl ≫ G.hom = (pt k).hom := by
    rw [pt_hom]
    exact pointOfClosedPoint_comp G.hom p hpc
  have hp : ∀ a, zl a = p := fun a => pointOfClosedPoint_apply G.hom p hpc a
  obtain ⟨a, ha⟩ := exists_preimage_transl G inc g zl hzl p hp hpg
  obtain ⟨b, hb⟩ := exists_preimage_transl G inc h zl hzl p hp hph
  refine ⟨a, b, ?_⟩
  rw [← pt_comp_transl, ← pt_comp_transl, ha, hb]

/-- **`[G(k) : U(k)] < ∞`.** -/
theorem finiteIndex_pt_range [QuasiCompact G.hom] :
    (IsMonHom.monoidHom inc (pt k)).range.FiniteIndex := by
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  suffices Finite ((pt k ⟶ G) ⧸ (IsMonHom.monoidHom inc (pt k)).range) from
    Subgroup.finiteIndex_of_finite_quotient
  by_contra hfin
  rw [not_finite_iff_infinite] at hfin
  let c : ℕ ↪ (pt k ⟶ G) ⧸ (IsMonHom.monoidHom inc (pt k)).range := Infinite.natEmbedding _
  let g : ℕ → (pt k ⟶ G) := fun n => (c n).out
  let V : ℕ → Set G.left := fun n => Set.range (inc.left ≫ (transl G (g n)).left)
  have hVo : ∀ n, IsOpen (V n) := fun n => IsOpenImmersion.isOpen_range _
  have hdisj : ∀ i j, (V i ∩ V j).Nonempty → i = j := by
    intro i j hij
    obtain ⟨a, b, hab⟩ := exists_of_meet G inc (g i) (g j) hij
    apply c.injective
    rw [← QuotientGroup.out_eq' (c i), ← QuotientGroup.out_eq' (c j), QuotientGroup.eq]
    have h1 : g j = g i * (a ≫ inc) * (b ≫ inc)⁻¹ := eq_mul_inv_of_mul_eq hab.symm
    have h2 : (g i)⁻¹ * g j = (a ≫ inc) * (b ≫ inc)⁻¹ := by
      rw [h1, _root_.mul_assoc, inv_mul_cancel_left]
    have h3 : (c i).out⁻¹ * (c j).out = (a ≫ inc) * (b ≫ inc)⁻¹ := h2
    rw [h3]
    exact ⟨a * b⁻¹, (map_mul _ _ _).trans (congrArg _ (map_inv _ _))⟩
  have hne : ∀ n, (V n).Nonempty := fun n =>
    ⟨(inc.left ≫ (transl G (g n)).left) ((1 : pt k ⟶ U).left (IsLocalRing.closedPoint k)),
      ⟨_, rfl⟩⟩
  obtain ⟨t, ht⟩ := (TopologicalSpace.NoetherianSpace.isCompact (⋃ n, V n)).elim_finite_subcover
    V hVo subset_rfl
  have hn : t.sup id + 1 ∉ t := fun h => by
    have h1 := Finset.le_sup (f := id) h
    simp only [id_eq] at h1
    omega
  obtain ⟨p, hp⟩ := hne (t.sup id + 1)
  obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_iUnion.2 ⟨_, hp⟩))
  have := hdisj _ _ ⟨p, hp, hpi⟩
  rw [this] at hn
  exact hn hi

end Index

/-! ## Commutativity of the open subgroup -/

theorem isCommMonObj_of_mono' {C : Type*} [Category C] [CartesianMonoidalCategory C]
    [BraidedCategory C] {X Y : C} [MonObj X] [MonObj Y] [IsCommMonObj Y] (f : X ⟶ Y)
    [IsMonHom f] [Mono f] : IsCommMonObj X where
  mul_comm := by
    rw [← cancel_mono f, Category.assoc, IsMonHom.mul_hom,
      ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]

/-! ## The all-`ℓ` Tate bijection for an open subgroup -/

section Wrapper

variable [IsAlgClosed k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [IsCommMonObj G]
  [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
  {U : Over (Spec (CommRingCat.of k))} [GrpObj U] (inc : U ⟶ G) [IsOpenImmersion inc.left]
  [IsMonHom inc]

theorem mono_inc : Mono inc :=
  (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono inc.left))

theorem inc_pt_injective : Function.Injective (IsMonHom.monoidHom inc (pt k)) := by
  haveI := mono_inc G inc
  intro a b h
  exact (cancel_mono inc).1 h

/-- **All-`ℓ` Tate bijection** `T_ℓ(U(k)) ≅ T_ℓ(G(k))` for an open subgroup. -/
theorem tate_open_subgroup_bijective (ℓ : ℕ) [Fact ℓ.Prime] :
    letI : Mono inc := mono_inc G inc
    letI : IsCommMonObj U := isCommMonObj_of_mono' inc
    Function.Bijective
      (PkgI3.Tate.map (ℓ := ℓ) (MonoidHom.toAdditive (IsMonHom.monoidHom inc (pt k)))) := by
  letI : Mono inc := mono_inc G inc
  letI : IsCommMonObj U := isCommMonObj_of_mono' inc
  haveI := finiteIndex_pt_range G inc
  exact tate_bijective_of_finiteIndex_mul ℓ _ (inc_pt_injective G inc)

/-- **Coordinate image identity for an open subgroup**: the level-`n` coordinates of
`T_ℓ(G(k))` are `inc` applied to the level-`n` coordinates of `T_ℓ(U(k))`. -/
theorem range_coord_open_subgroup (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    letI : Mono inc := mono_inc G inc
    letI : IsCommMonObj U := isCommMonObj_of_mono' inc
    Set.range (fun t : PkgI3.Tate.T ℓ (Additive (pt k ⟶ G)) => Additive.toMul (t.1 n)) =
      (IsMonHom.monoidHom inc (pt k)) ''
        Set.range (fun s : PkgI3.Tate.T ℓ (Additive (pt k ⟶ U)) => Additive.toMul (s.1 n)) := by
  letI : Mono inc := mono_inc G inc
  letI : IsCommMonObj U := isCommMonObj_of_mono' inc
  haveI := finiteIndex_pt_range G inc
  exact range_coord_eq_image_mul ℓ _ (inc_pt_injective G inc) n

end Wrapper

/-! ## Level-`n` coordinates are the whole `ℓⁿ`-torsion under compatible roots -/

section Roots

variable (ℓ : ℕ) [Fact ℓ.Prime] {M : Type*} [CommGroup M]

/-- With compatible `ℓ`-th roots of `ℓ`-power torsion, every `x ∈ M[ℓⁿ]` is a level-`n`
coordinate of `T_ℓ(M)`. -/
theorem exists_tate_of_root
    (hroot : ∀ (j : ℕ) (x : M), x ^ (ℓ ^ j) = 1 → ∃ y : M, y ^ (ℓ ^ (j + 1)) = 1 ∧ y ^ ℓ = x)
    (n : ℕ) (x : M) (hx : x ^ (ℓ ^ n) = 1) :
    ∃ t : PkgI3.Tate.T ℓ (Additive M), Additive.toMul (t.1 n) = x := by
  classical
  have step : ∀ j : ℕ, ∀ y : {y : M // y ^ (ℓ ^ (n + j)) = 1},
      ∃ z : {z : M // z ^ (ℓ ^ (n + (j + 1))) = 1}, z.1 ^ ℓ = y.1 := by
    intro j y
    obtain ⟨z, hz, hz'⟩ := hroot (n + j) y.1 y.2
    exact ⟨⟨z, by rw [← Nat.add_assoc]; exact hz⟩, hz'⟩
  let s : (j : ℕ) → {y : M // y ^ (ℓ ^ (n + j)) = 1} :=
    fun j => Nat.rec ⟨x, by simpa using hx⟩ (fun j y => (step j y).choose) j
  have hs : ∀ j, (s (j + 1)).1 ^ ℓ = (s j).1 := fun j => (step j (s j)).choose_spec
  let u : ℕ → M := fun m => if m ≤ n then x ^ (ℓ ^ (n - m)) else (s (m - n)).1
  refine ⟨⟨fun m => Additive.ofMul (u m), ?_, ?_⟩, ?_⟩
  · show Additive.ofMul (u 0) = 0
    simp only [u, Nat.zero_le, ite_true, Nat.sub_zero, hx]
    rfl
  · intro m
    show ℓ • Additive.ofMul (u (m + 1)) = Additive.ofMul (u m)
    rw [← ofMul_pow]
    congr 1
    by_cases h : m + 1 ≤ n
    · simp only [u, h, ite_true, show m ≤ n by omega]
      rw [← pow_mul, ← pow_succ, show n - (m + 1) + 1 = n - m by omega]
    · by_cases h' : m = n
      · subst h'
        simp only [u, h, ite_false, le_refl, ite_true, Nat.sub_self, pow_zero, pow_one]
        rw [show m + 1 - m = 0 + 1 by omega, hs 0]
        rfl
      · simp only [u, h, ite_false, show ¬ m ≤ n by omega]
        rw [show m + 1 - n = (m - n) + 1 by omega, hs]
  · show u n = x
    simp [u]

/-- **Level-`n` coordinates of `T_ℓ(M)` = `M[ℓⁿ]`** under compatible roots. -/
theorem range_coord_eq_torsion_of_root
    (hroot : ∀ (j : ℕ) (x : M), x ^ (ℓ ^ j) = 1 → ∃ y : M, y ^ (ℓ ^ (j + 1)) = 1 ∧ y ^ ℓ = x)
    (n : ℕ) :
    Set.range (fun s : PkgI3.Tate.T ℓ (Additive M) => Additive.toMul (s.1 n)) =
      {x : M | x ^ (ℓ ^ n) = 1} := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact PkgI3.Tate.pow_smul_eq_zero s.2 n
  · intro hx
    obtain ⟨t, ht⟩ := exists_tate_of_root ℓ hroot n x hx
    exact ⟨t, ht⟩

end Roots

/-- **The level-`n` coordinates of `T_ℓ(G(k))` are `inc(U(k)[ℓⁿ])`**, given compatible `ℓ`-th
roots in `U(k)` (a hypothesis, not proved here). -/
theorem range_coord_open_subgroup_eq_image_torsion [IsAlgClosed k]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [IsCommMonObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    {U : Over (Spec (CommRingCat.of k))} [GrpObj U] (inc : U ⟶ G) [IsOpenImmersion inc.left]
    [IsMonHom inc] (ℓ : ℕ) [Fact ℓ.Prime]
    (hroot : ∀ (j : ℕ) (x : pt k ⟶ U), x ^ (ℓ ^ j) = 1 →
      ∃ y : pt k ⟶ U, y ^ (ℓ ^ (j + 1)) = 1 ∧ y ^ ℓ = x) (n : ℕ) :
    letI : Mono inc := mono_inc G inc
    letI : IsCommMonObj U := isCommMonObj_of_mono' inc
    Set.range (fun t : PkgI3.Tate.T ℓ (Additive (pt k ⟶ G)) => Additive.toMul (t.1 n)) =
      (IsMonHom.monoidHom inc (pt k)) '' {x : pt k ⟶ U | x ^ (ℓ ^ n) = 1} := by
  letI : Mono inc := mono_inc G inc
  letI : IsCommMonObj U := isCommMonObj_of_mono' inc
  rw [range_coord_open_subgroup G inc ℓ n, range_coord_eq_torsion_of_root ℓ hroot n]

end FiniteIndexTate

#check @FiniteIndexTate.finiteIndex_pt_range
#check @FiniteIndexTate.tate_open_subgroup_bijective
#check @FiniteIndexTate.range_coord_open_subgroup
#check @FiniteIndexTate.range_coord_open_subgroup_eq_image_torsion
#print axioms FiniteIndexTate.finiteIndex_pt_range
#print axioms FiniteIndexTate.isCommMonObj_of_mono'
#print axioms FiniteIndexTate.tate_open_subgroup_bijective
#print axioms FiniteIndexTate.range_coord_open_subgroup
#print axioms FiniteIndexTate.range_coord_eq_torsion_of_root
#print axioms FiniteIndexTate.range_coord_open_subgroup_eq_image_torsion

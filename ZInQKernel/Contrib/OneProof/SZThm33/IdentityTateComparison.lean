import ZInQKernel.Contrib.OneProof.SZThm33.ConnectedTateLift

/-! A group comparison restricts to its geometric connected identity
components, without changing rational Tate modules. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace Topology
open ZInQ.HeightSplit SmoothGroup

set_option linter.style.haveILetI false

namespace SZRaynaud

variable {k : Type} [Field k] [IsAlgClosed k]

private theorem map_identity_mem_range
    {X Y X₀ Y₀ : (Over (Spec (CommRingCat.of k)))} [GrpObj X] [GrpObj Y] [GrpObj X₀] [GrpObj Y₀]
    [ConnectedSpace X₀.left] [ConnectedSpace Y₀.left] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsMonHom f] (i : X₀ ⟶ X) [IsMonHom i]
    (j : Y₀ ⟶ Y) [IsOpenImmersion j.left] [IsMonHom j] :
    Set.range (i ≫ f).left ⊆ Set.range j.left := by
  rw [range_openConnectedSubgroup_eq_connectedComponent j]
  have hη : (1 : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ Y).left (IsLocalRing.closedPoint k) ∈ Set.range (i ≫ f).left :=
    ⟨(1 : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ X₀).left (IsLocalRing.closedPoint k),
      congrArg (fun p : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ Y => p.left (IsLocalRing.closedPoint k))
        (map_one (mapGroupPoint (i ≫ f) (P := (𝟙_ (Over (Spec (CommRingCat.of k)))))))⟩
  exact (isPreconnected_range (i ≫ f).left.continuous).subset_connectedComponent hη

/-- The comparison sends the connected identity component into the connected
identity component. -/
theorem exists_map_connectedOpenSubgroup
    {X Y X₀ Y₀ : (Over (Spec (CommRingCat.of k)))} [GrpObj X] [GrpObj Y] [GrpObj X₀] [GrpObj Y₀]
    [ConnectedSpace X₀.left] [ConnectedSpace Y₀.left] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsMonHom f] (i : X₀ ⟶ X) [IsMonHom i]
    (j : Y₀ ⟶ Y) [IsOpenImmersion j.left] [IsMonHom j] :
    ∃ f₀ : X₀ ⟶ Y₀, f₀ ≫ j = i ≫ f ∧ IsMonHom f₀ := by
  let a := IsOpenImmersion.lift j.left (i ≫ f).left (map_identity_mem_range f i j)
  have ha : a ≫ j.left = (i ≫ f).left := IsOpenImmersion.lift_fac ..
  let f₀ : X₀ ⟶ Y₀ := Over.homMk a (by
    rw [← Over.w j, ← Category.assoc, ha, Over.w])
  have eq : f₀ ≫ j = i ≫ f := Over.OverMorphism.ext ha
  haveI : Mono j := Over.mono_of_mono_left j
  haveI : IsMonHom (f₀ ≫ j) := eq ▸ inferInstanceAs (IsMonHom (i ≫ f))
  exact ⟨f₀, eq, AVGlue.isMonHom_of_comp_mono f₀ j⟩

variable {ℓ : ℕ} [Fact ℓ.Prime]

omit [IsAlgClosed k] in
private theorem mapModelTate'_comp
    {X Y Z : (Over (Spec (CommRingCat.of k)))} [GrpObj X] [GrpObj Y] [GrpObj Z]
    [IsCommMonObj X] [IsCommMonObj Y] [IsCommMonObj Z]
    (a : X ⟶ Y) (b : Y ⟶ Z) [IsMonHom a] [IsMonHom b] :
    mapModelTate (ℓ := ℓ) (a ≫ b) (Spec.map (CommRingCat.ofHom (algebraMap k k))) =
      (mapModelTate (ℓ := ℓ) b (Spec.map (CommRingCat.ofHom (algebraMap k k)))).comp (mapModelTate (ℓ := ℓ) a (Spec.map (CommRingCat.ofHom (algebraMap k k)))) := by
  apply LinearMap.ext
  intro t
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (Category.assoc (Additive.toMul (t.1 n)) a b).symm

/-- Restricting a comparison to the identity components preserves
surjectivity on rational Tate modules. -/
theorem rationalTate_surjective_connectedOpenSubgroup
    {X Y X₀ Y₀ : (Over (Spec (CommRingCat.of k)))} [GrpObj X] [GrpObj Y] [GrpObj X₀] [GrpObj Y₀]
    [IsCommMonObj X] [IsCommMonObj Y] [IsCommMonObj X₀] [IsCommMonObj Y₀]
    [ConnectedSpace X₀.left] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : X ⟶ Y) [IsMonHom f] (i : X₀ ⟶ X) [IsOpenImmersion i.left] [IsMonHom i]
    (j : Y₀ ⟶ Y) [IsOpenImmersion j.left] [IsMonHom j]
    (f₀ : X₀ ⟶ Y₀) [IsMonHom f₀] (hf₀ : f₀ ≫ j = i ≫ f)
    (hf : Function.Surjective ((mapModelTate (ℓ := ℓ) f (Spec.map (CommRingCat.ofHom (algebraMap k k)))).baseChange ℚ_[ℓ])) :
    Function.Surjective ((mapModelTate (ℓ := ℓ) f₀ (Spec.map (CommRingCat.ofHom (algebraMap k k)))).baseChange ℚ_[ℓ]) := by
  let a := mapModelTate (ℓ := ℓ) i (Spec.map (CommRingCat.ofHom (algebraMap k k)))
  let b := mapModelTate (ℓ := ℓ) j (Spec.map (CommRingCat.ofHom (algebraMap k k)))
  let c := mapModelTate (ℓ := ℓ) f₀ (Spec.map (CommRingCat.ofHom (algebraMap k k)))
  let d := mapModelTate (ℓ := ℓ) f (Spec.map (CommRingCat.ofHom (algebraMap k k)))
  have hEq : b.comp c = d.comp a := by
    rw [← mapModelTate'_comp f₀ j, ← mapModelTate'_comp i f]
    congr 1
  have hEqQ : (b.baseChange ℚ_[ℓ]).comp (c.baseChange ℚ_[ℓ]) =
      (d.baseChange ℚ_[ℓ]).comp (a.baseChange ℚ_[ℓ]) := by
    simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange ℚ_[ℓ]) hEq
  have ha : Function.Surjective (a.baseChange ℚ_[ℓ]) :=
    LinearMap.baseChange_surjective ℚ_[ℓ] (surjective_mapTate_connectedOpenSubgroup (ℓ := ℓ) i)
  have hb : Function.Injective b := by
    intro s t h
    apply Subtype.ext
    funext n
    apply Additive.toMul.injective
    haveI : Mono j := Over.mono_of_mono_left j
    apply (cancel_mono j).mp
    exact congrArg (fun z => Additive.toMul (z.1 n)) h
  have : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  have hbQ : Function.Injective (b.baseChange ℚ_[ℓ]) :=
    Module.Flat.lTensor_preserves_injective_linearMap b hb
  intro x
  obtain ⟨y, hy⟩ := hf (b.baseChange ℚ_[ℓ] x)
  obtain ⟨z, hz⟩ := ha y
  refine ⟨z, hbQ ?_⟩
  change ((b.baseChange ℚ_[ℓ]).comp (c.baseChange ℚ_[ℓ])) z = _
  rw [hEqQ, LinearMap.comp_apply, hz]
  exact hy

#print axioms exists_map_connectedOpenSubgroup
#print axioms rationalTate_surjective_connectedOpenSubgroup

end SZRaynaud

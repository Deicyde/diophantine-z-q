import ZInQKernel.OneProof.H.TailZ16

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.MumfordRigidity

open LeafQM.AV.R1UnivRigid PkgI3

/-! ## The two printed leaves -/

/-- **LEAF (the rigidity lemma over a base).** -/
def RigidityLemma : Prop :=
  ∀ (S X Y : Scheme.{0}) (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y), f ≫ q = p →
    IsLocallyNoetherian S → ConnectedSpace S → IsProper p → Smooth p → GeometricallyConnected p →
    IsSeparated q → LocallyOfFiniteType q →
    (∃ (s : S) (y : Y), ∀ x : X, p x = s → f x = y) →
    ∃ σ : S ⟶ Y, σ ≫ q = 𝟙 S ∧ f = p ≫ σ

/-- **LEAF (the group law).** -/
def MumfordGroupLaw : Prop :=
  ∀ (S : Scheme.{0}) (F : Over S) (e : S ⟶ F.left), IsLocallyNoetherian S → IsProper F.hom →
    Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 S →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e

/-! ## Topology -/

theorem isOpen_connectedComponent_of_noetherianSpace {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] (x : α) : IsOpen (connectedComponent x) := by
  classical
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := α)
  have hc : (connectedComponent x)ᶜ =
      ⋃₀ {Z ∈ irreducibleComponents α | Z ∩ connectedComponent x = ∅} := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_ofPred_eq]
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩,
        mem_irreducibleComponent⟩
      by_contra hne
      obtain ⟨z, hzZ, hzC⟩ := Set.nonempty_iff_ne_empty.2 hne
      apply hy
      have hZc : irreducibleComponent y ⊆ connectedComponent z :=
        (IsIrreducible.isConnected (isIrreducible_irreducibleComponent (x := y))).isPreconnected |>.subset_connectedComponent hzZ
      rw [connectedComponent_eq hzC]
      exact hZc mem_irreducibleComponent
    · rintro ⟨Z, ⟨-, hZC⟩, hyZ⟩ hyC
      exact (Set.eq_empty_iff_forall_notMem.1 hZC) y ⟨hyZ, hyC⟩
  rw [← isClosed_compl_iff, hc]
  exact (hfin.subset (fun Z hZ => hZ.1)).isClosed_sUnion
    (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)

theorem isOpen_connectedComponent_of_isLocallyNoetherian (T : Scheme.{0})
    [IsLocallyNoetherian T] (t : T) : IsOpen (connectedComponent t) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  have : IsNoetherianRing Γ(T, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : TopologicalSpace.NoetherianSpace V := noetherianSpace_of_isAffineOpen V hV
  refine ⟨Subtype.val '' connectedComponent (⟨y, hyV⟩ : V), ?_, ?_, ⟨⟨y, hyV⟩,
    mem_connectedComponent, rfl⟩⟩
  · rw [connectedComponent_eq hy]
    exact (isConnected_connectedComponent.image _
      continuous_subtype_val.continuousOn).isPreconnected.subset_connectedComponent
      ⟨⟨y, hyV⟩, mem_connectedComponent, rfl⟩
  · exact V.isOpen.isOpenMap_subtype_val _
      (isOpen_connectedComponent_of_noetherianSpace (α := V) ⟨y, hyV⟩)

/-! ## Cor. 6.4 from the rigidity lemma -/

section Cor64

variable {S : Scheme.{0}} (F : Over S) [GrpObj F]

theorem one_comp_eq_one {f : F ⟶ F} (hf : η[F] ≫ f = η[F]) : (1 : F ⟶ F) ≫ f = 1 := by
  rw [Hom.one_def, Category.assoc, hf]

/-- The defect `(x, y) ↦ f(xy) · (f(x) f(y))⁻¹`. -/
noncomputable def defect (f : F ⟶ F) : F ⊗ F ⟶ F :=
  (μ ≫ f) * ((fst F F ≫ f) * (snd F F ≫ f))⁻¹

/-- `x ↦ (1, x)`. -/
noncomputable def jl : F ⟶ F ⊗ F := lift 1 (𝟙 F)

/-- `x ↦ (x, 1)`. -/
noncomputable def jr : F ⟶ F ⊗ F := lift (𝟙 F) 1

theorem jl_defect {f : F ⟶ F} (hf : η[F] ≫ f = η[F]) : jl F ≫ defect F f = 1 := by
  have e1 : lift (1 : F ⟶ F) (𝟙 F) ≫ μ[F] = 𝟙 F := by
    change (1 : F ⟶ F) * 𝟙 F = 𝟙 F
    exact _root_.one_mul _
  simp only [jl, defect, comp_mul, GrpObj.comp_inv, ← Category.assoc, e1, lift_fst, lift_snd,
    Category.id_comp, one_comp_eq_one F hf, _root_.one_mul, mul_inv_cancel]

theorem jr_defect {f : F ⟶ F} (hf : η[F] ≫ f = η[F]) : jr F ≫ defect F f = 1 := by
  have e1 : lift (𝟙 F) (1 : F ⟶ F) ≫ μ[F] = 𝟙 F := by
    change 𝟙 F * (1 : F ⟶ F) = 𝟙 F
    exact _root_.mul_one _
  simp only [jr, defect, comp_mul, GrpObj.comp_inv, ← Category.assoc, e1, lift_fst, lift_snd,
    Category.id_comp, one_comp_eq_one F hf, _root_.mul_one, mul_inv_cancel]

end Cor64

/-! ## The scheme part -/

set_option linter.unusedSectionVars false

/-- **Rigidity on every connected component** (from the printed `RigidityLemma`, applied over each
connected component of `T`, which is open since `T` is locally noetherian). -/
theorem eq_of_rigidity (hR : RigidityLemma) {T X : Scheme.{0}} [IsLocallyNoetherian T] (p : X ⟶ T)
    [IsProper p] [Smooth p] [GeometricallyConnected p] (f' : X ⟶ X) (j : T ⟶ X)
    (hf'p : f' ≫ p = p) (hjp : j ≫ p = 𝟙 T)
    (hfib : ∀ t : T, ∃ s ∈ connectedComponent t, ∃ y : X, ∀ x : X, p x = s → f' x = y) :
    f' = p ≫ j ≫ f' := by
  refine Scheme.hom_ext_of_forall f' (p ≫ j ≫ f') fun x => ?_
  let W : T.Opens := ⟨connectedComponent (p x), isOpen_connectedComponent_of_isLocallyNoetherian _ _⟩
  let U := p ⁻¹ᵁ W
  refine ⟨U, (mem_connectedComponent : p x ∈ connectedComponent (p x)), ?_⟩
  have hUle : U ≤ f' ⁻¹ᵁ U := fun y hy => by
    change p (f' y) ∈ connectedComponent (p x)
    rw [← Scheme.Hom.comp_apply, hf'p]
    exact hy
  let f'' := f'.resLE U U hUle
  have hW : ConnectedSpace W := Subtype.connectedSpace isConnected_connectedComponent
  have hProp : f'' ≫ (p ∣_ W) = p ∣_ W := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, hf'p]
  obtain ⟨s, hs, y, hy⟩ := hfib (p x)
  obtain ⟨x0, hx0⟩ := (inferInstance : Surjective p).surj s
  have hyU : y ∈ U := by
    change p y ∈ connectedComponent (p x)
    rw [← hy x0 hx0, ← Scheme.Hom.comp_apply, hf'p, hx0]
    exact hs
  obtain ⟨σ, -, hfσ⟩ := hR W U U (p ∣_ W) (p ∣_ W) f'' hProp inferInstance hW inferInstance
    inferInstance inferInstance inferInstance inferInstance ⟨⟨s, hs⟩, ⟨y, hyU⟩, fun x' hx' => by
      apply Subtype.ext
      change (f'' ≫ U.ι) x' = y
      rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
      apply hy
      have := congrArg Subtype.val hx'
      change ((p ∣_ W) ≫ W.ι) x' = s at this
      rwa [morphismRestrict_ι, Scheme.Hom.comp_apply] at this⟩
  let jW : W.toScheme ⟶ U.toScheme := j.resLE U W (fun y hy => by
    change p (j y) ∈ connectedComponent (p x)
    rw [← Scheme.Hom.comp_apply, hjp]
    exact hy)
  have hjW : jW ≫ (p ∣_ W) = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, hjp, Category.comp_id, Category.id_comp]
  have hσ' : σ = jW ≫ f'' := by rw [hfσ, ← Category.assoc, hjW, Category.id_comp]
  calc U.ι ≫ f' = f'' ≫ U.ι := (Scheme.Hom.resLE_comp_ι _ _).symm
    _ = (p ∣_ W) ≫ σ ≫ U.ι := by rw [← Category.assoc, ← hfσ]
    _ = (p ∣_ W) ≫ W.ι ≫ j ≫ f' := by
      rw [hσ', Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc jW,
        Scheme.Hom.resLE_comp_ι, Category.assoc]
    _ = U.ι ≫ p ≫ j ≫ f' := by rw [← Category.assoc, morphismRestrict_ι, Category.assoc]

section Cor64Main

variable {S : Scheme.{0}} (F : Over S) [GrpObj F]

/-- The square `x ↦ (x, 1)`, `F → S`, `snd`, `η` is a pullback. -/
theorem isPullback_jr : IsPullback (jr F).left F.hom (snd F F).left η[F].left := by
  have hw : (jr F).left ≫ (snd F F).left = F.hom ≫ η[F].left := by
    rw [← Over.comp_left, jr, lift_snd]; rfl
  have h1 : (jr F).left ≫ pullback.fst F.hom F.hom = 𝟙 F.left := by
    rw [← Over.fst_left, ← Over.comp_left, jr, lift_fst]; rfl
  have h2 : η[F].left ≫ F.hom = 𝟙 S := Over.w η[F]
  refine IsPullback.of_right ?_ hw (IsPullback.of_hasPullback F.hom F.hom)
  rw [h1, h2]
  exact IsPullback.id_horiz F.hom

/-- On the fibre of `snd : F ×_S F → F` over `η(s)`, the map `(defect, snd)` is constant. -/
theorem fibre_value {f : F ⟶ F} (hf : η[F] ≫ f = η[F]) (x : (F ⊗ F).left) (s : S)
    (hx : (snd F F).left x = η[F].left s) :
    (lift (defect F f) (snd F F)).left x = (lift η[F] η[F]).left s := by
  obtain ⟨w, hw1, hw2⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := (snd F F).left) (g := η[F].left) x s hx
  have hpb := isPullback_jr F
  have hz1 : (jr F).left (hpb.isoPullback.inv w) = x := by
    rw [← hw1, ← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst]
  have hz2 : F.hom (hpb.isoPullback.inv w) = s := by
    rw [← hw2, ← Scheme.Hom.comp_apply, hpb.isoPullback_inv_snd]
  have key : jr F ≫ lift (defect F f) (snd F F) = toUnit F ≫ lift η[F] η[F] := by
    rw [comp_lift, comp_lift, jr_defect F hf, jr, lift_snd]; rfl
  rw [← hz1, ← hz2, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, key,
    Over.comp_left, Over.toUnit_left]
  rfl

theorem eta_mem_connectedComponent [GeometricallyConnected F.hom] (t : F.left) :
    η[F].left (F.hom t) ∈ connectedComponent t := by
  have hc := F.hom.isConnected_preimage_singleton (F.hom t)
  refine hc.isPreconnected.subset_connectedComponent (x := t) rfl ?_
  change F.hom (η[F].left (F.hom t)) = F.hom t
  rw [← Scheme.Hom.comp_apply, Over.w η[F]]
  rfl

/-- **The defect vanishes** (Mumford's proof of *GIT* Cor. 6.4). -/
theorem defect_eq_one (hR : RigidityLemma) [IsLocallyNoetherian S] [IsProper F.hom] [Smooth F.hom]
    [GeometricallyConnected F.hom] {f : F ⟶ F} (hf : η[F] ≫ f = η[F]) : defect F f = 1 := by
  have : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian F.hom
  have : IsProper (snd F F).left := by
    change IsProper (pullback.snd F.hom F.hom); infer_instance
  have : Smooth (snd F F).left := by
    change Smooth (pullback.snd F.hom F.hom); infer_instance
  have : GeometricallyConnected (snd F F).left := by
    change GeometricallyConnected (pullback.snd F.hom F.hom); infer_instance
  have hf'p : (lift (defect F f) (snd F F)).left ≫ (snd F F).left = (snd F F).left := by
    rw [← Over.comp_left, lift_snd]
  have hjp : (jl F).left ≫ (snd F F).left = 𝟙 _ := by
    rw [← Over.comp_left, jl, lift_snd]; rfl
  have key := eq_of_rigidity hR (snd F F).left _ (jl F).left hf'p hjp fun t =>
    ⟨η[F].left (F.hom t), eta_mem_connectedComponent F t, _, fun x hx => fibre_value F hf x _ hx⟩
  have key2 : lift (defect F f) (snd F F) = snd F F ≫ jl F ≫ lift (defect F f) (snd F F) :=
    Over.OverMorphism.ext key
  have := congrArg (· ≫ fst F F) key2
  simp only [Category.assoc, lift_fst] at this
  rw [this, jl_defect F hf, Hom.one_def, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

/-- **Mumford, *GIT* Cor. 6.4 for endomorphisms**, from the rigidity lemma. -/
theorem isMonHom_of_rigidity (hR : RigidityLemma) [IsLocallyNoetherian S] [IsProper F.hom]
    [Smooth F.hom] [GeometricallyConnected F.hom] {f : F ⟶ F} (hf : η[F] ≫ f = η[F]) :
    IsMonHom f where
  one_hom := hf
  mul_hom := by
    have h := defect_eq_one F hR hf
    rw [defect, mul_inv_eq_one] at h
    rw [h, Hom.mul_def, lift_fst_comp_snd_comp]

end Cor64Main

/-- **`MumfordRigidityCore` from its two printed leaves.** -/
theorem mumfordRigidityCore_of_printed (hG : MumfordGroupLaw) (hR : RigidityLemma) :
    MumfordRigidityCore := by
  intro S F e hN hP hS hC he hfib
  obtain ⟨G, hη⟩ := hG S F e hN hP hS hC he hfib
  refine ⟨G, hη, fun f hf => ?_⟩
  exact isMonHom_of_rigidity F hR (Over.OverMorphism.ext (by rw [Over.comp_left, hη, hf]))

end ZInQ.Contrib.MumfordRigidity

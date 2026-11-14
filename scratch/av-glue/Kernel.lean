import Mathlib
import ZInQKernel.Contrib.AVB1.Poincare

/-!
# av-glue, part C: `KernelAbSubvariety` from a statement about the kernel group scheme

Check with `lake env lean scratch/av-glue/Kernel.lean`.

`KernelAbSubvariety` (part A's leaf) has the hypothesis "`h` is not locally quasi-finite". Here
that hypothesis is moved to the kernel: if the kernel `ker h = A ×_B Spec k` (Mathlib's fibre
product of `h` with the identity section of `B`) is locally quasi-finite over `k`, then so is `h`
(the shear isomorphism `A ×_k ker h ≅ A ×_B A`, `(a, x) ↦ (a, a + x)`, proved here). So
`KernelAbSubvariety` follows from `KernelIdentityComponent`: if `ker h` is not quasi-finite over
`k`, `(ker h)⁰_red` is a positive-dimensional abelian subvariety killed by `h`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace AVGlue

/-- (verbatim from `scratch/av-glue/SurjIsog.lean`) **LEAF (new; `(ker h)⁰_red` is an abelian
subvariety).** See there. -/
def KernelAbSubvariety : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A B : _root_.PkgI3.AbVar k)
    (h : _root_.PkgI3.AbVar.Hom A B), ¬ LocallyQuasiFinite h.hom.left →
    ∃ (C : _root_.PkgI3.AbVar k) (j : _root_.PkgI3.AbVar.Hom C A),
      IsClosedImmersion j.hom.left ∧ 0 < C.dim ∧ j.hom ≫ h.hom = 1

section Kernel

variable {k : Type} [Field k] {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X)

/-- The kernel `ker h = A ×_B Spec k` (fibre product of `h` with the identity section), as a
`k`-scheme. -/
noncomputable abbrev kerOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (pullback.fst h.left (η[B.X]).left ≫ A.X.hom)

/-- The inclusion of the kernel. -/
noncomputable def kerι : kerOver h ⟶ A.X := Over.homMk (pullback.fst h.left (η[B.X]).left) rfl

lemma kerι_left : (kerι h).left = pullback.fst h.left (η[B.X]).left := rfl

instance : Mono (kerι h) := by
  haveI : Mono (kerι h).left := (inferInstance : Mono (pullback.fst h.left (η[B.X]).left))
  exact Over.mono_of_mono_left _

lemma ker_snd_eq :
    pullback.snd h.left (η[B.X]).left = pullback.fst h.left (η[B.X]).left ≫ A.X.hom := by
  have h2 := congrArg (· ≫ B.X.hom) (pullback.condition (f := h.left) (g := (η[B.X]).left))
  simp only [Category.assoc, Over.w] at h2
  simpa using h2.symm

lemma kerι_comp : kerι h ≫ h = 1 := by
  ext1
  rw [Over.comp_left, Hom.one_def, Over.comp_left, Over.toUnit_left, kerι_left, pullback.condition,
    ker_snd_eq]
  rfl

/-- Lifting into the kernel. -/
noncomputable def kerLift {W : Over (Spec (CommRingCat.of k))} (g : W ⟶ A.X) (hg : g ≫ h = 1) :
    W ⟶ kerOver h :=
  Over.homMk (pullback.lift g.left W.hom (by
    have := congrArg Over.Hom.left hg
    rwa [Over.comp_left, Hom.one_def, Over.comp_left, Over.toUnit_left] at this)) (by simp)

@[reassoc (attr := simp)]
lemma kerLift_ι {W : Over (Spec (CommRingCat.of k))} (g : W ⟶ A.X) (hg : g ≫ h = 1) :
    kerLift h g hg ≫ kerι h = g := by
  ext1; simp [kerLift, kerι]

/-! ### The shear isomorphism `A ×_k ker h ≅ A ×_B A` -/

variable [IsMonHom h]

/-- `(a, x) ↦ a + x`. -/
noncomputable def shearS : A.X ⊗ kerOver h ⟶ A.X := fst _ _ * (snd _ _ ≫ kerι h)

lemma shearS_comp : shearS h ≫ h = fst _ _ ≫ h := by
  rw [shearS, MonObj.mul_comp, Category.assoc, kerι_comp, MonObj.comp_one, _root_.mul_one]

/-- `A ×_B A` as a `k`-scheme. -/
noncomputable abbrev pbOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk (pullback.fst h.left h.left ≫ A.X.hom)

lemma pb_w : pullback.snd h.left h.left ≫ A.X.hom = pullback.fst h.left h.left ≫ A.X.hom := by
  have h2 := congrArg (· ≫ B.X.hom) (pullback.condition (f := h.left) (g := h.left))
  simp only [Category.assoc, Over.w] at h2
  exact h2.symm

noncomputable def pbFst : pbOver h ⟶ A.X := Over.homMk (pullback.fst h.left h.left) rfl
noncomputable def pbSnd : pbOver h ⟶ A.X := Over.homMk (pullback.snd h.left h.left) (pb_w h)

lemma pbFst_comp : pbFst h ≫ h = pbSnd h ≫ h := by
  ext1; exact pullback.condition

/-- `(a, a') ↦ a' - a`. -/
noncomputable def pbD : pbOver h ⟶ A.X := (pbFst h)⁻¹ * pbSnd h

lemma pbD_comp : pbD h ≫ h = 1 := by
  rw [pbD, MonObj.mul_comp, GrpObj.inv_comp, pbFst_comp, inv_mul_cancel]

noncomputable def pbT : pbOver h ⟶ kerOver h := kerLift h (pbD h) (pbD_comp h)

/-- The shear map `A ×_k ker h → A ×_B A`. -/
noncomputable def shearHom : (A.X ⊗ kerOver h).left ⟶ pullback h.left h.left :=
  pullback.lift (fst A.X (kerOver h)).left (shearS h).left (by
    rw [← Over.comp_left, ← Over.comp_left, shearS_comp])

/-- Its inverse. -/
noncomputable def shearInv : pullback h.left h.left ⟶ (A.X ⊗ kerOver h).left :=
  pullback.lift (pullback.fst h.left h.left) (pbT h).left (by
    have := Over.w (pbT h)
    simpa using this.symm)

noncomputable def shearHomO : A.X ⊗ kerOver h ⟶ pbOver h :=
  Over.homMk (shearHom h) (by simp [shearHom])

noncomputable def shearInvO : pbOver h ⟶ A.X ⊗ kerOver h :=
  Over.homMk (shearInv h) (by simp [shearInv])

lemma shearHomO_fst : shearHomO h ≫ pbFst h = fst _ _ := by
  ext1; simp [shearHomO, pbFst, shearHom]

lemma shearHomO_snd : shearHomO h ≫ pbSnd h = shearS h := by
  ext1; simp [shearHomO, pbSnd, shearHom]

lemma shearInvO_fst : shearInvO h ≫ fst _ _ = pbFst h := by
  ext1; simp [shearInvO, pbFst, shearInv]

lemma shearInvO_snd : shearInvO h ≫ snd _ _ = pbT h := by
  ext1; simp [shearInvO, shearInv]

/-- The shear isomorphism. -/
noncomputable def shearIso : (A.X ⊗ kerOver h).left ≅ pullback h.left h.left where
  hom := shearHom h
  inv := shearInv h
  hom_inv_id := by
    apply pullback.hom_ext
    · simp [shearHom, shearInv]
    · apply (cancel_mono (pullback.fst h.left (η[B.X]).left)).1
      have e1 : shearHomO h ≫ pbD h = snd _ _ ≫ kerι h := by
        rw [pbD, MonObj.comp_mul, GrpObj.comp_inv, shearHomO_fst, shearHomO_snd, shearS,
          inv_mul_cancel_left]
      have e2 := congrArg Over.Hom.left e1
      simp only [Over.comp_left] at e2
      simp only [Category.assoc, shearInv, pullback.lift_snd]
      change shearHom h ≫ (pbT h ≫ kerι h).left = _
      rw [pbT, kerLift_ι]
      exact e2.trans (by simp [kerι])
  inv_hom_id := by
    apply pullback.hom_ext
    · simp [shearHom, shearInv]
    · have e1 : shearInvO h ≫ shearS h = pbSnd h := by
        rw [shearS, MonObj.comp_mul, ← Category.assoc, shearInvO_fst, shearInvO_snd, pbT,
          kerLift_ι, pbD, mul_inv_cancel_left]
      have e2 := congrArg Over.Hom.left e1
      simp only [Over.comp_left] at e2
      simp only [Category.assoc, shearHom, pullback.lift_snd]
      change shearInv h ≫ (shearS h).left = _
      exact e2.trans (by simp [pbSnd])

lemma shearIso_hom_fst :
    (shearIso h).hom ≫ pullback.fst h.left h.left = pullback.fst A.X.hom (kerOver h).hom := by
  simp [shearIso, shearHom]

/-- **If the kernel is locally quasi-finite over `k`, so is `h`.** -/
theorem lqf_of_ker [IsProper h.left] (hK : LocallyQuasiFinite (kerOver h).hom) :
    LocallyQuasiFinite h.left := by
  haveI : LocallyQuasiFinite (pullback.fst A.X.hom (kerOver h).hom) := inferInstance
  haveI : LocallyQuasiFinite (pullback.fst h.left h.left) := by
    have : pullback.fst h.left h.left =
        (shearIso h).inv ≫ pullback.fst A.X.hom (kerOver h).hom := by
      rw [← shearIso_hom_fst, Iso.inv_hom_id_assoc]
    rw [this]; infer_instance
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
  by_cases hy : y ∈ Set.range h.left
  · obtain ⟨x0, rfl⟩ := hy
    refine (((pullback.fst h.left h.left).finite_preimage_singleton x0).image
      (pullback.snd h.left h.left)).subset ?_
    intro a ha
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x0 a ha.symm
    exact ⟨z, hz1, hz2⟩
  · exact Set.finite_empty.subset fun a ha => hy ⟨a, ha⟩

end Kernel

-- BEGIN DUP (verbatim from scratch/av-glue/ImageFact.lean; dropped by mk_combined.py)
section Transport

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G Y : C} [GrpObj G]

/-- The group object structure on a subobject `i : Y ↪ G` closed under the group law. -/
@[reducible] noncomputable def grpObjOfMono (i : Y ⟶ G) [Mono i]
    (mulY : Y ⊗ Y ⟶ Y) (hmul : mulY ≫ i = fst Y Y ≫ i * snd Y Y ≫ i)
    (oneY : 𝟙_ C ⟶ Y) (hone : oneY ≫ i = η[G])
    (invY : Y ⟶ Y) (hinv : invY ≫ i = i⁻¹) : GrpObj Y where
  one := oneY
  mul := mulY
  one_mul := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, whiskerRight_fst_assoc,
      whiskerRight_snd_assoc, hone, leftUnitor_hom]
    rw [show fst (𝟙_ C) Y ≫ η[G] = 1 by rw [Hom.one_def]; congr 1; exact toUnit_unique _ _,
      _root_.one_mul]
  mul_one := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc, hone, rightUnitor_hom]
    rw [show snd Y (𝟙_ C) ≫ η[G] = 1 by rw [Hom.one_def]; congr 1; exact toUnit_unique _ _,
      _root_.mul_one]
  mul_assoc := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, whiskerRight_fst_assoc,
      whiskerRight_snd_assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
      associator_hom_fst_assoc, associator_hom_snd_fst_assoc, associator_hom_snd_snd_assoc]
    rw [_root_.mul_assoc]
  inv := invY
  left_inv := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hinv,
      hone, Category.id_comp]
    rw [inv_mul_cancel, Hom.one_def]
  right_inv := by
    apply (cancel_mono i).1
    simp only [Category.assoc, hmul, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hinv,
      hone, Category.id_comp]
    rw [mul_inv_cancel, Hom.one_def]

/-- The inclusion is a homomorphism for `grpObjOfMono`. -/
theorem isMonHom_grpObjOfMono (i : Y ⟶ G) [Mono i]
    (mulY : Y ⊗ Y ⟶ Y) (hmul : mulY ≫ i = fst Y Y ≫ i * snd Y Y ≫ i)
    (oneY : 𝟙_ C ⟶ Y) (hone : oneY ≫ i = η[G])
    (invY : Y ⟶ Y) (hinv : invY ≫ i = i⁻¹) :
    letI := grpObjOfMono i mulY hmul oneY hone invY hinv
    IsMonHom i := by
  letI := grpObjOfMono i mulY hmul oneY hone invY hinv
  refine ⟨hone, ?_⟩
  change mulY ≫ i = _
  rw [hmul, Hom.mul_def, ← lift_fst_comp_snd_comp]

/-- If `i` is a monic homomorphism and `π ≫ i` is a homomorphism, so is `π`. -/
theorem isMonHom_of_comp_mono {M : C} [MonObj M] [MonObj Y] (π : M ⟶ Y) (i : Y ⟶ G) [Mono i]
    [IsMonHom i] [IsMonHom (π ≫ i)] : IsMonHom π := by
  refine ⟨?_, ?_⟩
  · apply (cancel_mono i).1
    rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · apply (cancel_mono i).1
    rw [Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
      ← tensorHom_comp_tensorHom]

end Transport
-- END DUP

/-! ## The identity component of the kernel -/

/-- In a noetherian space, connected components are open. -/
theorem isOpen_connectedComponent_of_noetherian {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] (x : X) : IsOpen (connectedComponent x) := by
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have heq : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | Disjoint Z (connectedComponent x)}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
        isIrreducible_singleton
      refine ⟨Z, ⟨hZ, ?_⟩, hyZ rfl⟩
      have hZy : Z ⊆ connectedComponent y :=
        hZ.1.isConnected.isPreconnected.subset_connectedComponent
          (hyZ rfl)
      refine Set.disjoint_of_subset_left hZy ?_
      rw [Set.disjoint_iff]
      rintro w ⟨hw1, hw2⟩
      apply hy
      rw [connectedComponent_eq hw2, ← connectedComponent_eq hw1]
      exact mem_connectedComponent
    · rintro ⟨Z, ⟨-, hdisj⟩, hyZ⟩ hy
      exact Set.disjoint_left.mp hdisj hyZ hy
  rw [← isClosed_compl_iff, heq]
  exact (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion fun Z hZ =>
    isClosed_of_mem_irreducibleComponents Z hZ.1

/-- **LEAF (Stacks, Varieties, Lemma 33.7.14, Tag 04KV; UNVERIFIED locator).** A connected
scheme locally of finite type over a field `k` with a `k`-rational point is geometrically
connected. (Stacks states it without the finiteness hypothesis and with "a point `x` such that `k`
is algebraically closed in `κ(x)`"; a `k`-rational point is such a point, so this is a
consequence, never stronger.) -/
def GeomConnOfRationalPoint : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    (s : Spec (CommRingCat.of k) ⟶ X), s ≫ f = 𝟙 _ → LocallyOfFiniteType f →
    ConnectedSpace X → GeometricallyConnected f

/-- **LEAF (group schemes are equidimensional; Stacks, Groupoids, Lemma 39.8.? "`G` is
equidimensional and `dim G = dim_g G`" (UNVERIFIED locator); SGA 3, Exp. VI_A, 2.4; Milne,
*Algebraic Groups* (2017), Prop. 1.37? (UNVERIFIED)).** For a group scheme `G` of finite type over
a field, every irreducible component of `G` has the dimension of `G` (Krull dimensions of the
underlying spaces; a component with its subspace topology). A consequence of the published
statement (restricted to finite type), never stronger. -/
def GroupSchemeEquidim : Prop :=
  ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
    LocallyOfFiniteType G.hom → QuasiCompact G.hom →
    ∀ Z ∈ irreducibleComponents G.left, topologicalKrullDim Z = topologicalKrullDim G.left

/-- **LEAF: Cartier's theorem** (copy of `CartierSmooth` in `scratch/av-glue/ImageFact.lean`). -/
def CartierSmooth' : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
    LocallyOfFiniteType G.hom → Smooth G.hom

section IdComp

variable {k : Type} [Field k] {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X) [IsMonHom h]

noncomputable def kerMul : kerOver h ⊗ kerOver h ⟶ kerOver h :=
  kerLift h (fst _ _ ≫ kerι h * snd _ _ ≫ kerι h) (by
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, kerι_comp, MonObj.comp_one,
      MonObj.comp_one, _root_.mul_one])

lemma kerMul_ι : kerMul h ≫ kerι h = fst _ _ ≫ kerι h * snd _ _ ≫ kerι h := by
  rw [kerMul, kerLift_ι]

noncomputable def kerOne : 𝟙_ _ ⟶ kerOver h :=
  kerLift h η[A.X] (by
    rw [IsMonHom.one_hom, Hom.one_def, show toUnit (𝟙_ (Over (Spec (CommRingCat.of k)))) = 𝟙 _
      from toUnit_unique _ _, Category.id_comp])

lemma kerOne_ι : kerOne h ≫ kerι h = η[A.X] := by rw [kerOne, kerLift_ι]

noncomputable def kerInv : kerOver h ⟶ kerOver h :=
  kerLift h (kerι h)⁻¹ (by rw [GrpObj.inv_comp, kerι_comp, inv_one])

lemma kerInv_ι : kerInv h ≫ kerι h = (kerι h)⁻¹ := by rw [kerInv, kerLift_ι]

/-- The group structure of the kernel. -/
noncomputable instance kerGrp : GrpObj (kerOver h) :=
  grpObjOfMono (kerι h) (kerMul h) (kerMul_ι h) (kerOne h) (kerOne_ι h) (kerInv h) (kerInv_ι h)

instance isMonHom_kerι : IsMonHom (kerι h) :=
  isMonHom_grpObjOfMono (kerι h) (kerMul h) (kerMul_ι h) (kerOne h) (kerOne_ι h) (kerInv h)
    (kerInv_ι h)

instance : IsClosedImmersion (η[B.X]).left := by
  have : IsClosedImmersion ((η[B.X]).left ≫ B.X.hom) := by
    rw [Over.w]; dsimp; infer_instance
  exact IsClosedImmersion.of_comp _ B.X.hom

instance : IsClosedImmersion (kerι h).left :=
  inferInstanceAs (IsClosedImmersion (pullback.fst h.left (η[B.X]).left))

instance : IsProper (kerOver h).hom := by
  dsimp only [kerOver, Over.mk_hom]; infer_instance

instance : IsLocallyNoetherian (kerOver h).left :=
  LocallyOfFiniteType.isLocallyNoetherian (kerOver h).hom

instance : CompactSpace (kerOver h).left :=
  QuasiCompact.compactSpace_of_compactSpace (kerOver h).hom

instance : IsNoetherian (kerOver h).left := {}

instance subsingleton_unit_left : Subsingleton (𝟙_ (Over (Spec (CommRingCat.of k)))).left :=
  (inferInstance : Subsingleton (Spec (CommRingCat.of k)))

/-- The unit point of the kernel. -/
noncomputable def ePt : (kerOver h).left :=
  (η[kerOver h]).left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of k))))

/-- The identity component `(ker h)⁰` as an open subscheme. -/
noncomputable def U0 : (kerOver h).left.Opens :=
  ⟨connectedComponent (ePt h), isOpen_connectedComponent_of_noetherian _⟩

/-- `(ker h)⁰` as a `k`-scheme. -/
noncomputable abbrev covOver : Over (Spec (CommRingCat.of k)) :=
  Over.mk ((U0 h).ι ≫ (kerOver h).hom)

noncomputable def jK : covOver h ⟶ kerOver h := Over.homMk (U0 h).ι rfl

instance : Mono (jK h) := by
  haveI : Mono (jK h).left := (inferInstance : Mono (U0 h).ι)
  exact Over.mono_of_mono_left _

instance : IsClosedImmersion (jK h).left := by
  change IsClosedImmersion (U0 h).ι
  exact IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)

instance : ConnectedSpace (covOver h).left := by
  change ConnectedSpace (connectedComponent (ePt h))
  exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent

/-- Lift a map into the kernel whose range lies in `(ker h)⁰`. -/
noncomputable def liftCov {W : Over (Spec (CommRingCat.of k))} (g : W ⟶ kerOver h)
    (hg : Set.range g.left ⊆ connectedComponent (ePt h)) : W ⟶ covOver h :=
  Over.homMk (IsOpenImmersion.lift (U0 h).ι g.left (by rw [Scheme.Opens.range_ι]; exact hg))
    (by
      change IsOpenImmersion.lift _ _ _ ≫ (U0 h).ι ≫ (kerOver h).hom = W.hom
      rw [IsOpenImmersion.lift_fac_assoc]; exact Over.w g)

@[reassoc (attr := simp)]
lemma liftCov_jK {W : Over (Spec (CommRingCat.of k))} (g : W ⟶ kerOver h)
    (hg : Set.range g.left ⊆ connectedComponent (ePt h)) : liftCov h g hg ≫ jK h = g := by
  ext1; simp [liftCov, jK]

lemma range_sub {W : Over (Spec (CommRingCat.of k))} [ConnectedSpace W.left]
    (g : W ⟶ kerOver h) (w0 : W.left) (hw0 : g.left w0 = ePt h) :
    Set.range g.left ⊆ connectedComponent (ePt h) :=
  (isPreconnected_range g.left.continuous).subset_connectedComponent ⟨w0, hw0⟩

lemma eta_left_apply {W : Over (Spec (CommRingCat.of k))} (u : 𝟙_ _ ⟶ W) (g : W ⟶ kerOver h)
    (hu : u ≫ g = η[kerOver h]) (p : Spec (CommRingCat.of k)) : g.left (u.left p) = ePt h := by
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hu, ePt]
  congr 1
  exact Subsingleton.elim _ _

/-- The unit of `(ker h)⁰`. -/
noncomputable def oneCov : 𝟙_ _ ⟶ covOver h :=
  liftCov h η[kerOver h] (by
    rintro _ ⟨p, rfl⟩
    rw [show (η[kerOver h]).left p = ePt h by
      rw [ePt]; congr 1; exact Subsingleton.elim _ _]
    exact mem_connectedComponent)

lemma oneCov_jK : oneCov h ≫ jK h = η[kerOver h] := liftCov_jK _ _ _

variable (hG : GeomConnOfRationalPoint) (hC : CartierSmooth')

include hG in
theorem geomConn_cov : GeometricallyConnected (covOver h).hom := by
  refine hG k (covOver h).left (covOver h).hom (oneCov h).left (Over.w (oneCov h)) ?_ inferInstance
  dsimp only [covOver, Over.mk_hom]; infer_instance

lemma one_eq_eta : (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ kerOver h) = η[kerOver h] := by
  rw [Hom.one_def, show toUnit (𝟙_ (Over (Spec (CommRingCat.of k)))) = 𝟙 _
    from toUnit_unique _ _, Category.id_comp]

include hG in
theorem exists_mulCov : ∃ m : covOver h ⊗ covOver h ⟶ covOver h,
    m ≫ jK h = fst _ _ ≫ jK h * snd _ _ ≫ jK h := by
  haveI := geomConn_cov h hG
  haveI : ConnectedSpace (covOver h ⊗ covOver h).left :=
    (inferInstance : ConnectedSpace (pullback (C := Scheme.{0}) (covOver h).hom (covOver h).hom))
  refine ⟨liftCov h _ (range_sub h _ ((lift (oneCov h) (oneCov h)).left
    (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of k))))) ?_), liftCov_jK _ _ _⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, MonObj.comp_mul, ← Category.assoc,
    ← Category.assoc, lift_fst, lift_snd, oneCov_jK, ← one_eq_eta, _root_.mul_one, one_eq_eta, ePt]

theorem exists_invCov : ∃ v : covOver h ⟶ covOver h, v ≫ jK h = (jK h)⁻¹ := by
  refine ⟨liftCov h _ (range_sub h _ ((oneCov h).left
    (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of k))))) ?_), liftCov_jK _ _ _⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.comp_inv, oneCov_jK, ← one_eq_eta,
    inv_one, one_eq_eta, ePt]

/-- The group structure of `(ker h)⁰`. -/
noncomputable abbrev covGrp : GrpObj (covOver h) :=
  grpObjOfMono (jK h) (exists_mulCov h hG).choose (exists_mulCov h hG).choose_spec
    (oneCov h) (oneCov_jK h) (exists_invCov h).choose (exists_invCov h).choose_spec

end IdComp

/-- **LEAF (`(ker h)⁰_red` is an abelian subvariety, kernel form).** Over a field of
characteristic `0`, let `h : A → B` be a homomorphism of abelian varieties and
`ker h = A ×_B Spec k` its kernel (Mathlib's fibre product of `h` with the identity section of
`B`). If `ker h` is not locally quasi-finite over `k` (i.e. `ker h` is positive-dimensional),
there is an abelian variety `C` with a homomorphism `j : C → A` that is a closed immersion,
`0 < dim C`, and `h ∘ j = 0`: take `C = (ker h)⁰_red`. Sources (UNVERIFIED locators): Milne,
*Abelian varieties* (Cornell-Silverman 1986), §8; Milne's notes (2008) I §8; Mumford §8; reduced
group schemes over a perfect field are smooth, and in characteristic `0` every group scheme of
finite type is reduced (Cartier; Mumford §11 Thm 1); `dim (ker h)⁰ = dim ker h` (a group scheme of
finite type over a field is equidimensional). A consequence of these, never stronger. -/
def KernelIdentityComponent : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A B : _root_.PkgI3.AbVar k)
    (h : _root_.PkgI3.AbVar.Hom A B),
    ¬ LocallyQuasiFinite (pullback.fst h.hom.left (η[B.X]).left ≫ A.X.hom) →
    ∃ (C : _root_.PkgI3.AbVar k) (j : _root_.PkgI3.AbVar.Hom C A),
      IsClosedImmersion j.hom.left ∧ 0 < C.dim ∧ j.hom ≫ h.hom = 1

/-- A homomorphism of abelian varieties is proper. -/
theorem isProper_hom'' {k : Type} [Field k] {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X) :
    IsProper h.left := by
  have : IsProper (h.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp h.left B.X.hom

/-- **`KernelAbSubvariety` from `KernelIdentityComponent`** (glue: the shear isomorphism). -/
theorem kernelAbSubvariety_of_identityComponent (hK1 : KernelIdentityComponent) :
    KernelAbSubvariety := by
  intro k _ _ A B h hnot
  refine hK1 k A B h fun hq => hnot ?_
  haveI := isProper_hom'' h.hom
  exact lqf_of_ker h.hom hq

end AVGlue

#print axioms AVGlue.kernelAbSubvariety_of_identityComponent

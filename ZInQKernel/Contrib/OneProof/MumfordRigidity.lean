import ZInQKernel.Contrib.OneProof.H.TailZ16

/-!
# gt-rigidity: `MumfordRigidityCore` from two printed leaves

`LeafQM.AV.R1UnivRigid.MumfordRigidityCore` (field `mumfordRigidityCore` of the open research bundle,
`ZInQKernel/Contrib/OneProof/H/TailZ16.lean`) says: a proper smooth geometrically connected `F → S` over a locally
noetherian `S`, with a section `e` and every field fibre an abelian variety with origin `e(s)`, carries a group
object structure in `Over S` with identity `e`, and (a) every `S`-endomorphism of `F` fixing `e` is a
homomorphism. Its sources are Mumford's *GIT* Thm. 6.14 (existence) and Cor. 6.4 (clause (a)).

This file proves it from two printed statements, each stated over Mathlib's definitions:

* `MumfordGroupLaw`: the existence half of `MumfordRigidityCore` alone (*GIT* Thm. 6.14 on each connected
  component). It is implied by `MumfordRigidityCore` (`mumfordGroupLaw_of_core`), so strictly weaker.
* `RigidityLemma`: the rigidity lemma over a connected base (*GIT* Prop. 6.1), with stronger hypotheses than
  printed (smooth instead of flat with `H⁰(X_s, 𝒪) = k(s)`, `Y` separated and locally of finite type).

Clause (a), *GIT* Cor. 6.4 for endomorphisms, is **proved** from `RigidityLemma` by Mumford's argument
(`isMonHom_of_rigidity`). Take the defect `d(x, y) = f(xy) · (f(x) f(y))⁻¹ : F ×_S F → F`. Over the base `F`
(second projection, proper smooth geometrically connected, being a base change of `F → S`), the map
`(d, pr₂)` sends the fibre over `e(s)` to the single point `(e(s), e(s))` (`fibre_value`: that fibre is the
image of `x ↦ (x, 1)`, the base change of `e` along `pr₂`, `isPullback_jr`). Every connected component of `F`
contains such a point (fibres of `F → S` are connected) and is open (`F` is locally noetherian; a noetherian
space has open connected components, `isOpen_connectedComponent_of_isLocallyNoetherian`). The rigidity lemma
on each component (`eq_of_rigidity`, restriction to the open component and `Scheme.hom_ext_of_forall`) gives
`(d, pr₂) = pr₂ ≫ (x ↦ (1, x)) ≫ (d, pr₂)`, i.e. `d = 1` (`defect_eq_one`).

**Second route** (recommended: the new leaf is a textbook theorem). `PushforwardStructureSheaf` (`𝒪_S ≅ p_*𝒪_X`
for `p` proper, smooth and geometrically connected over a locally noetherian base; EGA III 7.8.6, cohomology and
base change) replaces `RigidityLemma`. With it, the local half of the rigidity lemma is proved
(`eq_of_pushforward`). The global half is not needed: the defect is constant on *every* fibre of `pr₂`
(`fibre_point_of_field`), by the kernel's field-level rigidity (`MulRigidity.isMonHom_of_geometricallyIntegral`)
applied to the base change of `F` to the residue field. That base change is geometrically integral, because the
field fibres of `F` are abelian varieties (`geometricallyIntegral_of_isAbVarFibre`).

Main results:
* `mumfordRigidityCore_of_pushforward : MumfordGroupLaw → PushforwardStructureSheaf → MumfordRigidityCore`;
* `mumfordRigidityCore_of_printed : MumfordGroupLaw → RigidityLemma → MumfordRigidityCore`.
Report: `docs/research/gt-rigidity.md`.
-/

set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.MumfordRigidity

open LeafQM.AV.R1UnivRigid PkgI3

/-! ## The two printed leaves -/

/-- **LEAF (Mumford's rigidity lemma over a connected base).** Let `S` be a connected locally noetherian scheme,
`p : X → S` proper, smooth, with geometrically connected fibres, `q : Y → S` separated and locally of finite type,
and `f : X → Y` an `S`-morphism. If for one point `s ∈ S` the image `f(X_s)` of the fibre is a single point,
then `f` factors through a section of `Y`: `f = p ≫ σ` with `σ ≫ q = 𝟙`.

Source (numbers UNVERIFIED, no network): Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, Ch. 6 §1,
Prop. 6.1 (rigidity lemma), whose hypotheses are `p` proper and flat with `H⁰(X_s, 𝒪_{X_s}) = k(s)` for all
`s`, `S` connected, `f(X_s)` a point for one `s`. *Form*: a consequence of the printed statement: smooth implies
flat with geometrically reduced fibres, and a proper geometrically reduced geometrically connected `k`-scheme
has `H⁰ = k` (Stacks 0BUG, UNVERIFIED tag); the assumptions on `Y` and on `S` (locally noetherian) are extra.
Over a field it is Mumford, *Abelian varieties*, §4 (Rigidity Lemma), which the kernel proves over
algebraically closed fields (`ZInQ.Contrib.CloudW06PoincareRigidity.rigidity_family`). -/
def RigidityLemma : Prop :=
  ∀ (S X Y : Scheme.{0}) (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y), f ≫ q = p →
    IsLocallyNoetherian S → ConnectedSpace S → IsProper p → Smooth p → GeometricallyConnected p →
    IsSeparated q → LocallyOfFiniteType q →
    (∃ (s : S) (y : Y), ∀ x : X, p x = s → f x = y) →
    ∃ σ : S ⟶ Y, σ ≫ q = 𝟙 S ∧ f = p ≫ σ

/-- **LEAF (Mumford's Thm. 6.14: the group law on a smooth proper family with a section).** With the hypotheses
of `MumfordRigidityCore` (`S` locally noetherian, `F → S` proper, smooth, geometrically connected, a section
`e`, every field fibre an abelian variety with origin `e(s)`), `F` carries a group object structure in `Over S`
with identity `e`. This is the existence half of `MumfordRigidityCore`, verbatim, without clause (a).

Source (numbers UNVERIFIED): Mumford–Fogarty–Kirwan, *GIT*, Ch. 6, Thm. 6.14 (`S` connected and locally
noetherian, `F → S` smooth proper with a section `e`, one fibre an abelian variety with origin `e(s)`: then `F`
is an abelian scheme with identity `e`; Grothendieck's proof via rigidity of deformations, §6.3). *Form*: a
consequence: Thm. 6.14 on each connected component of `S` (open, `S` being locally noetherian), the group laws
glued over the disjoint union; every fibre is assumed to be an abelian variety. -/
def MumfordGroupLaw : Prop :=
  ∀ (S : Scheme.{0}) (F : Over S) (e : S ⟶ F.left), IsLocallyNoetherian S → IsProper F.hom →
    Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 S →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    ∃ _G : GrpObj F, η[F].left = e

/-! ## Topology -/

/-- In a noetherian space connected components are open (finitely many irreducible components, each
contained in one connected component). -/
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

/-- In a locally noetherian scheme connected components are open. -/
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

/-- `f(1) = 1` as maps `F → F`. -/
theorem one_comp_eq_one {f : F ⟶ F} (hf : η[F] ≫ f = η[F]) : (1 : F ⟶ F) ≫ f = 1 := by
  rw [Hom.one_def, Category.assoc, hf]

/-- The defect `(x, y) ↦ f(xy) · (f(x) f(y))⁻¹`. -/
noncomputable def defect (f : F ⟶ F) : F ⊗ F ⟶ F :=
  (μ ≫ f) * ((fst F F ≫ f) * (snd F F ≫ f))⁻¹

/-- `x ↦ (1, x)`. -/
noncomputable def jl : F ⟶ F ⊗ F := lift 1 (𝟙 F)

/-- `x ↦ (x, 1)`. -/
noncomputable def jr : F ⟶ F ⊗ F := lift (𝟙 F) 1

/-- `d(1, x) = 1`. -/
theorem jl_defect {f : F ⟶ F} (hf : η[F] ≫ f = η[F]) : jl F ≫ defect F f = 1 := by
  have e1 : lift (1 : F ⟶ F) (𝟙 F) ≫ μ[F] = 𝟙 F := by
    change (1 : F ⟶ F) * 𝟙 F = 𝟙 F
    exact _root_.one_mul _
  simp only [jl, defect, comp_mul, GrpObj.comp_inv, ← Category.assoc, e1, lift_fst, lift_snd,
    Category.id_comp, one_comp_eq_one F hf, _root_.one_mul, mul_inv_cancel]

/-- `d(x, 1) = 1`. -/
theorem jr_defect {f : F ⟶ F} (hf : η[F] ≫ f = η[F]) : jr F ≫ defect F f = 1 := by
  have e1 : lift (𝟙 F) (1 : F ⟶ F) ≫ μ[F] = 𝟙 F := by
    change 𝟙 F * (1 : F ⟶ F) = 𝟙 F
    exact _root_.mul_one _
  simp only [jr, defect, comp_mul, GrpObj.comp_inv, ← Category.assoc, e1, lift_fst, lift_snd,
    Category.id_comp, one_comp_eq_one F hf, _root_.mul_one, mul_inv_cancel]

end Cor64

/-! ## The scheme part -/

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

/-- `e(F.hom t)` lies in the connected component of `t` (the fibre through `t` is connected). -/
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

/-- `MumfordGroupLaw` is the existence half of `MumfordRigidityCore` (so it is strictly weaker). -/
theorem mumfordGroupLaw_of_core (h : MumfordRigidityCore) : MumfordGroupLaw := by
  intro S F e hN hP hS hC he hfib
  obtain ⟨G, hη, -⟩ := h S F e hN hP hS hC he hfib
  exact ⟨G, hη⟩

/-- **`MumfordRigidityCore` from its two printed leaves**: the group law is `MumfordGroupLaw` (*GIT*
Thm. 6.14), clause (a) is `isMonHom_of_rigidity` (*GIT* Cor. 6.4, proved here from the rigidity lemma). -/
theorem mumfordRigidityCore_of_printed (hG : MumfordGroupLaw) (hR : RigidityLemma) :
    MumfordRigidityCore := by
  intro S F e hN hP hS hC he hfib
  obtain ⟨G, hη⟩ := hG S F e hN hP hS hC he hfib
  refine ⟨G, hη, fun f hf => ?_⟩
  exact isMonHom_of_rigidity F hR (Over.OverMorphism.ext (by rw [Over.comp_left, hη, hf]))


/-! ## Second route: `𝒪_S ≅ p_*𝒪_X` and field-level rigidity instead of the rigidity lemma -/

/-- **LEAF (`𝒪_S ≅ p_*𝒪_X` for a proper smooth morphism with geometrically connected fibres).** For `p : X → S`
proper, smooth and geometrically connected over a locally noetherian `S`, the map `p^# : Γ(S, U) → Γ(X, p⁻¹U)`
is bijective for every open `U`, i.e. `𝒪_S → p_*𝒪_X` is an isomorphism.

Sources (numbers UNVERIFIED, no network): EGA III₂ (7.8.6) (for `p` proper and flat over a locally noetherian
base with `H⁰(X_s, 𝒪) = k(s)` on every fibre, `𝒪_S → p_*𝒪_X` is an isomorphism, universally); Stacks Project,
Tag 0E0L (proper, flat, of finite presentation, geometrically connected and geometrically reduced fibres);
Mumford, *Abelian varieties*, §5 (cohomology and base change, Cor. 2 and 3). *Form*: a consequence: smooth gives
flat, of finite presentation (with proper), with geometrically reduced fibres; with proper and geometrically
connected, `H⁰(X_s, 𝒪) = k(s)` (Stacks 0BUG). The proof of *GIT* Prop. 6.1 uses exactly this statement. -/
def PushforwardStructureSheaf : Prop :=
  ∀ (S X : Scheme.{0}) (p : X ⟶ S), IsLocallyNoetherian S → IsProper p → Smooth p →
    GeometricallyConnected p → ∀ U : S.Opens, Function.Bijective (p.app U)

/-- `g^#` on `U` is the identity when `g = 𝟙`. -/
theorem appLE_id_eq {T : Scheme.{0}} (g : T ⟶ T) (hg : g = 𝟙 T) (U : T.Opens)
    (e : U ≤ g ⁻¹ᵁ U) : g.appLE U U e = 𝟙 _ := by
  subst hg
  exact (Scheme.Hom.appLE_eq_app (𝟙 T)).trans (Scheme.Hom.id_app U)

/-- **Local rigidity** from `𝒪_S ≅ p_*𝒪_X` (the first half of Mumford's proof of *GIT* Prop. 6.1, with a
section `j` of `p` and `f'` over `X`): if `f'` sends every fibre of `p` to a point, then `f' = p ≫ j ≫ f'`.
Near `x`, take an affine `V ∋ f'(X_{p x})`, an affine `U ∋ p x` with `p⁻¹U ⊆ f'⁻¹V` (`p` is closed); both maps
`p⁻¹U → V` induce the same ring map `Γ(V) → Γ(p⁻¹U)`, since `p^#` is bijective and `j^# ∘ p^# = 1`. -/
theorem eq_of_pushforward (hP : PushforwardStructureSheaf) {T X : Scheme.{0}}
    [IsLocallyNoetherian T] (p : X ⟶ T) [IsProper p] [Smooth p] [GeometricallyConnected p]
    (f' : X ⟶ X) (j : T ⟶ X) (hjp : j ≫ p = 𝟙 T)
    (hfib : ∀ t : T, ∃ y : X, ∀ x : X, p x = t → f' x = y) :
    f' = p ≫ j ≫ f' := by
  refine Scheme.hom_ext_of_forall f' (p ≫ j ≫ f') fun x => ?_
  obtain ⟨y, hy⟩ := hfib (p x)
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  have hZ : IsClosed (p '' ((f' ⁻¹ᵁ V : X.Opens) : Set X)ᶜ) :=
    p.isClosedMap _ (f' ⁻¹ᵁ V).isOpen.isClosed_compl
  have htZ : p x ∉ p '' ((f' ⁻¹ᵁ V : X.Opens) : Set X)ᶜ := by
    rintro ⟨x', hx', hpx'⟩
    exact hx' (show f' x' ∈ V by rw [hy x' hpx']; exact hyV)
  obtain ⟨U, hU, htU, hUZ⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨_, hZ.isOpen_compl⟩) (x := p x) htZ
  refine ⟨p ⁻¹ᵁ U, htU, ?_⟩
  have hW : p ⁻¹ᵁ U ≤ f' ⁻¹ᵁ V := fun x' hx' => by
    by_contra h
    exact hUZ hx' ⟨x', h, rfl⟩
  have hjU : U ≤ j ⁻¹ᵁ (p ⁻¹ᵁ U) := fun t ht => by
    change p (j t) ∈ U
    rw [← Scheme.Hom.comp_apply, hjp]
    exact ht
  have hWc : p ⁻¹ᵁ U ≤ (p ≫ j ≫ f') ⁻¹ᵁ V := fun x' hx' => hW (hjU hx')
  have : IsAffine V := hV
  rw [← Scheme.Hom.resLE_comp_ι f' hW, ← Scheme.Hom.resLE_comp_ι (p ≫ j ≫ f') hWc]
  congr 1
  apply ext_of_isAffine
  rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.resLE_app_top]
  congr 2
  have hbij := hP T X p inferInstance inferInstance inferInstance inferInstance U
  rw [Scheme.Hom.app_eq_appLE] at hbij
  have hiso : IsIso (p.appLE U (p ⁻¹ᵁ U) le_rfl) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hbij
  have h1 : p.appLE U (p ⁻¹ᵁ U) le_rfl ≫ j.appLE (p ⁻¹ᵁ U) U hjU = 𝟙 _ := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_id_eq _ hjp _ _
  have h2 : j.appLE (p ⁻¹ᵁ U) U hjU ≫ p.appLE U (p ⁻¹ᵁ U) le_rfl = 𝟙 _ := by
    rw [IsIso.eq_inv_of_hom_inv_id h1, IsIso.inv_hom_id]
  have e1 := Scheme.Hom.appLE_comp_appLE j f' V (p ⁻¹ᵁ U) U hW hjU
  have e2 := Scheme.Hom.appLE_comp_appLE p (j ≫ f') V U (p ⁻¹ᵁ U)
    (fun t ht => hW (hjU ht)) le_rfl
  rw [← e1] at e2
  rw [← e2, Category.assoc, h2, Category.comp_id]

section FieldFibre

open scoped CategoryTheory.Obj

variable {S : Scheme.{0}} (F : Over S) [GrpObj F]

/-- **The defect is constant on every fibre of `snd`** (field-level rigidity, the kernel's
`MulRigidity.isMonHom_of_geometricallyIntegral`, on the base change of `F` to the residue field). -/
theorem fibre_point_of_field [IsProper F.hom]
    (hGI : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      GeometricallyIntegral (pullback.snd F.hom s))
    {f : F ⟶ F} (hf : η[F] ≫ f = η[F]) (y : F.left) :
    ∃ y₀ : (F ⊗ F).left, ∀ x : (F ⊗ F).left, (snd F F).left x = y →
      (lift (defect F f) (snd F F)).left x = y₀ := by
  let K : Type := F.left.residueField y
  let yb : Spec (CommRingCat.of K) ⟶ F.left := F.left.fromSpecResidueField y
  let sb : Spec (CommRingCat.of K) ⟶ S := yb ≫ F.hom
  let P := Over.pullback sb
  let FK : Over (Spec (CommRingCat.of K)) := P.obj F
  let fK : FK ⟶ FK := P.map f
  have : IsProper FK.hom := by dsimp [FK, P]; infer_instance
  have : GeometricallyIntegral FK.hom := hGI K sb
  have hηK : η[FK] ≫ fK = η[FK] := by
    change (Functor.LaxMonoidal.ε P ≫ P.map η[F]) ≫ P.map f = Functor.LaxMonoidal.ε P ≫ P.map η[F]
    rw [Category.assoc, ← Functor.map_comp, hf]
  have hmon : IsMonHom fK := MulRigidity.isMonHom_of_geometricallyIntegral FK FK fK hηK
  have hdK : defect FK fK = 1 := by
    rw [defect, hmon.mul_hom, ← lift_fst_comp_snd_comp, ← Hom.mul_def, mul_inv_cancel]
  have hμd : Functor.LaxMonoidal.μ P F F ≫ P.map (defect F f) = defect FK fK := by
    rw [defect, defect, Functor.map_mul, Functor.map_inv', Functor.map_mul, comp_mul,
      GrpObj.comp_inv, comp_mul, Functor.map_comp, Functor.map_comp, Functor.map_comp,
      ← Category.assoc, ← Category.assoc (Functor.LaxMonoidal.μ P F F),
      ← Category.assoc (Functor.LaxMonoidal.μ P F F), Functor.Monoidal.μ_fst,
      Functor.Monoidal.μ_snd]
    rfl
  let yt : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ FK :=
    Over.homMk (pullback.lift yb (𝟙 _) (by simp [sb])) (by simp [FK, P])
  let jK : FK ⟶ FK ⊗ FK := lift (𝟙 FK) (toUnit FK ≫ yt)
  have hjK : jK ≫ defect FK fK = 1 := by
    rw [hdK, Hom.one_def, Hom.one_def, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  let ψ : FK.left ⟶ (F ⊗ F).left :=
    (jK ≫ Functor.LaxMonoidal.μ P F F).left ≫ pullback.fst _ _
  have hmap : ∀ {A B : Over S} (g : A ⟶ B),
      (P.map g).left ≫ pullback.fst B.hom sb = pullback.fst A.hom sb ≫ g.left := fun g =>
    pullback.lift_fst _ _ _
  have hψd : ψ ≫ (defect F f).left = FK.hom ≫ η[FK].left ≫ pullback.fst F.hom sb := by
    calc ψ ≫ (defect F f).left
        = (jK ≫ Functor.LaxMonoidal.μ P F F ≫ P.map (defect F f)).left ≫
            pullback.fst F.hom sb := by
          simp only [ψ, Over.comp_left, Category.assoc]
          rw [hmap]
      _ = (jK ≫ defect FK fK).left ≫ pullback.fst F.hom sb := by rw [hμd]
      _ = _ := by rw [hjK]; rfl
  have hψs : ψ ≫ (snd F F).left = FK.hom ≫ yb := by
    simp only [ψ, Over.comp_left, Category.assoc]
    rw [Over.snd_left, Over.μ_pullback_left_fst_snd, ← Category.assoc, ← Over.snd_left,
      ← Over.comp_left, lift_snd, Over.comp_left, Over.toUnit_left, Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _
  have hψf : ψ ≫ pullback.fst F.hom F.hom = pullback.fst F.hom sb := by
    simp only [ψ, Over.comp_left, Category.assoc]
    rw [Over.μ_pullback_left_fst_fst, ← Category.assoc, ← Over.fst_left,
      ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp]
  have hpb : IsPullback ψ FK.hom (snd F F).left yb := by
    refine IsPullback.of_right ?_ hψs (IsPullback.of_hasPullback F.hom F.hom)
    rw [hψf]
    exact IsPullback.of_hasPullback F.hom sb
  clear_value ψ
  have hcond : (η[FK].left ≫ pullback.fst F.hom sb) ≫ F.hom = yb ≫ F.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have : η[FK].left ≫ FK.hom = 𝟙 _ := Over.w η[FK]
    erw [this, Category.id_comp]
  refine ⟨(pullback.lift (η[FK].left ≫ pullback.fst F.hom sb) yb hcond) (default : Spec (CommRingCat.of K)), fun x hx => ?_⟩
  have hx' : (snd F F).left x = yb (default : Spec (CommRingCat.of K)) := by
    rw [hx]
    exact (Scheme.fromSpecResidueField_apply _ _).symm
  obtain ⟨w, hw1, hw2⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := (snd F F).left) (g := yb) x default hx'
  have hz : ψ (hpb.isoPullback.inv w) = x := by
    rw [← hw1, ← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst]
  have key : ψ ≫ (lift (defect F f) (snd F F)).left =
      FK.hom ≫ pullback.lift (η[FK].left ≫ pullback.fst F.hom sb) yb hcond := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst]
      change ψ ≫ ((lift (defect F f) (snd F F)) ≫ fst F F).left = _
      rw [lift_fst, hψd]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd]
      change ψ ≫ ((lift (defect F f) (snd F F)) ≫ snd F F).left = _
      rw [lift_snd, hψs]
  rw [← hz, ← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply]
  congr 1
  exact Subsingleton.elim _ _

/-- **The defect vanishes**, from `𝒪_S ≅ p_*𝒪_X` and field-level rigidity. -/
theorem defect_eq_one_of_pushforward (hP : PushforwardStructureSheaf) [IsLocallyNoetherian S]
    [IsProper F.hom] [Smooth F.hom] [GeometricallyConnected F.hom]
    (hGI : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      GeometricallyIntegral (pullback.snd F.hom s))
    {f : F ⟶ F} (hf : η[F] ≫ f = η[F]) : defect F f = 1 := by
  have : IsLocallyNoetherian F.left := LocallyOfFiniteType.isLocallyNoetherian F.hom
  have : IsProper (snd F F).left := by
    change IsProper (pullback.snd F.hom F.hom); infer_instance
  have : Smooth (snd F F).left := by
    change Smooth (pullback.snd F.hom F.hom); infer_instance
  have : GeometricallyConnected (snd F F).left := by
    change GeometricallyConnected (pullback.snd F.hom F.hom); infer_instance
  have hjp : (jl F).left ≫ (snd F F).left = 𝟙 _ := by
    rw [← Over.comp_left, jl, lift_snd]; rfl
  have key := eq_of_pushforward hP (snd F F).left (lift (defect F f) (snd F F)).left (jl F).left hjp
    fun t => fibre_point_of_field F hGI hf t
  have key2 : lift (defect F f) (snd F F) = snd F F ≫ jl F ≫ lift (defect F f) (snd F F) :=
    Over.OverMorphism.ext key
  have := congrArg (· ≫ fst F F) key2
  simp only [Category.assoc, lift_fst] at this
  rw [this, jl_defect F hf, Hom.one_def, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

/-- **Mumford, *GIT* Cor. 6.4 for endomorphisms**, from `𝒪_S ≅ p_*𝒪_X`, when every field fibre is
geometrically integral. -/
theorem isMonHom_of_pushforward (hP : PushforwardStructureSheaf) [IsLocallyNoetherian S]
    [IsProper F.hom] [Smooth F.hom] [GeometricallyConnected F.hom]
    (hGI : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
      GeometricallyIntegral (pullback.snd F.hom s))
    {f : F ⟶ F} (hf : η[F] ≫ f = η[F]) : IsMonHom f where
  one_hom := hf
  mul_hom := by
    have h := defect_eq_one_of_pushforward F hP hGI hf
    rw [defect, mul_inv_eq_one] at h
    rw [h, Hom.mul_def, lift_fst_comp_snd_comp]

end FieldFibre

/-- A field fibre that is an abelian variety makes `pullback.snd F.hom s` geometrically integral. -/
theorem geometricallyIntegral_of_isAbVarFibre {S : Scheme.{0}} (F : Over S) (e : S ⟶ F.left)
    {K : Type} [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K) (g : A.X.left ⟶ F.left)
    (h : IsAbVarFibre F e s A g) : GeometricallyIntegral (pullback.snd F.hom s) := by
  have hR : MorphismProperty.RespectsIso (C := Scheme) @GeometricallyIntegral := by
    rw [GeometricallyIntegral.eq_geometrically]; infer_instance
  rw [← h.1.isoPullback_inv_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral _ A.X.hom).2
    inferInstance

/-- **`MumfordRigidityCore` from `MumfordGroupLaw` and `𝒪_S ≅ p_*𝒪_X`.** -/
theorem mumfordRigidityCore_of_pushforward (hG : MumfordGroupLaw)
    (hP : PushforwardStructureSheaf) : MumfordRigidityCore := by
  intro S F e hN hPr hS hC he hfib
  obtain ⟨G, hη⟩ := hG S F e hN hPr hS hC he hfib
  refine ⟨G, hη, fun f hf => ?_⟩
  refine isMonHom_of_pushforward F hP (fun K _ s => ?_)
    (Over.OverMorphism.ext (by rw [Over.comp_left, hη, hf]))
  obtain ⟨A, g, hg⟩ := hfib K s
  exact geometricallyIntegral_of_isAbVarFibre F e s A g hg

end ZInQ.Contrib.MumfordRigidity

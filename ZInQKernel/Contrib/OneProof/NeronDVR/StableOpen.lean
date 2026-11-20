import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import ZInQKernel.Contrib.OneProof.NeronDVR.DescentDatum
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.InvariantOpen

/-!
# Stable opens defined on the generic fibre

Taking the complement of the closure of the generic complement commutes with
open base change. This gives the stable open used in Bosch–Lütkebohmert–Raynaud,
*Néron Models*, §6.5, proof of Theorem 1, case (b), printed p. 160.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace NeronDVR

noncomputable section

universe u

variable {X Y X₀ Y₀ : Scheme.{u}}

/-- The largest open of `X` whose inverse image under an open immersion `i` is `V`. -/
def openCompletion (i : X₀ ⟶ X) (V : X₀.Opens) : X.Opens :=
  ⟨(closure (i '' (V : Set X₀)ᶜ))ᶜ, isClosed_closure.isOpen_compl⟩

@[simp]
theorem preimage_openCompletion (i : X₀ ⟶ X) [IsOpenImmersion i] (V : X₀.Opens) :
    i ⁻¹ᵁ openCompletion i V = V := by
  apply Opens.ext
  change i ⁻¹' (closure (i '' (V : Set X₀)ᶜ))ᶜ = (V : Set X₀)
  rw [Set.preimage_compl,
    i.isOpenEmbedding.isOpenMap.preimage_closure_image i.isOpenEmbedding.injective
      i.continuous _ V.isOpen.isClosed_compl, compl_compl]

theorem le_openCompletion_iff (i : X₀ ⟶ X) (V : X₀.Opens) (U : X.Opens) :
    U ≤ openCompletion i V ↔ i ⁻¹ᵁ U ≤ V := by
  change (U : Set X) ⊆ (closure (i '' (V : Set X₀)ᶜ))ᶜ ↔
    i ⁻¹' (U : Set X) ⊆ (V : Set X₀)
  constructor
  · intro h x hx
    by_contra hV
    exact h hx (subset_closure ⟨x, hV, rfl⟩)
  · intro h
    rw [Set.subset_compl_comm]
    apply closure_minimal _ U.isOpen.isClosed_compl
    rintro _ ⟨x, hx, rfl⟩
    exact fun hxU => hx (h hxU)

/-- A pullback of an open immersion commutes with taking the image of a subset of
its source, for the underlying spaces. -/
private theorem image_preimage_of_isPullback
    {i : X₀ ⟶ X} [IsOpenImmersion i]
    {f : Y ⟶ X} {i' : Y₀ ⟶ Y} {f₀ : Y₀ ⟶ X₀}
    (h : IsPullback f₀ i' i f) (A : Set X₀) :
    i' '' (f₀ ⁻¹' A) = f ⁻¹' (i '' A) := by
  ext y
  constructor
  · rintro ⟨y₀, hy₀, rfl⟩
    exact ⟨f₀ y₀, hy₀, by simp only [← Scheme.Hom.comp_apply, h.w]⟩
  · rintro ⟨x₀, hx₀, hx⟩
    obtain ⟨z, hz⟩ := (IsOpenImmersion.range_pullbackSnd i f).ge ⟨x₀, hx⟩
    let y₀ := h.isoPullback.inv z
    have hy : i' y₀ = y := by
      change (h.isoPullback.inv ≫ i') z = y
      rw [h.isoPullback_inv_snd]
      exact hz
    have hxy : f₀ y₀ = x₀ := by
      apply i.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply, hy, hx]
    exact ⟨y₀, by simpa only [Set.mem_preimage, hxy] using hx₀, hy⟩

/-- The range of a pullback of an open immersion is the inverse image of its range. -/
theorem range_of_isPullback_open
    {i : X₀ ⟶ X} [IsOpenImmersion i]
    {f : Y ⟶ X} {i' : Y₀ ⟶ Y} {f₀ : Y₀ ⟶ X₀}
    (h : IsPullback f₀ i' i f) : Set.range i' = f ⁻¹' Set.range i := by
  simpa only [Set.preimage_univ, Set.image_univ] using image_preimage_of_isPullback h Set.univ

/-- Pullback by an open morphism commutes with taking the largest open extending
a given open of an open subscheme. -/
theorem preimage_openCompletion_of_isPullback
    {i : X₀ ⟶ X} [IsOpenImmersion i]
    {f : Y ⟶ X} {i' : Y₀ ⟶ Y} {f₀ : Y₀ ⟶ X₀}
    (h : IsPullback f₀ i' i f) (hf : IsOpenMap f) (V : X₀.Opens) :
    f ⁻¹ᵁ openCompletion i V = openCompletion i' (f₀ ⁻¹ᵁ V) := by
  apply Opens.ext
  change f ⁻¹' (closure (i '' (V : Set X₀)ᶜ))ᶜ =
    (closure (i' '' (f₀ ⁻¹' (V : Set X₀))ᶜ))ᶜ
  rw [Set.preimage_compl, hf.preimage_closure_eq_closure_preimage f.continuous,
    ← image_preimage_of_isPullback h, Set.preimage_compl]

/-- If the complement of an open is the closure of its part in the open
subscheme, completion of a smaller open is still contained in that open. -/
theorem openCompletion_le_of_closure_compl (i : X₀ ⟶ X)
    {V : X₀.Opens} {U : X.Opens}
    (h : V ≤ i ⁻¹ᵁ U)
    (hU : (U : Set X)ᶜ = closure (i '' ((i ⁻¹ᵁ U : X₀.Opens) : Set X₀)ᶜ)) :
    openCompletion i V ≤ U := by
  have hc := closure_mono (Set.image_mono (Set.compl_subset_compl.mpr h) (f := i))
  rw [← hU] at hc
  exact Set.compl_subset_comm.mp hc

end

end NeronDVR

namespace CategoryTheory.Over.DescentDatum

noncomputable section

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S} {N : Over S'} (d : DescentDatum p N)

private abbrev overlap := Limits.pullback (N.hom ≫ p) p
private abbrev first : overlap (p := p) (N := N) ⟶ N.left := pullback.fst (N.hom ≫ p) p
private abbrev a : overlap (p := p) (N := N) ⟶ S' := first ≫ N.hom
private abbrev b : overlap (p := p) (N := N) ⟶ S' := pullback.snd (N.hom ≫ p) p

private theorem ab : a (p := p) (N := N) ≫ p = b ≫ p := by
  rw [Category.assoc, pullback.condition]

private def reverseOverlap : overlap (p := p) (N := N) ⟶ overlap (p := p) (N := N) :=
  pullback.lift d.toHom a (by rw [← Category.assoc, toHom_comp_hom, ab])

@[reassoc (attr := simp)]
private theorem reverseOverlap_fst : reverseOverlap d ≫ first = d.toHom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem reverseOverlap_snd : reverseOverlap d ≫ b = a :=
  pullback.lift_snd _ _ _

private theorem reverseOverlap_toHom : reverseOverlap d ≫ d.toHom = first := by
  let x : Over.mk (a (p := p) (N := N)) ⟶ N := universalPoint
  let y := d.transport a b ab x
  have h := d.transport_transport a b a ab ab.symm x
  rw [d.transport_self] at h
  exact (d.transport_left_eq_lift_toHom b a ab.symm y).symm.trans
    (congrArg CommaMorphism.left h)

private theorem reverseOverlap_involution : reverseOverlap d ≫ reverseOverlap d = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, reverseOverlap_fst, reverseOverlap_toHom, Category.id_comp]
  · rw [Category.assoc, reverseOverlap_snd, ← Category.assoc, reverseOverlap_fst, toHom_comp_hom]
    exact (Category.id_comp _).symm

private def reverseOverlapIso : overlap (p := p) (N := N) ≅ overlap (p := p) (N := N) :=
  ⟨reverseOverlap d, reverseOverlap d, reverseOverlap_involution d, reverseOverlap_involution d⟩

/-- The transport projection is open when the covering map is universally open. -/
theorem isOpenMap_toHom [UniversallyOpen p] : IsOpenMap d.toHom := by
  rw [← reverseOverlap_fst d]
  exact (pullback.fst (N.hom ≫ p) p).isOpenMap.comp
    (reverseOverlapIso d).hom.homeomorph.isOpenMap

/-- The transport projection is smooth when the covering map is smooth. -/
theorem smooth_toHom [Smooth p] : Smooth d.toHom := by
  rw [← reverseOverlap_fst d]
  change Smooth ((reverseOverlapIso d).hom ≫ first)
  infer_instance

/-- Both overlap projections pull an invariant open back to the same open. -/
theorem preimage_toHom_eq {U : N.left.Opens} (hU : d.IsInvariant U) :
    d.toHom ⁻¹ᵁ U = first ⁻¹ᵁ U := by
  have h := (d.isInvariant_iff U).mp hU
  ext x
  change d.toHom x ∈ U ↔ first x ∈ U
  refine ⟨fun hx => ?_, h x⟩
  have h₁ : first (reverseOverlap d x) = d.toHom x := by
    rw [← Scheme.Hom.comp_apply, reverseOverlap_fst]
  have h₂ : d.toHom (reverseOverlap d x) = first x := by
    rw [← Scheme.Hom.comp_apply, reverseOverlap_toHom]
  rw [← h₂]
  exact h _ (h₁.symm ▸ hx)

end

end CategoryTheory.Over.DescentDatum

namespace NeronDVR

noncomputable section

universe u

variable {S T X Y : Scheme.{u}} (j : T ⟶ S)

/-- The morphism on restrictions along `j` induced by a morphism over `S`. -/
def restrictOver {q : X ⟶ S} {q' : Y ⟶ S} (f : Y ⟶ X) (hf : f ≫ q = q') :
    pullback q' j ⟶ pullback q j :=
  pullback.lift (pullback.fst q' j ≫ f) (pullback.snd q' j) (by
    rw [Category.assoc, hf, pullback.condition])

theorem isPullback_restrictOver {q : X ⟶ S} {q' : Y ⟶ S} (f : Y ⟶ X) (hf : f ≫ q = q') :
    IsPullback (restrictOver j f hf) (pullback.fst q' j) (pullback.fst q j) f := by
  have h : IsPullback (pullback.snd q' j) (pullback.fst q' j) j (f ≫ q) :=
    hf.symm ▸ (IsPullback.of_hasPullback q' j).flip
  let hq := (IsPullback.of_hasPullback q j).flip
  convert h.of_right' hq using 1
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans (hq.lift_snd _ _ _).symm
  · exact (pullback.lift_snd _ _ _).trans (hq.lift_fst _ _ _).symm

end

end NeronDVR

namespace CategoryTheory.Over.DescentDatum

noncomputable section

universe u

variable {S S' T A : Scheme.{u}} {p : S' ⟶ S} {N : Over S'} (d : DescentDatum p N)
  (j : T ⟶ S)

open NeronDVR

/-- The generic map takes equal values at the two endpoints of the overlap. -/
def CompatibleOnOpen (r : Limits.pullback (N.hom ≫ p) j ⟶ A) : Prop :=
  restrictOver j d.toHom (by rw [← Category.assoc, toHom_comp_hom]) ≫ r =
    restrictOver j (pullback.fst (N.hom ≫ p) p) pullback.condition ≫ r

/-- Complete the preimage of an open of an already descended restriction. The
resulting open in the whole scheme is stable under the descent datum. -/
theorem isInvariant_openCompletion [IsOpenImmersion j] [UniversallyOpen p]
    (r : Limits.pullback (N.hom ≫ p) j ⟶ A) (hr : d.CompatibleOnOpen j r)
    (V : A.Opens) :
    d.IsInvariant (openCompletion (pullback.fst (N.hom ≫ p) j) (r ⁻¹ᵁ V)) := by
  let U := openCompletion (pullback.fst (N.hom ≫ p) j) (r ⁻¹ᵁ V)
  have hd : d.toHom ≫ (N.hom ≫ p) = pullback.snd (N.hom ≫ p) p ≫ p := by
    rw [← Category.assoc, toHom_comp_hom]
  have hpre : d.toHom ⁻¹ᵁ U = pullback.fst (N.hom ≫ p) p ⁻¹ᵁ U := by
    dsimp only [U]
    rw [preimage_openCompletion_of_isPullback (isPullback_restrictOver j d.toHom hd)
        d.isOpenMap_toHom,
      preimage_openCompletion_of_isPullback
        (isPullback_restrictOver j (pullback.fst _ _) pullback.condition)
        (pullback.fst (N.hom ≫ p) p).isOpenMap,
      ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hr]
  refine (d.isInvariant_iff U).mpr fun x hx => ?_
  change x ∈ d.toHom ⁻¹ᵁ U
  rw [hpre]
  exact hx

end

end CategoryTheory.Over.DescentDatum

namespace NeronDVR

noncomputable section

variable {S S' T T' : Scheme.{0}}
  (j : T ⟶ S) (p : S' ⟶ S) (N : Over S') (j' : T' ⟶ S') (t : T' ⟶ T)
  (hpb : IsPullback j' t p j)
  {A : Over T} (e : (Over.pullback j').obj N ≅ (Over.pullback t).obj A)
  [Smooth N.hom] [Smooth p]
  (hex : ∀ (Y : Over S') [Smooth Y.hom],
    Function.Bijective (fun f : Y ⟶ N => (Over.pullback j').map f))

/-- The descent datum induced by the Néron property is compatible with the map
to the prescribed generic fibre. -/
theorem neronDescentDatum_compatibleOnOpen :
    (neronDescentDatum j p N j' t hpb e hex).CompatibleOnOpen j
      (restrictionToGeneric j p N j' t hpb e).left := by
  let d := neronDescentDatum j p N j' t hpb e hex
  let i := pullback.fst (pullback.snd (N.hom ≫ p) p ≫ p) j
  let u := pullback.snd (pullback.snd (N.hom ≫ p) p ≫ p) j
  let a := pullback.fst (N.hom ≫ p) p ≫ N.hom
  let b := pullback.snd (N.hom ≫ p) p
  have hab : a ≫ p = b ≫ p := by simp only [a, b, Category.assoc, pullback.condition]
  let x₀ : Over.mk a ⟶ N := Over.DescentDatum.universalPoint
  let x : Over.mk (i ≫ a) ⟶ N := (Over.homMk i : Over.mk (i ≫ a) ⟶ Over.mk a) ≫ x₀
  have h : (i ≫ a) ≫ p = (i ≫ b) ≫ p := by simp only [Category.assoc, hab]
  have hu : (i ≫ b) ≫ p = u ≫ j := (Category.assoc _ _ _).trans pullback.condition
  have hx : x.left = i ≫ pullback.fst (N.hom ≫ p) p := rfl
  have hy : (d.transport (i ≫ a) (i ≫ b) h x).left = i ≫ d.toHom :=
    congrArg CommaMorphism.left (d.transport_homMk_comp i a b hab x₀)
  have htransport := neronDescentDatum_transportAtGenericPoint j p N j' t hpb e hex
    (i ≫ a) (i ≫ b) h x u hu
  change restrictOver j d.toHom _ ≫ _ = restrictOver j (pullback.fst (N.hom ≫ p) p) _ ≫ _
  simpa only [d, restrictOver, hx, hy] using htransport

end

end NeronDVR

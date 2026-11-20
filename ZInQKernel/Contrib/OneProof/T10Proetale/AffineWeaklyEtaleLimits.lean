import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Weakly étale covering maps from affine inverse limits

Flatness in the affine limit is the equational criterion: the coefficients, the
unknowns, and their relation are all realized at a single stage. Apply this to
the map and to its diagonal. Surjectivity follows by taking a limit on each fibre.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

private theorem lift_finite_family {J : Type} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ CommRingCat.{0}} {c : Cocone D} (hc : IsColimit c)
    {k : ℕ} (x : Fin k → c.pt) :
    ∃ (j : J) (y : Fin k → D.obj j), ∀ i, c.ι.app j (y i) = x i := by
  classical
  let h := isColimitOfPreserves (forget CommRingCat) hc
  have hx (i : Fin k) : ∃ (j : J) (y : D.obj j), c.ι.app j y = x i :=
    Types.jointly_surjective_of_isColimit h (x i)
  choose j y hy using hx
  let T := Finset.univ.image j
  obtain ⟨s, hs⟩ := IsFiltered.sup_objs_exists T
  let e (i : Fin k) : j i ⟶ s := (hs (Finset.mem_image_of_mem j (Finset.mem_univ i))).some
  exact ⟨s, fun i => D.map (e i) (y i), fun i =>
    (ConcreteCategory.congr_hom (c.w (e i)) (y i)).trans (hy i)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Flat ring maps remain flat under filtered colimits, even with varying base rings. -/
theorem flat_of_filteredCocones {J : Type} [SmallCategory J] [IsFiltered J]
    {D E : J ⥤ CommRingCat.{0}} (p : D ⟶ E) {c : Cocone D} {d : Cocone E}
    (hc : IsColimit c) (hd : IsColimit d) (f : c.pt ⟶ d.pt)
    (hf : ∀ i, c.ι.app i ≫ f = p.app i ≫ d.ι.app i)
    (hp : ∀ i, (p.app i).hom.Flat) : f.hom.Flat := by
  classical
  let : Algebra c.pt d.pt := f.hom.toAlgebra
  change Module.Flat c.pt d.pt
  apply Module.Flat.of_forall_isTrivialRelation
  intro k a x hax
  change (∑ r, f (a r) * x r) = 0 at hax
  obtain ⟨i, a', ha'⟩ := lift_finite_family hc a
  obtain ⟨j, x', hx'⟩ := lift_finite_family hd x
  let m := IsFiltered.max i j
  let a₀ (r : Fin k) := D.map (IsFiltered.leftToMax i j) (a' r)
  let x₀ (r : Fin k) := E.map (IsFiltered.rightToMax i j) (x' r)
  have ha₀ (r : Fin k) : c.ι.app m (a₀ r) = a r :=
    (ConcreteCategory.congr_hom (c.w (IsFiltered.leftToMax i j)) (a' r)).trans (ha' r)
  have hx₀ (r : Fin k) : d.ι.app m (x₀ r) = x r :=
    (ConcreteCategory.congr_hom (d.w (IsFiltered.rightToMax i j)) (x' r)).trans (hx' r)
  have he₀ : d.ι.app m (∑ r, p.app m (a₀ r) * x₀ r) = d.ι.app m 0 := by
    simp only [map_sum, map_mul, map_zero, hx₀]
    have hw (r : Fin k) : d.ι.app m (p.app m (a₀ r)) = f (a r) :=
      (ConcreteCategory.congr_hom (hf m) (a₀ r)).symm.trans (congrArg f (ha₀ r))
    simpa only [hw] using hax
  obtain ⟨n, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (forget CommRingCat) hd) _ _).mp he₀
  change E.map g (∑ r, p.app m (a₀ r) * x₀ r) = E.map g 0 at hg
  let a₁ (r : Fin k) := D.map g (a₀ r)
  let x₁ (r : Fin k) := E.map g (x₀ r)
  let : Algebra (D.obj n) (E.obj n) := (p.app n).hom.toAlgebra
  let : Module.Flat (D.obj n) (E.obj n) := hp n
  have he₁ : ∑ r, a₁ r • x₁ r = 0 := by
    change (∑ r, p.app n (D.map g (a₀ r)) * E.map g (x₀ r)) = 0
    have hw (r : Fin k) : p.app n (D.map g (a₀ r)) = E.map g (p.app m (a₀ r)) :=
      ConcreteCategory.congr_hom (p.naturality g) (a₀ r)
    simpa only [hw, map_sum, map_mul, map_zero] using hg
  obtain ⟨l, b, y, h₁, h₂⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero he₁
  have ha₁ (r : Fin k) : c.ι.app n (a₁ r) = a r :=
    (ConcreteCategory.congr_hom (c.w g) (a₀ r)).trans (ha₀ r)
  have hx₁ (r : Fin k) : d.ι.app n (x₁ r) = x r :=
    (ConcreteCategory.congr_hom (d.w g) (x₀ r)).trans (hx₀ r)
  refine ⟨l, fun r s => c.ι.app n (b r s), fun s => d.ι.app n (y s), ?_, ?_⟩
  · intro r
    have hw (s : Fin l) : d.ι.app n (p.app n (b r s)) = f (c.ι.app n (b r s)) :=
      (ConcreteCategory.congr_hom (hf n) (b r s)).symm
    let dι : E.obj n ⟶ d.pt := d.ι.app n
    change x r = ∑ s, f (c.ι.app n (b r s)) * dι (y s)
    have h' : x₁ r = ∑ s, p.app n (b r s) * y s := h₁ r
    have hwl (s : Fin l) : dι (p.app n (b r s)) = f (c.ι.app n (b r s)) := hw s
    have hxr : dι (x₁ r) = x r := hx₁ r
    simpa only [map_sum, map_mul, hwl, hxr] using congrArg dι h'
  · intro s
    simpa only [map_sum, map_mul, map_zero, ha₁] using congrArg (c.ι.app n) (h₂ s)

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- A map between limits of cofiltered affine diagrams is flat if its stage maps are flat. -/
theorem flat_of_affineLimits {I : Type} [SmallCategory I] [IsCofiltered I]
    {D E : I ⥤ Scheme.{0}} [∀ i, IsAffine (D.obj i)] [∀ i, IsAffine (E.obj i)]
    (p : D ⟶ E) {c : Cone D} {d : Cone E} (hc : IsLimit c) (hd : IsLimit d)
    (f : c.pt ⟶ d.pt) (hf : ∀ i, f ≫ d.π.app i = c.π.app i ≫ p.app i)
    (hp : ∀ i, Flat (p.app i)) : Flat f := by
  let : IsAffine c.pt := Scheme.isAffine_of_isLimit _ hc
  let : IsAffine d.pt := Scheme.isAffine_of_isLimit _ hd
  let {i j : I} (e : i ⟶ j) : IsAffineHom (D.map e) := inferInstance
  let {i j : I} (e : i ⟶ j) : IsAffineHom (E.map e) := inferInstance
  let α : E.op ⋙ Scheme.Γ ⟶ D.op ⋙ Scheme.Γ :=
    { app i := (p.app i.unop).appTop
      naturality i j g := by
        change (E.map g.unop).appTop ≫ (p.app j.unop).appTop =
          (p.app i.unop).appTop ≫ (D.map g.unop).appTop
        rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, p.naturality] }
  let eC : Cocone (E.op ⋙ Scheme.Γ) := Scheme.Γ.mapCocone d.op
  let dC : Cocone (D.op ⋙ Scheme.Γ) := Scheme.Γ.mapCocone c.op
  have h := flat_of_filteredCocones α (c := eC) (d := dC)
    (nonempty_isColimit_Γ_mapCocone E d hd).some
    (nonempty_isColimit_Γ_mapCocone D c hc).some
    f.appTop (fun i => by
      change (d.π.app i.unop).appTop ≫ f.appTop =
        (p.app i.unop).appTop ≫ (c.π.app i.unop).appTop
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hf])
    (fun i => by
      let := hp i.unop
      exact (p.app i.unop).flat_appTop)
  exact (MorphismProperty.arrow_mk_iso_iff @Flat (arrowIsoSpecΓOfIsAffine f)).mpr
    (Flat.SpecMap_iff.mpr h)

section Pullbacks

variable {I : Type} [SmallCategory I] {D E : I ⥤ Scheme.{0}} {S : Scheme.{0}}
    (t : D ⟶ (Functor.const I).obj S) (v : E ⟶ (Functor.const I).obj S)

set_option backward.isDefEq.respectTransparency false in
private def pullbackDiagram : I ⥤ Scheme.{0} where
  obj i := pullback (t.app i) (v.app i)
  map {i j} g := pullback.map _ _ _ _ (D.map g) (E.map g) (𝟙 S)
    (by simp) (by simp)
  map_id i := by apply pullback.hom_ext <;> simp
  map_comp g h := by apply pullback.hom_ext <;> simp

variable {c : Cone D} {d : Cone E} {f : c.pt ⟶ S} {g : d.pt ⟶ S}
    (hf : ∀ i, c.π.app i ≫ t.app i = f) (hg : ∀ i, d.π.app i ≫ v.app i = g)

set_option backward.isDefEq.respectTransparency false in
private def pullbackDiagramCone : Cone (pullbackDiagram t v) where
  pt := pullback f g
  π :=
    { app i := pullback.map _ _ _ _ (c.π.app i) (d.π.app i) (𝟙 S)
        (by simp [hf i]) (by simp [hg i])
      naturality i j e := by
        apply pullback.hom_ext <;> simp [pullbackDiagram] }

set_option backward.isDefEq.respectTransparency false in
private def pullbackDiagramConeIsLimit [Nonempty I] (hc : IsLimit c) (hd : IsLimit d) :
    IsLimit (pullbackDiagramCone t v hf hg) := by
  let p : pullbackDiagram t v ⟶ D :=
    { app _ := pullback.fst _ _
      naturality _ _ _ := by simp [pullbackDiagram] }
  let q : pullbackDiagram t v ⟶ E :=
    { app _ := pullback.snd _ _
      naturality _ _ _ := by simp [pullbackDiagram] }
  let l (s : Cone (pullbackDiagram t v)) := hc.lift ((Cone.postcompose p).obj s)
  let r (s : Cone (pullbackDiagram t v)) := hd.lift ((Cone.postcompose q).obj s)
  have hl (s : Cone (pullbackDiagram t v)) (i : I) :
      l s ≫ c.π.app i = s.π.app i ≫ pullback.fst (t.app i) (v.app i) :=
    hc.fac _ i
  have hr (s : Cone (pullbackDiagram t v)) (i : I) :
      r s ≫ d.π.app i = s.π.app i ≫ pullback.snd (t.app i) (v.app i) :=
    hd.fac _ i
  let i := Classical.arbitrary I
  refine
    { lift s := pullback.lift (l s) (r s) (by
        rw [← hf i, ← hg i, ← Category.assoc, ← Category.assoc, hl, hr]
        simp only [Category.assoc, pullback.condition])
      fac s j := by
        apply pullback.hom_ext <;> simp [pullbackDiagramCone, hl, hr]
      uniq s h hh := by
        apply pullback.hom_ext
        · simp only [pullback.lift_fst]
          apply hc.hom_ext
          intro j
          simpa [pullbackDiagramCone, hl, Category.assoc] using
            congrArg (fun a => a ≫ pullback.fst (t.app j) (v.app j)) (hh j)
        · simp only [pullback.lift_snd]
          apply hd.hom_ext
          intro j
          simpa [pullbackDiagramCone, hr, Category.assoc] using
            congrArg (fun a => a ≫ pullback.snd (t.app j) (v.app j)) (hh j) }

end Pullbacks

section Affine

variable {I : Type} [SmallCategory I] {D : I ⥤ Scheme.{0}} {S : Scheme.{0}}
    (t : D ⟶ (Functor.const I).obj S)
    {c : Cone D} (hc : IsLimit c) {f : c.pt ⟶ S}
    (hf : ∀ i, c.π.app i ≫ t.app i = f)

include hc hf

set_option backward.isDefEq.respectTransparency false in
/-- An affine cofiltered limit of weakly étale schemes over an affine base is weakly étale. -/
theorem weaklyEtale_of_affineLimit [IsCofiltered I]
    [IsAffine S] [∀ i, IsAffine (D.obj i)] (ht : ∀ i, WeaklyEtale (t.app i)) :
    WeaklyEtale f := by
  let := IsCofiltered.isConnected I
  let (i : I) : IsAffine (((Functor.const I).obj S).obj i) := ‹IsAffine S›
  refine ⟨flat_of_affineLimits t hc (isLimitConstCone I S) f
    (fun i => by simpa [constCone] using (hf i).symm) (fun i => (ht i).flat), ?_⟩
  let a : D ⟶ pullbackDiagram t t :=
    { app i := pullback.diagonal (t.app i)
      naturality i j e := by apply pullback.hom_ext <;> simp [pullbackDiagram] }
  let (i : I) : IsAffine ((pullbackDiagram t t).obj i) := by
    change IsAffine (pullback (t.app i) (t.app i))
    have : IsAffineHom (t.app i) := isAffineHom_of_isAffine (t.app i)
    exact isAffine_of_isAffineHom (pullback.fst (t.app i) (t.app i))
  exact flat_of_affineLimits a hc (pullbackDiagramConeIsLimit t t hf hf hc hc)
    (pullback.diagonal f) (fun i => by
      apply pullback.hom_ext <;> simp [pullbackDiagramCone, a])
    (fun i => (ht i).flat_diagonal)

set_option backward.isDefEq.respectTransparency false in
/-- A limit of affine schemes over an affine base is surjective over that base if
every stage is surjective. -/
theorem surjective_of_affineLimit [IsCofiltered I]
    [IsAffine S] [∀ i, IsAffine (D.obj i)] (ht : ∀ i, Surjective (t.app i)) :
    Surjective f := by
  let := IsCofiltered.isConnected I
  let (i : I) : IsAffine (((Functor.const I).obj S).obj i) := ‹IsAffine S›
  constructor
  intro x
  let v := (Functor.const I).map (S.fromSpecResidueField x)
  have hv (i : I) : (constCone I (Spec (S.residueField x))).π.app i ≫ v.app i =
      S.fromSpecResidueField x := by simp [v, constCone]
  let F := pullbackDiagram t v
  let (i : I) : IsAffine (F.obj i) := by
    change IsAffine ((t.app i).fiber x)
    have : IsAffineHom (t.app i) := isAffineHom_of_isAffine (t.app i)
    infer_instance
  let {i j : I} (e : i ⟶ j) : IsAffineHom (F.map e) := inferInstance
  let (i : I) : Nonempty (F.obj i) := by
    change Nonempty ((t.app i).fiber x)
    obtain ⟨y, hy⟩ := (ht i).surj x
    exact ⟨((t.app i).fiberHomeo x).symm ⟨y, hy⟩⟩
  let (i : I) : CompactSpace (F.obj i) := inferInstance
  have hh := Scheme.nonempty_of_isLimit F _ (pullbackDiagramConeIsLimit t v hf hv hc
    (isLimitConstCone I (Spec (S.residueField x))))
  change Nonempty (f.fiber x) at hh
  obtain ⟨a⟩ := hh
  exact ⟨(f.fiberHomeo x a).1, (f.fiberHomeo x a).2⟩

end Affine

set_option backward.isDefEq.respectTransparency false in
/-- An inverse limit cone for a countable diagram of affine schemes. -/
def affineDiagramLimit {I : Type} [SmallCategory I] (D : I ⥤ Scheme.{0})
    [∀ i, IsAffine (D.obj i)] : LimitCone D := by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  let (i : I) : IsIso (α.app i) := IsAffine.affine
  let : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨_, (IsLimit.postcomposeHomEquiv (asIso α).symm _).symm
    (isLimitOfPreserves Scheme.Spec (limit.isLimit (D ⋙ Scheme.Γ.rightOp)))⟩

set_option backward.isDefEq.respectTransparency false in
/-- A tower of affine weakly étale surjections has an affine limit whose
projection to stage zero is a weakly étale surjection. -/
theorem affineSequenceLimitCover {U : ℕ → Scheme.{0}} [∀ n, IsAffine (U n)]
    (a : ∀ n, U (n + 1) ⟶ U n) (ha : ∀ n, WeaklyEtale (a n))
    (hs : ∀ n, Surjective (a n)) :
    let D := Functor.ofOpSequence a
    ∃ (c : Cone D), IsAffine c.pt ∧ WeaklyEtale (c.π.app (op 0)) ∧ Surjective (c.π.app (op 0)) := by
  let D := Functor.ofOpSequence a
  let (i : ℕᵒᵖ) : IsAffine (D.obj i) := inferInstanceAs (IsAffine (U i.unop))
  let c := affineDiagramLimit D
  let t : D ⟶ (Functor.const ℕᵒᵖ).obj (U 0) :=
    { app i := D.map (homOfLE (Nat.zero_le i.unop)).op
      naturality i j f := by
        simp only [Functor.const_obj_map, ← D.map_comp]
        congr 1 }
  have hf (i : ℕᵒᵖ) : c.cone.π.app i ≫ t.app i = c.cone.π.app (op 0) :=
    c.cone.w (homOfLE (Nat.zero_le i.unop)).op
  have hstage (n : ℕ) : WeaklyEtale (t.app (op n)) ∧ Surjective (t.app (op n)) := by
    induction n with
    | zero =>
      have h : t.app (op 0) = 𝟙 (U 0) := D.map_id (op 0)
      rw [h]
      exact ⟨MorphismProperty.id_mem (@WeaklyEtale) _, ⟨Function.surjective_id⟩⟩
    | succ n ih =>
      have heq : t.app (op (n + 1)) = a n ≫ t.app (op n) := by
        change D.map (homOfLE (Nat.zero_le (n + 1))).op =
          a n ≫ D.map (homOfLE (Nat.zero_le n)).op
        rw [← Functor.ofOpSequence_map_homOfLE_succ a n]
        change _ = D.map _ ≫ D.map _
        rw [← D.map_comp]
        congr 1
      rw [heq]
      let := ha n
      let := hs n
      let := ih.1
      let := ih.2
      exact ⟨inferInstance, inferInstance⟩
  exact ⟨c.cone, Scheme.isAffine_of_isLimit c.cone c.isLimit,
    weaklyEtale_of_affineLimit t c.isLimit hf (fun i => (hstage i.unop).1),
    surjective_of_affineLimit t c.isLimit hf (fun i => (hstage i.unop).2)⟩

end
end ZInQ.Manuscript.T10Proetale

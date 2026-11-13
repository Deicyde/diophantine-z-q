import PGBase
/-! # period-glue: `BaseChangeClassUnique` proved

Task period-glue, 2026-11-13. `PGBase` contains, verbatim, period-map's statement
`HSyn.G0Split.FibreQM.PeriodMapH.BaseChangeClassUnique` (from `scratch/period-map/part_heavy.lean`)
and everything it depends on (fibre-qm-period's `QML3`, `IsBaseChangeOf`, `M3`). This file proves
it from Mathlib only. The one non-formal input named in period-map's docstring, rigidity (a pointed
morphism of abelian varieties is a homomorphism, Mumford §4 Cor. 1), is proved from Mathlib in
mul-rigidity (`scratch/mul-rigidity/Rigidity.lean`, copied verbatim below as `MulRigidity`).

Proof. Both base changes `Q, Q'` of `P` along `ι` are pullbacks of `P.A → Spec ℚ̄` along
`Spec ι`, so the pullback property of `Q'` gives `θ : Q.A → Q'.A` over `Spec ℂ` with
`θ ≫ g' = g`; the same for `θ'`. Every compatibility is an equality of maps into the pullback
`Q'.A`, checked after composing with `g'` (`eq_of_comp`). Level clause at `a = 0` gives that `θ`
keeps the identity section, so rigidity makes `θ` a homomorphism. -/

/-! ## Rigidity (copied verbatim from `scratch/mul-rigidity/Rigidity.lean`, namespace renamed
`PeriodGlue.MulRigidity`) -/

noncomputable section

namespace PeriodGlue.MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj


universe u

variable {K : Type u} [Field K]

theorem isClosedImmersion_point (G : Over (Spec (.of K))) (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    IsClosedImmersion x.left :=
  isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom x.left (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Rigidity lemma (two-sided form), over an algebraically closed field.** Let `G` be proper
over `K` with `G ×_K G` integral, `Z` separated of finite type, and `c : G × G → Z` with
`c(e, y) = z` and `c(x, e) = z` (as morphisms, for all `T`-points). Then `c` is constant. -/
theorem rigidity_algClosed [IsAlgClosed K]
    (G Z : Over (Spec (.of K))) [IsProper G.hom] [IsIntegral (G ⊗ G).left]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ G) (z : 𝟙_ (Over (Spec (.of K))) ⟶ Z) (c : G ⊗ G ⟶ Z)
    (h1 : ∀ (T : Over (Spec (.of K))) (y : T ⟶ G), lift (toUnit T ≫ e) y ≫ c = toUnit T ≫ z)
    (h2 : ∀ (T : Over (Spec (.of K))) (x : T ⟶ G), lift x (toUnit T ≫ e) ≫ c = toUnit T ≫ z) :
    c = toUnit _ ≫ z := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : IsClosedImmersion e.left := isClosedImmersion_point G e
  have : Nonempty G.left := ⟨e.left point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsSeparated (fst G Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst G Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (c.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  have : IsClosedImmersion ((lift e z).left ≫ (fst G Z).left) := by
    simpa using inferInstanceAs (IsClosedImmersion e.left)
  have : IsClosedImmersion (lift e z).left := .of_comp _ (g := (fst G Z).left)
  let gm : G ⊗ G ⟶ G ⊗ Z := lift (fst _ _) c
  have : IsProper (gm.left ≫ (fst G Z).left) := by simpa [gm]
  have : IsProper gm.left := .of_comp _ (fst G Z).left
  ext1
  have H : gm.left '' ((fst G G).left ⁻¹' {e.left point}) ⊆ {(lift e z).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro H
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton];
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift e z).left.isClosedMap _ hpoint).preimage gm.left.continuous).isOpen_compl
      · exact (e.left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨p, hp⟩, hpe⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : p point = c₀ := congr(($hpe).1)
    let pt : 𝟙_ (Over S) ⟶ G ⊗ G := Over.homMk p hp
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (pt ≫ snd G G)
    have : p ≫ pullback.fst G.hom G.hom = e.left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa) (by simp) (by simpa)
    have H₁ : p = fc.left ≫ (e ▷ G).left := by dsimp; ext <;> simp [fc, pt, S, this]
    have H₂ : fc ≫ e ▷ G ≫ gm = lift e z := by
      have h1' := h1 _ (pt ≫ snd G G)
      rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at h1'
      ext1
      · simp [fc, gm, S]
      · simpa [fc, gm, S] using h1'
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  obtain ⟨U, hηU, H⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    gm.left (fst G Z).left (e.left point) (by
      dsimp [-Scheme.Hom.comp_base, gm]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset H)
  have H (x : U) : ((pullback.fst G.hom Z.hom) ⁻¹' {x.1} ∩ Set.range ⇑gm.left).Finite := by
    refine ((((gm.left.imageι ≫ (fst G Z).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ gm.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G Z).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact gm.left.isClosedMap.isClosed_range)]
  refine ext_of_apply_eq Z.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by simpa using (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    let xe : (G ⊗ Z).left := (lift (fst G G) (toUnit _ ≫ z)).left y
    have hgm : lift (fst G G) (toUnit _ ≫ e) ≫ gm = lift (fst G G) (toUnit _ ≫ z) := by
      ext1
      · simp [gm]
      · simpa [gm] using h2 _ (fst G G)
    have : gm.left y = xe := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ gm.left.continuous
        gm.left.isClosedMap ((H ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, gm])) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨(lift (fst G G) (toUnit _ ≫ e)).left y, subset_closure ?_, ?_⟩
        · rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, ← Over.comp_left,
            lift_fst]
        · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hgm]
    convert congr((snd G Z).left $this) using 1
    · simp [gm, ← Scheme.Hom.comp_apply]
    · simp only [xe]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
  · simp

/-- **A pointed morphism of proper group schemes is a homomorphism, over an algebraically closed
field** (rigidity, Mumford §4 Cor. 1). Apply `rigidity_algClosed` to
`c = (μ ≫ h) * ((h ⊗ h) ≫ μ)⁻¹`. -/
theorem isMonHom_of_algClosed [IsAlgClosed K]
    (G B : Over (Spec (.of K))) [GrpObj G] [GrpObj B] [IsProper G.hom] [IsIntegral (G ⊗ G).left]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (h : G ⟶ B) (h0 : η[G] ≫ h = η[B]) : IsMonHom h := by
  have hone : ∀ (T : Over (Spec (.of K))), (1 : T ⟶ G) ≫ h = 1 := fun T => by
    rw [Hom.one_def, Hom.one_def, Category.assoc, h0]
  have key := rigidity_algClosed G B η[G] η[B] ((μ ≫ h) * ((h ⊗ₘ h) ≫ μ)⁻¹)
    (fun T y => by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, lift_map, ← Hom.mul_def,
        ← Hom.mul_def, ← Hom.one_def, _root_.one_mul, hone, _root_.one_mul, mul_inv_cancel,
        Hom.one_def])
    (fun T x => by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, lift_map, ← Hom.mul_def,
        ← Hom.mul_def, ← Hom.one_def, _root_.mul_one, hone, _root_.mul_one, mul_inv_cancel,
        Hom.one_def])
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact ⟨h0, key⟩

/-- **Rigidity over any field** (Mumford §4 Cor. 1 / Milne Cor. 2.2): base change to `K̄` and
`isMonHom_of_algClosed`; `Over.pullback` along `Spec K̄ → Spec K` is faithful and monoidal. -/
theorem isMonHom_of_geometricallyIntegral
    (G B : Over (Spec (.of K))) [GrpObj G] [GrpObj B] [IsProper G.hom]
    [GeometricallyIntegral G.hom] [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (h : G ⟶ B) (h0 : η[G] ≫ h = η[B]) : IsMonHom h := by
  let f := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback f
  let G' := F.obj G
  let B' := F.obj B
  have : IsProper G'.hom := by dsimp [G', F]; infer_instance
  have : IsIntegral (G' ⊗ G').left := by dsimp [G', F]; infer_instance
  have : IsSeparated B'.hom := by dsimp [B', F]; infer_instance
  have : LocallyOfFiniteType B'.hom := by dsimp [B', F]; infer_instance
  let : GrpObj G' := Functor.grpObjObj
  let : GrpObj B' := Functor.grpObjObj
  have h0' : η[G'] ≫ F.map h = η[B'] := by
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, ← F.map_comp, h0]
  have := isMonHom_of_algClosed G' B' (F.map h) h0'
  refine ⟨h0, F.map_injective ?_⟩
  have hm := IsMonHom.mul_hom (F.map h)
  rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc]
    at hm
  simp only [← F.map_comp] at hm
  exact (cancel_epi _).mp hm


end PeriodGlue.MulRigidity

/-! ## `BaseChangeClassUnique` -/

namespace HSyn.G0Split.FibreQM.PeriodGlue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM

section BC

variable {ιe : Qbar →+* ℂ} {P : QML3 Qbar} {Q Q' : QML3 ℂ}

/-- Maps into a base change are determined by their composite with the map to `P.A`. -/
theorem eq_of_comp {g' : Q'.A.X.left ⟶ P.A.X.left}
    (hg' : IsPullback g' Q'.A.X.hom P.A.X.hom (Spec.map (CommRingCat.ofHom ιe)))
    {T : Over (Spec (CommRingCat.of ℂ))} {u v : T ⟶ Q'.A.X} (h : u.left ≫ g' = v.left ≫ g') :
    u = v := by
  ext1
  exact hg'.hom_ext h (by rw [Over.w u, Over.w v])

/-- The comparison morphism `Q.A → Q'.A` over `Spec ℂ`. -/
def cmp {g : Q.A.X.left ⟶ P.A.X.left} {g' : Q'.A.X.left ⟶ P.A.X.left}
    (hg : IsPullback g Q.A.X.hom P.A.X.hom (Spec.map (CommRingCat.ofHom ιe)))
    (hg' : IsPullback g' Q'.A.X.hom P.A.X.hom (Spec.map (CommRingCat.ofHom ιe))) :
    Q.A.X ⟶ Q'.A.X :=
  Over.homMk (hg'.lift g Q.A.X.hom hg.w) (hg'.lift_snd _ _ _)

theorem cmp_left_comp {g : Q.A.X.left ⟶ P.A.X.left} {g' : Q'.A.X.left ⟶ P.A.X.left}
    (hg : IsPullback g Q.A.X.hom P.A.X.hom (Spec.map (CommRingCat.ofHom ιe)))
    (hg' : IsPullback g' Q'.A.X.hom P.A.X.hom (Spec.map (CommRingCat.ofHom ιe))) :
    (cmp hg hg').left ≫ g' = g :=
  hg'.lift_fst _ _ _

/-- `Spec ℂ → Spec ℂ` of `algebraMap ℂ ℂ` is the identity. -/
theorem ptObj_hom_self : (PkgI3.AbVar.ptObj (K := ℂ) ℂ).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ)) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

theorem ptObj_hom_self' : (PkgI3.AbVar.ptObj (K := Qbar) Qbar).hom = 𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (algebraMap Qbar Qbar)) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- The identity section of `Q` composed with `g` (from the level clause at `a = 0`). -/
theorem eta_comp {g : Q.A.X.left ⟶ P.A.X.left}
    (hl : ∀ a : LeafQM.O, (Additive.toMul (Q.e.eta a)).left ≫ g =
        Spec.map (CommRingCat.ofHom ιe) ≫ (Additive.toMul (P.e.eta a)).left) :
    η[Q.A.X].left ≫ g = Spec.map (CommRingCat.ofHom ιe) ≫ η[P.A.X].left := by
  have h0 := hl 0
  rw [Q.e.eta.map_zero, P.e.eta.map_zero] at h0
  change ((1 : PkgI3.AbVar.Pt ℂ Q.A)).left ≫ g =
    Spec.map (CommRingCat.ofHom ιe) ≫ ((1 : PkgI3.AbVar.Pt Qbar P.A)).left at h0
  rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    ptObj_hom_self, ptObj_hom_self'] at h0
  erw [Category.id_comp, Category.id_comp] at h0
  exact h0

end BC

theorem baseChangeClassUnique_proof : PeriodMapH.BaseChangeClassUnique := by
  intro ιe P Q Q' ⟨g, hg, hι, hl⟩ ⟨g', hg', hι', hl'⟩
  set θ := cmp hg hg' with hθ
  set θ' := cmp hg' hg with hθ'
  have hθg : θ.left ≫ g' = g := cmp_left_comp hg hg'
  have hθg' : θ'.left ≫ g = g' := cmp_left_comp hg' hg
  -- `θ` and `θ'` keep the identity section
  have hη : η[Q.A.X] ≫ θ = η[Q'.A.X] := eq_of_comp hg' (by
    rw [Over.comp_left, Category.assoc, hθg, eta_comp hl, eta_comp hl'])
  have hη' : η[Q'.A.X] ≫ θ' = η[Q.A.X] := eq_of_comp hg (by
    rw [Over.comp_left, Category.assoc, hθg', eta_comp hl, eta_comp hl'])
  have : IsMonHom θ :=
    _root_.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral Q.A.X Q'.A.X θ hη
  have : IsMonHom θ' :=
    _root_.PeriodGlue.MulRigidity.isMonHom_of_geometricallyIntegral Q'.A.X Q.A.X θ' hη'
  refine Quotient.sound ⟨{
    φ := PkgI3.AbVar.Hom.mk' θ
    ψ := PkgI3.AbVar.Hom.mk' θ'
    left := ?_
    right := ?_
    equivariant := ?_
    level := ?_ }⟩
  · simp only [PkgI3.AbVar.Hom.hom_mk']
    exact eq_of_comp hg (by rw [Over.comp_left, Category.assoc, hθg', hθg, Over.id_left,
      Category.id_comp])
  · simp only [PkgI3.AbVar.Hom.hom_mk']
    exact eq_of_comp hg' (by rw [Over.comp_left, Category.assoc, hθg, hθg', Over.id_left,
      Category.id_comp])
  · intro a
    simp only [PkgI3.AbVar.Hom.hom_mk']
    exact eq_of_comp hg' (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hθg, hι' a,
        ← Category.assoc, hθg, hι a])
  · intro a
    simp only [PkgI3.AbVar.Hom.hom_mk']
    have hx : Additive.toMul (Q.e.eta a) ≫ θ = Additive.toMul (Q'.e.eta a) :=
      eq_of_comp hg' (by rw [Over.comp_left, Category.assoc, hθg, hl a, hl' a])
    rw [hx]; rfl

end HSyn.G0Split.FibreQM.PeriodGlue

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.baseChangeClassUnique_proof

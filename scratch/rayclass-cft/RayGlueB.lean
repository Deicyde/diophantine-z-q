import RayGlueA

/-! # rayclass-cft, Part G4: the glue `CMBaseChange`, proved

`IsPullback g` makes `Q.A` isomorphic over `L` to the base change `(P.A)_L` (`bcIso`); the isomorphism
preserves the identity (the `η`-clause at `a = 0`), hence is a homomorphism (the kernel's proved
rigidity `G0FibreSimple.rigidityHom`); conjugation by it after the kernel's `endBC` is a ring map
`End P.A → End Q.A` carrying `ι_P` to `ι_Q` (the `ι`-clause), hence `End_𝒪(P)` into `End_𝒪(Q)`. -/

set_option linter.all false

noncomputable section

namespace RayClassCFT

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- The map `Spec L → Spec K`. -/
abbrev fS (K L : Type) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

/-- The identity point of `A(K)` is the unit section. -/
theorem one_pt_left (A : PkgI3.AbVar K) :
    ((1 : A.Pt K) : PkgI3.AbVar.ptObj K ⟶ A.X).left = η[A.X].left := by
  rw [Hom.one_def, Over.comp_left]
  have h1 : (toUnit (PkgI3.AbVar.ptObj (K := K) K)).left = 𝟙 (Spec (CommRingCat.of K)) := by
    have h := Over.w (toUnit (PkgI3.AbVar.ptObj (K := K) K))
    have h' : (toUnit (PkgI3.AbVar.ptObj (K := K) K)).left = (PkgI3.AbVar.ptObj (K := K) K).hom :=
      (Category.comp_id _).symm.trans h
    rw [h']
    show Spec.map (CommRingCat.ofHom (algebraMap K K)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rw [h1]
  exact Category.id_comp _

theorem eta_compat {P : QML3 K} {Q : QML3 L} {g : Q.A.X.left ⟶ P.A.X.left}
    (hη : ∀ a : O, (Additive.toMul (Q.e.eta a)).left ≫ g =
      fS K L ≫ (Additive.toMul (P.e.eta a)).left) :
    η[Q.A.X].left ≫ g = fS K L ≫ η[P.A.X].left := by
  have h := hη 0
  have eQ : (Additive.toMul (Q.e.eta 0)).left = η[Q.A.X].left := by
    rw [show Additive.toMul (Q.e.eta 0) = 1 by rw [map_zero]; rfl]
    exact one_pt_left Q.A
  have eP : (Additive.toMul (P.e.eta 0)).left = η[P.A.X].left := by
    rw [show Additive.toMul (P.e.eta 0) = 1 by rw [map_zero]; rfl]
    exact one_pt_left P.A
  have h' : (Additive.toMul (Q.e.eta 0)).left ≫ g = fS K L ≫ η[P.A.X].left := by
    rw [h]; congr 1
  rw [← h']; congr 1; exact eQ.symm

/-- `Q.A ≅ (P.A)_L` over `L` from the pullback square. -/
def bcIso {P : QML3 K} {Q : QML3 L} {g : Q.A.X.left ⟶ P.A.X.left}
    (hpb : IsPullback g Q.A.X.hom P.A.X.hom (fS K L)) : Q.A.X ≅ (P.A.baseChange L).X :=
  Over.isoMk hpb.isoPullback (by
    show hpb.isoPullback.hom ≫ pullback.snd _ _ = _
    exact hpb.isoPullback_hom_snd)

theorem bcIso_fst {P : QML3 K} {Q : QML3 L} {g : Q.A.X.left ⟶ P.A.X.left}
    (hpb : IsPullback g Q.A.X.hom P.A.X.hom (fS K L)) :
    (bcIso hpb).hom.left ≫ pullback.fst P.A.X.hom (fS K L) = g :=
  hpb.isoPullback_hom_fst

theorem bcIso_snd {P : QML3 K} {Q : QML3 L} {g : Q.A.X.left ⟶ P.A.X.left}
    (hpb : IsPullback g Q.A.X.hom P.A.X.hom (fS K L)) :
    (bcIso hpb).hom.left ≫ pullback.snd P.A.X.hom (fS K L) = Q.A.X.hom :=
  hpb.isoPullback_hom_snd

/-- The unit of `(P.A)_L`, on the pullback projections. -/
theorem eta_bc_fst (A : PkgI3.AbVar K) :
    η[(A.baseChange L).X].left ≫ pullback.fst A.X.hom (fS K L) = fS K L ≫ η[A.X].left := by
  let F := Over.pullback (fS K L)
  have hε1 : (Functor.LaxMonoidal.ε F).left ≫ pullback.snd (𝟙_ (Over (Spec (CommRingCat.of K)))).hom (fS K L) = 𝟙 _ := by
    exact Over.w (Functor.LaxMonoidal.ε F)
  have hε2 : (Functor.LaxMonoidal.ε F).left ≫ pullback.fst (𝟙_ (Over (Spec (CommRingCat.of K)))).hom (fS K L) = fS K L := by
    have hc : pullback.fst (𝟙_ (Over (Spec (CommRingCat.of K)))).hom (fS K L) =
        pullback.snd (𝟙_ (Over (Spec (CommRingCat.of K)))).hom (fS K L) ≫ fS K L :=
      (Category.comp_id _).symm.trans pullback.condition
    rw [hc, ← Category.assoc, hε1, Category.id_comp]
  show (Functor.LaxMonoidal.ε F ≫ F.map η[A.X]).left ≫ pullback.fst A.X.hom (fS K L) = _
  rw [Over.comp_left, Category.assoc]
  show (Functor.LaxMonoidal.ε F).left ≫ pullback.lift (pullback.fst _ _ ≫ η[A.X].left) (pullback.snd _ _) _ ≫
    pullback.fst A.X.hom (fS K L) = _
  rw [pullback.lift_fst, ← Category.assoc, hε2]

theorem eta_bc_snd (A : PkgI3.AbVar K) :
    η[(A.baseChange L).X].left ≫ pullback.snd A.X.hom (fS K L) = 𝟙 _ := by
  exact Over.w η[(A.baseChange L).X]

theorem bcIso_eta {P : QML3 K} {Q : QML3 L} {g : Q.A.X.left ⟶ P.A.X.left}
    (hpb : IsPullback g Q.A.X.hom P.A.X.hom (fS K L))
    (hη : η[Q.A.X].left ≫ g = fS K L ≫ η[P.A.X].left) :
    η[Q.A.X] ≫ (bcIso hpb).hom = η[(P.A.baseChange L).X] := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  apply pullback.hom_ext
  · calc (η[Q.A.X].left ≫ (bcIso hpb).hom.left) ≫ pullback.fst P.A.X.hom (fS K L)
        = η[Q.A.X].left ≫ ((bcIso hpb).hom.left ≫ pullback.fst P.A.X.hom (fS K L)) :=
          Category.assoc _ _ _
      _ = η[Q.A.X].left ≫ g := by rw [bcIso_fst]
      _ = fS K L ≫ η[P.A.X].left := hη
      _ = _ := (eta_bc_fst P.A).symm
  · calc (η[Q.A.X].left ≫ (bcIso hpb).hom.left) ≫ pullback.snd P.A.X.hom (fS K L)
        = η[Q.A.X].left ≫ ((bcIso hpb).hom.left ≫ pullback.snd P.A.X.hom (fS K L)) :=
          Category.assoc _ _ _
      _ = η[Q.A.X].left ≫ Q.A.X.hom := by rw [bcIso_snd]
      _ = 𝟙 _ := Over.w η[Q.A.X]
      _ = _ := (eta_bc_snd P.A).symm

/-! ## Rigidity: `bcIso` is a homomorphism -/

theorem bcIso_isMonHom {P : QML3 K} {Q : QML3 L} {g : Q.A.X.left ⟶ P.A.X.left}
    (hpb : IsPullback g Q.A.X.hom P.A.X.hom (fS K L))
    (hη : η[Q.A.X].left ≫ g = fS K L ≫ η[P.A.X].left) : IsMonHom (bcIso hpb).hom :=
  G0FibreSimple.rigidityHom L Q.A (P.A.baseChange L) (bcIso hpb).hom (bcIso_eta hpb hη)

theorem bcIso_inv_isMonHom {P : QML3 K} {Q : QML3 L} {g : Q.A.X.left ⟶ P.A.X.left}
    (hpb : IsPullback g Q.A.X.hom P.A.X.hom (fS K L))
    (hη : η[Q.A.X].left ≫ g = fS K L ≫ η[P.A.X].left) : IsMonHom (bcIso hpb).inv :=
  G0FibreSimple.rigidityHom L (P.A.baseChange L) Q.A (bcIso hpb).inv (by
    rw [← bcIso_eta hpb hη, Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-! ## Conjugation by a group isomorphism -/

/-- `f ↦ e ∘ f ∘ e⁻¹`, `End B → End A`, for an isomorphism of abelian varieties `e : A ≅ B`. -/
def conjEnd {A B : PkgI3.AbVar L} (e : A.X ≅ B.X) (h1 : IsMonHom e.hom) (h2 : IsMonHom e.inv) :
    PkgI3.AbVar.End B →+* PkgI3.AbVar.End A where
  toFun f := @PkgI3.AbVar.Hom.mk' L _ A A (e.hom ≫ f.hom ≫ e.inv) inferInstance
  map_one' := PkgI3.AbVar.Hom.ext' (by
    change e.hom ≫ 𝟙 _ ≫ e.inv = 𝟙 _
    simp)
  map_mul' f g := PkgI3.AbVar.Hom.ext' (by
    change e.hom ≫ (g.hom ≫ f.hom) ≫ e.inv = (e.hom ≫ g.hom ≫ e.inv) ≫ (e.hom ≫ f.hom ≫ e.inv)
    simp)
  map_zero' := PkgI3.AbVar.Hom.ext' (by
    change e.hom ≫ (1 : B.X ⟶ B.X) ≫ e.inv = 1
    rw [MonObj.one_comp, MonObj.comp_one])
  map_add' f g := PkgI3.AbVar.Hom.ext' (by
    change e.hom ≫ (f.hom * g.hom) ≫ e.inv = (e.hom ≫ f.hom ≫ e.inv) * (e.hom ≫ g.hom ≫ e.inv)
    rw [MonObj.mul_comp, MonObj.comp_mul])

/-! ## `bcIso` intertwines `ι_Q` and the base change of `ι_P` -/

theorem pb_map_fst {X Y : Over (Spec (CommRingCat.of K))} (u : X ⟶ Y) :
    ((Over.pullback (fS K L)).map u).left ≫ pullback.fst Y.hom (fS K L) =
      pullback.fst X.hom (fS K L) ≫ u.left :=
  pullback.lift_fst _ _ _

theorem pb_map_snd {X Y : Over (Spec (CommRingCat.of K))} (u : X ⟶ Y) :
    ((Over.pullback (fS K L)).map u).left ≫ pullback.snd Y.hom (fS K L) =
      pullback.snd X.hom (fS K L) :=
  pullback.lift_snd _ _ _

theorem endBC_fst (A : PkgI3.AbVar K) (f : PkgI3.AbVar.End A) :
    (HDec.G0ModField.KernelField.endBC A L f).hom.left ≫ pullback.fst A.X.hom (fS K L) =
      pullback.fst A.X.hom (fS K L) ≫ f.hom.left :=
  pb_map_fst f.hom

theorem endBC_snd (A : PkgI3.AbVar K) (f : PkgI3.AbVar.End A) :
    (HDec.G0ModField.KernelField.endBC A L f).hom.left ≫ pullback.snd A.X.hom (fS K L) =
      pullback.snd A.X.hom (fS K L) :=
  pb_map_snd f.hom

theorem bc_iota {P : QML3 K} {Q : QML3 L} {g : Q.A.X.left ⟶ P.A.X.left}
    (hpb : IsPullback g Q.A.X.hom P.A.X.hom (fS K L))
    (hι : ∀ a : O, (Q.q.iota a).hom.left ≫ g = g ≫ (P.q.iota a).hom.left) (a : O) :
    (bcIso hpb).hom ≫ (HDec.G0ModField.KernelField.endBC P.A L (P.q.iota a)).hom =
      (Q.q.iota a).hom ≫ (bcIso hpb).hom := by
  apply Over.OverMorphism.ext
  show hpb.isoPullback.hom ≫ pullback.lift (pullback.fst P.A.X.hom (fS K L) ≫ (P.q.iota a).hom.left)
      (pullback.snd P.A.X.hom (fS K L)) _ = (Q.q.iota a).hom.left ≫ hpb.isoPullback.hom
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hpb.isoPullback_hom_fst, Category.assoc,
      hpb.isoPullback_hom_fst, hι]
  · rw [Category.assoc, pullback.lift_snd, hpb.isoPullback_hom_snd, Category.assoc,
      hpb.isoPullback_hom_snd]
    exact (Over.w (Q.q.iota a).hom).symm

/-! ## The ring map `End P.A → End Q.A` and `CMBaseChange` -/

theorem exists_bc_ringHom {P : QML3 K} {Q : QML3 L} (h : IsBaseChangeOf (algebraMap K L) P Q) :
    ∃ R : PkgI3.AbVar.End P.A →+* PkgI3.AbVar.End Q.A, ∀ a : O, R (P.q.iota a) = Q.q.iota a := by
  obtain ⟨g, hpb, hι, hη⟩ := h
  have hη0 := eta_compat (P := P) (Q := Q) (g := g) hη
  let e := bcIso hpb
  have h1 := bcIso_isMonHom hpb hη0
  have h2 := bcIso_inv_isMonHom hpb hη0
  refine ⟨(conjEnd e h1 h2).comp (HDec.G0ModField.KernelField.endBC P.A L), fun a => ?_⟩
  apply PkgI3.AbVar.Hom.ext'
  change e.hom ≫ (HDec.G0ModField.KernelField.endBC P.A L (P.q.iota a)).hom ≫ e.inv = (Q.q.iota a).hom
  rw [← Category.assoc, bc_iota hpb hι a, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem com_map {P : QML3 K} {Q : QML3 L} (R : PkgI3.AbVar.End P.A →+* PkgI3.AbVar.End Q.A)
    (hR : ∀ a : O, R (P.q.iota a) = Q.q.iota a) {φ : PkgI3.AbVar.End P.A} (hφ : φ ∈ com P.q) :
    R φ ∈ com Q.q := by
  rw [com, Subring.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  rw [← hR, ← map_mul, ← map_mul, (Subring.mem_centralizer_iff.1 hφ) _ ⟨a, rfl⟩]

/-- **The glue `CMBaseChange`, proved** (rigidity is the kernel's proved `G0FibreSimple.rigidityHom`). -/
theorem cmBaseChange : CMBaseChange := by
  intro ιe P Q h
  letI : Algebra Qbar ℂ := ιe.toAlgebra
  obtain ⟨R, hR⟩ := exists_bc_ringHom (K := Qbar) (L := ℂ) (P := P) (Q := Q) h
  refine ⟨fun ⟨φ, hφ, h2⟩ => ⟨R φ, com_map R hR hφ, ?_⟩, fun ⟨φ, hφ, h2⟩ => ⟨R φ, com_map R hR hφ, ?_⟩,
    fun ⟨φ, hφ, h2⟩ => ⟨R φ, com_map R hR hφ, ?_⟩⟩
  · rw [← map_mul, h2, map_neg, map_one]
  · have := congrArg R h2
    rwa [map_add, map_sub, map_mul, map_one, map_zero] at this
  · rw [← map_mul, h2, map_neg, map_ofNat]

/-- **`RayClassCM` from published-form leaves only**: shimura-cft's Deligne leaf with the moduli clause
at `𝒪̂^×` (`ShimuraMainThmIDeligneY3AbU`), Eichler's class number one (`ClassNumberOneB`), and the
bundle leaves `MumfordRigidityCore` and `HomLinearLift`. -/
theorem rayClassCM_of_leaves (hL : ShimuraMainThmIDeligneY3AbU)
    (hMR : LeafQM.AV.R1UnivRigid.MumfordRigidityCore) (hCN : ClassNumberOneB)
    (hHL : ZInQ.HomUnify.HomLinearLift) : ShimuraGlue.Ray.RayClassCM :=
  rayClassCM_of4 hL hMR hCN cmBaseChange hHL

end RayClassCFT

#print axioms RayClassCFT.cmBaseChange
#print axioms RayClassCFT.rayClassCM_of_leaves

import ZInQKernel.Contrib.OneProof.MumfordRigidity

set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.MumfordRigidity

open LeafQM.AV.R1UnivRigid PkgI3

/-- **LEAF (`𝒪_S ≅ p_*𝒪_X`).** -/
def PushforwardStructureSheaf : Prop :=
  ∀ (S X : Scheme.{0}) (p : X ⟶ S), IsLocallyNoetherian S → IsProper p → Smooth p →
    GeometricallyConnected p → ∀ U : S.Opens, Function.Bijective (p.app U)

theorem appLE_id_eq {T : Scheme.{0}} (g : T ⟶ T) (hg : g = 𝟙 T) (U : T.Opens)
    (e : U ≤ g ⁻¹ᵁ U) : g.appLE U U e = 𝟙 _ := by
  subst hg
  exact (Scheme.Hom.appLE_eq_app (𝟙 T)).trans (Scheme.Hom.id_app U)

/-- **Local rigidity** from `𝒪_S ≅ p_*𝒪_X`. -/
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

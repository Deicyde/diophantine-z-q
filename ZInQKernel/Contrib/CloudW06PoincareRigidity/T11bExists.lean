import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudW06PoincareRigidity.Rigidity
import ZInQKernel.Contrib.CloudW06PoincareRigidity.AdjoinFinset
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# H-75: T11(b), rigidity, existence half (`T11bExists`), proved

Task cloud-w06 (frontier row H-75, issue elliotglazer/diophantine-z-q#82), 2026-11-14.

## The statement (a verbatim copy)

`T11bExists` below is a verbatim copy (docstring and body) of the definition `HDec.AVB2.T11bExists`
in `scratch/av-b2/olean/AVB2Main.lean`, lines 209-219, at fork `main` commit
`cba8157f7d5d09a4a3c8462aba2f3245494a870e` (the file is unchanged at `f70ec251`). That file is a
scratch assembly compiled on top of leaf-fold3's olean chain, in which `PkgI3` resolves to
`HDec.PkgI3`, leaf-fold3's renamed copy of the kernel's `PkgI3`; here the same text resolves to the
kernel's `_root_.PkgI3` (`ZInQKernel/HDecomp/Objects.lean`), whose `AbVar`, `baseChange` and
instances are the text the chain copies (the chain's section differs only by the line-wrap of one
docstring).

## The proof

`T11bExists_proof : T11bExists`. Let `ψ : A_L ⟶ B_L` be a homomorphism.
1. *Spreading out* (EGA IV 8.14.2, Mathlib's
   `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`): `A_L` is the limit of the
   `A_R = Spec R ×_k A` over the finitely generated `k`-subalgebras `R = k[s] ⊆ L`
   (`AdjoinFinset.isLimitBcCone`, vendored from AxiomMath/Stacks), so the `k`-morphism
   `A_L ⟶ B_L ⟶ B` factors through some `g : Spec R ×_k A ⟶ B`.
2. *A `k`-point of `Spec R`*: `R ≠ 0` is of finite type over the algebraically closed `k`.
3. *Rigidity* (`rigidity_family`): `h(y, a) = g(y, a) / (g(y₀, a) g(y, 0) / g(y₀, 0))` is trivial on
   `y₀ × A` and on `Spec R × 0`, so it is trivial; hence `g(y, a) = φ(a) · c(y)` with
   `φ(a) = g(y₀, a) / g(y₀, 0)`.
4. Since `ψ(0) = 0`, the factor `c` is trivial on `Spec L`, so `ψ = φ_L`; and `φ` is a
   homomorphism because base change along `Spec L ⟶ Spec k` is faithful and monoidal.

No extra hypotheses; the characteristic-`0` assumption of the statement is not used.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.CloudW06PoincareRigidity

/-- **Leaf (T11(b), existence half).** For abelian varieties over an algebraically closed field `k`
of characteristic `0` and an extension `L/k`, every homomorphism `A_L → B_L` is the base change of a
homomorphism `A → B`. Published: Conrad, *Chow's `K/k`-image and `K/k`-trace, and the Lang–Néron
theorem*, Enseign. Math. 52 (2006), §3 (rigidity of `Hom` for primary extensions, locator UNVERIFIED);
Milne, *Abelian varieties* (Cornell–Silverman 1986), §20 (UNVERIFIED). `LeafPush2.T11b_Rigidity`
without its uniqueness clause, which `baseChange_map_injective` proves. -/
def T11bExists : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (L : Type) [Field L] [Algebra k L]
    (A B : PkgI3.AbVar k) (ψ : (A.baseChange L).X ⟶ (B.baseChange L).X), IsMonHom ψ →
    ∃ φ : A.X ⟶ B.X, IsMonHom φ ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map φ = ψ

/-! ## A faithful monoidal functor reflects `IsMonHom` -/

section Reflect

open scoped CategoryTheory.Obj

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

/-- A faithful monoidal functor reflects morphisms of monoid objects (the proof of Mathlib's
`Functor.FullyFaithful.isMonHom_preimage`). -/
theorem isMonHom_of_isMonHom_map (F : C ⥤ D) [F.Monoidal] [F.Faithful] {X Y : C} [MonObj X]
    [MonObj Y] (f : X ⟶ Y) (hf : IsMonHom (F.map f)) : IsMonHom f where
  one_hom := F.map_injective <| by
    simp [← Functor.obj.η_def_assoc, ← Functor.obj.η_def, ← cancel_epi (Functor.LaxMonoidal.ε F)]
  mul_hom := F.map_injective <| by
    simp [← Functor.obj.μ_def_assoc, ← Functor.obj.μ_def, ← Functor.LaxMonoidal.μ_natural_assoc,
      ← cancel_epi (Functor.LaxMonoidal.μ F ..)]

end Reflect

/-! ## Spreading out -/

section Spread

variable {k : Type} [Field k] (L : Type) [Field L] [Algebra k L]

/-- The structure maps of the stages `Spec k[s] ×_k A` to `Spec k`. -/
noncomputable def stageToBase (A : PkgI3.AbVar k) :
    AdjoinFinset.bcDiagram k L A.X.hom ⟶
      (Functor.const (Finset L)ᵒᵖ).obj (Spec (CommRingCat.of k)) where
  app i := pullback.snd _ A.X.hom ≫ A.X.hom
  naturality i j e := by
    have h := Over.w ((Over.pullback A.X.hom).map ((AdjoinFinset.specOverDiagram k L).map e))
    simp only [Over.pullback_obj_hom] at h
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    exact (reassoc_of% h) A.X.hom

/-- **Spreading out a morphism** `Spec L ×_k A ⟶ B` to a stage `Spec k[s] ×_k A`
(EGA IV 8.14.2, `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`). -/
theorem exists_stage_factorization (A B : PkgI3.AbVar k)
    (a : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) A.X.hom ⟶ B.X.left)
    (ha : a ≫ B.X.hom = pullback.snd _ A.X.hom ≫ A.X.hom) :
    ∃ (i : (Finset L)ᵒᵖ) (g : (AdjoinFinset.bcDiagram k L A.X.hom).obj i ⟶ B.X.left),
      (AdjoinFinset.bcCone k L A.X.hom).π.app i ≫ g = a ∧
        g ≫ B.X.hom = pullback.snd _ A.X.hom ≫ A.X.hom := by
  have hcq (i : (Finset L)ᵒᵖ) :=
    AdjoinFinset.bcDiagram_compactSpace_and_quasiSeparatedSpace k L A.X.hom i
  haveI (i : (Finset L)ᵒᵖ) : CompactSpace ((AdjoinFinset.bcDiagram k L A.X.hom).obj i) := (hcq i).1
  haveI (i : (Finset L)ᵒᵖ) : QuasiSeparatedSpace ((AdjoinFinset.bcDiagram k L A.X.hom).obj i) :=
    (hcq i).2
  haveI {i j : (Finset L)ᵒᵖ} (e : i ⟶ j) :
      IsAffineHom ((AdjoinFinset.bcDiagram k L A.X.hom).map e) :=
    AdjoinFinset.bcDiagram_isAffineHom k L A.X.hom e
  obtain ⟨i, g, hg, hg'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (AdjoinFinset.bcDiagram k L A.X.hom) (stageToBase L A) B.X.hom
    (AdjoinFinset.bcCone k L A.X.hom) (AdjoinFinset.isLimitBcCone k L A.X.hom) a (by
      ext i
      simp only [NatTrans.comp_app, Functor.const_obj_obj, Functor.const_map_app]
      change AdjoinFinset.bcProj k L A.X.hom i ≫ pullback.snd _ A.X.hom ≫ A.X.hom = _
      rw [← Category.assoc, AdjoinFinset.bcProj_snd]
      exact ha.symm)
  exact ⟨i, g, hg, hg'⟩

end Spread

/-! ## A `k`-point of a stage -/

section Point

variable {k : Type} [Field k] [IsAlgClosed k] {L : Type} [Field L] [Algebra k L]

/-- The structure morphism `Spec k[s] ⟶ Spec k` is locally of finite type. -/
theorem locallyOfFiniteType_stage (s : Finset L) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap k (Algebra.adjoin k (s : Set L))))) := by
  have : Algebra.FiniteType k (Algebra.adjoin k (s : Set L)) :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- **`Spec k[s]` has a `k`-point** (`k[s] ≠ 0` is of finite type over the algebraically closed
field `k`; a closed point is a `k`-point). -/
theorem exists_point_stage (s : Finset L) :
    ∃ y₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Algebra.adjoin k (s : Set L))),
      y₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Algebra.adjoin k (s : Set L)))) = 𝟙 _ := by
  have := locallyOfFiniteType_stage (k := k) s
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton
    (X := Spec (CommRingCat.of (Algebra.adjoin k (s : Set L)))) isClosed_univ Set.univ_nonempty
  exact ⟨pointOfClosedPoint _ x hx, pointOfClosedPoint_comp _ x hx⟩

end Point

/-! ## Splitting a family of morphisms by rigidity -/

section Split

variable {k : Type} [Field k] [IsAlgClosed k]

/-- **A family `G : Y ×_k A ⟶ B` splits** as `G(y, a) = G(y₀, a) · G(y, 0) / G(y₀, 0)`: by
`rigidity_family`, the quotient of the two sides is trivial on `y₀ × A` and on `Y × 0`. -/
theorem family_split (Y : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType Y.hom]
    (A B : PkgI3.AbVar k) [IsIntegral (Y ⊗ A.X).left] (y₀ : 𝟙_ _ ⟶ Y) (G : Y ⊗ A.X ⟶ B.X) :
    G = (lift (toUnit _ ≫ y₀) (snd Y A.X) ≫ G) * (lift (fst Y A.X) (toUnit _ ≫ η[A.X]) ≫ G) /
      (toUnit _ ≫ lift y₀ η[A.X] ≫ G) := by
  set G2 := lift (toUnit _ ≫ y₀) (snd Y A.X) ≫ G with hG2
  set G3 := lift (fst Y A.X) (toUnit _ ≫ η[A.X]) ≫ G with hG3
  set G4 := toUnit (Y ⊗ A.X) ≫ lift y₀ η[A.X] ≫ G with hG4
  have e12 : y₀ ▷ A.X ≫ G2 = y₀ ▷ A.X ≫ G := by
    rw [hG2, ← Category.assoc]
    congr 1
    ext1
    · rw [Category.assoc, lift_fst, ← Category.assoc, toUnit_unique (y₀ ▷ A.X ≫ toUnit _) (fst _ _),
        whiskerRight_fst]
    · rw [Category.assoc, lift_snd, whiskerRight_snd]
  have e34 : y₀ ▷ A.X ≫ G3 = y₀ ▷ A.X ≫ G4 := by
    rw [hG3, hG4, ← Category.assoc, ← Category.assoc, ← Category.assoc]
    congr 1
    ext1
    · rw [Category.assoc, lift_fst, whiskerRight_fst, Category.assoc, lift_fst,
        toUnit_unique (fst (𝟙_ _) A.X) (y₀ ▷ A.X ≫ toUnit _)]
    · rw [Category.assoc, lift_snd, Category.assoc, lift_snd, ← Category.assoc,
        toUnit_unique (y₀ ▷ A.X ≫ toUnit _) (toUnit _)]
  have f13 : Y ◁ η[A.X] ≫ G3 = Y ◁ η[A.X] ≫ G := by
    rw [hG3, ← Category.assoc]
    congr 1
    ext1
    · rw [Category.assoc, lift_fst, whiskerLeft_fst]
    · rw [Category.assoc, lift_snd, whiskerLeft_snd, ← Category.assoc,
        toUnit_unique (Y ◁ η[A.X] ≫ toUnit _) (snd _ _)]
  have f24 : Y ◁ η[A.X] ≫ G2 = Y ◁ η[A.X] ≫ G4 := by
    rw [hG2, hG4, ← Category.assoc, ← Category.assoc, ← Category.assoc]
    congr 1
    ext1
    · rw [Category.assoc, lift_fst, Category.assoc, lift_fst, ← Category.assoc,
        toUnit_unique (Y ◁ η[A.X] ≫ toUnit _) (toUnit _)]
    · rw [Category.assoc, lift_snd, whiskerLeft_snd, Category.assoc, lift_snd,
        toUnit_unique (snd Y (𝟙_ _)) (toUnit _), toUnit_unique (Y ◁ η[A.X] ≫ toUnit _) (toUnit _)]
  have h := rigidity_family Y A.X B.X y₀ η[A.X] η[B.X] (G / (G2 * G3 / G4))
    (by rw [GrpObj.comp_div, GrpObj.comp_div, MonObj.comp_mul, e12, e34, mul_div_cancel_right,
      div_self']; exact Hom.one_def)
    (by rw [GrpObj.comp_div, GrpObj.comp_div, MonObj.comp_mul, f13, f24, mul_div_cancel_left,
      div_self']; exact Hom.one_def)
  rw [← Hom.one_def] at h
  exact div_eq_one.mp h

end Split

/-! ## The proof of `T11bExists` -/

/-- **T11(b), existence half, proved** (frontier row H-75). -/
theorem T11bExists_proof : T11bExists := by
  intro k _ _ _ L _ _ A B ψ hψ
  let s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k L))
  -- Retype `ψ` with source and target written as `Over.pullback s` (`AbVar.baseChange` is not
  -- reducible).
  obtain ⟨ψ, rfl⟩ : ∃ ψ' : (Over.pullback s).obj A.X ⟶ (Over.pullback s).obj B.X, ψ' = ψ :=
    ⟨ψ, rfl⟩
  -- The `k`-morphism `a : Spec L ×_k A ⟶ B` underlying `ψ`.
  let a : pullback s A.X.hom ⟶ B.X.left :=
    (pullbackSymmetry s A.X.hom).hom ≫ ψ.left ≫ pullback.fst B.X.hom s
  have hψw : ψ.left ≫ pullback.snd B.X.hom s = pullback.snd A.X.hom s := Over.w ψ
  have ha : a ≫ B.X.hom = pullback.snd s A.X.hom ≫ A.X.hom := by
    simp only [a, Category.assoc]
    rw [pullback.condition, reassoc_of% hψw, pullbackSymmetry_hom_comp_snd_assoc]
    exact pullback.condition
  -- Step 1: spreading out to a stage `Spec R ×_k A`, `R = k[s]` finitely generated.
  obtain ⟨i, g, hga, hgB⟩ := exists_stage_factorization L A B a ha
  let R := Algebra.adjoin k ((Opposite.unop i : Finset L) : Set L)
  let y : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  let Yo : Over (Spec (CommRingCat.of k)) := Over.mk y
  haveI : LocallyOfFiniteType Yo.hom := locallyOfFiniteType_stage (Opposite.unop i)
  haveI : Algebra.FiniteType k R :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  haveI : IsIntegral (Yo ⊗ A.X).left := by
    change IsIntegral (pullback y A.X.hom)
    infer_instance
  -- Step 2: a `k`-point `y₀` of `Spec R`.
  obtain ⟨y₀l, hy₀l⟩ := exists_point_stage (k := k) (Opposite.unop i)
  let y₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Yo := Over.homMk y₀l hy₀l
  -- Step 3: rigidity splits the family `G = g`.
  let g' : pullback y A.X.hom ⟶ B.X.left := g
  let G : Yo ⊗ A.X ⟶ B.X := Over.homMk g' (by
    change g' ≫ B.X.hom = pullback.fst y A.X.hom ≫ y
    rw [pullback.condition]
    exact hgB)
  have hsplit := family_split Yo A B y₀ G
  -- Step 4: restriction to the limit point `Spec L ×_k A`.
  let Po : Over (Spec (CommRingCat.of k)) := Over.mk (pullback.snd s A.X.hom ≫ A.X.hom)
  let Lo : Over (Spec (CommRingCat.of k)) := Over.mk s
  let π : pullback s A.X.hom ⟶ pullback y A.X.hom := AdjoinFinset.bcProj k L A.X.hom i
  have hπ1 : π ≫ pullback.fst y A.X.hom =
      pullback.fst s A.X.hom ≫ Spec.map (CommRingCat.ofHom R.val.toRingHom) :=
    AdjoinFinset.bcProj_fst k L A.X.hom i
  have hπ2 : π ≫ pullback.snd y A.X.hom = pullback.snd s A.X.hom :=
    AdjoinFinset.bcProj_snd k L A.X.hom i
  let πo : Po ⟶ Yo ⊗ A.X := Over.homMk π (by
    change π ≫ pullback.fst y A.X.hom ≫ y = pullback.snd s A.X.hom ≫ A.X.hom
    rw [pullback.condition, ← Category.assoc, hπ2])
  have hj : Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ y = s := by
    simp only [y, s, ← Spec.map_comp]
    rw [Spec.map_inj]
    exact CommRingCat.hom_ext (by ext x; rfl)
  let jo : Lo ⟶ Yo := Over.homMk (Spec.map (CommRingCat.ofHom R.val.toRingHom)) hj
  let qo : Po ⟶ Lo := Over.homMk (pullback.fst s A.X.hom) pullback.condition
  let pAo : Po ⟶ A.X := Over.homMk (pullback.snd s A.X.hom) rfl
  let Ao : Po ⟶ B.X := Over.homMk a ha
  have hπfst : πo ≫ fst Yo A.X = qo ≫ jo := by
    ext1
    exact hπ1
  have hπsnd : πo ≫ snd Yo A.X = pAo := by
    ext1
    exact hπ2
  have hπG : πo ≫ G = Ao := by
    ext1
    exact hga
  let φ1 : A.X ⟶ B.X := lift (toUnit A.X ≫ y₀) (𝟙 A.X) ≫ G
  let c3 : Lo ⟶ B.X := lift jo (toUnit Lo ≫ η[A.X]) ≫ G
  let c0 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ B.X := lift y₀ η[A.X] ≫ G
  let φ : A.X ⟶ B.X := φ1 / (toUnit A.X ≫ c0)
  have h2 : πo ≫ lift (toUnit _ ≫ y₀) (snd Yo A.X) ≫ G = pAo ≫ φ1 := by
    rw [← Category.assoc, comp_lift, comp_toUnit_assoc, hπsnd, ← Category.assoc, comp_lift,
      comp_toUnit_assoc, Category.comp_id]
  have h3 : πo ≫ lift (fst Yo A.X) (toUnit _ ≫ η[A.X]) ≫ G = qo ≫ c3 := by
    rw [← Category.assoc, comp_lift, comp_toUnit_assoc, hπfst, ← Category.assoc, comp_lift,
      comp_toUnit_assoc]
  have h4 : πo ≫ toUnit _ ≫ lift y₀ η[A.X] ≫ G = toUnit Po ≫ c0 := by
    rw [comp_toUnit_assoc]
  have hAo : Ao = (pAo ≫ φ) * (qo ≫ c3) := by
    rw [← hπG, hsplit, GrpObj.comp_div, MonObj.comp_mul, h2, h3, h4, GrpObj.comp_div,
      comp_toUnit_assoc, div_mul_eq_mul_div]
  -- Step 5: `ψ` preserves the unit, so the correction `c3` is trivial.
  have h1 : (Functor.LaxMonoidal.ε (Over.pullback s) ≫ (Over.pullback s).map η[A.X]) ≫ ψ =
      Functor.LaxMonoidal.ε (Over.pullback s) ≫ (Over.pullback s).map η[B.X] := hψ.one_hom
  rw [Category.assoc, cancel_epi] at h1
  let E : Spec (CommRingCat.of L) ⟶ pullback s A.X.hom :=
    pullback.lift (𝟙 _) (s ≫ η[A.X].left) (by
      rw [Category.id_comp, Category.assoc, Over.w η[A.X]]
      exact (Category.comp_id s).symm)
  let E' : Spec (CommRingCat.of L) ⟶ pullback (𝟙 (Spec (CommRingCat.of k))) s :=
    pullback.lift s (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
  have hEE' : E ≫ (pullbackSymmetry s A.X.hom).hom =
      E' ≫ ((Over.pullback s).map η[A.X]).left := by
    apply pullback.hom_ext
    · simp [E, E']
    · simp [E, E']
  have hEa : E ≫ a = s ≫ η[B.X].left := by
    have h1l := congrArg (fun f => f.left ≫ pullback.fst B.X.hom s) h1
    simp only [Over.comp_left, Category.assoc] at h1l
    simp only [a, ← Category.assoc, hEE']
    simp only [Category.assoc, h1l]
    simp [E']
  let Eo : Lo ⟶ Po := Over.homMk E (by
    change E ≫ pullback.snd s A.X.hom ≫ A.X.hom = s
    rw [← Category.assoc, pullback.lift_snd, Category.assoc, Over.w η[A.X]]
    exact Category.comp_id s)
  have hEq : Eo ≫ qo = 𝟙 Lo := by
    ext1
    exact pullback.lift_fst _ _ _
  have hEp : Eo ≫ pAo = toUnit Lo ≫ η[A.X] := by
    ext1
    exact pullback.lift_snd _ _ _
  have hEA : Eo ≫ Ao = toUnit Lo ≫ η[B.X] := by
    ext1
    exact hEa
  have hηφ : η[A.X] ≫ φ = 1 := by
    have hηφ1 : η[A.X] ≫ φ1 = c0 := by
      rw [← Category.assoc, comp_lift, ← Category.assoc,
        toUnit_unique (η[A.X] ≫ toUnit A.X) (𝟙 _), Category.id_comp, Category.comp_id]
    rw [GrpObj.comp_div, hηφ1, ← Category.assoc, toUnit_unique (η[A.X] ≫ toUnit A.X) (𝟙 _),
      Category.id_comp, div_self']
  have hc3 : c3 = 1 := by
    have := congrArg (fun f => Eo ≫ f) hAo
    simp only [hEA, MonObj.comp_mul, ← Category.assoc, hEq, hEp, Category.id_comp] at this
    rw [Category.assoc, hηφ, MonObj.comp_one, _root_.one_mul, ← Hom.one_def] at this
    exact this.symm
  have hAoφ : Ao = pAo ≫ φ := by
    rw [hAo, hc3, MonObj.comp_one, _root_.mul_one]
  -- Step 6: `ψ` is the base change of `φ`, and `φ` is a homomorphism.
  have haφ : ψ.left ≫ pullback.fst B.X.hom s = pullback.fst A.X.hom s ≫ φ.left := by
    have h := congrArg (fun f => (pullbackSymmetry s A.X.hom).inv ≫ f.left) hAoφ
    simp only [Ao, pAo, Over.homMk_left, Over.comp_left, a, Iso.inv_hom_id_assoc] at h
    rw [h, pullbackSymmetry_inv_comp_snd_assoc]
  have hφψ : (Over.pullback s).map φ = ψ := by
    ext1
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst]
      exact haφ.symm
    · simp only [Over.pullback_map_left, pullback.lift_snd]
      exact hψw.symm
  exact ⟨φ, isMonHom_of_isMonHom_map (Over.pullback s) φ (hφψ ▸ hψ), hφψ⟩

/-! ## Corollary: T11(b) with uniqueness -/

/-- **T11(b), rigidity, with uniqueness.** The statement is the body of the kernel's
`ZInQ.LeafPush2.T11b_Rigidity` (`ZInQKernel/HDecomp/LeafPush2/T.lean`, line 56), written with
`PkgI3.AbVar` for its `AbVar` (that file opens `PkgI3`); this module does not import it.
Existence is `T11bExists_proof`; uniqueness holds because base change along
`Spec L ⟶ Spec k` is faithful (a Mathlib instance), the argument of av-b2's
`baseChange_map_injective`. -/
theorem T11bRigidity_unique : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (L : Type)
    [Field L] [Algebra k L] (A B : PkgI3.AbVar k) (ψ : (A.baseChange L).X ⟶ (B.baseChange L).X),
    IsMonHom ψ → ∃! φ : A.X ⟶ B.X, IsMonHom φ ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map φ = ψ := by
  intro k _ _ _ L _ _ A B ψ hψ
  obtain ⟨φ, hφ, hφψ⟩ := T11bExists_proof k L A B ψ hψ
  exact ⟨φ, ⟨hφ, hφψ⟩, fun φ' hφ' => (Over.pullback _).map_injective (hφ'.2.trans hφψ.symm)⟩

end ZInQ.Contrib.CloudW06PoincareRigidity

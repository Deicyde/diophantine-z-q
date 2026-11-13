import Mathlib
import ZInQKernel.HDecomp.Objects


/-!
# mul-rigidity: the textbook leaf `RigidityHom` proved from Mathlib

`RigidityHom` is copied verbatim from scratch/g0-fibresimple/FibreSimple.lean (§4‴). The proof
follows Mathlib's proof that proper geometrically integral group schemes are commutative
(`AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`, Stacks 0BFD),
with the commutator replaced by an arbitrary `c : G ⊗ G ⟶ Z` that is constant on `{e} × G` and on
`G × {e}` (the rigidity lemma, Mumford §4).
-/

noncomputable section

namespace MulRigidity

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

end MulRigidity

/-! ## The leaf, copied verbatim, and its proof -/

namespace G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Textbook leaf (rigidity; Mumford, *Abelian varieties*, §4 Cor. 1; Milne, *Abelian
varieties* (Cornell–Silverman 1986), Cor. 2.2, over any field; locators UNVERIFIED).** A morphism
of `k`-schemes between abelian varieties that sends the identity to the identity is a
homomorphism. -/
def RigidityHom : Prop :=
  ∀ (k : Type) [Field k] (A B : PkgI3.AbVar k) (h : A.X ⟶ B.X), η[A.X] ≫ h = η[B.X] → IsMonHom h

/-- **`RigidityHom` holds** (proved from Mathlib; no new hypotheses). -/
theorem rigidityHom : RigidityHom := fun _ _ A B h h0 =>
  MulRigidity.isMonHom_of_geometricallyIntegral A.X B.X h h0

end G0FibreSimple

#print axioms G0FibreSimple.rigidityHom


/-!
# mul-rigidity: the textbook leaf `MulIsogeny` reduced to smaller named Props

`MulIsogeny` is copied verbatim from scratch/g0-fibresimple/FibreSimple.lean (§4″). Mathlib
proves "finite and surjective" from local properties of `[n]`: proper (`A` proper) and locally
quasi-finite give finite (Zariski's main theorem, Mathlib `IsFinite.of_isProper_of_locallyQuasiFinite`,
Stacks 02LS); open (flat + locally of finite presentation, `UniversallyOpen.of_flat`) and closed
(proper) with `A` irreducible and nonempty give surjective.
-/

noncomputable section

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- Formally unramified and locally of finite type implies locally quasi-finite (Mathlib's algebra
instance `Algebra.QuasiFinite` from `EssFiniteType` and `FormallyUnramified`, made affine-local). -/
theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h1 : (f.appLE U V e).hom.FormallyUnramified :=
    HasRingHomProperty.appLE @FormallyUnramified f inferInstance U V e
  have h2 : (f.appLE U V e).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance U V e
  algebraize [(f.appLE U V e).hom]
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

variable {K : Type} [Field K]

/-- A `K`-morphism between abelian varieties is proper (source proper, target separated). -/
theorem isProper_left (A B : PkgI3.AbVar K) (f : A.X ⟶ B.X) : IsProper f.left := by
  have : IsProper (f.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp f.left B.X.hom

/-- **Glue.** A locally quasi-finite open `K`-endomorphism of an abelian variety is finite and
surjective. -/
theorem isIsogenyMor_of_lqf_of_isOpenMap (A : PkgI3.AbVar K) (f : A.X ⟶ A.X)
    [LocallyQuasiFinite f.left] (ho : IsOpenMap f.left.base) : PkgI3.AbVar.IsIsogenyMor f := by
  have := isProper_left A A f
  refine ⟨IsFinite.of_isProper_of_locallyQuasiFinite f.left, ⟨?_⟩⟩
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := A.X.hom)
  have hcl : IsClopen (Set.range f.left.base) :=
    ⟨f.left.isClosedMap.isClosed_range, ho.isOpen_range⟩
  have hne : (Set.range f.left.base).Nonempty :=
    ⟨_, ⟨η[A.X].left (IsLocalRing.closedPoint K), rfl⟩⟩
  exact Set.range_eq_univ.mp (hcl.eq_univ hne)

/-- Under a locally quasi-finite morphism, a strict specialization maps to two distinct points
(the fibres are discrete, Mathlib `Scheme.Hom.isDiscrete_preimage_singleton`). -/
theorem ne_of_specializes_of_lqf {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f]
    {x y : X} (hxy : x ⤳ y) (hne : x ≠ y) : f x ≠ f y := by
  intro heq
  have hd := (f.isDiscrete_preimage_singleton (f y)).to_subtype
  let x' : (f.base ⁻¹' {f y} : Set X) := ⟨x, heq⟩
  let y' : (f.base ⁻¹' {f y} : Set X) := ⟨y, rfl⟩
  have h' : x' ⤳ y' := (subtype_specializes_iff x' y').mpr hxy
  exact hne (congrArg Subtype.val h'.eq)

/-- **A locally quasi-finite closed self-map of an irreducible Noetherian scheme is
surjective.** If `f ξ ≠ ξ` for the generic point `ξ`, then `ξ ⤳ f ξ ⤳ f² ξ ⤳ ⋯` are strict
specializations (continuity, and `ne_of_specializes_of_lqf`), so the closures `cl{fᵐ ξ}` form a
strictly decreasing chain of closed sets, contradicting Noetherianity. So `ξ ∈ range f`, which is
closed, hence everything. -/
theorem surjective_of_lqf_self {X : Scheme} [IrreducibleSpace X] [TopologicalSpace.NoetherianSpace X]
    (f : X ⟶ X) [LocallyQuasiFinite f] (hc : IsClosedMap f.base) :
    Function.Surjective f.base := by
  set ξ := genericPoint X
  have hξ : ∀ x : X, ξ ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hfix : f ξ = ξ := by
    by_contra hne
    let s : ℕ → X := fun m => (f.base)^[m] ξ
    have hs : ∀ m, s m ⤳ s (m + 1) ∧ s m ≠ s (m + 1) := by
      intro m
      induction m with
      | zero => exact ⟨hξ _, fun h => hne h.symm⟩
      | succ m ih =>
        have e1 : s (m + 1) = f (s m) := Function.iterate_succ_apply' _ _ _
        have e2 : s (m + 1 + 1) = f (s (m + 1)) := Function.iterate_succ_apply' _ _ _
        rw [e1, e2]
        exact ⟨ih.1.map f.base.hom.continuous, ne_of_specializes_of_lqf f ih.1 ih.2⟩
    let c : ℕ → TopologicalSpace.Closeds X := fun m => ⟨closure {s m}, isClosed_closure⟩
    have hc' : StrictAnti c := by
      refine strictAnti_nat_of_succ_lt fun m => ?_
      refine lt_of_le_of_ne ?_ ?_
      · change closure {s (m + 1)} ⊆ closure {s m}
        exact specializes_iff_closure_subset.mp (hs m).1
      · intro h
        have h2 : closure {s (m + 1)} = closure {s m} := congrArg SetLike.coe h
        exact (hs m).2 (inseparable_iff_closure_eq.mpr h2.symm).eq
    exact not_strictAnti_of_wellFoundedLT c hc'
  intro y
  have hy : y ∈ closure {ξ} := specializes_iff_mem_closure.mp (hξ y)
  exact (hc.isClosed_range.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr ⟨ξ, hfix⟩)) hy

end MulRigidity

namespace G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Textbook leaf (Mumford, *Abelian varieties*, §4, Application 2 / §6, over an algebraically
closed field; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2, over any field;
locators UNVERIFIED): multiplication by `n ≠ 0` is an isogeny** (finite and surjective, of degree
`n^{2g}`), stated in characteristic `0`. The degree is dropped, so this is a consequence of the
published statement. -/
def MulIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)

end G0FibreSimple

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Leaf (Mumford, *Abelian varieties*, §4 Application 2 and §6: `n_X` is separable when
`char k ∤ n`; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2: `n_A` is étale iff
`char k ∤ n`; locators UNVERIFIED).** In characteristic `0`, `[n]` is étale for `n ≠ 0`. A
consequence of the published statement (only characteristic `0`). -/
def MulEtale : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    Etale ((n : PkgI3.AbVar.End A).hom).left

/-- **Leaf (the infinitesimal half of `MulEtale`; Mumford §4: `d(n_X) = n` on the tangent space
at `0`, so `n_X^* ω = n ω` for invariant differentials; locator UNVERIFIED).** In characteristic
`0`, `[n]` is formally unramified (`Ω_{[n]} = 0`) for `n ≠ 0`. Implied by `MulEtale`
(`mulUnramified_of_mulEtale`). -/
def MulUnramified : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    FormallyUnramified ((n : PkgI3.AbVar.End A).hom).left

/-- **Leaf (dimension theory; Mumford §4 / Milne, *Abelian varieties*, Prop. 8.1: a homomorphism
of abelian varieties of the same dimension with finite kernel is surjective, an isogeny; locators
UNVERIFIED).** A locally quasi-finite endomorphism of an abelian variety is surjective
(any characteristic). -/
def QuasiFiniteEndSurjective : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (f : PkgI3.AbVar.End A),
    LocallyQuasiFinite f.hom.left → Surjective f.hom.left

theorem mulUnramified_of_mulEtale (h : MulEtale) : MulUnramified := by
  intro k _ _ A n hn
  have := h k A n hn
  infer_instance

/-- **`MulIsogeny` from `MulEtale`** (glue proved here). -/
theorem mulIsogeny_of_mulEtale (h : MulEtale) : G0FibreSimple.MulIsogeny := by
  intro k _ _ A n hn
  have := h k A n hn
  have := isProper_left A A ((n : PkgI3.AbVar.End A).hom)
  have := locallyQuasiFinite_of_formallyUnramified ((n : PkgI3.AbVar.End A).hom).left
  exact isIsogenyMor_of_lqf_of_isOpenMap A _ (Scheme.Hom.isOpenMap _)

/-- **`MulIsogeny` from `MulUnramified` and `QuasiFiniteEndSurjective`** (glue proved here). -/
theorem mulIsogeny_of_mulUnramified (h1 : MulUnramified) (h2 : QuasiFiniteEndSurjective) :
    G0FibreSimple.MulIsogeny := by
  intro k _ _ A n hn
  have := h1 k A n hn
  have := isProper_left A A ((n : PkgI3.AbVar.End A).hom)
  have := locallyQuasiFinite_of_formallyUnramified ((n : PkgI3.AbVar.End A).hom).left
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, h2 k A _ inferInstance⟩

/-- **`QuasiFiniteEndSurjective` holds** (proved from Mathlib; it is not a leaf). -/
theorem quasiFiniteEndSurjective : QuasiFiniteEndSurjective := by
  intro k _ A f hf
  have := isProper_left A A f.hom
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := A.X.hom)
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : IsNoetherian A.X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian A.X.hom }
  exact ⟨surjective_of_lqf_self f.hom.left f.hom.left.isClosedMap⟩

/-- **`MulIsogeny` from the single leaf `MulUnramified`** (glue proved here). -/
theorem mulIsogeny_of_mulUnramified' (h : MulUnramified) : G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_mulUnramified h quasiFiniteEndSurjective

end MulRigidity


/-! ## `MulUnramified` reduced to a statement at the origin of the kernel `A[n]` -/

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type} [Field K]

/-- The unit section `Spec K → ker f = A ×_{f, A, e} Spec K` of the kernel of a homomorphism. -/
def kerUnit (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    𝟙_ (Over (Spec (.of K))) ⟶ pullback f η[A.X] :=
  pullback.lift η[A.X] (𝟙 _) (by rw [IsMonHom.one_hom, Category.id_comp])

/-- `(x, y) ↦ x⁻¹ y : A ×_{f, A, f} A → ker f`. -/
def diffKer (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    pullback f f ⟶ pullback f η[A.X] :=
  pullback.lift ((pullback.fst f f)⁻¹ * pullback.snd f f) (toUnit _) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, pullback.condition, inv_mul_cancel, Hom.one_def])

/-- **The diagonal of a homomorphism `f` is the base change of the unit section of `ker f`**
along `(x, y) ↦ x⁻¹ y` (the square is cartesian: `x⁻¹ y = e ⇔ x = y`). -/
theorem diagonal_isPullback (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    IsPullback (toUnit A.X) (pullback.diagonal f) (kerUnit A f) (diffKer A f) := by
  have key : ∀ {T : Over (Spec (.of K))} (a : T ⟶ pullback f f),
      a ≫ diffKer A f ≫ pullback.fst f η[A.X] = (a ≫ pullback.fst f f)⁻¹ * (a ≫ pullback.snd f f) := by
    intro T a
    simp only [diffKer, pullback.lift_fst, MonObj.comp_mul, GrpObj.comp_inv]
  refine IsPullback.flip ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ pullback.fst f f)
    ?_ ?_ ?_⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, key, pullback.diagonal_fst, pullback.diagonal_snd, inv_mul_cancel,
        Category.assoc]
      simp only [kerUnit, pullback.lift_fst, Hom.one_def]
    · exact toUnit_unique _ _
  · intro c
    have hc := congrArg (· ≫ pullback.fst f η[A.X]) c.condition
    simp only [Category.assoc] at hc
    simp only [kerUnit, pullback.lift_fst] at hc
    rw [key, toUnit_unique c.snd (toUnit _), ← Hom.one_def, inv_mul_eq_one] at hc
    apply pullback.hom_ext
    · simp
    · simp [hc]
  · intro c
    exact toUnit_unique _ _
  · intro c m hm _
    rw [← hm, Category.assoc, pullback.diagonal_fst, Category.comp_id]

/-- **Glue.** If the unit section of `ker f` is an open immersion, the homomorphism `f` is formally
unramified (its diagonal is an open immersion, as a base change of the unit section). -/
theorem formallyUnramified_of_kerUnit (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f]
    (h : IsOpenImmersion (kerUnit A f).left) : FormallyUnramified f.left := by
  have hP := (Over.forget _).map_isPullback (diagonal_isPullback A f)
  have h1 : IsOpenImmersion (pullback.diagonal f).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hP h
  let e := PreservesPullback.iso (Over.forget (Spec (.of K))) f f
  have he : pullback.diagonal f.left = (pullback.diagonal f).left ≫ e.hom := by
    apply pullback.hom_ext
    · rw [pullback.diagonal_fst, Category.assoc]
      erw [PreservesPullback.iso_hom_fst]
      show 𝟙 _ = (pullback.diagonal f).left ≫ (pullback.fst f f).left
      rw [← Over.comp_left, pullback.diagonal_fst]
      rfl
    · rw [pullback.diagonal_snd, Category.assoc]
      erw [PreservesPullback.iso_hom_snd]
      show 𝟙 _ = (pullback.diagonal f).left ≫ (pullback.snd f f).left
      rw [← Over.comp_left, pullback.diagonal_snd]
      rfl
  have : IsOpenImmersion (pullback.diagonal f.left) := by rw [he]; infer_instance
  infer_instance

/-- **Leaf (Mumford, *Abelian varieties*, §4, Application 2 and §6: `A[n]` is étale, of order
`n^{2g}`, when `char k ∤ n`; equivalently `d[n] = n` on the tangent space at `0`; Milne, *Abelian
varieties* (Cornell–Silverman 1986), Thm 8.2; locators UNVERIFIED).** In characteristic `0`, for
`n ≠ 0`, the unit section of the kernel `A[n] = A ×_{[n], A, e} Spec k` is an open immersion
(`A[n]` is unramified over `k` at the origin: its tangent space there, `ker(n · : Lie A → Lie A)`,
vanishes). A consequence of "`A[n]` is étale over `k`" (a section of an étale separated morphism
is an open immersion; `kerUnitOpen_of_mulEtale`). -/
def KerUnitOpen : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    IsOpenImmersion (kerUnit A ((n : PkgI3.AbVar.End A).hom)).left

/-- A section of a formally unramified morphism locally of finite type is an open immersion
(Stacks 024T; from Mathlib's `isOpenImmersion_diagonal` and
`MorphismProperty.hasOfPostcompProperty_iff_le_diagonal`). -/
theorem isOpenImmersion_of_section {X Y : Scheme} (s : Y ⟶ X) (q : X ⟶ Y)
    [FormallyUnramified q] [LocallyOfFiniteType q] (h : s ≫ q = 𝟙 _) : IsOpenImmersion s := by
  set gr : Y ⟶ pullback (s ≫ q) q := pullback.lift (𝟙 Y) s (by simp)
  have e : s = gr ≫ pullback.snd _ _ := by simp [gr]
  rw [e]
  have h1 : IsOpenImmersion gr :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pullback_lift_diagonal_isPullback s q)
      (FormallyUnramified.isOpenImmersion_diagonal q)
  have h2 : IsOpenImmersion (pullback.snd (s ≫ q) q) :=
    MorphismProperty.pullback_snd (P := @IsOpenImmersion) _ _
      (by rw [h]; exact (inferInstance : IsOpenImmersion (𝟙 Y)))
  infer_instance

/-- **`KerUnitOpen` is a consequence of `MulEtale`** (so it is implied by the published
statement): the kernel is a base change of `[n]`, hence étale over `k`, and its unit section is a
section of an étale morphism. -/
theorem kerUnitOpen_of_mulEtale (h : MulEtale) : KerUnitOpen := by
  intro k _ _ A n hn
  have hE : Etale ((n : PkgI3.AbVar.End A).hom).left := h k A n hn
  have hP := (Over.forget _).map_isPullback
    (IsPullback.of_hasPullback ((n : PkgI3.AbVar.End A).hom) η[A.X])
  have : Etale (pullback.snd ((n : PkgI3.AbVar.End A).hom) η[A.X]).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hP hE
  refine isOpenImmersion_of_section _ (pullback.snd ((n : PkgI3.AbVar.End A).hom) η[A.X]).left ?_
  rw [← Over.comp_left]
  simp [kerUnit]

/-- `MulUnramified` from `KerUnitOpen` (glue proved here). -/
theorem mulUnramified_of_kerUnitOpen (h : KerUnitOpen) : MulUnramified := by
  intro k _ _ A n hn
  exact formallyUnramified_of_kerUnit A _ (h k A n hn)

/-- **`MulIsogeny` from the single leaf `KerUnitOpen`.** -/
theorem mulIsogeny_of_kerUnitOpen (h : KerUnitOpen) : G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_mulUnramified' (mulUnramified_of_kerUnitOpen h)

end MulRigidity

#print axioms MulRigidity.mulIsogeny_of_mulEtale
#print axioms MulRigidity.mulIsogeny_of_mulUnramified
#print axioms MulRigidity.mulIsogeny_of_mulUnramified'
#print axioms MulRigidity.mulIsogeny_of_kerUnitOpen
#print axioms MulRigidity.kerUnitOpen_of_mulEtale

/-! ## Consumers in g0-fibresimple: FS2 closed, FS3 from T6 and `KerUnitOpen`

`EndDivisionOfSchemeIso`, `EndDivisionOfEnd0Division` and the proofs
`endDivisionOfSchemeIso_of_rigidity`, `end0Division_of_homFree` are copied verbatim from
scratch/g0-fibresimple/FibreSimple.lean (§4″, §4‴). -/

namespace G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Quaternion TensorProduct

/-- **Glue piece FS2 (rigidity: simplicity is invariant under scheme isomorphism).** If two
abelian varieties over `k` have isomorphic underlying `k`-schemes, and every nonzero endomorphism
of one is an isogeny, the same holds for the other. *Why true* (STANDARD): by rigidity
(Mumford, *Abelian varieties*, §4 Cor. 1, UNVERIFIED number) a `k`-isomorphism `φ` followed by the
translation by `-φ(0)` is an isomorphism of group schemes, and conjugation by it identifies the
endomorphism rings, preserving "finite and surjective". `FibreOver` gives only an isomorphism of
`ℚ̄`-schemes, so this step is needed. Glue. -/
def EndDivisionOfSchemeIso : Prop :=
  ∀ (k : Type) [Field k] (A B : PkgI3.AbVar k), Nonempty (A.X ≅ B.X) →
    PkgI3.EndDivision B → PkgI3.EndDivision A

/-- **Glue piece FS3 (`End⁰(A)` a division algebra ⇒ every nonzero endomorphism is an isogeny;
Mumford §19 Cor. 2 direction "End⁰ division ⇒ simple", UNVERIFIED number).** *Why true*
(STANDARD): `End(A)` is torsion-free (Mumford §19 Thm 3), so `f ≠ 0` gives `1 ⊗ f ≠ 0` in
`End⁰(A)`; a unit there gives `g` with `g ∘ f = [n]`, `n ≠ 0`; `[n]` is an isogeny (Mumford §4),
so `ker f` is finite, `f(A)` is closed of dimension `dim A`, hence `f` is surjective, and
proper quasi-finite, hence finite. Glue (textbook). -/
def EndDivisionOfEnd0Division : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k),
    (∀ x : PkgI3.AbVar.End0 A, x ≠ 0 → IsUnit x) → PkgI3.EndDivision A
/-- **FS3 is proved from T6 (`PkgI3.HomFreeFinite`) and `MulIsogeny`.** If `1 ⊗ f` is a unit of
`End⁰(A)` with inverse `u⁻¹`, clearing denominators gives `g` and `s ≠ 0` with `g ∘ f = [s]` and
`f ∘ g = [s]` (freeness of `End(A)` makes `m ↦ 1 ⊗ m` injective). `[s]` is finite and surjective,
so `f` is finite (Mathlib `IsFinite.of_comp`, `g` separated since `A` is proper) and surjective
(`Surjective.of_comp`). -/
theorem end0Division_of_homFree (hHF : PkgI3.HomFreeFinite) (hMul : MulIsogeny) :
    EndDivisionOfEnd0Division := by
  intro k _ _ A hdiv f hf
  have hfree : Module.Free ℤ (PkgI3.AbVar.End A) := (hHF k A A).1
  let F := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) F :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ F).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  have hinj : ∀ m : PkgI3.AbVar.End A, (1 : ℚ) ⊗ₜ[ℤ] m = 0 → m = 0 := by
    intro m hm
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) F).mp hm
    rw [Submonoid.smul_def] at hs'
    exact (smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s')
  have e1 : ∀ x y : PkgI3.AbVar.End A,
      (1 : ℚ) ⊗ₜ[ℤ] (x * y) = ((1 : ℚ) ⊗ₜ[ℤ] x) * ((1 : ℚ) ⊗ₜ[ℤ] y) := by
    intro x y; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hx : (1 : ℚ) ⊗ₜ[ℤ] f ≠ 0 := fun h => hf (hinj f h)
  obtain ⟨u, hu⟩ := hdiv _ hx
  obtain ⟨⟨g, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) F (↑u⁻¹ : PkgI3.AbVar.End0 A)
  have hs' : (1 : ℚ) ⊗ₜ[ℤ] g = (s : ℤ) • (↑u⁻¹ : PkgI3.AbVar.End0 A) := by
    rw [Submonoid.smul_def] at hs; exact hs.symm
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hcast : (1 : ℚ) ⊗ₜ[ℤ] ((s : ℤ) : PkgI3.AbVar.End A) = ((s : ℤ) : PkgI3.AbVar.End0 A) :=
    map_intCast (Algebra.TensorProduct.includeRight :
      PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A) _
  have hgf : g * f = ((s : ℤ) : PkgI3.AbVar.End A) := by
    apply sub_eq_zero.mp; apply hinj
    rw [TensorProduct.tmul_sub, e1, hs', ← hu, smul_mul_assoc, Units.inv_mul, hcast,
      zsmul_eq_mul, _root_.mul_one, sub_self]
  have hfg : f * g = ((s : ℤ) : PkgI3.AbVar.End A) := by
    apply sub_eq_zero.mp; apply hinj
    rw [TensorProduct.tmul_sub, e1, hs', ← hu, mul_smul_comm, Units.mul_inv, hcast,
      zsmul_eq_mul, _root_.mul_one, sub_self]
  obtain ⟨hfin, hsurj⟩ := hMul k A (s : ℤ) hs0
  rw [← hgf] at hfin
  rw [← hfg] at hsurj
  change IsFinite (f.hom ≫ g.hom).left at hfin
  change Surjective (g.hom ≫ f.hom).left at hsurj
  rw [Over.comp_left] at hfin hsurj
  have hsep : IsSeparated (g.hom.left ≫ A.X.hom) := by rw [Over.w g.hom]; infer_instance
  have : IsSeparated g.hom.left := IsSeparated.of_comp (f := g.hom.left) (g := A.X.hom)
  exact ⟨IsFinite.of_comp f.hom.left g.hom.left, Surjective.of_comp g.hom.left f.hom.left⟩

/-- **FS2 is proved from `RigidityHom`.** For a `k`-isomorphism `e : A.X ≅ B.X`, put
`b = e(0)`, `ψ = e - b` and `ψ' = e⁻¹ ∘ (· + b)` (translations, in the group of morphisms into
the group object). They are inverse, preserve the identity, hence are homomorphisms by rigidity;
conjugation by them carries nonzero endomorphisms of `A` to nonzero endomorphisms of `B`, and
"finite and surjective" back. -/
theorem endDivisionOfSchemeIso_of_rigidity (hR : RigidityHom) : EndDivisionOfSchemeIso := by
  intro k _ A B ⟨e⟩ hB
  set b : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ B.X := η[A.X] ≫ e.hom with hb
  set ψ : A.X ⟶ B.X := e.hom * (toUnit A.X ≫ b⁻¹) with hψdef
  set ψ' : B.X ⟶ A.X := (𝟙 B.X * (toUnit B.X ≫ b)) ≫ e.inv with hψ'def
  have hu : η[A.X] ≫ toUnit A.X = 𝟙 _ := toUnit_unique _ _
  have hu' : η[B.X] ≫ toUnit B.X = 𝟙 _ := toUnit_unique _ _
  have h1 : ψ ≫ ψ' = 𝟙 A.X := by
    rw [hψ'def, ← Category.assoc, MonObj.comp_mul, Category.comp_id,
      ← Category.assoc, toUnit_unique (ψ ≫ toUnit B.X) (toUnit A.X), hψdef, _root_.mul_assoc,
      ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one, e.hom_inv_id]
  have h2 : ψ' ≫ ψ = 𝟙 B.X := by
    have k1 : ψ' ≫ e.hom = 𝟙 B.X * (toUnit B.X ≫ b) := by
      rw [hψ'def, Category.assoc, e.inv_hom_id, Category.comp_id]
    have k2 : ψ' ≫ toUnit A.X ≫ b⁻¹ = toUnit B.X ≫ b⁻¹ := by
      rw [← Category.assoc, toUnit_unique (ψ' ≫ toUnit A.X) (toUnit B.X)]
    rw [hψdef, MonObj.comp_mul, k1, k2, _root_.mul_assoc, ← MonObj.comp_mul, mul_inv_cancel,
      MonObj.comp_one, _root_.mul_one]
  have h3 : η[A.X] ≫ ψ = η[B.X] := by
    rw [hψdef, MonObj.comp_mul, ← Category.assoc, hu, Category.id_comp, ← hb, mul_inv_cancel,
      MonObj.one_eq_one]
  have h4 : η[B.X] ≫ ψ' = η[A.X] := by
    rw [hψ'def, ← Category.assoc, MonObj.comp_mul, Category.comp_id, ← Category.assoc, hu',
      Category.id_comp, MonObj.one_eq_one, _root_.one_mul, hb, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  have hψ : IsMonHom ψ := hR k A B ψ h3
  have hψ' : IsMonHom ψ' := hR k B A ψ' h4
  intro f hf
  let g : PkgI3.AbVar.End B := PkgI3.AbVar.Hom.mk' (ψ' ≫ f.hom ≫ ψ)
  have hfg : f.hom = ψ ≫ g.hom ≫ ψ' := by
    change f.hom = ψ ≫ (ψ' ≫ f.hom ≫ ψ) ≫ ψ'
    simp only [Category.assoc, h1, Category.comp_id]
    rw [← Category.assoc, h1, Category.id_comp]
  have hg0 : g ≠ 0 := by
    intro hg
    apply hf
    apply PkgI3.AbVar.Hom.ext'
    rw [hfg, hg, PkgI3.AbVar.Hom.hom_zero, MonObj.one_comp, MonObj.comp_one,
      PkgI3.AbVar.Hom.hom_zero]
  obtain ⟨hfin, hsurj⟩ := hB g hg0
  have : IsIso ψ.left := ⟨ψ'.left, by rw [← Over.comp_left, h1]; rfl,
    by rw [← Over.comp_left, h2]; rfl⟩
  have : IsIso ψ'.left := ⟨ψ.left, by rw [← Over.comp_left, h2]; rfl,
    by rw [← Over.comp_left, h1]; rfl⟩
  rw [hfg]
  show IsFinite (ψ ≫ g.hom ≫ ψ').left ∧ Surjective (ψ ≫ g.hom ≫ ψ').left
  rw [Over.comp_left, Over.comp_left]
  exact ⟨inferInstance, inferInstance⟩


/-- **FS2 holds unconditionally** (`RigidityHom` is proved, `rigidityHom`). -/
theorem endDivisionOfSchemeIso : EndDivisionOfSchemeIso :=
  endDivisionOfSchemeIso_of_rigidity rigidityHom

/-- **FS3 from the leaf T6 (`PkgI3.HomFreeFinite`) and the leaf `KerUnitOpen`.** -/
theorem end0Division_of_homFree_kerUnitOpen (hHF : PkgI3.HomFreeFinite)
    (h : MulRigidity.KerUnitOpen) : EndDivisionOfEnd0Division :=
  end0Division_of_homFree hHF (MulRigidity.mulIsogeny_of_kerUnitOpen h)

end G0FibreSimple

#print axioms G0FibreSimple.endDivisionOfSchemeIso
#print axioms G0FibreSimple.end0Division_of_homFree_kerUnitOpen

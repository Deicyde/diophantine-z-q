import ZInQKernel.Contrib.OneProof.MumfordRigidity

/-!
# group-law, I: gluing local group laws on a family with abelian-variety fibres over a reduced base

Setting: `F → S` proper and smooth with a section `e`, every field fibre an abelian variety with origin `e(s)`
(`FibreHyp F e`, the fibre hypothesis of `ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw`).

A **local group law** (`LocalLaw F e`) is an open immersion `j : T → S` with a base change `P` of `F` along `j`
(`IsPullback q P.hom F.hom j`) carrying a group object structure whose identity is the base change of `e`.

Main result (`exists_grpObj_of_localLaws`): if every point of `S` lies in the image of a local group law and `F`,
`F ×_S F`, `(F ×_S F) ×_S F` are reduced, then `F` is a group object of `Over S` with identity `e`.

Proof. On a field point of `P ×_T P` the multiplication of `P` is the multiplication of the abelian-variety fibre
(`mulP_pt`): the fibre identification is a homomorphism by the chain's `isGrpFibre_of_rigidity` (clause (b), from the
kernel's field-level rigidity). So the local multiplications agree on every field point of the overlaps, which are
reduced: they glue (`glue_of_rel`, Mathlib's `Scheme.Cover.glueMorphisms` and the chain's `hom_ext_pts`). The same
for the inverses (`invP_pt`). The group axioms of the glued maps hold on every field point, by the axioms of the
fibres, hence hold (`hom_ext_pts` on the reduced sources).

No hypothesis beyond Mathlib and the chain's proved lemmas.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.GroupLaw

open LeafQM.AV.R1UnivRigid PkgI3

/-- `Spec K` over itself (the source of `K`-points of a `K`-scheme). -/
abbrev pt0 (K : Type) [Field K] : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 (Spec (CommRingCat.of K)))

/-- The fibre hypothesis of `MumfordGroupLaw`. -/
def FibreHyp {S : Scheme.{0}} (F : Over S) (e : S ⟶ F.left) : Prop :=
  ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S),
    ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g

/-! ## §1 Points of a fibre -/

section Pts

variable {S : Scheme.{0}} {F : Over S} {K : Type} [Field K] {σ : Spec (CommRingCat.of K) ⟶ S}
  {A : AbVar K} {g : A.X.left ⟶ F.left}

/-- The `K`-point of the fibre `A` through a field point `x` of `F` over `σ`. -/
def fpt (hpb : IsPullback g A.X.hom F.hom σ) (x : Spec (CommRingCat.of K) ⟶ F.left)
    (hx : x ≫ F.hom = σ) : pt0 K ⟶ A.X :=
  Over.homMk (hpb.lift x (𝟙 _) (by simp [hx])) (by simp)

@[reassoc (attr := simp)]
theorem fpt_left_g (hpb : IsPullback g A.X.hom F.hom σ) (x : Spec (CommRingCat.of K) ⟶ F.left)
    (hx : x ≫ F.hom = σ) : (fpt hpb x hx).left ≫ g = x :=
  hpb.lift_fst _ _ _

theorem fpt_eq (hpb : IsPullback g A.X.hom F.hom σ) {x : Spec (CommRingCat.of K) ⟶ F.left}
    (hx : x ≫ F.hom = σ) {c : pt0 K ⟶ A.X} (h : c.left ≫ g = x) : fpt hpb x hx = c := by
  apply Over.OverMorphism.ext
  apply hpb.hom_ext
  · rw [fpt_left_g, h]
  · change hpb.lift x (𝟙 _) _ ≫ A.X.hom = _
    rw [hpb.lift_snd]
    exact (Over.w c).symm

theorem fpt_congr (hpb : IsPullback g A.X.hom F.hom σ) {x x' : Spec (CommRingCat.of K) ⟶ F.left}
    (hx : x ≫ F.hom = σ) (hx' : x' ≫ F.hom = σ) (h : x = x') : fpt hpb x hx = fpt hpb x' hx' := by
  subst h; rfl

theorem pt_ext (hpb : IsPullback g A.X.hom F.hom σ) {c c' : pt0 K ⟶ A.X}
    (h : c.left ≫ g = c'.left ≫ g) : c = c' := by
  apply Over.OverMorphism.ext
  apply hpb.hom_ext h
  rw [Over.w c, Over.w c']

open scoped CategoryTheory.MonObj in
/-- The unit point of `A` over `ptObj K` composed with `g`, as the unit point over `pt0`. -/
theorem one_pt0_comp {Z : Scheme.{0}} (g : A.X.left ⟶ Z) (z : Spec (CommRingCat.of K) ⟶ Z)
    (h : (1 : A.Pt K).left ≫ g = z) : (1 : pt0 K ⟶ A.X).left ≫ g = z := by
  change (toUnit (pt0 K) ≫ η[A.X]).left ≫ g = z
  change (toUnit (AbVar.ptObj (K := K) K) ≫ η[A.X]).left ≫ g = z at h
  rw [Over.comp_left, Over.toUnit_left] at h ⊢
  simp only [AbVar.ptObj, Over.mk_hom, Algebra.algebraMap_self] at h
  simpa using h

theorem one_ptObj_hom : (1 : A.Pt K).left ≫ A.X.hom = 𝟙 _ := by
  have : (1 : A.Pt K).left ≫ A.X.hom = (AbVar.ptObj (K := K) K).hom := Over.w _
  rw [this]
  simp [AbVar.ptObj, Algebra.algebraMap_self]

theorem one_ptObj_hom_comp {Z : Scheme.{0}} (τ : Spec (CommRingCat.of K) ⟶ Z) :
    (1 : A.Pt K).left ≫ A.X.hom ≫ τ = τ := by
  rw [← Category.assoc, one_ptObj_hom]
  exact Category.id_comp τ

end Pts

/-! ## §2 Base change of the fibre hypothesis -/

section BaseChange

variable {S T : Scheme.{0}} {F : Over S} {e : S ⟶ F.left} {j : T ⟶ S} {P : Over T}
  {q : P.left ⟶ F.left}

/-- The fibre identification transported along a base change `P = F ×_S T`. -/
theorem isAbVarFibre_of_isPullback (hq : IsPullback q P.hom F.hom j) {eP : T ⟶ P.left}
    (heP : eP ≫ P.hom = 𝟙 T) (hq' : eP ≫ q = j ≫ e)
    {K : Type} [Field K] (τ : Spec (CommRingCat.of K) ⟶ T) (A : AbVar K) (g : A.X.left ⟶ F.left)
    (h : IsAbVarFibre F e (τ ≫ j) A g) :
    IsAbVarFibre P eP τ A (hq.lift g (A.X.hom ≫ τ) (by rw [h.1.w, Category.assoc])) := by
  obtain ⟨hpb, h1⟩ := h
  refine ⟨IsPullback.of_right (by rwa [hq.lift_fst]) (hq.lift_snd _ _ _) hq, ?_⟩
  apply hq.hom_ext
  · rw [Category.assoc, hq.lift_fst]
    refine h1.trans ?_
    show (τ ≫ j) ≫ e = (τ ≫ eP) ≫ q
    rw [Category.assoc, Category.assoc, hq']
  · rw [Category.assoc, hq.lift_snd, one_ptObj_hom_comp]
    show τ = (τ ≫ eP) ≫ P.hom
    rw [Category.assoc, heP, Category.comp_id]

/-- The fibre hypothesis passes to base changes. -/
theorem fibreHyp_of_isPullback (hq : IsPullback q P.hom F.hom j) {eP : T ⟶ P.left}
    (heP : eP ≫ P.hom = 𝟙 T) (hq' : eP ≫ q = j ≫ e) (h : FibreHyp F e) : FibreHyp P eP := by
  intro K _ τ
  obtain ⟨A, g, hA⟩ := h K (τ ≫ j)
  exact ⟨A, _, isAbVarFibre_of_isPullback hq heP hq' τ A g hA⟩

end BaseChange

/-! ## §3 Local group laws and their values on field points -/

/-- A group law on the base change of `F` to an open of `S`, with identity the base change of `e`. -/
structure LocalLaw {S : Scheme.{0}} (F : Over S) (e : S ⟶ F.left) where
  /-- the open -/
  T : Scheme.{0}
  /-- its inclusion -/
  j : T ⟶ S
  [isOpenImm : IsOpenImmersion j]
  /-- the base change -/
  P : Over T
  /-- its projection to `F` -/
  q : P.left ⟶ F.left
  hq : IsPullback q P.hom F.hom j
  /-- the group law -/
  grp : GrpObj P
  hη : η[P].left ≫ q = j ≫ e

attribute [instance] LocalLaw.isOpenImm LocalLaw.grp

section LocalPts

variable {S : Scheme.{0}} {F : Over S} {e : S ⟶ F.left} (L : LocalLaw F e)

theorem LocalLaw.isProper [IsProper F.hom] : IsProper L.P.hom :=
  MorphismProperty.of_isPullback L.hq inferInstance

theorem LocalLaw.smooth [Smooth F.hom] : Smooth L.P.hom :=
  MorphismProperty.of_isPullback L.hq inferInstance

theorem LocalLaw.eta_sec : η[L.P].left ≫ L.P.hom = 𝟙 L.T := Over.w η[L.P]

open scoped CategoryTheory.MonObj

/-- **The multiplication of a local group law on field points** is that of the abelian-variety fibre. -/
theorem mulP_pt [IsProper F.hom] [Smooth F.hom] {K : Type} [Field K]
    (τ : Spec (CommRingCat.of K) ⟶ L.T) (y₁ y₂ : Spec (CommRingCat.of K) ⟶ L.P.left)
    (h₁ : y₁ ≫ L.P.hom = τ) (h₂ : y₂ ≫ L.P.hom = τ) {σ : Spec (CommRingCat.of K) ⟶ S}
    (hσ : τ ≫ L.j = σ) (A : AbVar K) (g : A.X.left ⟶ F.left) (hA : IsAbVarFibre F e σ A g) :
    (pullback.lift y₁ y₂ (h₁.trans h₂.symm) : Spec (CommRingCat.of K) ⟶ (L.P ⊗ L.P).left) ≫
        μ[L.P].left ≫ L.q =
      (fpt hA.1 (y₁ ≫ L.q) (by rw [Category.assoc, L.hq.w, ← Category.assoc, h₁, hσ]) *
        fpt hA.1 (y₂ ≫ L.q) (by rw [Category.assoc, L.hq.w, ← Category.assoc, h₂, hσ])).left ≫ g := by
  have := L.isProper
  have := L.smooth
  subst hσ
  set g' := L.hq.lift g (A.X.hom ≫ τ) (by rw [hA.1.w, Category.assoc]) with hg'
  have hA' := isAbVarFibre_of_isPullback L.hq L.eta_sec L.hη τ A g hA
  obtain ⟨φ, hφ₁, hφ₂, hφμ⟩ := isGrpFibre_of_rigidity L.P τ A g' hA'
  set c₁ := fpt hA.1 (y₁ ≫ L.q) (by rw [Category.assoc, L.hq.w, ← Category.assoc, h₁])
  set c₂ := fpt hA.1 (y₂ ≫ L.q) (by rw [Category.assoc, L.hq.w, ← Category.assoc, h₂])
  have hc : ∀ (c : pt0 K ⟶ A.X) (y : Spec (CommRingCat.of K) ⟶ L.P.left), y ≫ L.P.hom = τ →
      c.left ≫ g = y ≫ L.q → c.left ≫ g' = y := by
    intro c y hy hcy
    apply L.hq.hom_ext
    · rw [Category.assoc, L.hq.lift_fst, hcy]
    · rw [Category.assoc, L.hq.lift_snd, ← Category.assoc, Over.w c, hy]
      exact Category.id_comp _
  set u : Spec (CommRingCat.of K) ⟶ (L.P ⊗ L.P).left := pullback.lift y₁ y₂ (h₁.trans h₂.symm)
  have hu₁ : u ≫ (fst L.P L.P).left = y₁ := pullback.lift_fst _ _ _
  have hu₂ : u ≫ (snd L.P L.P).left = y₂ := pullback.lift_snd _ _ _
  have e₁ : c₁.left ≫ g' = u ≫ (fst L.P L.P).left := by
    rw [hu₁]; exact hc c₁ y₁ h₁ (fpt_left_g _ _ _)
  have e₂ : c₂.left ≫ g' = u ≫ (snd L.P L.P).left := by
    rw [hu₂]; exact hc c₂ y₂ h₂ (fpt_left_g _ _ _)
  have hx : (lift c₁ c₂).left ≫ φ = u := by
    rw [lift_comp_φ c₁ c₂ (fst L.P L.P) (snd L.P L.P) u φ hφ₁ hφ₂ e₁ e₂, lift_fst_snd, Over.id_left,
      Category.comp_id]
  rw [← hx, Category.assoc, ← reassoc_of% hφμ, hg', L.hq.lift_fst, Hom.mul_def, Over.comp_left,
    Category.assoc]

/-- **The inverse of a local group law on field points** is that of the abelian-variety fibre. -/
theorem invP_pt [IsProper F.hom] [Smooth F.hom] {K : Type} [Field K]
    (τ : Spec (CommRingCat.of K) ⟶ L.T) (y : Spec (CommRingCat.of K) ⟶ L.P.left)
    (hy : y ≫ L.P.hom = τ) {σ : Spec (CommRingCat.of K) ⟶ S}
    (hσ : τ ≫ L.j = σ) (A : AbVar K) (g : A.X.left ⟶ F.left) (hA : IsAbVarFibre F e σ A g) :
    y ≫ ι[L.P].left ≫ L.q =
      (fpt hA.1 (y ≫ L.q) (by rw [Category.assoc, L.hq.w, ← Category.assoc, hy, hσ]))⁻¹.left ≫ g := by
  have hy' : (y ≫ ι[L.P].left) ≫ L.P.hom = τ := by
    rw [Category.assoc, Over.w ι[L.P], hy]
  have hm := mulP_pt L τ y (y ≫ ι[L.P].left) hy hy' hσ A g hA
  set c := fpt hA.1 (y ≫ L.q) (by rw [Category.assoc, L.hq.w, ← Category.assoc, hy, hσ])
  set c' := fpt hA.1 ((y ≫ ι[L.P].left) ≫ L.q)
    (by rw [Category.assoc, L.hq.w, ← Category.assoc, hy', hσ])
  -- the left side of `hm` is the identity section at `τ`
  have hl : (pullback.lift y (y ≫ ι[L.P].left) (hy.trans hy'.symm) :
      Spec (CommRingCat.of K) ⟶ (L.P ⊗ L.P).left) = y ≫ (lift (𝟙 L.P) ι[L.P]).left := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]
      change _ = y ≫ (lift (𝟙 L.P) ι[L.P]).left ≫ (fst L.P L.P).left
      rw [← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
    · rw [pullback.lift_snd, Category.assoc]
      change _ = y ≫ (lift (𝟙 L.P) ι[L.P]).left ≫ (snd L.P L.P).left
      rw [← Over.comp_left, lift_snd]
  have e1 : y ≫ (lift (𝟙 L.P) ι[L.P]).left ≫ μ[L.P].left ≫ L.q = σ ≫ e := by
    rw [← Over.comp_left_assoc, GrpObj.right_inv, Over.comp_left, Over.toUnit_left]
    simp only [Category.assoc]
    rw [L.hη, ← Category.assoc, ← Category.assoc, hy, hσ]
  have h1 : (c * c').left ≫ g = (1 : pt0 K ⟶ A.X).left ≫ g := by
    rw [← hm, hl, Category.assoc, e1]
    exact (one_pt0_comp g _ hA.2).symm
  have h2 : c * c' = 1 := pt_ext hA.1 h1
  have h3 : c' = c⁻¹ := by rw [eq_inv_iff_mul_eq_one, mul_comm]; exact h2
  rw [← h3]
  exact (fpt_left_g _ _ _).symm

end LocalPts

/-! ## §4 Gluing morphisms characterized on field points -/

section Glue

variable {S : Scheme.{0}} {F : Over S} {e : S ⟶ F.left} (L : S → LocalLaw F e)
  (hL : ∀ s : S, s ∈ Set.range (L s).j)

/-- The open cover of a scheme `X` over `S` by the preimages of the opens of the local laws. -/
def cov (X : Over S) : X.left.OpenCover :=
  Scheme.Cover.mkOfCovers S (fun s => pullback X.hom (L s).j) (fun s => pullback.fst _ _)
    (fun x => by
      obtain ⟨t, ht⟩ := hL (X.hom x)
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x t ht.symm
      exact ⟨X.hom x, z, hz⟩)

include hL in
/-- A field point factors through some member of the cover. -/
theorem exists_factor (X : Over S) {K : Type} [Field K] (x : Spec (CommRingCat.of K) ⟶ X.left) :
    ∃ (s : (cov L hL X).I₀) (y : Spec (CommRingCat.of K) ⟶ (cov L hL X).X s),
      y ≫ (cov L hL X).f s = x := by
  let p : Spec (CommRingCat.of K) := default
  obtain ⟨t, ht⟩ := hL (X.hom (x p))
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (x p) t ht.symm
  haveI : IsOpenImmersion ((cov L hL X).f (X.hom (x p))) :=
    show IsOpenImmersion (pullback.fst X.hom (L (X.hom (x p))).j) from inferInstance
  refine ⟨X.hom (x p), IsOpenImmersion.lift ((cov L hL X).f (X.hom (x p))) x ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p', rfl⟩
  rw [Subsingleton.elim p' p]
  exact ⟨z, hz⟩

include hL in
/-- **Gluing.** Morphisms on the members of the cover, related on field points to the field points of `X` by a
relation with unique values, glue to a morphism `X → Y` related to every field point. -/
theorem glue_of_rel (X : Over S) [IsReduced X.left] {Y : Scheme.{0}} (i : Y ⟶ S) [IsSeparated i]
    (f : ∀ s : (cov L hL X).I₀, (cov L hL X).X s ⟶ Y) (hf : ∀ s, f s ≫ i = (cov L hL X).f s ≫ X.hom)
    (R : ∀ (K : Type) [Field K], (Spec (CommRingCat.of K) ⟶ X.left) →
      (Spec (CommRingCat.of K) ⟶ Y) → Prop)
    (hR : ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ X.left) (a b), R K x a → R K x b → a = b)
    (hc : ∀ (s : (cov L hL X).I₀) (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ (cov L hL X).X s),
      R K (y ≫ (cov L hL X).f s) (y ≫ f s)) :
    ∃ m : X.left ⟶ Y, m ≫ i = X.hom ∧
      ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ X.left), R K x (x ≫ m) := by
  let 𝒰 := cov L hL X
  have hcompat : ∀ s t, pullback.fst (𝒰.f s) (𝒰.f t) ≫ f s = pullback.snd (𝒰.f s) (𝒰.f t) ≫ f t := by
    intro s t
    haveI : IsOpenImmersion (𝒰.f s) := 𝒰.map_prop s
    haveI : IsReduced (pullback (𝒰.f s) (𝒰.f t)) :=
      isReduced_of_isOpenImmersion (pullback.fst (𝒰.f s) (𝒰.f t) ≫ 𝒰.f s)
    refine hom_ext_pts i _ _ ?_ (fun K _ z => ?_)
    · rw [Category.assoc, Category.assoc, hf, hf, ← Category.assoc, ← Category.assoc,
        pullback.condition]
    · have h1 := hc s K (z ≫ pullback.fst (𝒰.f s) (𝒰.f t))
      have h2 := hc t K (z ≫ pullback.snd (𝒰.f s) (𝒰.f t))
      have hz : (z ≫ pullback.fst (𝒰.f s) (𝒰.f t)) ≫ 𝒰.f s =
          (z ≫ pullback.snd (𝒰.f s) (𝒰.f t)) ≫ 𝒰.f t := by
        rw [Category.assoc, Category.assoc, pullback.condition]
      rw [hz] at h1
      rw [← Category.assoc, ← Category.assoc]
      exact hR K _ _ _ h1 h2
  refine ⟨𝒰.glueMorphisms f hcompat, ?_, ?_⟩
  · refine Scheme.Cover.hom_ext 𝒰 _ _ (fun s => ?_)
    have := Scheme.Cover.ι_glueMorphisms 𝒰 f hcompat s
    rw [← Category.assoc]
    erw [this]
    exact hf s
  · intro K _ x
    obtain ⟨s, y, rfl⟩ := exists_factor L hL X x
    have := Scheme.Cover.ι_glueMorphisms 𝒰 f hcompat s
    rw [Category.assoc]
    erw [this]
    exact hc s K y

end Glue

/-! ## §5 The group object -/

section GrpObjOfLocal

variable {S : Scheme.{0}} {F : Over S} {e : S ⟶ F.left}

open scoped CategoryTheory.MonObj

/-- The multiplication on field points of `F ×_S F`, through the abelian-variety fibres. -/
def RMul (F : Over S) (e : S ⟶ F.left) (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ (F ⊗ F).left)
    (a : Spec (CommRingCat.of K) ⟶ F.left) : Prop :=
  ∀ (σ : Spec (CommRingCat.of K) ⟶ S) (hσ : x ≫ (F ⊗ F).hom = σ) (A : AbVar K) (g : A.X.left ⟶ F.left)
    (hA : IsAbVarFibre F e σ A g),
    a = (fpt hA.1 (x ≫ (fst F F).left) (by rw [Category.assoc, Over.w (fst F F), hσ]) *
      fpt hA.1 (x ≫ (snd F F).left) (by rw [Category.assoc, Over.w (snd F F), hσ])).left ≫ g

/-- The inverse on field points of `F`, through the abelian-variety fibres. -/
def RInv (F : Over S) (e : S ⟶ F.left) (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ F.left)
    (a : Spec (CommRingCat.of K) ⟶ F.left) : Prop :=
  ∀ (σ : Spec (CommRingCat.of K) ⟶ S) (hσ : x ≫ F.hom = σ) (A : AbVar K) (g : A.X.left ⟶ F.left)
    (hA : IsAbVarFibre F e σ A g), a = (fpt hA.1 x hσ)⁻¹.left ≫ g

theorem rMul_unique (hfib : FibreHyp F e) (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ (F ⊗ F).left)
    (a b : Spec (CommRingCat.of K) ⟶ F.left) (ha : RMul F e K x a) (hb : RMul F e K x b) : a = b := by
  obtain ⟨A, g, hA⟩ := hfib K (x ≫ (F ⊗ F).hom)
  rw [ha _ rfl A g hA, hb _ rfl A g hA]

theorem rInv_unique (hfib : FibreHyp F e) (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ F.left)
    (a b : Spec (CommRingCat.of K) ⟶ F.left) (ha : RInv F e K x a) (hb : RInv F e K x b) : a = b := by
  obtain ⟨A, g, hA⟩ := hfib K (x ≫ F.hom)
  rw [ha _ rfl A g hA, hb _ rfl A g hA]

/-- `F ×_S T` pulled back from `F ×_S F` to `P ×_T P`. -/
def psiMul (L : LocalLaw F e) : pullback (F ⊗ F).hom L.j ⟶ (L.P ⊗ L.P).left :=
  pullback.lift
    (L.hq.lift (pullback.fst _ _ ≫ (fst F F).left) (pullback.snd _ _)
      (by rw [Category.assoc, Over.w (fst F F), pullback.condition]))
    (L.hq.lift (pullback.fst _ _ ≫ (snd F F).left) (pullback.snd _ _)
      (by rw [Category.assoc, Over.w (snd F F), pullback.condition]))
    (by rw [L.hq.lift_snd, L.hq.lift_snd])

theorem psiMul_fst (L : LocalLaw F e) :
    psiMul L ≫ (fst L.P L.P).left = L.hq.lift (pullback.fst _ _ ≫ (fst F F).left) (pullback.snd _ _)
      (by rw [Category.assoc, Over.w (fst F F), pullback.condition]) :=
  pullback.lift_fst _ _ _

theorem psiMul_snd (L : LocalLaw F e) :
    psiMul L ≫ (snd L.P L.P).left = L.hq.lift (pullback.fst _ _ ≫ (snd F F).left) (pullback.snd _ _)
      (by rw [Category.assoc, Over.w (snd F F), pullback.condition]) :=
  pullback.lift_snd _ _ _

/-- `F ×_S T` identified with `P`. -/
def psiInv (L : LocalLaw F e) : pullback F.hom L.j ⟶ L.P.left :=
  L.hq.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition

variable [IsProper F.hom] [Smooth F.hom]

/-- The multiplication piece on `F ×_S F` over the open of `L`. -/
def mulPiece (L : LocalLaw F e) : pullback (F ⊗ F).hom L.j ⟶ F.left := psiMul L ≫ μ[L.P].left ≫ L.q

/-- The inverse piece on `F` over the open of `L`. -/
def invPiece (L : LocalLaw F e) : pullback F.hom L.j ⟶ F.left := psiInv L ≫ ι[L.P].left ≫ L.q

theorem mulPiece_over (L : LocalLaw F e) : mulPiece L ≫ F.hom = pullback.fst _ _ ≫ (F ⊗ F).hom := by
  have h : psiMul L ≫ (L.P ⊗ L.P).hom = pullback.snd _ _ := by
    rw [← Over.w (fst L.P L.P), ← Category.assoc, psiMul_fst, L.hq.lift_snd]
  simp only [mulPiece, Category.assoc, L.hq.w]
  rw [reassoc_of% (Over.w μ[L.P]), reassoc_of% h]
  exact pullback.condition.symm

theorem invPiece_over (L : LocalLaw F e) : invPiece L ≫ F.hom = pullback.fst _ _ ≫ F.hom := by
  rw [invPiece, Category.assoc, Category.assoc, L.hq.w, ← Category.assoc ι[L.P].left, Over.w ι[L.P],
    psiInv, L.hq.lift_snd_assoc, ← pullback.condition]

theorem mulPiece_rel (L : LocalLaw F e) (K : Type) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ pullback (F ⊗ F).hom L.j) :
    RMul F e K (y ≫ pullback.fst _ _) (y ≫ mulPiece L) := by
  intro σ hσ A g hA
  have hτ : (y ≫ pullback.snd _ _) ≫ L.j = σ := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hσ]
  have h₁ : (y ≫ psiMul L ≫ (fst L.P L.P).left) ≫ L.P.hom = y ≫ pullback.snd _ _ := by
    rw [psiMul_fst, Category.assoc, L.hq.lift_snd]
  have h₂ : (y ≫ psiMul L ≫ (snd L.P L.P).left) ≫ L.P.hom = y ≫ pullback.snd _ _ := by
    rw [psiMul_snd, Category.assoc, L.hq.lift_snd]
  have hm := mulP_pt L (y ≫ pullback.snd _ _) _ _ h₁ h₂ hτ A g hA
  have hu : (pullback.lift (y ≫ psiMul L ≫ (fst L.P L.P).left) (y ≫ psiMul L ≫ (snd L.P L.P).left)
      (h₁.trans h₂.symm) : Spec (CommRingCat.of K) ⟶ (L.P ⊗ L.P).left) = y ≫ psiMul L := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]; rfl
    · rw [pullback.lift_snd, Category.assoc]; rfl
  rw [hu] at hm
  rw [mulPiece, ← Category.assoc, hm]
  congr 3
  · exact fpt_congr _ _ _ (by rw [Category.assoc, psiMul_fst, L.hq.lift_fst, Category.assoc])
  · exact fpt_congr _ _ _ (by rw [Category.assoc, psiMul_snd, L.hq.lift_fst, Category.assoc])

theorem invPiece_rel (L : LocalLaw F e) (K : Type) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ pullback F.hom L.j) :
    RInv F e K (y ≫ pullback.fst _ _) (y ≫ invPiece L) := by
  intro σ hσ A g hA
  have hτ : (y ≫ pullback.snd _ _) ≫ L.j = σ := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hσ]
  have h₁ : (y ≫ psiInv L) ≫ L.P.hom = y ≫ pullback.snd _ _ := by
    rw [psiInv, Category.assoc, L.hq.lift_snd]
  have hi := invP_pt L (y ≫ pullback.snd _ _) (y ≫ psiInv L) h₁ hτ A g hA
  rw [invPiece, ← Category.assoc, hi]
  congr 3
  exact fpt_congr _ _ _ (by rw [psiInv, Category.assoc, L.hq.lift_fst])

variable (L : S → LocalLaw F e) (hL : ∀ s : S, s ∈ Set.range (L s).j)

/-- The two characterizations used in the axioms. -/
theorem mul_of_pts {m : (F ⊗ F).left ⟶ F.left} (hm : ∀ (K : Type) [Field K] x, RMul F e K x (x ≫ m))
    {K : Type} [Field K] {σ : Spec (CommRingCat.of K) ⟶ S} {A : AbVar K} {g : A.X.left ⟶ F.left}
    (hA : IsAbVarFibre F e σ A g) (x : Spec (CommRingCat.of K) ⟶ (F ⊗ F).left) (hσ : x ≫ (F ⊗ F).hom = σ)
    (a b : pt0 K ⟶ A.X) (ha : x ≫ (fst F F).left = a.left ≫ g) (hb : x ≫ (snd F F).left = b.left ≫ g) :
    x ≫ m = (a * b).left ≫ g := by
  rw [hm K x σ hσ A g hA, fpt_eq hA.1 _ ha.symm, fpt_eq hA.1 _ hb.symm]

theorem inv_of_pts {i : F.left ⟶ F.left} (hi : ∀ (K : Type) [Field K] x, RInv F e K x (x ≫ i))
    {K : Type} [Field K] {σ : Spec (CommRingCat.of K) ⟶ S} {A : AbVar K} {g : A.X.left ⟶ F.left}
    (hA : IsAbVarFibre F e σ A g) (x : Spec (CommRingCat.of K) ⟶ F.left) (hσ : x ≫ F.hom = σ)
    (a : pt0 K ⟶ A.X) (ha : x = a.left ≫ g) : x ≫ i = a⁻¹.left ≫ g := by
  rw [hi K x σ hσ A g hA, fpt_eq hA.1 _ ha.symm]

include hL in
/-- **The group law from local group laws** (reduced `F`, `F ×_S F`, `(F ×_S F) ×_S F`). -/
theorem exists_grpObj_of_localLaws [IsReduced F.left] [IsReduced (F ⊗ F).left]
    [IsReduced ((F ⊗ F) ⊗ F).left] (he : e ≫ F.hom = 𝟙 S) (hfib : FibreHyp F e) :
    ∃ _G : GrpObj F, η[F].left = e := by
  obtain ⟨m, hmS, hm⟩ := glue_of_rel L hL (F ⊗ F) F.hom (fun s => mulPiece (L s))
    (fun s => mulPiece_over (L s)) (RMul F e) (rMul_unique hfib) (fun s K _ y => mulPiece_rel (L s) K y)
  obtain ⟨i, hiS, hi⟩ := glue_of_rel L hL F F.hom (fun s => invPiece (L s))
    (fun s => invPiece_over (L s)) (RInv F e) (rInv_unique hfib) (fun s K _ y => invPiece_rel (L s) K y)
  let μF : F ⊗ F ⟶ F := Over.homMk m hmS
  let ηF : 𝟙_ (Over S) ⟶ F := Over.homMk e (by simpa using he)
  let ιF : F ⟶ F := Over.homMk i hiS
  have hμl : μF.left = m := rfl
  have hfst1 : ((fst (𝟙_ (Over S)) F).left) = (𝟙_ (Over S) ⊗ F).hom := by
    have := Over.w (fst (𝟙_ (Over S)) F); simpa using this
  have hsnd1 : ((snd F (𝟙_ (Over S))).left) = (F ⊗ 𝟙_ (Over S)).hom := by
    have := Over.w (snd F (𝟙_ (Over S))); simpa using this
  haveI : IsIso ((λ_ F).hom.left) := (Over.forget S).map_isIso (λ_ F).hom
  haveI : IsIso ((ρ_ F).hom.left) := (Over.forget S).map_isIso (ρ_ F).hom
  haveI : IsReduced (𝟙_ (Over S) ⊗ F).left := isReduced_of_isOpenImmersion ((λ_ F).hom.left)
  haveI : IsReduced (F ⊗ 𝟙_ (Over S)).left := isReduced_of_isOpenImmersion ((ρ_ F).hom.left)
  have hP := F.hom
  let G : GrpObj F :=
    { one := ηF
      mul := μF
      inv := ιF
      one_mul := by
        apply Over.OverMorphism.ext
        refine hom_ext_pts F.hom _ _ (by rw [Over.w, Over.w]) (fun K _ z => ?_)
        obtain ⟨A, g, hA⟩ := hfib K (z ≫ (𝟙_ (Over S) ⊗ F).hom)
        have hb := fpt_left_g hA.1 (z ≫ (snd (𝟙_ (Over S)) F).left)
          (by rw [Category.assoc, Over.w (snd _ _)])
        rw [Over.comp_left, hμl, ← Category.assoc,
          mul_of_pts hm hA _ (by rw [Category.assoc, Over.w]) 1 _ ?_ ?_, _root_.one_mul, hb, leftUnitor_hom]
        · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc,
            hfst1]
          exact (one_pt0_comp g _ hA.2).symm
        · rw [Category.assoc, ← Over.comp_left, whiskerRight_snd, hb]
      mul_one := by
        apply Over.OverMorphism.ext
        refine hom_ext_pts F.hom _ _ (by rw [Over.w, Over.w]) (fun K _ z => ?_)
        obtain ⟨A, g, hA⟩ := hfib K (z ≫ (F ⊗ 𝟙_ (Over S)).hom)
        have ha := fpt_left_g hA.1 (z ≫ (fst F (𝟙_ (Over S))).left)
          (by rw [Category.assoc, Over.w (fst _ _)])
        rw [Over.comp_left, hμl, ← Category.assoc,
          mul_of_pts hm hA _ (by rw [Category.assoc, Over.w]) _ 1 ?_ ?_, _root_.mul_one, ha, rightUnitor_hom]
        · rw [Category.assoc, ← Over.comp_left, whiskerLeft_fst, ha]
        · rw [Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, ← Category.assoc,
            hsnd1]
          exact (one_pt0_comp g _ hA.2).symm
      mul_assoc := by
        apply Over.OverMorphism.ext
        refine hom_ext_pts F.hom _ _ (by rw [Over.w, Over.w]) (fun K _ z => ?_)
        obtain ⟨A, g, hA⟩ := hfib K (z ≫ ((F ⊗ F) ⊗ F).hom)
        set σ := z ≫ ((F ⊗ F) ⊗ F).hom
        have ha := fpt_left_g hA.1 (z ≫ (fst (F ⊗ F) F ≫ fst F F).left)
          (by rw [Category.assoc, Over.w (fst (F ⊗ F) F ≫ fst F F)])
        have hb := fpt_left_g hA.1 (z ≫ (fst (F ⊗ F) F ≫ snd F F).left)
          (by rw [Category.assoc, Over.w (fst (F ⊗ F) F ≫ snd F F)])
        have hc := fpt_left_g hA.1 (z ≫ (snd (F ⊗ F) F).left)
          (by rw [Category.assoc, Over.w (snd (F ⊗ F) F)])
        set a := fpt hA.1 (z ≫ (fst (F ⊗ F) F ≫ fst F F).left) _
        set b := fpt hA.1 (z ≫ (fst (F ⊗ F) F ≫ snd F F).left) _
        set c := fpt hA.1 (z ≫ (snd (F ⊗ F) F).left) _
        have hab : (z ≫ (fst (F ⊗ F) F).left) ≫ m = (a * b).left ≫ g := by
          refine mul_of_pts hm hA _ (by rw [Category.assoc, Over.w (fst _ _)]) a b ?_ ?_
          · rw [ha, Category.assoc, Over.comp_left]
          · rw [hb, Category.assoc, Over.comp_left]
        have hbc : (z ≫ ((α_ F F F).hom ≫ snd F (F ⊗ F)).left) ≫ m = (b * c).left ≫ g := by
          refine mul_of_pts hm hA _ (by rw [Category.assoc, Over.w]) b c ?_ ?_
          · rw [hb, Category.assoc, ← Over.comp_left, Category.assoc, associator_hom_snd_fst]
          · rw [hc, Category.assoc, ← Over.comp_left, Category.assoc, associator_hom_snd_snd]
        have h1 : (z ≫ (μF ▷ F).left) ≫ (fst F F).left = (a * b).left ≫ g := by
          simp only [Category.assoc, ← Over.comp_left]
          rw [whiskerRight_fst, Over.comp_left, hμl, ← Category.assoc, hab]
        have h2 : (z ≫ (μF ▷ F).left) ≫ (snd F F).left = c.left ≫ g := by
          simp only [Category.assoc, ← Over.comp_left]
          rw [whiskerRight_snd]
          exact hc.symm
        have h3 : ((z ≫ (α_ F F F).hom.left) ≫ (F ◁ μF).left) ≫ (fst F F).left = a.left ≫ g := by
          simp only [Category.assoc, ← Over.comp_left]
          rw [whiskerLeft_fst, associator_hom_fst]
          exact ha.symm
        have h4 : ((z ≫ (α_ F F F).hom.left) ≫ (F ◁ μF).left) ≫ (snd F F).left = (b * c).left ≫ g := by
          simp only [Category.assoc, ← Over.comp_left]
          rw [whiskerLeft_snd, ← Category.assoc (α_ F F F).hom, Over.comp_left, hμl, ← Category.assoc, hbc]
        rw [Over.comp_left, Over.comp_left, Over.comp_left, hμl, ← Category.assoc,
          mul_of_pts hm hA _ (by rw [Category.assoc, Over.w]) (a * b) c h1 h2,
          ← Category.assoc, ← Category.assoc,
          mul_of_pts hm hA _ (by rw [Category.assoc, Category.assoc, Over.w, Over.w]) a (b * c) h3 h4,
          _root_.mul_assoc]
      left_inv := by
        apply Over.OverMorphism.ext
        refine hom_ext_pts F.hom _ _ (by rw [Over.w, Over.w]) (fun K _ z => ?_)
        obtain ⟨A, g, hA⟩ := hfib K (z ≫ F.hom)
        have ha := fpt_left_g hA.1 z rfl
        set a := fpt hA.1 z rfl
        rw [Over.comp_left, hμl, ← Category.assoc,
          mul_of_pts hm hA _ (by rw [Category.assoc, Over.w]) a⁻¹ a ?_ ?_, inv_mul_cancel,
          Over.comp_left, Over.toUnit_left, ← Category.assoc]
        · exact one_pt0_comp g _ hA.2
        · rw [Category.assoc, ← Over.comp_left, lift_fst]
          exact inv_of_pts hi hA z rfl a ha.symm
        · rw [Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id, ha]
      right_inv := by
        apply Over.OverMorphism.ext
        refine hom_ext_pts F.hom _ _ (by rw [Over.w, Over.w]) (fun K _ z => ?_)
        obtain ⟨A, g, hA⟩ := hfib K (z ≫ F.hom)
        have ha := fpt_left_g hA.1 z rfl
        set a := fpt hA.1 z rfl
        rw [Over.comp_left, hμl, ← Category.assoc,
          mul_of_pts hm hA _ (by rw [Category.assoc, Over.w]) a a⁻¹ ?_ ?_, mul_inv_cancel,
          Over.comp_left, Over.toUnit_left, ← Category.assoc]
        · exact one_pt0_comp g _ hA.2
        · rw [Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id, ha]
        · rw [Category.assoc, ← Over.comp_left, lift_snd]
          exact inv_of_pts hi hA z rfl a ha.symm }
  exact ⟨G, rfl⟩

end GrpObjOfLocal

end ZInQ.Contrib.GroupLaw

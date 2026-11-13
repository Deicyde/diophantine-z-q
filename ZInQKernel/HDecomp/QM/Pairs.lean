import ZInQKernel.HDecomp.QM.Structures

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt3 from
`scratch/leaf-qm-fp/QMLeaves.lean`, §4-§7.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

noncomputable section

namespace LeafQM

namespace AV

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

variable {K : Type} [Field K]

/-! ## §4 QM pairs `(A, ι)` (the objects of `X₆ = X₀(6,1)`), the centralizer and CM -/

/-- An isomorphism of QM pairs: an `𝒪`-equivariant isomorphism. -/
structure QMIso {A A' : AbVar K} (q : QMStr A) (q' : QMStr A') where
  φ : AbVar.Hom A A'
  ψ : AbVar.Hom A' A
  left : φ.hom ≫ ψ.hom = 𝟙 _
  right : ψ.hom ≫ φ.hom = 𝟙 _
  equivariant : ∀ a : O, (q.iota a).hom ≫ φ.hom = φ.hom ≫ (q'.iota a).hom

def QMIso.refl {A : AbVar K} (q : QMStr A) : QMIso q q where
  φ := 1
  ψ := 1
  left := by simp [AbVar.Hom.hom_mk', OfNat.ofNat, One.one]
  right := by simp [AbVar.Hom.hom_mk', OfNat.ofNat, One.one]
  equivariant a := by
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp

def QMIso.symm {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q') : QMIso q' q where
  φ := f.ψ
  ψ := f.φ
  left := f.right
  right := f.left
  equivariant a := by
    calc (q'.iota a).hom ≫ f.ψ.hom
        = f.ψ.hom ≫ f.φ.hom ≫ (q'.iota a).hom ≫ f.ψ.hom := by
          rw [reassoc_of% f.right]
      _ = f.ψ.hom ≫ (q.iota a).hom ≫ f.φ.hom ≫ f.ψ.hom := by
          rw [reassoc_of% (f.equivariant a)]
      _ = f.ψ.hom ≫ (q.iota a).hom := by rw [f.left, Category.comp_id]

def QMIso.trans {A A' A'' : AbVar K} {q : QMStr A} {q' : QMStr A'} {q'' : QMStr A''}
    (f : QMIso q q') (g : QMIso q' q'') : QMIso q q'' where
  φ := AbVar.Hom.mk' (f.φ.hom ≫ g.φ.hom)
  ψ := AbVar.Hom.mk' (g.ψ.hom ≫ f.ψ.hom)
  left := by
    simp only [AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% g.left, f.left]
  right := by
    simp only [AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% f.right, g.right]
  equivariant a := by
    simp only [AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% (f.equivariant a), g.equivariant a]

/-- An abelian surface over `K` with QM by `𝒪` (a point of `X₆ = X₀(6,1)` when `K = ℚ̄`). -/
structure QMPair (K : Type) [Field K] where
  A : AbVar K
  surface : A.dim = 2
  q : QMStr A

def pairSetoid (K : Type) [Field K] : Setoid (QMPair K) where
  r P Q := Nonempty (QMIso P.q Q.q)
  iseqv := ⟨fun P => ⟨QMIso.refl P.q⟩, fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

/-- Forgetting the level structure: `Y₃ → X₆` on objects. -/
def QML3.forget (P : QML3 K) : QMPair K := ⟨P.A, P.surface, P.q⟩

section CM

variable {A : AbVar K}

/-- The centralizer `End_𝒪(A)` of `ι(𝒪)` in `End_K(A)`. Over `ℚ̄` it is `ℤ` or an order in an
imaginary quadratic field (the CM order of the point). -/
def com (q : QMStr A) : Subring (AbVar.End A) := Subring.centralizer (Set.range q.iota)

/-- CM by an order containing `ℤ[i]`, i.e. (since `ℤ[i]` is maximal) by `ℤ[i]`, disc `−4`. -/
def HasCM4 (q : QMStr A) : Prop := ∃ φ ∈ com q, φ * φ = -1
/-- CM by `ℤ[ζ₃]`, disc `−3`. -/
def HasCM3 (q : QMStr A) : Prop := ∃ φ ∈ com q, φ * φ - φ + 1 = 0
/-- CM by `ℤ[√−6]`, disc `−24` (`ℤ[√−6]` is the maximal order of `ℚ(√−6)`). -/
def HasCM24 (q : QMStr A) : Prop := ∃ φ ∈ com q, φ * φ = -6

theorem intCast_mem_com (q : QMStr A) (n : ℤ) : (n : AbVar.End A) ∈ com q := by
  rw [com, Subring.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  exact (Int.cast_commute n _).symm.eq

/-- Sanity: the three CM predicates are invariant under `Aut(𝒪)`-twists (the centralizer of
`ι ∘ α` is that of `ι`). -/
theorem com_twist (q : QMStr A) (α : O ≃+* O) : com (q.twist α) = com q := by
  ext φ
  simp only [com, Subring.mem_centralizer_iff, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff]
  constructor
  · intro h a
    have := h (α.symm a)
    simpa [QMStr.twist] using this
  · intro h a
    exact h (α a)


/-- Conjugation by an isomorphism of QM pairs, `End(A) → End(A')`, `g ↦ ψ ∘ g ∘ φ⁻¹`-style
(`g ↦ f.ψ ≫ g ≫ f.φ`), a ring homomorphism carrying `ι` to `ι'`. -/
def conjHom {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q') :
    AbVar.End A →+* AbVar.End A' where
  toFun g := AbVar.Hom.mk' (f.ψ.hom ≫ g.hom ≫ f.φ.hom)
  map_one' := by
    apply AbVar.Hom.ext'
    change f.ψ.hom ≫ 𝟙 _ ≫ f.φ.hom = 𝟙 _
    rw [Category.id_comp, f.right]
  map_mul' g h := by
    apply AbVar.Hom.ext'
    change f.ψ.hom ≫ (h.hom ≫ g.hom) ≫ f.φ.hom =
      (f.ψ.hom ≫ h.hom ≫ f.φ.hom) ≫ (f.ψ.hom ≫ g.hom ≫ f.φ.hom)
    simp only [Category.assoc, reassoc_of% f.left]
  map_zero' := by
    apply AbVar.Hom.ext'
    change f.ψ.hom ≫ (1 : A.X ⟶ A.X) ≫ f.φ.hom = 1
    rw [MonObj.one_comp, MonObj.comp_one]
  map_add' g h := by
    apply AbVar.Hom.ext'
    change f.ψ.hom ≫ (g.hom * h.hom) ≫ f.φ.hom =
      (f.ψ.hom ≫ g.hom ≫ f.φ.hom) * (f.ψ.hom ≫ h.hom ≫ f.φ.hom)
    rw [MonObj.mul_comp, MonObj.comp_mul]

theorem conjHom_iota {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q') (a : O) :
    conjHom f (q.iota a) = q'.iota a := by
  apply AbVar.Hom.ext'
  change f.ψ.hom ≫ (q.iota a).hom ≫ f.φ.hom = (q'.iota a).hom
  rw [f.equivariant a, reassoc_of% f.right]

theorem conjHom_mem_com {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q')
    {φ : AbVar.End A} (hφ : φ ∈ com q) : conjHom f φ ∈ com q' := by
  rw [com, Subring.mem_centralizer_iff] at hφ ⊢
  rintro _ ⟨a, rfl⟩
  rw [← conjHom_iota f a, ← map_mul, ← map_mul, hφ _ ⟨a, rfl⟩]

/-- The CM predicates are invariant under isomorphisms of QM pairs. -/
theorem HasCM4.of_iso {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q') :
    HasCM4 q → HasCM4 q' := fun ⟨φ, hφ, h⟩ =>
  ⟨conjHom f φ, conjHom_mem_com f hφ, by rw [← map_mul, h, map_neg, map_one]⟩

theorem HasCM3.of_iso {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q') :
    HasCM3 q → HasCM3 q' := fun ⟨φ, hφ, h⟩ =>
  ⟨conjHom f φ, conjHom_mem_com f hφ, by
    rw [← map_mul, ← map_sub, ← map_one (conjHom f), ← map_add, h, map_zero]⟩

theorem HasCM24.of_iso {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q') :
    HasCM24 q → HasCM24 q' := fun ⟨φ, hφ, h⟩ =>
  ⟨conjHom f φ, conjHom_mem_com f hφ, by rw [← map_mul, h, map_neg, map_ofNat]⟩

theorem conjHom_symm_apply {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q')
    (g : AbVar.End A') : conjHom f (conjHom f.symm g) = g := by
  apply AbVar.Hom.ext'
  change f.ψ.hom ≫ (f.φ.hom ≫ g.hom ≫ f.ψ.hom) ≫ f.φ.hom = g.hom
  simp only [Category.assoc, reassoc_of% f.right, f.right, Category.comp_id]

/-- **The CM order is an isomorphism invariant** of QM pairs: `End_𝒪(A) ≅ End_𝒪(A')` (so "CM by
`R`" in `R5fp`, `R5fpCount` depends only on the class, and `W·x ⊆ CM(R)` by `com_twist`). -/
def comEquiv {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q') :
    com q ≃+* com q' where
  toFun g := ⟨conjHom f g, conjHom_mem_com f g.2⟩
  invFun g := ⟨conjHom f.symm g, conjHom_mem_com f.symm g.2⟩
  left_inv g := Subtype.ext (conjHom_symm_apply f.symm g)
  right_inv g := Subtype.ext (conjHom_symm_apply f g)
  map_mul' g h := Subtype.ext (map_mul (conjHom f) (g : AbVar.End A) h)
  map_add' g h := Subtype.ext (map_add (conjHom f) (g : AbVar.End A) h)

theorem hasCM4_twist {A : AbVar K} (q : QMStr A) (α : O ≃+* O) :
    HasCM4 (q.twist α) ↔ HasCM4 q := by simp only [HasCM4, com_twist]
theorem hasCM3_twist {A : AbVar K} (q : QMStr A) (α : O ≃+* O) :
    HasCM3 (q.twist α) ↔ HasCM3 q := by simp only [HasCM3, com_twist]
theorem hasCM24_twist {A : AbVar K} (q : QMStr A) (α : O ≃+* O) :
    HasCM24 (q.twist α) ↔ HasCM24 q := by simp only [HasCM24, com_twist]

end CM

/-! ## §5 Base change as a relation, and fields of moduli

`IsBaseChangeOf f P Q` says that `Q/L` is `P/K` base-changed along `f : K → L`: a morphism of
schemes `g : Q.A → P.A` over `Spec f` that makes the square a pullback (so `Q.A ≅ P.A ×_K L` as
`L`-schemes), commutes with `ι`, and carries `η_Q` to `η_P` (in particular, at `a = 0`, the
identity section to the identity section; a morphism of abelian varieties preserving the identity
is a homomorphism, Mumford §4 Cor. 1, so the group laws correspond). Stated as a relation, it
needs neither the object `P.A ×_K L` nor `dim (A_L) = dim A` (not in Mathlib). -/

def IsBaseChangeOf {K L : Type} [Field K] [Field L] (f : K →+* L) (P : QML3 K) (Q : QML3 L) :
    Prop :=
  ∃ g : Q.A.X.left ⟶ P.A.X.left,
    IsPullback g Q.A.X.hom P.A.X.hom (Spec.map (CommRingCat.ofHom f)) ∧
    (∀ a : O, (Q.q.iota a).hom.left ≫ g = g ≫ (P.q.iota a).hom.left) ∧
    (∀ a : O, (Additive.toMul (Q.e.eta a)).left ≫ g =
        Spec.map (CommRingCat.ofHom f) ≫ (Additive.toMul (P.e.eta a)).left)

/-- The same for QM pairs (identity sections stated explicitly). -/
def IsBaseChangeOfPair {K L : Type} [Field K] [Field L] (f : K →+* L) (P : QMPair K)
    (Q : QMPair L) : Prop :=
  ∃ g : Q.A.X.left ⟶ P.A.X.left,
    IsPullback g Q.A.X.hom P.A.X.hom (Spec.map (CommRingCat.ofHom f)) ∧
    (∀ a : O, (Q.q.iota a).hom.left ≫ g = g ≫ (P.q.iota a).hom.left) ∧
    (1 : Q.A.Pt L).left ≫ g = Spec.map (CommRingCat.ofHom f) ≫ (1 : P.A.Pt K).left

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `σ ∈ Aut(ℚ̄/ℚ)` with `σP ≅ P` (as level-3 objects). -/
def stab3 (P : QML3 Qbar) : Set (Qbar ≃ₐ[ℚ] Qbar) :=
  {σ | IsBaseChangeOf (σ : Qbar →+* Qbar) P P}

/-- **Field of moduli of a level-3 object over `ℚ̄`**: the fixed field of `{σ : σP ≅ P}` (its
generated subgroup, so that no group property needs proof). For a fine moduli scheme in
characteristic 0 this is the residue field `ℚ(y)` of the point `y ∈ Y₃` (STANDARD). -/
def fieldOfModuli3 (P : QML3 Qbar) : IntermediateField ℚ Qbar :=
  IntermediateField.fixedField (Subgroup.closure (stab3 P))

/-- `σ ∈ Aut(ℚ̄/ℚ)` with `σ(A, ι) ≅ (A, ι)`. -/
def stabPair (P : QMPair Qbar) : Set (Qbar ≃ₐ[ℚ] Qbar) :=
  {σ | IsBaseChangeOfPair (σ : Qbar →+* Qbar) P P}

/-- **Field of moduli of a QM pair over `ℚ̄`.** For the coarse moduli space `X₆` in
characteristic 0 this is the residue field `ℚ(x)` of the point `x ∈ X₆` (STANDARD). -/
def fieldOfModuliPair (P : QMPair Qbar) : IntermediateField ℚ Qbar :=
  IntermediateField.fixedField (Subgroup.closure (stabPair P))

/-- A subfield of `ℚ̄` that is a number field unramified at every prime `p ≥ 5` (`p ∤ disc F`,
which is equivalent to "unramified at `p`" by Dedekind's discriminant theorem). -/
def UnramifiedAbove5 (F : IntermediateField ℚ Qbar) : Prop :=
  ∃ h : FiniteDimensional ℚ F, ∀ p : ℕ, p.Prime → 5 ≤ p →
    ¬ ((p : ℤ) ∣ @NumberField.discr F _ (@NumberField.mk F _ _ h))

/-! ## §6 Maps to `P¹`, by charts

Mathlib v4.35 has no `P¹` with its point bijection. A morphism `π : X → P¹_ℤ` is the same as two
opens `U = π⁻¹(t ≠ ∞)`, `V = π⁻¹(t ≠ 0)` covering `X` with `f = π^*t ∈ Γ(U)`,
`g = π^*(1/t) ∈ Γ(V)`, `fg = 1` on `U ∩ V`, and `U ∩ V` the non-vanishing locus of `f` in `U` and
of `g` in `V` (glue the two charts `U → 𝔸¹`, `V → 𝔸¹` along `t ↦ 1/t`; STANDARD, e.g.
Hartshorne II.7.1). A scheme over `ℚ` maps to `P¹_ℚ` over `ℚ` exactly when it maps to `P¹_ℤ`. -/

/-- A morphism `X → P¹`, by charts. -/
structure ToP1 (X : Scheme.{0}) where
  U : X.Opens
  V : X.Opens
  cover : U ⊔ V = ⊤
  f : Γ(X, U)
  g : Γ(X, V)
  inv : X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op f *
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op g = 1
  basicOpen_f : X.basicOpen f = U ⊓ V
  basicOpen_g : X.basicOpen g = U ⊓ V

/-- The value `π(y) ∈ P¹(K) = K ∪ {∞}` at a `K`-point `y : Spec K → X`: if the point `x` of `y`
lies in `U`, the image of `f(x) ∈ κ(x)` under `κ(x) → K`; otherwise `∞`. -/
def ToP1.val {X : Scheme.{0}} (π : ToP1 X) {K : Type} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ X) : OnePoint K := by
  classical
  exact if h : (Scheme.SpecToEquivOfField K X y).1 ∈ π.U then
      OnePoint.some ((Scheme.SpecToEquivOfField K X y).2 (X.evaluation π.U _ h π.f))
    else OnePoint.infty

/-- Precomposing a field point with `Spec L → Spec K` keeps the point and composes the
residue-field embedding with `f`. -/
theorem specToEquivOfField_comp {K L : Type} [Field K] [Field L] {X : Scheme.{0}} (f : K →+* L)
    (y : Spec (CommRingCat.of K) ⟶ X) :
    Scheme.SpecToEquivOfField L X (Spec.map (CommRingCat.ofHom f) ≫ y) =
      ⟨(Scheme.SpecToEquivOfField K X y).1,
        (Scheme.SpecToEquivOfField K X y).2 ≫ CommRingCat.ofHom f⟩ := by
  obtain ⟨p, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  rw [Equiv.apply_symm_apply]
  have : Spec.map (CommRingCat.ofHom f) ≫ (Scheme.SpecToEquivOfField K X).symm p =
      (Scheme.SpecToEquivOfField L X).symm ⟨p.1, p.2 ≫ CommRingCat.ofHom f⟩ := by
    simp only [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc]
  rw [this, Equiv.apply_symm_apply]

/-- **Naturality of `π`-values**: `π(y ∘ Spec f) = f(π(y))`. -/
theorem ToP1.val_comp {X : Scheme.{0}} (π : ToP1 X) {K L : Type} [Field K] [Field L]
    (f : K →+* L) (y : Spec (CommRingCat.of K) ⟶ X) :
    π.val (Spec.map (CommRingCat.ofHom f) ≫ y) = (π.val y).map f := by
  unfold ToP1.val
  generalize hp : Scheme.SpecToEquivOfField L X (Spec.map (CommRingCat.ofHom f) ≫ y) = p
  rw [specToEquivOfField_comp] at hp
  subst hp
  split_ifs <;> rfl

/-- **Composition of a morphism to `P¹` with a morphism of schemes** (pull back the charts). -/
def ToP1.comp {X Y : Scheme.{0}} (h : Y ⟶ X) (π : ToP1 X) : ToP1 Y where
  U := h ⁻¹ᵁ π.U
  V := h ⁻¹ᵁ π.V
  cover := by rw [← Scheme.Hom.preimage_sup, π.cover]; rfl
  f := h.app π.U π.f
  g := h.app π.V π.g
  inv := by
    have n1 := ConcreteCategory.congr_hom
      (h.naturality (homOfLE (inf_le_left : π.U ⊓ π.V ≤ π.U)).op) π.f
    have n2 := ConcreteCategory.congr_hom
      (h.naturality (homOfLE (inf_le_right : π.U ⊓ π.V ≤ π.V)).op) π.g
    simp only [ConcreteCategory.comp_apply] at n1 n2
    have e := congrArg (h.app (π.U ⊓ π.V)) π.inv
    rw [map_mul, map_one, n1, n2] at e
    exact e
  basicOpen_f := by rw [← Scheme.preimage_basicOpen, π.basicOpen_f]; rfl
  basicOpen_g := by rw [← Scheme.preimage_basicOpen, π.basicOpen_g]; rfl

/-- Postcomposing a field point with `h` moves the point by `h` and precomposes the embedding
with the residue-field map. -/
theorem specToEquivOfField_comp_right {K : Type} [Field K] {X Y : Scheme.{0}} (h : Y ⟶ X)
    (y : Spec (CommRingCat.of K) ⟶ Y) :
    Scheme.SpecToEquivOfField K X (y ≫ h) =
      ⟨h (Scheme.SpecToEquivOfField K Y y).1,
        h.residueFieldMap (Scheme.SpecToEquivOfField K Y y).1 ≫
          (Scheme.SpecToEquivOfField K Y y).2⟩ := by
  obtain ⟨p, rfl⟩ := (Scheme.SpecToEquivOfField K Y).symm.surjective y
  rw [Equiv.apply_symm_apply]
  have : (Scheme.SpecToEquivOfField K Y).symm p ≫ h =
      (Scheme.SpecToEquivOfField K X).symm ⟨h p.1, h.residueFieldMap p.1 ≫ p.2⟩ := by
    simp only [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [this, Equiv.apply_symm_apply]

/-- `(π ∘ h)(y) = π(h ∘ y)`. -/
theorem ToP1.val_comp_right {X Y : Scheme.{0}} (π : ToP1 X) (h : Y ⟶ X) {K : Type} [Field K]
    (y : Spec (CommRingCat.of K) ⟶ Y) : (π.comp h).val y = π.val (y ≫ h) := by
  unfold ToP1.val
  generalize hp : Scheme.SpecToEquivOfField K X (y ≫ h) = p
  rw [specToEquivOfField_comp_right] at hp
  subst hp
  dsimp only
  split_ifs with h1 h2 h2
  · congr 1
    rw [ConcreteCategory.comp_apply, Scheme.evaluation_naturality_apply]
    rfl
  · exact (h2 h1).elim
  · exact (h1 h2).elim
  · rfl

/-! ## §7 Field points of a `ℚ`-scheme -/

/-- `Spec K` as a `ℚ`-scheme. -/
def fieldPt (K : Type) [Field K] [Algebra ℚ K] : Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))

/-- `Spec L → Spec K` over `ℚ`, for `f : K →ₐ[ℚ] L`. -/
def fieldMap {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L) :
    fieldPt L ⟶ fieldPt K :=
  Over.homMk (Spec.map (CommRingCat.ofHom (f : K →+* L))) (by
    simp only [fieldPt, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact f.comp_algebraMap)

/-- A bijection, for every field `K ⊇ ℚ`, between the `K`-points of `Y` over `ℚ` and the
isomorphism classes of level-3 QM surfaces over `K`. -/
abbrev PtEquiv (Y : Over (Spec (CommRingCat.of ℚ))) : Type 1 :=
  ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ M3 K


end AV

end LeafQM

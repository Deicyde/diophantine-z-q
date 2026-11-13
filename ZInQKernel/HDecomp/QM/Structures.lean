import ZInQKernel.HDecomp.A6.A6
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Module.RingHom
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Tactic

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt3 from
`scratch/leaf-qm-fp/QMLeaves.lean`, §0-§3.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# leaf-qm-fp: the field-point leaves R1fp, R1hecke, R2fp, R1rec, R5fp of the H decomposition

See `docs/research/leaf-qm-fp.md`. Blueprint: `docs/research/bp-qmmoduli.md` §2.3.
Over the kernel's `PkgI3.AbVar` (`ZInQKernel/HDecomp/Objects.lean`); the order `𝒪` and the QM
structures are copied from `scratch/bp-qmmoduli/QMAbVar.lean` (scratch files cannot import each
other). No `sorry`, no `axiom`.
-/

noncomputable section

namespace LeafQM

/-! ## §0 The order `𝒪` (copied from `scratch/bp-qmmoduli/QMAbVar.lean` §0) -/

abbrev B := QuaternionAlgebra ℚ 2 0 (-3)

def ofInt (n : Fin 4 → ℤ) : B :=
  ⟨n 0 + (n 2 : ℚ) / 2, n 1 + (n 3 : ℚ) / 2, (n 2 : ℚ) / 2, (n 3 : ℚ) / 2⟩

def InO (x : B) : Prop := ∃ n : Fin 4 → ℤ, x = ofInt n

def mulCoord (n m : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

theorem ofInt_mul (n m : Fin 4 → ℤ) : ofInt n * ofInt m = ofInt (mulCoord n m) := by
  ext <;> simp [ofInt, mulCoord] <;> ring

theorem ofInt_add (n m : Fin 4 → ℤ) : ofInt n + ofInt m = ofInt (n + m) := by
  ext <;> simp [ofInt] <;> ring

theorem ofInt_neg (n : Fin 4 → ℤ) : -ofInt n = ofInt (-n) := by
  ext <;> simp [ofInt] <;> ring

theorem ofInt_zero : ofInt 0 = 0 := by ext <;> simp [ofInt]

theorem ofInt_one : ofInt ![1, 0, 0, 0] = 1 := by ext <;> simp [ofInt]

/-- The maximal order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` of `B = (2,−3)`. -/
def O : Subring B where
  carrier := {x | InO x}
  mul_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨mulCoord n m, ofInt_mul n m⟩
  one_mem' := ⟨![1, 0, 0, 0], ofInt_one.symm⟩
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨n + m, ofInt_add n m⟩
  zero_mem' := ⟨0, ofInt_zero.symm⟩
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨-n, ofInt_neg n⟩

/-- `𝒪` is not the zero ring. -/
theorem O_nontrivial : (1 : O) ≠ 0 := by
  intro h
  have := congrArg (fun x : O => (x : B).re) h
  simp at this


namespace AV

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

variable {K : Type} [Field K]

/-! ## §1 QM structures (copied from `QMAbVar.lean` §§1-2) -/

section EndPt

variable (A : AbVar K) (L : Type) [Field L] [Algebra K L]

/-- `End_K(A) → End(A(L))`, `f ↦ (P ↦ P ≫ f)`, a ring homomorphism. -/
def endPt : AbVar.End A →+* AddMonoid.End (Additive (A.Pt L)) where
  toFun f := (AbVar.ptMap (L := L) f).toAdditive
  map_one' := by
    refine DFunLike.ext _ _ fun x => ?_
    change Additive.ofMul (Additive.toMul x ≫ 𝟙 _) = x
    rw [Category.comp_id]; rfl
  map_mul' f g := by
    refine DFunLike.ext _ _ fun x => ?_
    change Additive.ofMul (Additive.toMul x ≫ (g.hom ≫ f.hom)) =
      Additive.ofMul ((Additive.toMul x ≫ g.hom) ≫ f.hom)
    rw [Category.assoc]
  map_zero' := by
    refine DFunLike.ext _ _ fun x => ?_
    change Additive.ofMul (Additive.toMul x ≫ (1 : A.X ⟶ A.X)) = 0
    rw [MonObj.comp_one]; rfl
  map_add' f g := by
    refine DFunLike.ext _ _ fun x => ?_
    change Additive.ofMul (Additive.toMul x ≫ (f.hom * g.hom)) =
      Additive.ofMul ((Additive.toMul x ≫ f.hom) * (Additive.toMul x ≫ g.hom))
    rw [MonObj.comp_mul]

end EndPt

/-- **A QM structure by `𝒪` on `A`**: an injective unital ring homomorphism `ι : 𝒪 → End_K(A)`. -/
structure QMStr (A : AbVar K) where
  iota : O →+* AbVar.End A
  injective : Function.Injective iota

/-- The induced action of `𝒪` on `A(L)`. -/
def qmAct {A : AbVar K} (q : QMStr A) (L : Type) [Field L] [Algebra K L] :
    O →+* AddMonoid.End (Additive (A.Pt L)) :=
  (endPt A L).comp q.iota

/-- Sanity: the zero abelian variety carries no QM structure. -/
theorem not_qmStr_zero : IsEmpty (QMStr (AbVar.zero K)) := by
  constructor
  intro q
  have hsub : ∀ f g : AbVar.End (AbVar.zero K), f = g := by
    intro f g
    apply AbVar.Hom.ext'
    exact CartesianMonoidalCategory.toUnit_unique _ _
  exact O_nontrivial (q.injective (hsub _ _))

/-- `Aut(𝒪)` acting on QM structures: `ι ↦ ι ∘ α`. -/
def QMStr.twist {A : AbVar K} (q : QMStr A) (α : O ≃+* O) : QMStr A where
  iota := q.iota.comp α.toRingHom
  injective := q.injective.comp α.injective

/-! ## §2 Level-3 structures on `K`-rational points

**Change from bp-qmmoduli.** `QMAbVar.lean` puts `η` in `A(K̄)` with a Galois-invariance and an
ontoness clause; that form does not base-change without the counting leaf `TorsionStructure`.
Here `η : 𝒪 → A(K)` is `𝒪`-linear with kernel exactly `3𝒪`. For an abelian surface over a field
of characteristic `0` this is the same datum as an `𝒪`-linear isomorphism of group schemes
`(𝒪/3𝒪)_K ≅ A[3]`: `η` embeds `𝒪/3𝒪` (81 elements) into `A(K)[3] ⊆ A(K̄)[3]`, which has
`3^{2·2} = 81` elements (Mumford, *Abelian varieties*, §4 (iv), the kernel's leaf
`TorsionStructure`), so `η` is onto `A(K̄)[3]`, all of `A[3]` is `K`-rational, and the étale group
scheme `A[3]` is the constant one. Conversely an isomorphism `(𝒪/3𝒪)_K ≅ A[3]` gives such an `η`
on `K`-points. (STANDARD.) -/

/-- **A level-3 structure** on `(A, ι)`: an `𝒪`-linear additive map `η : 𝒪 → A(K)` with kernel
exactly `3𝒪` (see the section docstring for why this is the moduli problem's `K₃`-structure
in characteristic 0). -/
structure Level3 {A : AbVar K} (q : QMStr A) where
  eta : O →+ Additive (A.Pt K)
  linear : ∀ a b : O, eta (a * b) = qmAct q K a (eta b)
  ker : ∀ a : O, eta a = 0 ↔ ∃ b : O, a = 3 * b

namespace Level3

variable {A : AbVar K} {q : QMStr A}

theorem eq_iff (e : Level3 q) (a b : O) : e.eta a = e.eta b ↔ ∃ c : O, a - b = 3 * c := by
  rw [← sub_eq_zero, ← map_sub, e.ker]

/-- `𝒪^×` acts on level structures by right multiplication, `η ↦ η(· u)`. -/
def rightMul (e : Level3 q) (u : Oˣ) : Level3 q where
  eta := e.eta.comp (AddMonoidHom.mulRight (u : O))
  linear a b := by simp [_root_.mul_assoc, e.linear]
  ker a := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulRight]
    rw [e.ker]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c * ↑u⁻¹, by
        rw [← _root_.mul_assoc, ← hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c * u, by rw [_root_.mul_assoc]⟩

/-- Units `≡ 1 mod 3𝒪` act trivially (the action factors through `(𝒪/3𝒪)^×`). -/
theorem rightMul_eq_self (e : Level3 q) (u : Oˣ) (hu : ∃ c : O, (u : O) - 1 = 3 * c) (a : O) :
    (e.rightMul u).eta a = e.eta a := by
  change e.eta (a * u) = e.eta a
  rw [e.eq_iff]
  obtain ⟨c, hc⟩ := hu
  refine ⟨a * c, ?_⟩
  calc a * ↑u - a = a * (↑u - 1) := by noncomm_ring
    _ = a * (3 * c) := by rw [hc]
    _ = 3 * (a * c) := by noncomm_ring

/-- `Aut(𝒪)` acting on level structures: `η ↦ η ∘ α` (a level structure for `ι ∘ α`). -/
def twist (e : Level3 q) (α : O ≃+* O) : Level3 (q.twist α) where
  eta := e.eta.comp α.toAddMonoidHom
  linear a b := by
    change e.eta (α (a * b)) = qmAct q K (α a) (e.eta (α b))
    rw [map_mul, e.linear]
  ker a := by
    change e.eta (α a) = 0 ↔ _
    rw [e.ker]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨α.symm c, by
        apply α.injective
        rw [hc, map_mul, RingEquiv.apply_symm_apply, map_ofNat]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨α c, by rw [map_mul, map_ofNat]⟩

end Level3

/-! ## §3 The objects `(A, ι, η)`, their isomorphisms and classes, and the action of `Γ'` -/

/-- **An abelian surface over `K` with QM by `𝒪` and a level-3 structure.** (No polarization:
by Lemma P (rv-qm-polar §0): for a fixed `μ` (N5's `2j+ij`), the type-`μ` principal
polarization of `(A, ι)` exists and is unique in characteristic 0, also at CM points;
VERIFIED as an argument, lattice cores compiled (`RvQMPolar.eq_pm_E0_of_principal`,
`RvQMPolar.type_eq_mu_mul`, `RvQMPolar.lemmaP_lattice` in `QM/Polar.lean`), published
locators UNVERIFIED. Without fixing `μ` it is
not unique.) -/
structure QML3 (K : Type) [Field K] where
  A : AbVar K
  surface : A.dim = 2
  q : QMStr A
  e : Level3 q

/-- Isomorphisms of objects: an `𝒪`-equivariant isomorphism of abelian varieties carrying `η`
to `η'`. -/
structure QML3.Iso (P Q : QML3 K) where
  φ : AbVar.Hom P.A Q.A
  ψ : AbVar.Hom Q.A P.A
  left : φ.hom ≫ ψ.hom = 𝟙 _
  right : ψ.hom ≫ φ.hom = 𝟙 _
  equivariant : ∀ a : O, (P.q.iota a).hom ≫ φ.hom = φ.hom ≫ (Q.q.iota a).hom
  level : ∀ a : O, Additive.ofMul (Additive.toMul (P.e.eta a) ≫ φ.hom) = Q.e.eta a

section Classes

variable {P Q R : QML3 K}

def QML3.Iso.refl (P : QML3 K) : P.Iso P where
  φ := 1
  ψ := 1
  left := by simp [AbVar.Hom.hom_mk', OfNat.ofNat, One.one]
  right := by simp [AbVar.Hom.hom_mk', OfNat.ofNat, One.one]
  equivariant a := by
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp
  level a := by
    change Additive.ofMul (Additive.toMul (P.e.eta a) ≫ 𝟙 _) = _
    rw [Category.comp_id]; rfl

def QML3.Iso.symm (f : P.Iso Q) : Q.Iso P where
  φ := f.ψ
  ψ := f.φ
  left := f.right
  right := f.left
  equivariant a := by
    calc (Q.q.iota a).hom ≫ f.ψ.hom
        = f.ψ.hom ≫ f.φ.hom ≫ (Q.q.iota a).hom ≫ f.ψ.hom := by
          rw [reassoc_of% f.right]
      _ = f.ψ.hom ≫ (P.q.iota a).hom ≫ f.φ.hom ≫ f.ψ.hom := by
          rw [reassoc_of% (f.equivariant a)]
      _ = f.ψ.hom ≫ (P.q.iota a).hom := by rw [f.left, Category.comp_id]
  level a := by
    rw [← f.level a]
    change Additive.ofMul ((Additive.toMul (P.e.eta a) ≫ f.φ.hom) ≫ f.ψ.hom) = _
    rw [Category.assoc, f.left, Category.comp_id]; rfl

def QML3.Iso.trans (f : P.Iso Q) (g : Q.Iso R) : P.Iso R where
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
  level a := by
    rw [← g.level a, ← f.level a]
    simp only [AbVar.Hom.hom_mk']
    rfl

/-- Isomorphism of objects is an equivalence relation. -/
def isoSetoid (K : Type) [Field K] : Setoid (QML3 K) where
  r P Q := Nonempty (P.Iso Q)
  iseqv := ⟨fun P => ⟨QML3.Iso.refl P⟩, fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

/-- **The field-valued points of the moduli problem**: isomorphism classes of `QML3 K`. -/
def M3 (K : Type) [Field K] : Type 1 := Quotient (isoSetoid K)

/-- The class of an object. -/
def M3.mk (P : QML3 K) : M3 K := Quotient.mk (isoSetoid K) P

/-- `Γ'` acts through `Aut(𝒪)` (`twist`) and `𝒪^×` (`rightMul`), never changing `A`. -/
def QML3.twist (P : QML3 K) (α : O ≃+* O) : QML3 K :=
  ⟨P.A, P.surface, P.q.twist α, P.e.twist α⟩

def QML3.rightMul (P : QML3 K) (u : Oˣ) : QML3 K :=
  ⟨P.A, P.surface, P.q, P.e.rightMul u⟩

theorem QML3.twist_A (P : QML3 K) (α : O ≃+* O) : (P.twist α).A = P.A := rfl
theorem QML3.rightMul_A (P : QML3 K) (u : Oˣ) : (P.rightMul u).A = P.A := rfl

def QML3.Iso.twist {P Q : QML3 K} (f : P.Iso Q) (α : O ≃+* O) :
    (P.twist α).Iso (Q.twist α) where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant a := by
    change (P.q.iota (α a)).hom ≫ f.φ.hom = f.φ.hom ≫ (Q.q.iota (α a)).hom
    exact f.equivariant (α a)
  level a := by
    change Additive.ofMul (Additive.toMul (P.e.eta (α a)) ≫ f.φ.hom) = Q.e.eta (α a)
    exact f.level (α a)

def QML3.Iso.rightMul {P Q : QML3 K} (f : P.Iso Q) (u : Oˣ) :
    (P.rightMul u).Iso (Q.rightMul u) where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant a := f.equivariant a
  level a := by
    change Additive.ofMul (Additive.toMul (P.e.eta (a * u)) ≫ f.φ.hom) = Q.e.eta (a * u)
    exact f.level (a * u)

/-- `twist α` on classes. -/
def M3.twist (α : O ≃+* O) : M3 K → M3 K :=
  Quotient.map (fun P => P.twist α) (fun _ _ ⟨f⟩ => ⟨f.twist α⟩)

/-- `rightMul u` on classes. -/
def M3.rightMul (u : Oˣ) : M3 K → M3 K :=
  Quotient.map (fun P => P.rightMul u) (fun _ _ ⟨f⟩ => ⟨f.rightMul u⟩)

theorem M3.twist_mk (α : O ≃+* O) (P : QML3 K) : M3.twist α (M3.mk P) = M3.mk (P.twist α) :=
  rfl


/-! ### Glue for A3: composition laws of `Γ'` on classes, and the level-structure torsor -/

theorem Level3.ext' {A : AbVar K} {q : QMStr A} {e e' : Level3 q} (h : e.eta = e'.eta) :
    e = e' := by
  cases e; cases e'; cases h; rfl

theorem Level3.rightMul_rightMul {A : AbVar K} {q : QMStr A} (e : Level3 q) (u v : Oˣ) :
    (e.rightMul u).rightMul v = e.rightMul (v * u) := by
  apply Level3.ext'
  ext a
  simp [Level3.rightMul, _root_.mul_assoc]

theorem QML3.rightMul_rightMul (P : QML3 K) (u v : Oˣ) :
    (P.rightMul u).rightMul v = P.rightMul (v * u) := by
  simp only [QML3.rightMul, Level3.rightMul_rightMul]

theorem M3.rightMul_rightMul (u v : Oˣ) (c : M3 K) :
    M3.rightMul v (M3.rightMul u c) = M3.rightMul (v * u) c := by
  induction c using Quotient.inductionOn with
  | h P => exact congrArg M3.mk (QML3.rightMul_rightMul P u v)

/-- **The level-structure torsor (algebraic core).** Two level structures `η, η'` on the same
`(A, ι)` such that the image of `η'` lies in that of `η` differ by right multiplication by an
element `u₀ ∈ 𝒪` that is a unit modulo `3𝒪`. (Over `K̄` the containment holds for all pairs:
both images are `A[3]`, by `TorsionStructure`, 81 = 81. So a geometric fibre of `Y₃ → X₆` has at
most `#(𝒪/3𝒪)^× = 72` points, `Units72`; this is A3's count.) -/
theorem Level3.exists_mul_of_range_le {A : AbVar K} {q : QMStr A} (e e' : Level3 q)
    (h' : ∀ a, ∃ b, e'.eta a = e.eta b) (h : ∀ a, ∃ b, e.eta a = e'.eta b) :
    ∃ u₀ v₀ : O, (∃ c : O, v₀ * u₀ - 1 = 3 * c) ∧ ∀ a : O, e'.eta a = e.eta (a * u₀) := by
  obtain ⟨u₀, hu⟩ := h' 1
  obtain ⟨v₀, hv⟩ := h 1
  have hlin : ∀ a, e'.eta a = e.eta (a * u₀) := by
    intro a
    calc e'.eta a = e'.eta (a * 1) := by rw [_root_.mul_one]
      _ = qmAct q K a (e'.eta 1) := e'.linear a 1
      _ = qmAct q K a (e.eta u₀) := by rw [hu]
      _ = e.eta (a * u₀) := (e.linear a u₀).symm
  refine ⟨u₀, v₀, ?_, hlin⟩
  have h1 : e.eta (v₀ * u₀) = e.eta 1 := by rw [← hlin, ← hv]
  obtain ⟨c, hc⟩ := (e.eq_iff _ _).1 h1
  exact ⟨c, hc⟩

end Classes

/-! ### Glue for A3 and A6: a level structure is onto `A(K̄)[3]` (from `TorsionStructure`) -/

section Onto

open ObjBridge

instance specMap_flat (L : Type) [Field L] [Algebra K L] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

instance specMap_surjective (L : Type) [Field L] [Algebra K L] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

variable (K) in
/-- `Spec K̄ → Spec K` over `K`. -/
def toKbar : PkgI2.specOver K (AlgebraicClosure K) ⟶ AbVar.ptObj (K := K) K :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (by
    simp only [PkgI2.specOver, AbVar.ptObj, Over.mk_hom, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp])

/-- A `K`-point as a `K̄`-point. -/
def bcPt (A : AbVar K) (y : A.Pt K) : PkgI2.Pts (toGrp A) (AlgebraicClosure K) := toKbar K ≫ y

theorem bcPt_injective (A : AbVar K) : Function.Injective (bcPt A) := by
  intro y y' h
  have : Epi (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) :=
    Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  exact (cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).1
    (congrArg CommaMorphism.left h)

theorem ofInt_injective : Function.Injective ofInt := by
  intro n m h
  have h0 : (n 0 : ℚ) + (n 2 : ℚ) / 2 = m 0 + (m 2 : ℚ) / 2 := congrArg QuaternionAlgebra.re h
  have h1 : (n 1 : ℚ) + (n 3 : ℚ) / 2 = m 1 + (m 3 : ℚ) / 2 := congrArg QuaternionAlgebra.imI h
  have h2 : (n 2 : ℚ) / 2 = (m 2 : ℚ) / 2 := congrArg QuaternionAlgebra.imJ h
  have h3 : (n 3 : ℚ) / 2 = (m 3 : ℚ) / 2 := congrArg QuaternionAlgebra.imK h
  have e2 : (n 2 : ℚ) = m 2 := by linarith
  have e3 : (n 3 : ℚ) = m 3 := by linarith
  have e0 : (n 0 : ℚ) = m 0 := by linarith
  have e1 : (n 1 : ℚ) = m 1 := by linarith
  funext i
  fin_cases i
  · exact_mod_cast e0
  · exact_mod_cast e1
  · exact_mod_cast e2
  · exact_mod_cast e3

theorem ofInt_sub (n m : Fin 4 → ℤ) : ofInt n - ofInt m = ofInt (n - m) := by
  ext <;> simp [ofInt] <;> ring

theorem three_mul_ofInt (k : Fin 4 → ℤ) : (3 : B) * ofInt k = ofInt (fun i => 3 * k i) := by
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring

/-- The level points are 3-torsion as `K̄`-points. -/
theorem Level3.bcPt_pow_three {A : AbVar K} {q : QMStr A} (e : Level3 q) (a : O) :
    bcPt A (Additive.toMul (e.eta a)) ^ 3 = 1 := by
  have h3 : (3 : ℕ) • e.eta a = 0 := by
    rw [← map_nsmul, e.ker]
    exact ⟨a, by simp [nsmul_eq_mul]⟩
  have : Additive.toMul (e.eta a) ^ 3 = 1 := by
    rw [← toMul_nsmul, h3]; rfl
  rw [bcPt, ← MonObj.comp_pow, this]
  exact MonObj.comp_one _

/-- The element `n₀ + n₁ i + n₂ (1+j)/2 + n₃ (i+k)/2` of `𝒪` with `nᵢ ∈ {0,1,2}` lifting `c`. -/
def liftO (c : Fin 4 → ZMod 3) : O := ⟨ofInt (fun i => ((c i).val : ℤ)), ⟨_, rfl⟩⟩

/-- **A level structure is onto `A(K̄)[3]`** (given the kernel's leaf `TorsionStructure`, in
characteristic 0): `𝒪/3𝒪 ↪ A(K)[3] ↪ A(K̄)[3]`, and both ends have `3^4 = 81` elements. So the
image of `η` is all of `A[3]`, which is therefore `K`-rational (the hypothesis `hrat` of the
kernel's A6). -/
theorem Level3.onto (hT : ObjBridge.TorsionStructure) [CharZero K] (P : QML3 K)
    (x : PkgI2.Pts (toGrp P.A) (AlgebraicClosure K)) (hx : x ^ 3 = 1) :
    ∃ a : O, bcPt P.A (Additive.toMul (P.e.eta a)) = x := by
  have hdim : ObjBridge.dim (toGrp P.A) = ((2 : ℕ) : WithBot ℕ∞) := by
    change P.A.dim = _
    rw [P.surface]; rfl
  obtain ⟨e, -⟩ := hT K (toGrp P.A) 2 3 hdim (by norm_num) (Nat.cast_ne_zero.mpr (by norm_num))
  let F : (Fin 4 → ZMod 3) → PkgI2.torsion (toGrp P.A) (AlgebraicClosure K) 3 := fun c =>
    ⟨bcPt P.A (Additive.toMul (P.e.eta (liftO c))), P.e.bcPt_pow_three _⟩
  have hF : Function.Injective F := by
    intro c c' h
    have h1 : bcPt P.A (Additive.toMul (P.e.eta (liftO c))) =
        bcPt P.A (Additive.toMul (P.e.eta (liftO c'))) := congrArg Subtype.val h
    have h2 := Additive.toMul.injective (bcPt_injective P.A h1)
    obtain ⟨d, hd⟩ := (P.e.eq_iff _ _).1 h2
    obtain ⟨k, hk⟩ := d.2
    have h3 : ofInt (fun i => ((c i).val : ℤ)) - ofInt (fun i => ((c' i).val : ℤ)) =
        3 * ofInt k := by
      have := congrArg Subtype.val hd
      have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
      simp only [liftO, hk, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, h33] at this
      exact this
    rw [ofInt_sub, three_mul_ofInt] at h3
    have h4 := ofInt_injective h3
    funext i
    have h5 := congrFun h4 i
    simp only [Pi.sub_apply] at h5
    have h6 : (((c i).val : ℤ) : ZMod 3) - (((c' i).val : ℤ) : ZMod 3) = 0 := by
      rw [← Int.cast_sub, h5]; push_cast
      rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
    simpa [sub_eq_zero] using h6
  have hbij : Function.Bijective (e ∘ F) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨e.injective.comp hF, by simp⟩
  obtain ⟨c, hc⟩ := hbij.2 (e ⟨x, hx⟩)
  exact ⟨liftO c, congrArg Subtype.val (e.injective hc)⟩

/-- Two level structures on one `(A, ι)` have the same range (given `TorsionStructure`). -/
theorem Level3.range_le (hT : ObjBridge.TorsionStructure) [CharZero K] (P : QML3 K)
    (e' : Level3 P.q) (a : O) : ∃ b : O, e'.eta a = P.e.eta b := by
  obtain ⟨b, hb⟩ := Level3.onto hT P _ (e'.bcPt_pow_three a)
  exact ⟨b, (Additive.toMul.injective (bcPt_injective P.A hb)).symm⟩

/-- **The level-structure torsor (A3), unconditional given `TorsionStructure`**: any two level
structures on one `(A, ι)` over a field of characteristic 0 differ by right multiplication by an
element of `𝒪` invertible mod `3𝒪`. So a fibre of `Y₃ → X₆` over `ℚ̄` has at most
`#(𝒪/3𝒪)^× = 72` points (`Units72`). -/
theorem Level3.torsor (hT : ObjBridge.TorsionStructure) [CharZero K] (P : QML3 K)
    (e' : Level3 P.q) :
    ∃ u₀ v₀ : O, (∃ c : O, v₀ * u₀ - 1 = 3 * c) ∧ ∀ a : O, e'.eta a = P.e.eta (a * u₀) :=
  Level3.exists_mul_of_range_le P.e e' (Level3.range_le hT P e')
    (Level3.range_le hT ⟨P.A, P.surface, P.q, e'⟩ P.e)

end Onto

/-! ### Glue A6 on the objects of the leaves (good reduction away from 3) -/

/-- `i ∈ 𝒪`. -/
def oi : O := ⟨ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩
/-- `j = −1 + 2·(1+j)/2 ∈ 𝒪`. -/
def oj : O := ⟨ofInt ![-1, 0, 2, 0], ⟨_, rfl⟩⟩

theorem oi_mul_oi : oi * oi = 2 := by
  apply Subtype.ext
  change ofInt ![0, 1, 0, 0] * ofInt ![0, 1, 0, 0] = (2 : B)
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]

theorem oj_mul_oj : oj * oj = -3 := by
  apply Subtype.ext
  change ofInt ![-1, 0, 2, 0] * ofInt ![-1, 0, 2, 0] = -(3 : B)
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]

theorem oj_mul_oi_add : oj * oi + oi * oj = 0 := by
  apply Subtype.ext
  change ofInt ![-1, 0, 2, 0] * ofInt ![0, 1, 0, 0] + ofInt ![0, 1, 0, 0] * ofInt ![-1, 0, 2, 0]
    = (0 : B)
  ext <;> simp [ofInt]

section A6

open ObjBridge

variable (P : QML3 K)

local notation "Kb" => AlgebraicClosure K

theorem act_mul_apply (a b : O) (y : Additive (P.A.Pt Kb)) :
    qmAct P.q Kb (a * b) y = qmAct P.q Kb a (qmAct P.q Kb b y) := by
  rw [map_mul]; rfl

theorem hI (x : PkgI2.Pts (toGrp P.A) Kb) :
    (x ≫ (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oi)).hom.hom) ≫
      (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oi)).hom.hom = x ^ 2 := by
  apply Additive.ofMul.injective
  rw [ofMul_pow]
  change qmAct P.q Kb oi (qmAct P.q Kb oi (Additive.ofMul x)) = _
  rw [← act_mul_apply, oi_mul_oi, map_ofNat]
  rfl

theorem hJ (x : PkgI2.Pts (toGrp P.A) Kb) :
    (x ≫ (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oj)).hom.hom) ≫
      (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oj)).hom.hom * x ^ 3 = 1 := by
  apply Additive.ofMul.injective
  rw [ofMul_mul, ofMul_pow, ofMul_one]
  have h : qmAct P.q Kb (oj * oj) (Additive.ofMul x : Additive (P.A.Pt Kb))
      = -((3 : ℕ) • (Additive.ofMul x : Additive (P.A.Pt Kb))) := by
    rw [oj_mul_oj, map_neg, map_ofNat]; rfl
  rw [act_mul_apply] at h
  exact (congrArg (· + (3 : ℕ) • (Additive.ofMul x : Additive (P.A.Pt Kb))) h).trans
    (neg_add_cancel _)

theorem hIJ (x : PkgI2.Pts (toGrp P.A) Kb) :
    (x ≫ (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oi)).hom.hom) ≫
        (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oj)).hom.hom *
      (x ≫ (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oj)).hom.hom) ≫
        (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oi)).hom.hom = 1 := by
  apply Additive.ofMul.injective
  rw [ofMul_mul, ofMul_one]
  have h : qmAct P.q Kb (oj * oi + oi * oj)
      (Additive.ofMul x : Additive (P.A.Pt Kb)) = 0 := by
    rw [oj_mul_oi_add, map_zero]; rfl
  rw [map_add] at h
  have h2 : qmAct P.q Kb (oj * oi) (Additive.ofMul x : Additive (P.A.Pt Kb)) +
      qmAct P.q Kb (oi * oj) (Additive.ofMul x : Additive (P.A.Pt Kb)) = 0 := h
  rw [act_mul_apply, act_mul_apply] at h2
  exact h2

/-- `K`-points base-changed to `K̄` are Galois-fixed. -/
theorem galAct_bcPt (σ : Kb ≃ₐ[K] Kb) (y : P.A.Pt K) :
    PkgI2.galAct (toGrp P.A) σ (bcPt P.A y) = bcPt P.A y := by
  have : PkgI2.galHom Kb σ ≫ toKbar K = toKbar K := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (σ : Kb →+* Kb)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K Kb)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Kb))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp
  change PkgI2.galHom Kb σ ≫ toKbar K ≫ y = toKbar K ≫ y
  rw [← Category.assoc, this]

/-- All of `A[3]` is Galois-fixed (from `Level3.onto`). -/
theorem hrat [CharZero K] (hT : ObjBridge.TorsionStructure) (σ : Kb ≃ₐ[K] Kb)
    (x : PkgI2.Pts (toGrp P.A) Kb) (hx : x ∈ PkgI2.torsion (toGrp P.A) Kb 3) :
    PkgI2.galAct (toGrp P.A) σ x = x := by
  obtain ⟨a, rfl⟩ := Level3.onto hT P x hx
  exact galAct_bcPt P σ _

/-- **Glue A6 on the objects of the leaves**: every `QML3` object over a field of characteristic
0 has good reduction at every DVR in which 3 is a unit, from the kernel's leaves
`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure` (via
`GlueA6Alg.goodReduction_of_QM_rational3'`). With R1fp, this applies to the fibre object over
`J(u)` (A4 + A6). -/
theorem QML3.goodReduction [CharZero K] (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : PkgI2.RaynaudCriterion.{0}) (hTors : PkgI2.TorsionStructure.{0})
    (Ov : ValuationSubring K) [IsDiscreteValuationRing Ov] (h3 : IsUnit (3 : Ov)) :
    PkgI2.HasGoodReduction (toGrp P.A) Ov := by
  have hdim : topologicalKrullDim (toGrp P.A).X.left = ((2 : ℕ) : WithBot ℕ∞) := P.surface
  exact GlueA6Alg.goodReduction_of_QM_rational3' hNOS hRay hTors Ov (toGrp P.A) hdim
    (grpOfHom (P.q.iota oi)) (grpOfHom (P.q.iota oj)) (hI P) (hJ P) (hIJ P) h3
    (hrat P hTors)

end A6


end AV

end LeafQM

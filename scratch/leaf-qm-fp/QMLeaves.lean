import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Module.RingHom
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Tactic

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
for this datum a principal polarization with Rosati involution `x ↦ μ⁻¹x̄μ` on `ι(𝒪)` exists and
is unique, bp-qmmoduli §2.2, whose lattice core is `BPQM.eq_pm_E0_of_principal`.) -/
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

end Classes

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

end AV

end LeafQM

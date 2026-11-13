import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Module.RingHom
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.PicardGroup
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
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

/-! ## §8 The leaves -/

/-- **R1fp, clause list** (for a candidate `Y₃` with its bijections `Φ`): `Y` is proper and smooth
of relative dimension 1 over `ℚ`, and `Φ` is natural in the field: the class of a point pulled
back along `f : K → L` is the base change of the class. -/
def R1fpProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom ∧
  ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y) (P : QML3 K), Φ K y = M3.mk P →
      ∃ Q : QML3 L, Φ L (fieldMap f ≫ y) = M3.mk Q ∧ IsBaseChangeOf (f : K →+* L) P Q

/-- **R1hecke, clause list**: each operation `twist α` (`α ∈ Aut 𝒪`) and `rightMul u`
(`u ∈ 𝒪^×`) of `Γ'` on the moduli problem is induced by an automorphism of `Y` over `ℚ`. -/
def R1heckeProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  (∀ α : O ≃+* O, ∃ g : Y ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      Φ K (y ≫ g.hom) = M3.twist α (Φ K y)) ∧
  (∀ u : Oˣ, ∃ g : Y ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      Φ K (y ≫ g.hom) = M3.rightMul u (Φ K y))

/-- **R2fp, clause list**: a morphism `π : Y → P¹` whose fibres on `ℚ̄`-points are exactly the
classes with `Aut(𝒪)`-twist-equivalent underlying QM pairs (the `W`-orbits on `X₆`), and which
takes the values `0, ∞, −16/27` at the CM points of discriminants `−4, −3, −24`. -/
def R2fpProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar),
    Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
      (HasCM4 P.q → π.val (K := Qbar) y.left = OnePoint.some 0) ∧
      (HasCM3 P.q → π.val (K := Qbar) y.left = OnePoint.infty) ∧
      (HasCM24 P.q → π.val (K := Qbar) y.left = OnePoint.some (-16 / 27))

/-- The `Aut(𝒪)`-twist of a QM pair (the `W`-action on `X₆`, inner twists being trivial on
classes). -/
def QMPair.twist (P : QMPair K) (α : O ≃+* O) : QMPair K := ⟨P.A, P.surface, P.q.twist α⟩

/-- **The level-one curve `X₆ = X₀(6,1)`, clause list** (coarse moduli on `ℚ̄`-points): `X` is a
proper smooth curve over `ℚ`; `Ψ : X(ℚ̄) ≃ {QM pairs over ℚ̄}/≅` is Galois-equivariant; each twist
`α ∈ Aut 𝒪` is induced by an automorphism of `X` over `ℚ` (the Atkin–Lehner group `W`); the
forgetful morphism `fY : Y₃ → X₆` is `(A, ι, η) ↦ (A, ι)` on `ℚ̄`-points. -/
def X6Props (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) : Prop :=
  IsProper X.hom ∧ SmoothOfRelativeDimension 1 X.hom ∧
  (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar),
    Ψ x = Quotient.mk _ P → ∃ Q : QMPair Qbar,
      Ψ (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = Quotient.mk _ Q ∧
      IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q) ∧
  (∀ α : O ≃+* O, ∃ g : X ≅ X, ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar),
    Ψ x = Quotient.mk _ P → Ψ (x ≫ g.hom) = Quotient.mk _ (P.twist α)) ∧
  (∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
    Ψ (y ≫ fY) = Quotient.mk _ P.forget)

/-- **R2 on `X₆` (Baba–Granath), clause list**: `π₆ : X₆ → X₆/W ≅ P¹`; two `ℚ̄`-points have the
same value iff their QM pairs are `Aut(𝒪)`-twists of each other (`W`-conjugate); the CM points
of discriminants `−4, −3, −24` go to `0, ∞, −16/27`. -/
def R2X6Props (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (π₆ : ToP1 X.left) : Prop :=
  ∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
    Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
      (π₆.val (K := Qbar) x.left = π₆.val (K := Qbar) x'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
      (HasCM4 P.q → π₆.val (K := Qbar) x.left = OnePoint.some 0) ∧
      (HasCM3 P.q → π₆.val (K := Qbar) x.left = OnePoint.infty) ∧
      (HasCM24 P.q → π₆.val (K := Qbar) x.left = OnePoint.some (-16 / 27))

/-- **Existence of the three CM points on `X₆`** (the "distinguished points" of Baba–Granath
Lemma 3.1 are images of CM points; CM points by `R` exist iff `R` embeds optimally in `𝒪`,
Shimura/Eichler; `ℤ[i], ℤ[ζ₃], ℤ[√−6]` do, by `i + j`, `(1 + j)/2`, `μ = 2j + k`). With the
fibre clause of `R2X6Props` and the invariance of `com` under twists (`com_twist`) and
isomorphisms, it gives the converse clauses "`π₆(x) = 0 ⇒` CM by `ℤ[i]`" etc. used by h-b1 M9. -/
def CMExists (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) : Prop :=
  (∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasCM4 P.q) ∧
  (∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasCM3 P.q) ∧
  (∃ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar), Ψ x = Quotient.mk _ P ∧ HasCM24 P.q)

/-- **Glue (compiled), h-b1 M9 on `X₆`**: every `ℚ̄`-point of `X₆` over `0` (resp. `∞`,
`−16/27`) has CM by `ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`), from the fibre clause, the existence of
one such CM point, and the invariance of the CM predicates under twists and isomorphisms. -/
theorem cm_of_val {X : Over (Spec (CommRingCat.of ℚ))}
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {π₆ : ToP1 X.left}
    (h2 : R2X6Props X Ψ π₆) (hE : CMExists X Ψ) (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar)
    (hP : Ψ x = Quotient.mk _ P) :
    (π₆.val (K := Qbar) x.left = OnePoint.some 0 → HasCM4 P.q) ∧
    (π₆.val (K := Qbar) x.left = OnePoint.infty → HasCM3 P.q) ∧
    (π₆.val (K := Qbar) x.left = OnePoint.some (-16 / 27) → HasCM24 P.q) := by
  obtain ⟨⟨x₄, P₄, h₄, c₄⟩, ⟨x₃, P₃, h₃, c₃⟩, ⟨x₂, P₂, h₂, c₂⟩⟩ := hE
  refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨α, ⟨g⟩⟩ := ((h2 x₄ x P₄ P h₄ hP).1).1 (((h2 x₄ x₄ P₄ P₄ h₄ h₄).2.1 c₄).trans hx.symm)
    exact HasCM4.of_iso g ((hasCM4_twist P₄.q α).2 c₄)
  · obtain ⟨α, ⟨g⟩⟩ := ((h2 x₃ x P₃ P h₃ hP).1).1
      (((h2 x₃ x₃ P₃ P₃ h₃ h₃).2.2.1 c₃).trans hx.symm)
    exact HasCM3.of_iso g ((hasCM3_twist P₃.q α).2 c₃)
  · obtain ⟨α, ⟨g⟩⟩ := ((h2 x₂ x P₂ P h₂ hP).1).1
      (((h2 x₂ x₂ P₂ P₂ h₂ h₂).2.2.2 c₂).trans hx.symm)
    exact HasCM24.of_iso g ((hasCM24_twist P₂.q α).2 c₂)

/-- **Glue (compiled): R2 on `Y₃` from R2 on `X₆`**, for `π = π₆ ∘ fY` (`ToP1.comp`). -/
theorem R2fpProps_of_X6 {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} {π₆ : ToP1 X.left} (hX : X6Props Y Φ X Ψ fY)
    (h2 : R2X6Props X Ψ π₆) : R2fpProps Y Φ (π₆.comp fY.left) := by
  obtain ⟨-, -, -, -, hf⟩ := hX
  intro y y' P Q hP hQ
  have h := h2 (y ≫ fY) (y' ≫ fY) P.forget Q.forget (hf y P hP) (hf y' Q hQ)
  have e : ∀ z : fieldPt Qbar ⟶ Y,
      (π₆.comp fY.left).val (K := Qbar) z.left = π₆.val (K := Qbar) (z ≫ fY).left :=
    fun z => ToP1.val_comp_right π₆ fY.left z.left
  rw [e y, e y']
  exact h

/-- **Leaf R1fp (field-point form of Shimura–Deligne R1(a)).**

*Published statement* (Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), Thm 4.21,
Cor. 5.7, Ex. 5.8, §§4.8-4.17 (read by the locator audit; printed page mapping not recovered);
Shimura, Ann. of Math. 85 (1967), Main Thms I-II (UNVERIFIED); alternatively Buzzard, Duke Math.
J. 87 (1997), Thm 2.1, Cor. 2.3 (UNVERIFIED), for `(A, ι)` with level structure and no
polarization): for the maximal order `𝒪` of `B = (2,−3)` and the neat level `K₃`, the functor on
`ℚ`-schemes of `(A, ι, λ, η)` (abelian surface scheme, `𝒪`-action, principal polarization with
Rosati involution `a ↦ μ⁻¹āμ`, `𝒪`-linear `η : 𝒪/3𝒪 ≅ A[3]`) is represented by a smooth
projective curve `Y₃/ℚ`.

*Lean form*: some `Y` over `ℚ`, proper and smooth of relative dimension 1, with bijections
`Y(K) ≃ M3 K` for all fields `K ⊇ ℚ`, natural in `K`.

*Why faithful (a consequence, never stronger)*: restrict the representing isomorphism to
`Spec K` for fields `K`; projective implies proper. `M3 K` drops `λ` (bp-qmmoduli §2.2: for this
datum `λ` exists and is unique in characteristic 0; SPECULATIVE until reviewed, lattice core
proved as `BPQM.eq_pm_E0_of_principal`; not needed on Buzzard's route), and puts `η` on
`K`-points (equivalent in characteristic 0, §2 docstring). `Y` is **not** required to be
geometrically connected (it has two geometric components over `ℚ(√−3)`, bp-qmmoduli §2.1). -/
def R1fp : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ

/-- **Leaves R1fp + R1hecke + R1 at level one + R2fp, on one `Y₃` and one `X₆`** (the form the
glue consumes; `R1R2fp_Y` extracts the `Y₃` form).

*R1 at level one (`X6Props`), published statement*: `X₆ = X₀(6,1)` (Shimura's curve for the
maximal order, no level) is a coarse moduli space over `ℚ` for `(A, ι, λ)` (Shimura 1967, Deligne
1971 as for R1fp; UNVERIFIED as a literal locator, the audit read Deligne's §§4.9-4.17); the
Atkin–Lehner group acts on it over `ℚ`. *Why faithful*: coarse moduli give `X₆(ℚ̄) = {(A, ι)}/≅`
Galois-equivariantly in characteristic 0; the twists `(A, ι) ↦ (A, ι∘α)` are natural in families,
so the coarse space inherits them; `Y₃ → X₆` exists by the coarse universal property; the
morphism `Y₃ → P¹` is `π₆ ∘ fY` (`ToP1.comp`, `R1R2fp_Y`). Smooth proper curve: `X₆` is the quotient of `ℍ` by a cocompact Fuchsian group without
cusps; its canonical model is smooth projective over `ℚ` (it is a smooth curve because a
coarse space of a one-dimensional smooth DM stack in characteristic 0 is a normal curve).

*R1hecke, published statement*: the finite-adelic normalizer of `K₃` acts on `Y₃` over `ℚ`
(Deligne 1971 §§4.15-4.21, Deligne 1979 §2.7, UNVERIFIED; the audit: at fixed level only the
subgroup preserving the level and the datum acts). *Why faithful*: `twist α` and `rightMul u`
are natural automorphisms of the moduli functor (they are defined for families over any base:
`(A, ι, η) ↦ (A, ι∘α, η∘α)` and `η ↦ η(·u)`), so by Yoneda each is induced by an automorphism of
the representing scheme. This is a consequence of R1(a) alone; on field points it is this
clause. (`α = Ad n`, `n ∈ N_B(𝒪)`, by Skolem–Noether T13; `u` acts through `(𝒪/3𝒪)^×`,
`Level3.rightMul_eq_self`.)

*R2fp, published statement* (Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 p. 737 and
Lemma 3.1 pp. 739-740, read by the audit: YES): the forgetful map identifies the polarized
moduli space with `X₆/W`, `W ≅ (ℤ/2)²` the Atkin–Lehner group; `X₆/W ≅ P¹_ℚ`; the images of the
CM points of discriminants `−4, −3, −24` are rational. *Lean form*: `π = (Y₃ → X₆ → X₆/W ≅ P¹)`,
with the coordinate chosen so that the three CM images are `0, ∞, −16/27` (three distinct
rational points of `P¹_ℚ` can be moved to any three by `PGL₂(ℚ)`; so this normalization adds
nothing; identifying `π` with N5's `J` is F1's business, `PkgI1.QMHauptmodul`). Fibre clause:
two `ℚ̄`-points have the same image in `X₆/W` iff their `(A, ι)` are `W`-conjugate, i.e.
`(A', ι') ≅ (A, ι ∘ Ad w)`; `Aut(𝒪) = N_B(𝒪)/ℚ^×` (Skolem–Noether) and inner twists are trivial
on classes (`ι(u)` is an isomorphism `(A, ι∘Ad u) ≅ (A, ι)`), so `W`-conjugacy is
`∃ α ∈ Aut 𝒪`. **Not asserted**: the orbifold orders `(4, 6, 2)` (they are not ramification
indices of `X₆ → X₆/W`, which are `(2, 2, 2)`; the indices `(4, 6, 2)` of `Y₃ → P¹` are glue,
`RvNocm.ramification_eq_orbifold_order`). Composite: R2fp's fibre clause uses R1 (the forgetful
morphism `Y₃ → X₆` and the moduli interpretation of `X₆`) together with Baba–Granath. -/
def R1R2fp : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6Props X Ψ π₆ ∧
      CMExists X Ψ

theorem R1fp_of_R1R2fp (h : R1R2fp) : R1fp := by
  obtain ⟨Y, Φ, -, -, -, -, h1, -, -, -, -⟩ := h
  exact ⟨Y, Φ, h1⟩

/-- The form consumed on `Y₃`: R1fp + R1hecke + R2fp on one `Y` with one `π`. -/
theorem R1R2fp_Y (h : R1R2fp) : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (π : ToP1 Y.left), R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ R2fpProps Y Φ π := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, hX, h2, -⟩ := h
  exact ⟨Y, Φ, π₆.comp fY.left, h1, hh, R2fpProps_of_X6 hX h2⟩

/-- **Glue A7 from R1fp + R2fp (compiled).** Let `y` be a `ℚ̄`-point of `Y` with object `P` whose
`π`-value is rational. Then every Galois conjugate of `P` (its base change `Q` along `σ`) has an
underlying QM pair that is an `Aut(𝒪)`-twist of `P`'s; in particular `σA ≅ A` over `ℚ̄`
(h-trust A7: "the conjugates of `A` are geometrically isomorphic"). -/
theorem conj_twist_of_rational {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) (π : ToP1 Y.left)
    (hfib : ∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar),
      Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)))
    (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar) (hP : Φ Qbar y = M3.mk P) (j₀ : ℚ)
    (hj : π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀))
    (σ : Qbar ≃ₐ[ℚ] Qbar) :
    ∃ Q : QML3 Qbar, IsBaseChangeOf (σ : Qbar →+* Qbar) P Q ∧
      ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q) := by
  obtain ⟨-, -, hnat⟩ := h1
  obtain ⟨Q, hQ, hbc⟩ := hnat Qbar Qbar (σ : Qbar →ₐ[ℚ] Qbar) y P hP
  refine ⟨Q, hbc, (hfib y _ P Q hP hQ).1 ?_⟩
  calc π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) := hj
    _ = (OnePoint.some (algebraMap ℚ Qbar j₀)).map (σ : Qbar →+* Qbar) := by simp
    _ = (π.val (K := Qbar) y.left).map (σ : Qbar →+* Qbar) := by rw [hj]
    _ = π.val (K := Qbar) (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y).left :=
        (π.val_comp (σ : Qbar →+* Qbar) y.left).symm

/-- **Glue A7 (compiled), the manuscript's form.** Let `y` be a `K`-point of `Y` (e.g. `K` the
fibre field) with object `P` and rational `π`-value. For any two embeddings `ι₁, ι₂ : K → ℚ̄`, the
two base changes `P ⊗_{ι₁} ℚ̄`, `P ⊗_{ι₂} ℚ̄` exist as objects and their QM pairs are
`Aut(𝒪)`-twists of each other; in particular their abelian surfaces are isomorphic over `ℚ̄`
("every conjugate `σA` is isomorphic to `A` over `ℚ̄`", pkg-I1 (I1-out)(ii)). Uses only
`R1fpProps` (naturality) and `R2fpProps` (fibre clause), via `ToP1.val_comp`. -/
theorem conj_iso_of_rational {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π)
    {K : Type} [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K) (hP : Φ K y = M3.mk P)
    (j₀ : ℚ) (hj : π.val (K := K) y.left = OnePoint.some (algebraMap ℚ K j₀))
    (e₁ e₂ : K →ₐ[ℚ] Qbar) :
    ∃ Q₁ Q₂ : QML3 Qbar, IsBaseChangeOf (e₁ : K →+* Qbar) P Q₁ ∧
      IsBaseChangeOf (e₂ : K →+* Qbar) P Q₂ ∧
      ∃ α : O ≃+* O, Nonempty (QMIso (Q₁.q.twist α) Q₂.q) := by
  obtain ⟨-, -, hnat⟩ := h1
  obtain ⟨Q₁, hQ₁, hb₁⟩ := hnat K Qbar e₁ y P hP
  obtain ⟨Q₂, hQ₂, hb₂⟩ := hnat K Qbar e₂ y P hP
  refine ⟨Q₁, Q₂, hb₁, hb₂, ((h2 _ _ Q₁ Q₂ hQ₁ hQ₂).1).1 ?_⟩
  have e : ∀ e : K →ₐ[ℚ] Qbar, π.val (K := Qbar) (fieldMap e ≫ y).left =
      OnePoint.some (algebraMap ℚ Qbar j₀) := by
    intro e
    calc π.val (K := Qbar) (fieldMap e ≫ y).left
        = (π.val (K := K) y.left).map (e : K →+* Qbar) := π.val_comp (e : K →+* Qbar) y.left
      _ = OnePoint.some (algebraMap ℚ Qbar j₀) := by rw [hj]; simp
  rw [e e₁, e e₂]

/-- The underlying abelian surfaces of a QM-pair twist are isomorphic (A7's conclusion). -/
theorem QMIso.nonempty_abVarIso {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'}
    (f : QMIso q q') : ∃ (φ : AbVar.Hom A A') (ψ : AbVar.Hom A' A),
      φ.hom ≫ ψ.hom = 𝟙 _ ∧ ψ.hom ≫ φ.hom = 𝟙 _ :=
  ⟨f.φ, f.ψ, f.left, f.right⟩

/-- **Leaf R1rec (Shimura reciprocity at the three elliptic CM points, unramified form).**

*Published statement*: Shimura reciprocity for CM points on the canonical model (Shimura 1967
Main Thm II; Deligne 1971 §§3.7-3.13, Thm 4.19 read by the audit, "CONSEQUENCE with
qualifications": reflex-field qualifications kept). For a CM point `y ∈ Y₃` with CM by the
maximal order `𝒪_E` of `E`, `Gal(E^ab/E)` acts on `y` through `rec : 𝔸_E^× → B̂^×/K₃`, and
`s ∈ ∏_{ℓ≠3} 𝒪_{E,ℓ}^×` maps into `K₃`, so `E(y)/E` is unramified outside `3` (h-b1 §3 step 2).

*Lean form*: for a level-3 object over `ℚ̄` whose centralizer contains `ℤ[i]`, `ℤ[ζ₃]` or
`ℤ[√−6]` (all maximal), the field of moduli `ℚ(y)` is a number field unramified at every
`p ≥ 5`.

*Why faithful*: `ℚ(y) ⊆ E(y)`, `E(y)/E` is unramified outside 3 and `E/ℚ` (discriminant `−4`,
`−3`, `−24`) is unramified outside `{2, 3}`; the field of moduli is `ℚ(y)` (fine moduli, R1). A
consequence of reciprocity plus R1's moduli interpretation; weaker than reciprocity. -/
def R1rec : Prop :=
  ∀ P : QML3 Qbar, (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) →
    UnramifiedAbove5 (fieldOfModuli3 P)

/-- The conductor `[𝒪_k : R]` of a subring `R ⊆ 𝒪_k` (0 if the index is infinite). -/
def conductor {k : Type} [Field k] (R : Subring k) : ℕ :=
  R.toAddSubgroup.relIndex (integralClosure ℤ k).toSubring.toAddSubgroup

open Classical in
/-- `b(k) = #{p ∣ 6 : p inert in k}` (`p·𝒪_k` prime). For an order of conductor prime to 6 this
is `b(R) = #{p ∣ D(R)}` of rv-nocm §3.1. -/
def inertCount6 (k : Type) [Field k] [NumberField k] : ℕ :=
  (if (Ideal.span {(2 : NumberField.RingOfIntegers k)}).IsPrime then 1 else 0) +
    (if (Ideal.span {(3 : NumberField.RingOfIntegers k)}).IsPrime then 1 else 0)

/-- **Leaf R5fp (González–Rotger, fields of definition of CM points on `X₆`, degree form).**

*Published statement* (González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946, with
Thm 5.8, pp. 943-944, read by the audit in arXiv v1/v2 and the journal: YES on `X₀(D, N)`): for a
CM point `x ∈ X₀(6,1)` by an order `R` of conductor `f`, `(f, 6) = 1`, of an imaginary quadratic
`k`: `ℚ(x) = H_R` (the ring class field, `[H_R : ℚ] = 2h(R)`) if `D(R) ≠ 1`, and `ℚ(x)` is a
specified subfield of index 2 of `H_R` if `D(R) = 1`; `D(R)` = product of the primes `p ∣ 6`
inert in `k` (rv-nocm §3.1, h-decomposition R5).

*Lean form*: for a QM pair over `ℚ̄` with `End_𝒪(A) ≅ R`,
`[ℚ(x) : ℚ] = 2h(R)` if `b(k) ≥ 1` and `h(R)` if `b(k) = 0`, `h(R) = #Pic(R)`; and if
`b(k) ≥ 1`, `k` embeds in `ℚ(x)` (from `ℚ(x) = H_R ⊇ k`). The containment is needed by NoCM
(rv-h-cm §7.2, case `D(R) ≠ 1`): the degree alone does not exclude `k = ℚ(√−19)` (`h = 1`,
`b = 2`, degree 2) against a fibre field `ℚ(i)`.

*Why faithful*: the degree of the printed field; `ℚ(x)` is the field of moduli for the coarse
space `X₆` (STANDARD); the points of `X₆` are QM pairs `(A, ι)` (polarization unique, as in R1fp);
"CM by `R`" is `End_𝒪(A) = com ι ≅ R`. Only points of `X₆` (no level structure, no quotient). The
reading `D(R) = ∏_{p | 6 inert in k} p` is the audited one (checked on Elkies' 24 rows by
rv-nocm Part B); `R5fpWeak` below drops the case split. -/
def R5fp : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      ∀ P : QMPair Qbar, Nonempty (com P.q ≃+* R) →
        Module.finrank ℚ (fieldOfModuliPair P) =
          (if inertCount6 k = 0 then 1 else 2) * Nat.card (CommRing.Pic R) ∧
        (inertCount6 k ≠ 0 → Nonempty (k →ₐ[ℚ] fieldOfModuliPair P))

/-- R5fp without the case split (bp-qmmoduli's `R5fp`): `[ℚ(x) : ℚ] ∈ {h(R), 2h(R)}`. -/
def R5fpWeak : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      ∀ P : QMPair Qbar, Nonempty (com P.q ≃+* R) →
        Module.finrank ℚ (fieldOfModuliPair P) = Nat.card (CommRing.Pic R) ∨
          Module.finrank ℚ (fieldOfModuliPair P) = 2 * Nat.card (CommRing.Pic R)

theorem R5fpWeak_of_R5fp (h : R5fp) : R5fpWeak := by
  intro k _ _ _ hk R hR hc P hP
  have := (h k hk R hR hc P hP).1
  split_ifs at this
  · left; simpa using this
  · right; exact this

/-- **Leaf R5fpCount (González–Rotger Prop. 5.6, p. 943, read by the audit; Jordan 1981 §3),
corrected count.** For an order `R` of conductor prime to 6 in an imaginary quadratic `k`
occurring as some `End_𝒪(A)` (equivalently, embedding optimally in `𝒪`, so neither 2 nor 3
splits in `k`), the number of isomorphism classes of QM pairs over `ℚ̄` with `End_𝒪(A) ≅ R` (the
CM points by `R` on `X₆ = X₀(6,1)`) is `2^{b(R)} h(R)`. *Why faithful*: `#CM(R) =
2^{#{p | D(R)N(R)}} h(R)` with `N = 1`; points of `X₆(ℚ̄)` are classes of QM pairs. **Not** the
false `h(R)` (disc −19: `h = 1`, four points). -/
def R5fpCount : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      (∃ P : QMPair Qbar, Nonempty (com P.q ≃+* R)) →
        Nat.card {c : Quotient (pairSetoid Qbar) //
            ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)} =
          2 ^ inertCount6 k * Nat.card (CommRing.Pic R)

/-- **The bundle of this file's leaves** (replacing the placeholders `R01_ShimuraDeligne`,
`R02_BabaGranath`, `R05_GonzalezRotger` of `scratch/h-decomposition/Leaves.lean`, in their
field-point forms). -/
structure QMLeaves : Prop where
  r1r2 : R1R2fp
  r1rec : R1rec
  r5 : R5fp
  r5count : R5fpCount

end AV

end LeafQM

#print axioms LeafQM.AV.R1fp_of_R1R2fp
#print axioms LeafQM.AV.R5fpWeak_of_R5fp
#print axioms LeafQM.AV.com_twist
#print axioms LeafQM.AV.Level3.rightMul_eq_self
#print axioms LeafQM.AV.not_qmStr_zero
#print axioms LeafQM.AV.isoSetoid
#print axioms LeafQM.AV.M3.twist
#print axioms LeafQM.AV.ToP1.val
#print axioms LeafQM.AV.fieldMap
#print axioms LeafQM.AV.QMLeaves
#print axioms LeafQM.AV.ToP1.val_comp
#print axioms LeafQM.AV.conj_twist_of_rational
#print axioms LeafQM.AV.R1R2fp_Y
#print axioms LeafQM.AV.conj_iso_of_rational
#print axioms LeafQM.AV.cm_of_val
#print axioms LeafQM.AV.ToP1.val_comp_right
#print axioms LeafQM.AV.HasCM3.of_iso

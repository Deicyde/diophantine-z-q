import ZInQKernel.HDecomp.Objects
import Mathlib.Algebra.Module.RingHom
import Mathlib.Tactic

/-!
# bp-qmmoduli, layer 2: QM structures and level-3 structures on abelian varieties

Over the kernel's object layer `ZInQKernel/HDecomp/Objects.lean` (`PkgI3.AbVar K`: a group object
of `Over (Spec K)`, proper, smooth, geometrically integral; `End`, points `A(L)`, Galois action).
Blueprint `docs/research/bp-qmmoduli.md` §3, nodes N5-N8.

* `QMStr A`: an injective unital ring homomorphism `ι : 𝒪 → End_K(A)`.
* `qmAct`: the induced action of `𝒪` on `A(L)` (a ring homomorphism `𝒪 → End(A(L))`).
* `Level3 q`: an `𝒪`-linear isomorphism `𝒪/3𝒪 ≅ A(K̄)[3]` whose image is `Gal(K̄/K)`-fixed
  (i.e. `A[3]` is constant over `K` and trivialized `𝒪`-linearly), in the form used by A6
  (`PkgI2.goodReduction_of_QM_rational3`, hypothesis `hrat`).
* `QML3 K`: an abelian surface with QM by `𝒪` and a level-3 structure; isomorphisms `QML3.Iso`;
  the set of isomorphism classes `M3 K` (the field-valued points of the moduli problem, with the
  polarization dropped: for this datum it is unique and exists, blueprint §2.2, and its lattice
  form is `BPQM.eq_pm_E0_of_principal` in `QMOrder.lean`).
* The action of `Aut(𝒪)` (`twist`) and of `𝒪^×` (`rightMul`) on `(ι, η)` with `A` fixed: the
  group `Γ'` of A3, and the proof that units `≡ 1 mod 3𝒪` act trivially on level structures.
* Sanity: the zero abelian variety has no QM structure.

The quaternion datum is copied from `QMOrder.lean` (scratch files cannot import each other).
No `sorry`, no `axiom`.
-/

noncomputable section

namespace BPQM

/-! ## §0 The order `𝒪` (copied from `QMOrder.lean` §1) -/

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

/-! ## §1 The action of `End_K(A)` on `L`-points -/

section EndPt

variable (A : AbVar K) (L : Type) [Field L] [Algebra K L]

/-- `End_K(A) → End(A(L))`, `f ↦ (P ↦ P ≫ f)`, a ring homomorphism (`End` multiplies by
`f * g = f ∘ g`). -/
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

@[simp] theorem endPt_apply (f : AbVar.End A) (x : Additive (A.Pt L)) :
    endPt A L f x = Additive.ofMul (Additive.toMul x ≫ f.hom) := rfl

end EndPt

/-! ## §2 QM structures -/

/-- **A QM structure by `𝒪` on `A`**: an injective unital ring homomorphism `𝒪 → End_K(A)`.
(N5's `ι : 𝒪 ↪ End_K(A)`; with `A.dim = 2` this is an abelian surface with QM by the maximal
order of discriminant 6, defined over `K`.) -/
structure QMStr (A : AbVar K) where
  iota : O →+* AbVar.End A
  injective : Function.Injective iota

/-- The induced action of `𝒪` on `A(L)`. -/
def qmAct {A : AbVar K} (q : QMStr A) (L : Type) [Field L] [Algebra K L] :
    O →+* AddMonoid.End (Additive (A.Pt L)) :=
  (endPt A L).comp q.iota

/-- `A(L)` as an `𝒪`-module (a definition, not an instance). -/
abbrev qmModule {A : AbVar K} (q : QMStr A) (L : Type) [Field L] [Algebra K L] :
    Module O (Additive (A.Pt L)) :=
  Module.compHom (Additive (A.Pt L)) (qmAct q L)

/-- **Sanity: the zero abelian variety carries no QM structure** (its `End` is the zero ring). -/
theorem not_qmStr_zero : IsEmpty (QMStr (AbVar.zero K)) := by
  constructor
  intro q
  have hsub : ∀ f g : AbVar.End (AbVar.zero K), f = g := by
    intro f g
    apply AbVar.Hom.ext'
    exact CartesianMonoidalCategory.toUnit_unique _ _
  exact O_nontrivial (q.injective (hsub _ _))

/-! ## §3 Level-3 structures -/

/-- `Kbar = AlgebraicClosure K`. -/
abbrev Kbar (K : Type) [Field K] := AlgebraicClosure K

/-- The Galois action on `A(K̄)`, written additively. -/
def galAdd (A : AbVar K) (σ : Kbar K ≃ₐ[K] Kbar K) :
    Additive (A.Pt (Kbar K)) →+ Additive (A.Pt (Kbar K)) :=
  (A.galAct σ).toAdditive

/-- **A level-3 structure** on `(A, ι)`: an additive map `η : 𝒪 → A(K̄)` that is `𝒪`-linear,
has kernel exactly `3𝒪`, has image all of `A(K̄)[3]`, and is `Gal(K̄/K)`-invariant pointwise.
Equivalently, an `𝒪`-linear isomorphism `𝒪/3𝒪 ≅ A[3]` of constant group schemes over `K`
(the `K₃`-structure of h-trust A4 item 3; constancy is the hypothesis `hrat` of A6). -/
structure Level3 {A : AbVar K} (q : QMStr A) where
  eta : O →+ Additive (A.Pt (Kbar K))
  linear : ∀ a b : O, eta (a * b) = qmAct q (Kbar K) a (eta b)
  ker : ∀ a : O, eta a = 0 ↔ ∃ b : O, a = 3 * b
  onto : ∀ x : Additive (A.Pt (Kbar K)), (3 : ℕ) • x = 0 → ∃ a : O, eta a = x
  rational : ∀ (σ : Kbar K ≃ₐ[K] Kbar K) (a : O), galAdd A σ (eta a) = eta a

namespace Level3

variable {A : AbVar K} {q : QMStr A}

/-- The level-3 points are 3-torsion. -/
theorem tors (e : Level3 q) (a : O) : (3 : ℕ) • e.eta a = 0 := by
  rw [← map_nsmul, e.ker]
  exact ⟨a, by simp [nsmul_eq_mul]⟩

/-- `η` is injective modulo `3𝒪`. -/
theorem eq_iff (e : Level3 q) (a b : O) : e.eta a = e.eta b ↔ ∃ c : O, a - b = 3 * c := by
  rw [← sub_eq_zero, ← map_sub, e.ker]

/-- **`𝒪^×` acts on level structures by right multiplication** (`η ↦ η(· u)`, same `A`, same
`ι`): the level-3 part of the group `Γ'` of A3. -/
def rightMul (e : Level3 q) (u : Oˣ) : Level3 q where
  eta := e.eta.comp (AddMonoidHom.mulRight (u : O))
  linear a b := by simp [_root_.mul_assoc, e.linear]
  ker a := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulRight]
    rw [e.ker]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c * ↑u⁻¹, by rw [← _root_.mul_assoc, ← hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c * u, by rw [_root_.mul_assoc]⟩
  onto x hx := by
    obtain ⟨a, ha⟩ := e.onto x hx
    exact ⟨a * ↑u⁻¹, by simp [_root_.mul_assoc, ha]⟩
  rational σ a := e.rational σ _

/-- **Units `≡ 1 mod 3𝒪` act trivially**: so the action of `𝒪^×` factors through
`(𝒪/3𝒪)^×` (of order 72, h-trust A3). -/
theorem rightMul_eq_self (e : Level3 q) (u : Oˣ) (hu : ∃ c : O, (u : O) - 1 = 3 * c) (a : O) :
    (e.rightMul u).eta a = e.eta a := by
  change e.eta (a * u) = e.eta a
  rw [e.eq_iff]
  obtain ⟨c, hc⟩ := hu
  refine ⟨a * c, ?_⟩
  calc a * ↑u - a = a * (↑u - 1) := by noncomm_ring
    _ = a * (3 * c) := by rw [hc]
    _ = 3 * (a * c) := by noncomm_ring

end Level3

/-- **`Aut(𝒪)` acts on `(ι, η)` with `A` fixed**: `(ι, η) ↦ (ι ∘ α, η ∘ α)`. For `α = Ad(n)`,
`n ∈ N_B(𝒪)` (every automorphism of `𝒪` is of this form by Skolem–Noether, T13), this is the
action `(A, ι, η) ↦ (A, ι ∘ Ad(n), η ∘ Ad(n))` of the normalizer in pkg-I1's I1-a(2). -/
def QMStr.twist {A : AbVar K} (q : QMStr A) (α : O ≃+* O) : QMStr A where
  iota := q.iota.comp α.toRingHom
  injective := q.injective.comp α.injective

def Level3.twist {A : AbVar K} {q : QMStr A} (e : Level3 q) (α : O ≃+* O) :
    Level3 (q.twist α) where
  eta := e.eta.comp α.toAddMonoidHom
  linear a b := by
    change e.eta (α (a * b)) = qmAct q (Kbar K) (α a) (e.eta (α b))
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
  onto x hx := by
    obtain ⟨a, ha⟩ := e.onto x hx
    exact ⟨α.symm a, by simp [ha]⟩
  rational σ a := e.rational σ _

/-! ## §4 The objects of the moduli problem and their isomorphism classes -/

/-- **An abelian surface over `K` with QM by `𝒪` and a level-3 structure** (the polarization is
omitted: see the module docstring). -/
structure QML3 (K : Type) [Field K] where
  A : AbVar K
  surface : A.dim = 2
  q : QMStr A
  e : Level3 q

/-- An isomorphism of QM surfaces with level structure: an isomorphism `φ : A ≅ A'` of abelian
varieties, `𝒪`-equivariant, carrying `η` to `η'`. -/
structure QML3.Iso (P Q : QML3 K) where
  φ : AbVar.Hom P.A Q.A
  ψ : AbVar.Hom Q.A P.A
  left : φ.hom ≫ ψ.hom = 𝟙 _
  right : ψ.hom ≫ φ.hom = 𝟙 _
  equivariant : ∀ a : O, (P.q.iota a).hom ≫ φ.hom = φ.hom ≫ (Q.q.iota a).hom
  level : ∀ a : O, Additive.ofMul (Additive.toMul (P.e.eta a) ≫ φ.hom) = Q.e.eta a

/-- The identity isomorphism. -/
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

/-- **The field-valued points of the moduli problem**: isomorphism classes of `QML3 K`. The
leaf R1 in its field-point form (blueprint §2.3, statement `R1fp`) says that `K ↦ M3 K` is
`K ↦ Y₃(K)` for a smooth projective curve `Y₃/ℚ`, naturally in `K`. -/
def M3 (K : Type) [Field K] : Type 1 := Quot (fun P Q : QML3 K => Nonempty (P.Iso Q))

/-- The `Γ'`-action changes only `(ι, η)`, never `A` (A7's "conjugates are fibres of one
`Γ'`-orbit", h-trust A7 Remark). -/
def QML3.twist (P : QML3 K) (α : O ≃+* O) : QML3 K :=
  ⟨P.A, P.surface, P.q.twist α, P.e.twist α⟩

theorem QML3.twist_A (P : QML3 K) (α : O ≃+* O) : (P.twist α).A = P.A := rfl

def QML3.rightMul (P : QML3 K) (u : Oˣ) : QML3 K :=
  ⟨P.A, P.surface, P.q, P.e.rightMul u⟩

theorem QML3.rightMul_A (P : QML3 K) (u : Oˣ) : (P.rightMul u).A = P.A := rfl

end AV

end BPQM

#print axioms BPQM.AV.not_qmStr_zero
#print axioms BPQM.AV.Level3.rightMul_eq_self
#print axioms BPQM.AV.Level3.twist
#print axioms BPQM.AV.QML3.Iso.refl

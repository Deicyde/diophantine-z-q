import ZInQKernel.HDecomp.A6.A6
import Mathlib.Algebra.Module.RingHom
import Mathlib.Tactic

/-!
# bp-qmmoduli, layer 2: QM structures and level-3 structures on abelian varieties

Over the kernel's object layer `ZInQKernel/HDecomp/Objects.lean` (imported through
`ZInQKernel/HDecomp/A6/A6.lean`; run `lake build ZInQKernel.HDecomp.A6.A6` first) (`PkgI3.AbVar K`: a group object
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
* **Glue A6 on the moduli objects** (`QML3.goodReduction`): every `QML3` object over `K` has good
  reduction at every DVR of `K` in which 3 is a unit, from the kernel's A6 theorem
  (`GlueA6Alg.goodReduction_of_QM_rational3'`, leaves `NeronOggShafarevich`, `RaynaudCriterion`,
  `TorsionStructure`), with `I = ι(i)`, `J = ι(j)` and the level structure supplying its
  hypotheses.

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

/-! ## §5 Glue: step A6 (good reduction away from 3) holds for every object of the moduli problem

The kernel's A6 theorem `GlueA6Alg.goodReduction_of_QM_rational3'`
(`ZInQKernel/HDecomp/A6/A6.lean`, from the leaves `NeronOggShafarevich`, `RaynaudCriterion`,
`TorsionStructure`) takes endomorphisms `I, J` with `I² = 2`, `J² = −3`, `IJ + JI = 0` on points and
a `Gal(K̄/K)`-fixed 3-torsion. A `QML3` object supplies them: `I = ι(i)`, `J = ι(j)`, and the
level structure. So A6 applies to every abelian surface with QM by `𝒪` and level-3 structure over
any field with a DVR in which 3 is a unit (h-decomposition: "the instantiation on N5's `A` (which
needs A4 and the moduli objects) is not in Lean"; this is that instantiation, for every object). -/

section A6

open ObjBridge

/-- `i ∈ 𝒪`. -/
def oi : O := ⟨ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩
/-- `j = −1 + 2·(1+j)/2 ∈ 𝒪`. -/
def oj : O := ⟨ofInt ![-1, 0, 2, 0], ⟨_, rfl⟩⟩

theorem oi_mul_oi : oi * oi = 2 := by
  apply Subtype.ext
  change ofInt ![0, 1, 0, 0] * ofInt ![0, 1, 0, 0] = (2 : B)
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem oj_mul_oj : oj * oj = -3 := by
  apply Subtype.ext
  change ofInt ![-1, 0, 2, 0] * ofInt ![-1, 0, 2, 0] = -(3 : B)
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem oj_mul_oi_add : oj * oi + oi * oj = 0 := by
  apply Subtype.ext
  change ofInt ![-1, 0, 2, 0] * ofInt ![0, 1, 0, 0] + ofInt ![0, 1, 0, 0] * ofInt ![-1, 0, 2, 0]
    = (0 : B)
  ext <;> simp [ofInt] <;> norm_num

variable (P : QML3 K)

/-- Composition with `ι(a)` on points is the `𝒪`-action. -/
theorem ofMul_comp_iota (a : O) (x : P.A.Pt (Kbar K)) :
    Additive.ofMul (x ≫ (P.q.iota a).hom) = qmAct P.q (Kbar K) a (Additive.ofMul x) := rfl

theorem act_mul_apply (a b : O) (y : Additive (P.A.Pt (Kbar K))) :
    qmAct P.q (Kbar K) (a * b) y = qmAct P.q (Kbar K) a (qmAct P.q (Kbar K) b y) := by
  rw [map_mul]; rfl

theorem hI (x : PkgI2.Pts (toGrp P.A) (Kbar K)) :
    (x ≫ (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oi)).hom.hom) ≫
      (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oi)).hom.hom = x ^ 2 := by
  apply Additive.ofMul.injective
  rw [ofMul_pow]
  change qmAct P.q (Kbar K) oi (qmAct P.q (Kbar K) oi (Additive.ofMul x)) = _
  rw [← act_mul_apply, oi_mul_oi, map_ofNat]
  rfl

theorem hJ (x : PkgI2.Pts (toGrp P.A) (Kbar K)) :
    (x ≫ (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oj)).hom.hom) ≫
      (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oj)).hom.hom * x ^ 3 = 1 := by
  apply Additive.ofMul.injective
  rw [ofMul_mul, ofMul_pow, ofMul_one]
  have h : qmAct P.q (Kbar K) (oj * oj) (Additive.ofMul x : Additive (P.A.Pt (Kbar K)))
      = -((3 : ℕ) • (Additive.ofMul x : Additive (P.A.Pt (Kbar K)))) := by
    rw [oj_mul_oj, map_neg, map_ofNat]; rfl
  rw [act_mul_apply] at h
  exact (congrArg (· + (3 : ℕ) • (Additive.ofMul x : Additive (P.A.Pt (Kbar K)))) h).trans
    (neg_add_cancel _)

theorem hIJ (x : PkgI2.Pts (toGrp P.A) (Kbar K)) :
    (x ≫ (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oi)).hom.hom) ≫
        (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oj)).hom.hom *
      (x ≫ (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oj)).hom.hom) ≫
        (grpOfHom (A := toGrp P.A) (B := toGrp P.A) (P.q.iota oi)).hom.hom = 1 := by
  apply Additive.ofMul.injective
  rw [ofMul_mul, ofMul_one]
  have h : qmAct P.q (Kbar K) (oj * oi + oi * oj)
      (Additive.ofMul x : Additive (P.A.Pt (Kbar K))) = 0 := by
    rw [oj_mul_oi_add, map_zero]; rfl
  rw [map_add] at h
  have h2 : qmAct P.q (Kbar K) (oj * oi) (Additive.ofMul x : Additive (P.A.Pt (Kbar K))) +
      qmAct P.q (Kbar K) (oi * oj) (Additive.ofMul x : Additive (P.A.Pt (Kbar K))) = 0 := h
  rw [act_mul_apply, act_mul_apply] at h2
  exact h2

theorem hrat (σ : Kbar K ≃ₐ[K] Kbar K) (x : PkgI2.Pts (toGrp P.A) (Kbar K))
    (hx : x ∈ PkgI2.torsion (toGrp P.A) (Kbar K) 3) :
    PkgI2.galAct (toGrp P.A) σ x = x := by
  have h3 : (3 : ℕ) • Additive.ofMul x = 0 := by
    rw [← ofMul_pow]; exact congrArg Additive.ofMul hx
  obtain ⟨a, ha⟩ := P.e.onto (Additive.ofMul x) h3
  have := P.e.rational σ a
  rw [ha] at this
  exact Additive.ofMul.injective this

/-- **A6 for every QM surface with level-3 structure**: good reduction at every DVR of `K` in
which 3 is a unit, from the kernel's leaves `NeronOggShafarevich`, `RaynaudCriterion`,
`TorsionStructure`. -/
theorem QML3.goodReduction (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : PkgI2.RaynaudCriterion.{0}) (hTors : PkgI2.TorsionStructure.{0})
    (Ov : ValuationSubring K) [IsDiscreteValuationRing Ov] (h3 : IsUnit (3 : Ov)) :
    PkgI2.HasGoodReduction (toGrp P.A) Ov := by
  have hdim : topologicalKrullDim (toGrp P.A).X.left = ((2 : ℕ) : WithBot ℕ∞) := P.surface
  exact GlueA6Alg.goodReduction_of_QM_rational3' hNOS hRay hTors Ov (toGrp P.A) hdim
    (grpOfHom (P.q.iota oi)) (grpOfHom (P.q.iota oj)) (hI P) (hJ P) (hIJ P) h3 (hrat P)

end A6

/-! ## §6 Isomorphism classes as a quotient; centralizer and CM; base change of `End` -/

section Classes

variable {P Q R : QML3 K}

/-- Inverse of an isomorphism. -/
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

/-- Composition of isomorphisms. -/
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

/-- The set of isomorphism classes, as a `Quotient` (same as `M3 K`, now with the setoid). -/
def M3' (K : Type) [Field K] : Type 1 := Quotient (isoSetoid K)

end Classes

section CM

variable {A : AbVar K}

/-- The centralizer of `ι(𝒪)` in `End_K(A)` (the "CM order" of `(A, ι)` when it is larger than
`ℤ`). -/
def com (q : QMStr A) : Subring (AbVar.End A) := Subring.centralizer (Set.range q.iota)

/-- CM by `ℤ[i]` (discriminant −4) inside the centralizer. -/
def HasCM4 (q : QMStr A) : Prop := ∃ φ ∈ com q, φ * φ = -1
/-- CM by `ℤ[ζ₃]` (discriminant −3) inside the centralizer. -/
def HasCM3 (q : QMStr A) : Prop := ∃ φ ∈ com q, φ * φ - φ + 1 = 0
/-- CM by `ℤ[√−6]` (discriminant −24) inside the centralizer. -/
def HasCM24 (q : QMStr A) : Prop := ∃ φ ∈ com q, φ * φ = -6

/-- `ι(𝒪)`'s centre-like part: `ι(n)` for integers `n` lies in the centralizer. -/
theorem intCast_mem_com (q : QMStr A) (n : ℤ) : (n : AbVar.End A) ∈ com q := by
  rw [com, Subring.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  exact (Int.cast_commute n _).symm.eq

end CM

section BaseChangeEnd

open scoped CategoryTheory.Obj in
/-- **Base change on endomorphisms** (first half of node N8): `End_K(A) → End_L(A_L)`,
`f ↦ (Over.pullback (Spec L → Spec K)).map f`, a ring homomorphism (functoriality, and
`Functor.map_mul` for the monoidal functor `Over.pullback`). -/
def endBC (A : AbVar K) (L : Type) [Field L] [Algebra K L] :
    AbVar.End A →+* AbVar.End (A.baseChange L) where
  toFun f := @AbVar.Hom.mk' L _ (A.baseChange L) (A.baseChange L)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (f := f.hom))
  map_one' := by
    apply AbVar.Hom.ext'
    change (Over.pullback _).map (𝟙 A.X) = 𝟙 _
    exact (Over.pullback _).map_id _
  map_mul' f g := by
    apply AbVar.Hom.ext'
    change (Over.pullback _).map (g.hom ≫ f.hom) = _
    rw [Functor.map_comp]; rfl
  map_zero' := by
    apply AbVar.Hom.ext'
    change (Over.pullback _).map (1 : A.X ⟶ A.X) = 1
    exact Functor.map_one _
  map_add' f g := by
    apply AbVar.Hom.ext'
    change (Over.pullback _).map (f.hom * g.hom) = _
    rw [Functor.map_mul]; rfl

end BaseChangeEnd

end AV

end BPQM

#print axioms BPQM.AV.not_qmStr_zero
#print axioms BPQM.AV.Level3.rightMul_eq_self
#print axioms BPQM.AV.Level3.twist
#print axioms BPQM.AV.QML3.Iso.refl
#print axioms BPQM.AV.QML3.goodReduction
#print axioms BPQM.AV.isoSetoid
#print axioms BPQM.AV.endBC
#print axioms BPQM.AV.intCast_mem_com

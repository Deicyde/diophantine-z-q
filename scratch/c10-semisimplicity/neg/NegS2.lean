/-
S2 negative controls. Private isolated source, scaled/semisimplicity.

GENUINE counterexamples (must COMPILE), of the same kind as `s1/neg/S1Necessity.lean`:
the two hypotheses of S2 cannot be dropped. Each exhibits an actual representation whose
restriction to `H` IS semisimple while the representation is NOT.

  * `finiteIndex_necessary`     — `H` of INFINITE index (`H = ⊥ ≤ Multiplicative ℤ`), over `ℚ`.
  * `invertibleIndex_necessary` — `H` of index 2 over a field of characteristic 2, so the index
                                   is finite but ZERO in `k`.

Nothing is fabricated: in both the restriction is proved semisimple and the representation is
proved not semisimple, so S2 without the corresponding hypothesis is false.
-/

import Mathlib.RepresentationTheory.Semisimple
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic

namespace ScaledS2Neg

open Representation

/-! ## 1. Restriction to the trivial subgroup is always semisimple -/

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Subrepresentations of the restriction to `⊥` are just submodules. -/
def botOrderIso (ρ : Representation k G V) :
    Subrepresentation (ρ.comp (⊥ : Subgroup G).subtype) ≃o Submodule k V where
  toFun p := p.toSubmodule
  invFun N := ⟨N, fun h _v hv => by
    obtain ⟨h, hh⟩ := h
    rw [Subgroup.mem_bot] at hh
    subst hh
    simpa using hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The restriction of any representation to the trivial subgroup is semisimple. -/
theorem isSemisimple_comp_bot (ρ : Representation k G V) :
    Representation.IsSemisimpleRepresentation (ρ.comp (⊥ : Subgroup G).subtype) :=
  (OrderIso.complementedLattice_iff (botOrderIso ρ)).mpr Submodule.complementedLattice

/-! ## 2. The unipotent plane representation attached to an additive character -/

variable (k) in
/-- `n ↦ ((x, y) ↦ (x + φ n · y, y))`, a representation of `Multiplicative A` on `k × k`. -/
def unip {A : Type*} [AddCommGroup A] (φ : A →+ k) : Representation k (Multiplicative A) (k × k)
    where
  toFun n :=
    (LinearMap.fst k k k + (φ (Multiplicative.toAdd n)) • LinearMap.snd k k k).prod
      (LinearMap.snd k k k)
  map_one' := by ext <;> simp
  map_mul' m n := by
    ext <;> simp [Module.End.mul_eq_comp] <;> ring

@[simp] theorem unip_apply {A : Type*} [AddCommGroup A] (φ : A →+ k) (n : Multiplicative A)
    (v : k × k) : unip k φ n v = (v.1 + φ (Multiplicative.toAdd n) * v.2, v.2) := rfl

/-- The unipotent representation is **not** semisimple as soon as `φ` is nonzero: the line
`y = 0` is its only invariant line, so it has no invariant complement. -/
theorem not_isSemisimple_unip {A : Type*} [AddCommGroup A] (φ : A →+ k) {a₀ : A}
    (ha₀ : φ a₀ ≠ 0) : ¬ (unip k φ).IsSemisimpleRepresentation := by
  intro hss
  have hfix : ∀ (n : Multiplicative A) (v : k × k), v.2 = 0 → unip k φ n v = v := by
    intro n v hv
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩ <;> simp [unip_apply, hv]
  let p : Subrepresentation (unip k φ) :=
    ⟨LinearMap.ker (LinearMap.snd k k k), fun n v hv => by
      have hv2 : v.2 = 0 := by simpa using hv
      simpa [hfix n v hv2] using hv⟩
  obtain ⟨q, hq⟩ := hss.exists_isCompl p
  have hinf : p.toSubmodule ⊓ q.toSubmodule = (⊥ : Submodule k (k × k)) :=
    congrArg Subrepresentation.toSubmodule (disjoint_iff.mp hq.disjoint)
  have hsup : p.toSubmodule ⊔ q.toSubmodule = (⊤ : Submodule k (k × k)) :=
    congrArg Subrepresentation.toSubmodule (codisjoint_iff.mp hq.codisjoint)
  have hmemtop : ((0 : k), (1 : k)) ∈ p.toSubmodule ⊔ q.toSubmodule := by rw [hsup]; trivial
  obtain ⟨x, hx, w, hw, hxw⟩ := Submodule.mem_sup.mp hmemtop
  have hx2 : x.2 = 0 := by simpa [p] using hx
  have hw2 : w.2 = 1 := by
    have := congrArg Prod.snd hxw
    simp only [Prod.snd_add] at this
    rw [hx2, zero_add] at this
    exact this
  -- the commutator `ρ(g₀) w - w` lies in both `p` and `q`, hence is zero
  set g₀ : Multiplicative A := Multiplicative.ofAdd a₀ with hg₀
  have hdiff : unip k φ g₀ w - w = (φ a₀, 0) := by
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩ <;> simp [unip_apply, hw2, hg₀]
  have hq1 : unip k φ g₀ w - w ∈ q.toSubmodule :=
    q.toSubmodule.sub_mem (q.apply_mem_toSubmodule g₀ hw) hw
  have hp1 : unip k φ g₀ w - w ∈ p.toSubmodule := by
    rw [hdiff]
    simp [p]
  have hzero : unip k φ g₀ w - w = 0 := by
    have : unip k φ g₀ w - w ∈ p.toSubmodule ⊓ q.toSubmodule := ⟨hp1, hq1⟩
    rwa [hinf, Submodule.mem_bot] at this
  rw [hdiff] at hzero
  exact ha₀ (congrArg Prod.fst hzero)

/-! ## 3. The two controls -/

/-- **Finite index is necessary.** `H = ⊥ ≤ Multiplicative ℤ` has infinite index
(`H.index = 0`), the restriction is semisimple, and the representation is not. So S2 without
the finite-index hypothesis is false. -/
theorem finiteIndex_necessary :
    ∃ (G : Type) (_ : Group G) (V : Type) (_ : AddCommGroup V) (_ : Module ℚ V)
      (H : Subgroup G) (ρ : Representation ℚ G V),
      H.index = 0 ∧
      Representation.IsSemisimpleRepresentation (ρ.comp H.subtype) ∧
      ¬ ρ.IsSemisimpleRepresentation := by
  refine ⟨Multiplicative ℤ, inferInstance, ℚ × ℚ, inferInstance, inferInstance, ⊥,
    unip ℚ (Int.castAddHom ℚ), ?_, isSemisimple_comp_bot _, ?_⟩
  · rw [Subgroup.index_bot]
    exact Nat.card_eq_zero_of_infinite
  · exact not_isSemisimple_unip (Int.castAddHom ℚ) (a₀ := 1) (by norm_num)

/-- **Invertibility of the index is necessary.** Over any field of characteristic 2,
`H = ⊥ ≤ Multiplicative (ZMod 2)` has index 2 — finite — but `(2 : k) = 0`; the restriction is
semisimple and the representation is not. So S2 with "finite index" but without "index
invertible in `k`" is false. -/
theorem invertibleIndex_necessary (k : Type) [Field k] [CharP k 2] :
    ∃ (G : Type) (_ : Group G) (V : Type) (_ : AddCommGroup V) (_ : Module k V)
      (H : Subgroup G) (ρ : Representation k G V),
      H.index = 2 ∧ ((H.index : k) = 0) ∧
      Representation.IsSemisimpleRepresentation (ρ.comp H.subtype) ∧
      ¬ ρ.IsSemisimpleRepresentation := by
  have hidx : (⊥ : Subgroup (Multiplicative (ZMod 2))).index = 2 := by
    rw [Subgroup.index_bot, Nat.card_congr (Multiplicative.toAdd (α := ZMod 2)),
      Nat.card_eq_fintype_card, ZMod.card]
  refine ⟨Multiplicative (ZMod 2), inferInstance, k × k, inferInstance, inferInstance, ⊥,
    unip k ((ZMod.castHom (dvd_refl 2) k).toAddMonoidHom), hidx, ?_,
    isSemisimple_comp_bot _, ?_⟩
  · rw [hidx]
    exact_mod_cast CharP.cast_eq_zero k 2
  · refine not_isSemisimple_unip _ (a₀ := 1) ?_
    simp

/- RETAINED FAILURE (not a mathematical one): the same control stated at the concrete field
`ZMod 2` does not elaborate — in the STATEMENT, `Representation (ZMod 2) G V` picks the
`CommRing (ZMod n)` path to `Semiring`, while `IsSemisimpleRepresentation` demands the
`Field`-derived one, and the two do not unify syntactically (they are defeq). The control above
is stated over an arbitrary field of characteristic 2 instead, which is strictly more general. -/

#print axioms finiteIndex_necessary
#print axioms invertibleIndex_necessary
#print axioms not_isSemisimple_unip

end ScaledS2Neg

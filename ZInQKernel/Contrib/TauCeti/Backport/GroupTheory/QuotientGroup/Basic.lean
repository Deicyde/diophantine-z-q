/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 4d91513e4d30, module
-- TauCeti.GroupTheory.QuotientGroup.Basic), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which
-- is vendored as `ZInQKernel.Contrib.TauCeti.GroupTheory.QuotientGroup.Basic` (task t40-tate).
-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.
module

public import ZInQKernel.Contrib.TauCeti.GroupTheory.QuotientGroup.Basic

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import ZInQKernel.Contrib.TauCeti.Backport.Algebra.BigOperators.Group.List
public import ZInQKernel.Contrib.TauCeti.Algebra.Group.Subgroup.Finite
public import ZInQKernel.Contrib.TauCeti.Algebra.Group.Subgroup.Pointwise

/-!
# Left translation on a coset space

A group `G` acts on the quotient `G ⧸ H` by translation.  This file records the stabilizer of a
coset for that action, and, for the trivial subgroup, the compatibility of the identification
`QuotientGroup.quotientBot : G ⧸ ⊥ ≃* G` with translation.

The stabilizer of the coset `sH` is the conjugate subgroup `sHs⁻¹`
(`TauCeti.stabilizer_quotientGroup_mk`); this is Mathlib's `MulAction.stabilizer_quotient`, which
covers the trivial coset, transported along `MulAction.stabilizer_smul_eq_stabilizer_map_conj`.
Read on elements, it says that `g` fixes `sH` exactly when `s⁻¹ g s` lies in `H`
(`TauCeti.smul_quotientGroup_mk_eq_self_iff`), which is the form a fixed-coset count is checked
in.  Reading that criterion over all of `G` counts the elements `x` with `x⁻¹ g x ∈ H`: they form
the preimage of the `g`-fixed cosets, a union of `|(G ⧸ H)^g|` cosets of `H`, hence there are
`|H| * |(G ⧸ H)^g|` of them (`Subgroup.natCard_mul_natCard_fixedBy`).

The cosets of `⊥` in a group `G` are the elements of `G`, and Mathlib's
`QuotientGroup.quotientBot` is that identification.  The identification is equivariant for left
translation, and the only element of `G` fixing a coset of `⊥` is the identity.

For a finite group, a sum can also be split over the left or right cosets of a subgroup by using
`Quotient.out` as a transversal.

## Main statements

* `TauCeti.stabilizer_quotientGroup_mk`: the stabilizer of `sH` in `G` is `sHs⁻¹`.
* `Subgroup.card_orbit_quotientGroup_mk`: the size of the `K`-orbit of `sH` is the relative
  index of `H` in the conjugate of `K` by `s⁻¹`.
* `Subgroup.card_orbit_quotientGroup_mk_eq_relIndex_inf`: the same size as the index of `K ⊓ sHs⁻¹`
  in `K`.
* `TauCeti.smul_quotientGroup_mk_eq_self_iff`: `g` fixes the coset `sH` exactly when `s⁻¹ g s`
  lies in `H`.
* `Subgroup.natCard_mul_natCard_fixedBy`: the elements conjugating `g` into `H` number
  `|H| * |(G ⧸ H)^g|`.
* `Subgroup.natCard_stabilizer_mul_natCard_mem_carrier`: counted by the conjugate they produce,
  the same elements number `|C_G(g)| * #(H ∩ [g])`.
* `Subgroup.natCard_fixedBy_mul_natCard`: the fixed-coset identity
  `#(G ⧸ H)^g · |H| = |C_G(g)| · #(H ∩ [g])`.
* `TauCeti.smul_quotient_eq_self_of_mem`: an element of a normal subgroup fixes every coset.
* `TauCeti.quotientBot_equivariant`: `QuotientGroup.quotientBot` intertwines left translation on
  `G ⧸ ⊥` with left translation in `G`.
* `TauCeti.quotientBot_smul_eq_self_iff`: a group element fixes a coset of the trivial subgroup
  only when it is the identity.
* `Subgroup.sum_eq_sum_leftCosets` and `Subgroup.sum_eq_sum_rightCosets`: split a finite sum
  along the left or right cosets of a subgroup.
* `QuotientGroup.eq_subgroupOf`: two elements of a subgroup `H` lie in the same left coset of
  `N.subgroupOf H` exactly when they lie in the same left coset of `N`.
* `QuotientGroup.nontrivial_subgroupOf_of_inf_eq_bot`: `H ⧸ (Z ∩ H)` is nontrivial when `H`
  contains a nontrivial subgroup meeting `Z` trivially.
* `QuotientGroup.out_mul_out_mul_inv_mem`: the defect of the representatives chosen by
  `Quotient.out` from preserving multiplication lies in the subgroup.
* `QuotientGroup.mk_list_prod`: the class of a list product is the product of the classes.
* `QuotientGroup.inv_mul_mul_list_prod_map_mul_mem`: central corrections can be absorbed into the
  two tail products of a word, modulo a normal subgroup.
* `QuotientGroup.mk_inv_eq_self_of_sq_mem`: the class of `s` is its own inverse when `s ^ 2`
  lies in the normal subgroup.
-/

public section

open MulAction
open scoped Pointwise

-- Mathlib's `Subgroup.quotientEquivOfEq_mk` (a `rfl` lemma) is not a `simp` lemma. With it, `simp`
-- carries the class of a representative across an equality of subgroups.
attribute [simp] Subgroup.quotientEquivOfEq_mk

namespace TauCeti

variable {G : Type*} [Group G]

-- (omitted: `smul_quotient_eq_self_of_mem`, already in the vendored module)
-- (omitted: `stabilizer_quotientGroup_mk`, already in the vendored module)
-- (omitted: `smul_quotientGroup_mk_eq_self_iff`, already in the vendored module)
/-- The size of the orbit of `sH` under a subgroup `K` is the relative index of `H` in the
conjugate of `K` by `s⁻¹`. -/
theorem _root_.Subgroup.card_orbit_quotientGroup_mk (K H : Subgroup G) (s : G) :
    Nat.card (orbit K ((s : G) : G ⧸ H)) =
      H.relIndex (MulAut.conj s⁻¹ • K) := by
  -- The stabilizer of `sH` in `K` is `sHs⁻¹` read inside `K`; orbit-stabilizer then gives the
  -- index of `sHs⁻¹` in `K`, which conjugation by `s⁻¹` turns into the stated relative index.
  have hstab : stabilizer K ((s : G) : G ⧸ H) = (MulAut.conj s • H).subgroupOf K := by
    ext k
    simp [← stabilizer_quotientGroup_mk]
  rw [← Subgroup.relIndex_pointwise_smul (MulAut.conj s), map_inv, smul_inv_smul,
    Subgroup.relIndex, ← hstab, Nat.card_coe_set_eq, index_stabilizer]

/-- **Orbit-stabilizer for the intersection with a conjugate**: the `K`-orbit of the coset `sH` has
as many elements as `K ⊓ sHs⁻¹` has index in `K`. -/
theorem _root_.Subgroup.card_orbit_quotientGroup_mk_eq_relIndex_inf (K H : Subgroup G) (s : G) :
    Nat.card (orbit K ((s : G) : G ⧸ H)) = (K ⊓ MulAut.conj s • H).relIndex K := by
  rw [Subgroup.card_orbit_quotientGroup_mk, Subgroup.inf_relIndex_left]
  simpa using (Subgroup.relIndex_pointwise_smul (MulAut.conj s) H (MulAut.conj s⁻¹ • K)).symm

-- (omitted: `_root_.Subgroup.natCard_mul_natCard_fixedBy`, already in the vendored module)
/-- The elements `x` of `G` with `x⁻¹ g x ∈ H`, counted by the conjugate they produce: there are
`|C_G(g)|` of them over each element of `H` conjugate to `g`, where the centralizer `C_G(g)` is the
stabilizer of `g` for the conjugation action. This is the companion of
`Subgroup.natCard_mul_natCard_fixedBy`, which counts the same elements by their cosets. -/
theorem _root_.Subgroup.natCard_stabilizer_mul_natCard_mem_carrier (H : Subgroup G) (g : G) :
    Nat.card (stabilizer (ConjAct G) g) *
        Nat.card {x : G // x ∈ (ConjClasses.mk g).carrier ∧ x ∈ H} =
      Nat.card {x : G // x⁻¹ * g * x ∈ H} := by
  -- Reparametrize by `c = x⁻¹` in `ConjAct G`, for which `x⁻¹ * g * x = c • g`.
  have e₁ : {x : G // x⁻¹ * g * x ∈ H} ≃ {c : ConjAct G // c • g ∈ H} :=
    (Equiv.inv G).trans ConjAct.toConjAct.toEquiv |>.subtypeEquiv fun x ↦ by
      simp [ConjAct.smul_def]
  -- The conjugates `c • g` are the points of the orbit of `g`, identified with `G ⧸ C_G(g)`.
  set T : Set (ConjAct G ⧸ stabilizer (ConjAct G) g) :=
    {q | ofQuotientStabilizer (ConjAct G) g q ∈ H}
  have hset : {c : ConjAct G | c • g ∈ H} = QuotientGroup.mk ⁻¹' T := by
    ext c
    simp [T, ofQuotientStabilizer_mk]
  have e₂ : T ≃ {x : G // x ∈ (ConjClasses.mk g).carrier ∧ x ∈ H} :=
    ((orbitEquivQuotientStabilizer (ConjAct G) g).symm.subtypeEquiv
        (p := (· ∈ T)) (q := fun y : orbit (ConjAct G) g ↦ (y : G) ∈ H) fun q ↦ by
          induction q using QuotientGroup.induction_on
          simp [T, ofQuotientStabilizer_mk]).trans <|
      (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ orbit (ConjAct G) g) (· ∈ H)).trans <|
        Equiv.subtypeEquivRight fun x ↦ by rw [ConjAct.orbit_eq_carrier_conjClasses]
  rw [Nat.card_congr e₁, ← Nat.card_congr e₂, ← Nat.card_prod,
    ← Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet _ T), ← hset, Set.coe_ofPred]

/-- **The fixed-coset identity.** For a subgroup `H` of a group `G` and `g : G`,

`#(G ⧸ H)^g · |H| = |C_G(g)| · #(H ∩ [g])`,

where the centralizer `C_G(g)` is the stabilizer of `g` for the conjugation action and `[g]` is
the conjugacy class of `g`. Both sides count the `x : G` with `x⁻¹ g x ∈ H`; no finiteness is
needed, with the convention that `Nat.card` of an infinite type is `0`. -/
theorem _root_.Subgroup.natCard_fixedBy_mul_natCard (H : Subgroup G) (g : G) :
    Nat.card (fixedBy (G ⧸ H) g) * Nat.card H =
      Nat.card (stabilizer (ConjAct G) g) *
        Nat.card {x : G // x ∈ (ConjClasses.mk g).carrier ∧ x ∈ H} := by
  rw [mul_comm, Subgroup.natCard_mul_natCard_fixedBy,
    Subgroup.natCard_stabilizer_mul_natCard_mem_carrier]

-- (omitted: `quotientBot_smul`, already in the vendored module)
-- (omitted: `quotientBot_equivariant`, already in the vendored module)
-- (omitted: `quotientBot_smul_eq_self_iff`, already in the vendored module)
-- (omitted: `_root_.QuotientGroup.eq_subgroupOf`, already in the vendored module)
/-- If `H` contains a subgroup `U ≠ 1` meeting `Z` trivially, then `H ⧸ (Z ∩ H)` is nontrivial,
since otherwise `U ≤ H ≤ Z`. -/
theorem _root_.QuotientGroup.nontrivial_subgroupOf_of_inf_eq_bot {H U Z : Subgroup G}
    (hUH : U ≤ H) (hZU : Z ⊓ U = ⊥) (hU : U ≠ ⊥) : Nontrivial (H ⧸ Z.subgroupOf H) := by
  rw [QuotientGroup.nontrivial_iff, Ne, Subgroup.subgroupOf_eq_top]
  exact fun h ↦ hU (eq_bot_iff.mpr (hZU ▸ le_inf (hUH.trans h) le_rfl))

-- (omitted: `_root_.QuotientGroup.out_mul_out_mul_inv_mem`, already in the vendored module)
/-- The class modulo a normal subgroup of a list product is the product of the classes. -/
@[simp]
theorem _root_.QuotientGroup.mk_list_prod (K : Subgroup G) [K.Normal] (l : List G) :
    ((l.prod : G) : G ⧸ K) = (l.map ((↑) : G → G ⧸ K)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- **Absorbing central corrections into a word.** Let `K` be a normal subgroup of `G` and let
the classes of the `u_i` modulo `K` be central. If the class of
`(∏_{l₁} t_i) * w * (∏_{l₂} t_i) * ∏_{l₁ ++ l₂} u_i` modulo `K` is the class of `b`, then
`b⁻¹ * (∏_{l₁} t_i u_i) * w * (∏_{l₂} t_i u_i)` lies in `K`. -/
theorem _root_.QuotientGroup.inv_mul_mul_list_prod_map_mul_mem {ι : Type*} (K : Subgroup G)
    [K.Normal] {t u : ι → G} (hu : ∀ i, (u i : G ⧸ K) ∈ Submonoid.center (G ⧸ K))
    {l₁ l₂ : List ι} {b w : G}
    (h : (((l₁.map t).prod * w * (l₂.map t).prod * ((l₁ ++ l₂).map u).prod : G) : G ⧸ K) =
      (b : G ⧸ K)) :
    b⁻¹ * ((l₁.map fun i ↦ t i * u i).prod * w * (l₂.map fun i ↦ t i * u i).prod) ∈ K := by
  refine (QuotientGroup.eq_one_iff _).mp ?_
  have hprod : ∀ l : List ι, (((l.map fun i ↦ t i * u i).prod : G) : G ⧸ K) =
      ((l.map t).prod : G ⧸ K) * ((l.map u).prod : G ⧸ K) := fun l ↦ by
    simpa [Function.comp_def] using
      List.prod_map_mul_of_mem_center l (fun i ↦ ((t i : G) : G ⧸ K)) _ fun i _ ↦ hu i
  have hUcen : ∀ l : List ι, (((l.map u).prod : G) : G ⧸ K) ∈ Submonoid.center _ := fun l ↦ by
    rw [QuotientGroup.mk_list_prod, List.map_map]
    exact Submonoid.list_prod_mem _ fun x hx ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact hu i
  simp only [QuotientGroup.mk_mul, List.map_append, List.prod_append] at h
  set W := (w : G ⧸ K)
  set P₁ := (((l₁.map t).prod : G) : G ⧸ K)
  set P₂ := (((l₂.map t).prod : G) : G ⧸ K)
  set U₁ := (((l₁.map u).prod : G) : G ⧸ K)
  set U₂ := (((l₂.map u).prod : G) : G ⧸ K)
  have e₁ : ∀ q, q * U₁ = U₁ * q := Submonoid.mem_center_iff.mp (hUcen l₁)
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hprod, ← h, inv_mul_eq_one]
  calc P₁ * W * P₂ * (U₁ * U₂) = P₁ * (W * P₂ * U₁) * U₂ := by simp only [mul_assoc]
    _ = P₁ * (U₁ * (W * P₂)) * U₂ := by rw [e₁]
    _ = P₁ * U₁ * W * (P₂ * U₂) := by simp only [mul_assoc]

/-- The class of `s` in `G ⧸ N` is its own inverse when `s ^ 2 ∈ N`. -/
theorem _root_.QuotientGroup.mk_inv_eq_self_of_sq_mem {N : Subgroup G} [N.Normal] {s : G}
    (hs : s ^ 2 ∈ N) : (s : G ⧸ N)⁻¹ = s :=
  inv_eq_of_mul_eq_one_right <| by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← sq]
    exact hs

section Finite

attribute [local instance] Subgroup.fintypeOfFinite Subgroup.fintypeQuotientOfFiniteIndex

variable {M : Type*} [AddCommMonoid M] [Fintype G] (H : Subgroup G)

-- (omitted: `_root_.Subgroup.sum_eq_sum_leftCosets`, already in the vendored module)
-- (omitted: `_root_.Subgroup.sum_eq_sum_rightCosets`, already in the vendored module)
end Finite

end TauCeti

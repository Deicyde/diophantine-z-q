import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Componentwise quotients of restricted products of groups

Let `G i` be a family of groups, `H i` and `S i` subgroups with every `S i` normal, and let
`𝓕` be a filter on the index type (the classical case is `𝓕 = cofinite`). Assume `H i ≤ S i`
for `𝓕`-almost every `i`. Writing `R = Πʳ i, [G i, H i]_[𝓕]` and
`D = {x : R | ∀ i, x i ∈ S i}`, this file constructs

* `quotientHom : R →* Πʳ i, [G i ⧸ S i, ⊥]_[𝓕]`, the componentwise quotient map;
* `quotientHom_surjective`: it is surjective (a preimage takes the identity at every index where
  the target component is trivial, and an arbitrary representative elsewhere);
* `ker_quotientHom`: its kernel is `componentSubgroup H S = D`;
* `quotientEquiv : R ⧸ D ≃* Πʳ i, [G i ⧸ S i, ⊥]_[𝓕]`.

When `S i = ⊤` for every `i` outside a set `s` with `sᶜ ∈ 𝓕` (for `𝓕 = cofinite`: `s` finite),
`restrictedQuotientEquivPi` identifies the target with the plain product `Π i : s, G i ⧸ S i`,
and `quotientEquivPi` composes the two equivalences.

Everything here is generic group theory; no arithmetic input is used or assumed.
-/

namespace ZInQ.Contrib.AdelicNormalizer.RestrictedQuotient

open Filter Set RestrictedProduct
open scoped RestrictedProduct

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

section General

variable {𝓕 : Filter ι}

/-- The subgroup `D = {x | ∀ i, x i ∈ S i}` of the restricted product `Πʳ i, [G i, H i]_[𝓕]`. -/
def componentSubgroup (𝓕 : Filter ι) (H S : ∀ i, Subgroup (G i)) :
    Subgroup (Πʳ i, [G i, H i]_[𝓕]) where
  carrier := {x | ∀ i, x i ∈ S i}
  one_mem' := fun i => (S i).one_mem
  mul_mem' := fun hx hy i => (S i).mul_mem (hx i) (hy i)
  inv_mem' := fun hx i => (S i).inv_mem (hx i)

theorem mem_componentSubgroup {H S : ∀ i, Subgroup (G i)} {x : Πʳ i, [G i, H i]_[𝓕]} :
    x ∈ componentSubgroup 𝓕 H S ↔ ∀ i, x i ∈ S i :=
  Iff.rfl

instance componentSubgroup_normal (H S : ∀ i, Subgroup (G i)) [∀ i, (S i).Normal] :
    (componentSubgroup 𝓕 H S).Normal :=
  ⟨fun n hn g i => (inferInstance : (S i).Normal).conj_mem (n i) (hn i) (g i)⟩

variable {H S : ∀ i, Subgroup (G i)} [∀ i, (S i).Normal]

/-- The componentwise quotient map `Πʳ i, [G i, H i]_[𝓕] →* Πʳ i, [G i ⧸ S i, ⊥]_[𝓕]`. -/
def quotientHom (hHS : ∀ᶠ i in 𝓕, H i ≤ S i) :
    Πʳ i, [G i, H i]_[𝓕] →* Πʳ i, [G i ⧸ S i, (⊥ : Subgroup (G i ⧸ S i))]_[𝓕] where
  toFun x := ⟨fun i => ((x i : G i) : G i ⧸ S i), by
    filter_upwards [x.eventually, hHS] with i hx hi
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff (x i)).mpr (hi hx))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem quotientHom_apply (hHS : ∀ᶠ i in 𝓕, H i ≤ S i) (x : Πʳ i, [G i, H i]_[𝓕]) (i : ι) :
    quotientHom hHS x i = ((x i : G i) : G i ⧸ S i) :=
  rfl

theorem ker_quotientHom (hHS : ∀ᶠ i in 𝓕, H i ≤ S i) :
    (quotientHom hHS).ker = componentSubgroup 𝓕 H S := by
  ext x
  rw [MonoidHom.mem_ker, mem_componentSubgroup]
  constructor
  · intro h i
    have hi : quotientHom hHS x i = (1 : Πʳ i, [G i ⧸ S i, (⊥ : Subgroup (G i ⧸ S i))]_[𝓕]) i :=
      congrArg (fun y : Πʳ i, [G i ⧸ S i, (⊥ : Subgroup (G i ⧸ S i))]_[𝓕] => y i) h
    exact (QuotientGroup.eq_one_iff (x i)).mp hi
  · intro h
    ext i
    exact (QuotientGroup.eq_one_iff (x i)).mpr (h i)

theorem quotientHom_surjective (hHS : ∀ᶠ i in 𝓕, H i ≤ S i) :
    Function.Surjective (quotientHom hHS) := by
  classical
  intro y
  let rep : ∀ i, G i := fun i =>
    if y i = 1 then 1 else (QuotientGroup.mk_surjective (y i)).choose
  refine ⟨⟨rep, ?_⟩, ?_⟩
  · filter_upwards [y.eventually] with i hi
    have h1 : y i = 1 := Subgroup.mem_bot.mp hi
    change (if y i = 1 then 1 else (QuotientGroup.mk_surjective (y i)).choose) ∈ H i
    rw [ite_eq_left h1]
    exact (H i).one_mem
  · ext i
    change (((if y i = 1 then 1 else (QuotientGroup.mk_surjective (y i)).choose : G i)) :
      G i ⧸ S i) = y i
    by_cases h1 : y i = 1
    · rw [ite_eq_left h1, h1]
      rfl
    · rw [ite_eq_right h1]
      exact (QuotientGroup.mk_surjective (y i)).choose_spec

/-- `R ⧸ D ≃* Πʳ i, [G i ⧸ S i, ⊥]_[𝓕]`, induced by `quotientHom`. -/
noncomputable def quotientEquiv (hHS : ∀ᶠ i in 𝓕, H i ≤ S i) :
    (Πʳ i, [G i, H i]_[𝓕]) ⧸ componentSubgroup 𝓕 H S ≃*
      Πʳ i, [G i ⧸ S i, (⊥ : Subgroup (G i ⧸ S i))]_[𝓕] :=
  (QuotientGroup.quotientMulEquivOfEq (ker_quotientHom hHS).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (quotientHom hHS) (quotientHom_surjective hHS))

@[simp]
theorem quotientEquiv_mk (hHS : ∀ᶠ i in 𝓕, H i ≤ S i) (x : Πʳ i, [G i, H i]_[𝓕]) :
    quotientEquiv hHS (QuotientGroup.mk x) = quotientHom hHS x :=
  rfl

theorem quotientEquiv_mk_apply (hHS : ∀ᶠ i in 𝓕, H i ≤ S i) (x : Πʳ i, [G i, H i]_[𝓕])
    (i : ι) : quotientEquiv hHS (QuotientGroup.mk x) i = ((x i : G i) : G i ⧸ S i) :=
  rfl

end General

section Cofinite

variable {H S : ∀ i, Subgroup (G i)} [∀ i, (S i).Normal]

/-- The classical (cofinite) case with `H i ≤ S i` for every `i`. -/
noncomputable def quotientEquivCofinite (hHS : ∀ i, H i ≤ S i) :
    (Πʳ i, [G i, H i]) ⧸ componentSubgroup cofinite H S ≃*
      Πʳ i, [G i ⧸ S i, (⊥ : Subgroup (G i ⧸ S i))] :=
  quotientEquiv (Eventually.of_forall hHS)

theorem quotientEquivCofinite_mk_apply (hHS : ∀ i, H i ≤ S i) (x : Πʳ i, [G i, H i]) (i : ι) :
    quotientEquivCofinite hHS (QuotientGroup.mk x) i = ((x i : G i) : G i ⧸ S i) :=
  rfl

end Cofinite

section FiniteException

variable {𝓕 : Filter ι} {S : ∀ i, Subgroup (G i)} [∀ i, (S i).Normal]

theorem quotient_eq_one_of_eq_top {i : ι} (h : S i = ⊤) (q : G i ⧸ S i) : q = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine (QuotientGroup.eq_one_iff g).mpr ?_
  rw [h]
  exact Subgroup.mem_top g

open scoped Classical in
/-- If `S i = ⊤` outside `s` and `sᶜ ∈ 𝓕`, the restricted product of the local quotients is the
plain product over `s`. -/
noncomputable def restrictedQuotientEquivPi (s : Set ι) (hs : sᶜ ∈ 𝓕) (htop : ∀ i ∉ s, S i = ⊤) :
    Πʳ i, [G i ⧸ S i, (⊥ : Subgroup (G i ⧸ S i))]_[𝓕] ≃* ((i : s) → G i ⧸ S i) where
  toFun x i := x (i : ι)
  invFun y := ⟨fun i => if h : i ∈ s then y ⟨i, h⟩ else 1, by
    filter_upwards [hs] with i hi
    change (if h : i ∈ s then y ⟨i, h⟩ else 1) ∈ (⊥ : Subgroup (G i ⧸ S i))
    rw [dite_eq_right hi]
    exact (⊥ : Subgroup (G i ⧸ S i)).one_mem⟩
  left_inv x := by
    ext i
    change (if h : i ∈ s then x i else 1) = x i
    by_cases h : i ∈ s
    · rw [dite_eq_left h]
    · rw [dite_eq_right h]
      exact (quotient_eq_one_of_eq_top (htop i h) (x i)).symm
  right_inv y := by
    funext i
    change (if h : (i : ι) ∈ s then y ⟨(i : ι), h⟩ else (1 : G i ⧸ S i)) = y i
    rw [dite_eq_left i.2]
  map_mul' _ _ := rfl

@[simp]
theorem restrictedQuotientEquivPi_apply (s : Set ι) (hs : sᶜ ∈ 𝓕) (htop : ∀ i ∉ s, S i = ⊤)
    (x : Πʳ i, [G i ⧸ S i, (⊥ : Subgroup (G i ⧸ S i))]_[𝓕]) (i : s) :
    restrictedQuotientEquivPi s hs htop x i = x (i : ι) :=
  rfl

variable {H : ∀ i, Subgroup (G i)}

/-- `R ⧸ D ≃* Π i : s, G i ⧸ S i` when `S i = ⊤` outside `s` and `sᶜ ∈ 𝓕`. -/
noncomputable def quotientEquivPi (hHS : ∀ᶠ i in 𝓕, H i ≤ S i) (s : Set ι) (hs : sᶜ ∈ 𝓕)
    (htop : ∀ i ∉ s, S i = ⊤) :
    (Πʳ i, [G i, H i]_[𝓕]) ⧸ componentSubgroup 𝓕 H S ≃* ((i : s) → G i ⧸ S i) :=
  (quotientEquiv hHS).trans (restrictedQuotientEquivPi s hs htop)

theorem quotientEquivPi_mk_apply (hHS : ∀ᶠ i in 𝓕, H i ≤ S i) (s : Set ι) (hs : sᶜ ∈ 𝓕)
    (htop : ∀ i ∉ s, S i = ⊤) (x : Πʳ i, [G i, H i]_[𝓕]) (i : s) :
    quotientEquivPi hHS s hs htop (QuotientGroup.mk x) i = ((x (i : ι) : G i) : G i ⧸ S i) :=
  rfl

/-- The cofinite case: `s` finite and `H i ≤ S i` for every `i`. -/
noncomputable def quotientEquivPiOfFinite (hHS : ∀ i, H i ≤ S i) (s : Set ι) (hs : s.Finite)
    (htop : ∀ i ∉ s, S i = ⊤) :
    (Πʳ i, [G i, H i]) ⧸ componentSubgroup cofinite H S ≃* ((i : s) → G i ⧸ S i) :=
  quotientEquivPi (Eventually.of_forall hHS) s hs.compl_mem_cofinite htop

end FiniteException

end ZInQ.Contrib.AdelicNormalizer.RestrictedQuotient

import WeilTateCountV002
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# Left nondegeneracy from right perfectness and a homomorphism with finite kernel

No `n^{2g}` formula and no geometric degree.  `A`, `D` commutative groups (in the application: `A = X(k)`,
`D = Pic⁰(X)` over `k = k̄` of characteristic `0`), `n ≥ 1`:

* `card_torsion_le_of_hom`: if `A` is `n`-divisible and `φ : A →* D` has finite kernel, then
  `#A[n] ≤ #D[n]` (the compiled `card_range_torsion_eq`; `D[n]` finite);
* `left_perfect_of_right_perfect`: for a finite commutative group `G` and a field `k` with enough roots of unity
  of order `exp G`, a homomorphism `e : D →* Hom(G, kˣ)` with trivial kernel and `#G ≤ #D` has trivial left
  kernel (Mathlib's finite abelian duality: `#Hom(G, kˣ) = #G`, characters separate points);
* `left_nondeg_of_hom_finite_ker`: the two combined at level `n`: a pairing `D[n] × A[n] → kˣ`, given as
  `e : D[n] →* Hom(A[n], kˣ)`, with trivial right kernel, `A[n]` finite, `A` `n`-divisible and some
  `φ : A →* D` with finite kernel, has trivial left kernel.
-/

noncomputable section

namespace WeilTate

/-- **`#A[n] ≤ #D[n]`** from an `n`-divisible `A` and `φ : A →* D` with finite kernel. -/
theorem card_torsion_le_of_hom {A D : Type*} [CommGroup A] [CommGroup D] (n : ℕ)
    (hdiv : ∀ g : A, ∃ h : A, h ^ n = g) (φ : A →* D) [Finite φ.ker]
    [Finite (powMonoidHom n : D →* D).ker] :
    Nat.card (powMonoidHom n : A →* A).ker ≤ Nat.card (powMonoidHom n : D →* D).ker := by
  rw [← card_range_torsion_eq n hdiv φ]
  exact Subgroup.card_le_of_le inf_le_left

/-- **Left perfectness from right perfectness and a lower count** (finite abelian duality). -/
theorem left_perfect_of_right_perfect {G D : Type*} [CommGroup G] [CommGroup D] [Finite G]
    {k : Type*} [Field k] [HasEnoughRootsOfUnity k (Monoid.exponent G)]
    (e : D →* (G →* kˣ)) (hR : ∀ d, e d = 1 → d = 1) (hcard : Nat.card G ≤ Nat.card D)
    (x : G) (hx : ∀ d, e d x = 1) : x = 1 := by
  have hinj : Function.Injective e := (injective_iff_map_eq_one e).2 hR
  have hcardH : Nat.card (G →* kˣ) = Nat.card G :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G k
  haveI : Finite (G →* kˣ) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcardH]
    exact Nat.card_pos.ne'
  exact eq_one_of_count e hinj (by rw [hcardH]; exact hcard)
    (fun y hy => CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G k hy) x hx

/-- **Left nondegeneracy at level `n` without any degree formula.** -/
theorem left_nondeg_of_hom_finite_ker {A D : Type*} [CommGroup A] [CommGroup D] {k : Type*} [Field k]
    (n : ℕ) [Finite (powMonoidHom n : A →* A).ker]
    [HasEnoughRootsOfUnity k (Monoid.exponent (powMonoidHom n : A →* A).ker)]
    (hdiv : ∀ g : A, ∃ h : A, h ^ n = g) (φ : A →* D) [Finite φ.ker]
    (e : (powMonoidHom n : D →* D).ker →* ((powMonoidHom n : A →* A).ker →* kˣ))
    (hR : ∀ d, e d = 1 → d = 1) (x : (powMonoidHom n : A →* A).ker) (hx : ∀ d, e d x = 1) :
    x = 1 := by
  have hinj : Function.Injective e := (injective_iff_map_eq_one e).2 hR
  have hcardH : Nat.card ((powMonoidHom n : A →* A).ker →* kˣ) =
      Nat.card (powMonoidHom n : A →* A).ker :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ k
  haveI : Finite ((powMonoidHom n : A →* A).ker →* kˣ) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcardH]
    exact Nat.card_pos.ne'
  haveI : Finite (powMonoidHom n : D →* D).ker := Finite.of_injective e hinj
  exact left_perfect_of_right_perfect e hR (card_torsion_le_of_hom n hdiv φ) x hx

end WeilTate

#check @WeilTate.card_torsion_le_of_hom
#check @WeilTate.left_perfect_of_right_perfect
#check @WeilTate.left_nondeg_of_hom_finite_ker
#print axioms WeilTate.card_torsion_le_of_hom
#print axioms WeilTate.left_perfect_of_right_perfect
#print axioms WeilTate.left_nondeg_of_hom_finite_ker

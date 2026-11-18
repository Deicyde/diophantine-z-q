import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Index

/-!
# Finite-level duality counts for pairings into `ZMod N`

Three elementary finite-group facts used at each finite level `ℓⁿ`:

* an endomorphism of a finite abelian group has cokernel of the same order as its kernel, so
  every multiple of the kernel order kills the cokernel;
* for a left-nondegenerate pairing `e : G × G' → ZMod N`, the left annihilator of `F' ≤ G'`
  injects into the characters of `G'/F'`, hence `|ann F'| · |F'| ≤ |G'|`;
* if `T ≤ ann F'` and `T' ≤ ann F` (orthogonality on both sides), the pairing is nondegenerate on
  both sides, and the subgroup orders satisfy `|F| · |T| = |G|`, `|F'| · |T'| = |G'|`, then
  `ann F' = T`.

No rank, filtration or annihilator identity is assumed: the conclusion is forced by counting.
-/

noncomputable section
set_option autoImplicit false

namespace ToricFinitePart

section Cokernel

variable {H : Type*} [AddCommGroup H]

/-- An endomorphism `v` of a finite abelian group: any multiple of `|ker v|` sends every element
into `range v`, since `|H / range v| = |ker v|`. -/
theorem nsmul_mem_range_of_card_ker_dvd [Finite H] (v : H →+ H) {N : ℕ}
    (hN : Nat.card v.ker ∣ N) (y : H) : N • y ∈ v.range := by
  have h1 : Nat.card v.ker * v.ker.index = Nat.card H := AddSubgroup.card_mul_index v.ker
  have h2 : Nat.card v.range * v.range.index = Nat.card H := AddSubgroup.card_mul_index v.range
  rw [AddSubgroup.index_ker] at h1
  have hpos : 0 < Nat.card v.range := Nat.card_pos
  have hidx : v.range.index = Nat.card v.ker := by
    have h3 : Nat.card v.range * v.range.index = Nat.card v.range * Nat.card v.ker := by
      rw [h2, ← h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h3
  obtain ⟨k, rfl⟩ := hN
  have hmem : v.range.index • y ∈ v.range := AddSubgroup.nsmul_index_mem v.range y
  rw [hidx] at hmem
  rw [mul_comm, mul_smul]
  exact AddSubgroup.nsmul_mem _ hmem k

end Cokernel

section Pairing

variable {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] {N : ℕ}

/-- The left annihilator `{x | ∀ y ∈ F', e x y = 0}` of a subgroup of the right factor. -/
def annL (e : G →+ G' →+ ZMod N) (F' : AddSubgroup G') : AddSubgroup G where
  carrier := {x | ∀ y ∈ F', e x y = 0}
  zero_mem' := by
    intro y _
    simp
  add_mem' := by
    intro a b ha hb y hy
    simp only [Set.mem_ofPred_eq] at ha hb
    simp [ha y hy, hb y hy]
  neg_mem' := by
    intro a ha y hy
    simp only [Set.mem_ofPred_eq] at ha
    simp [ha y hy]

theorem mem_annL {e : G →+ G' →+ ZMod N} {F' : AddSubgroup G'} {x : G} :
    x ∈ annL e F' ↔ ∀ y ∈ F', e x y = 0 := Iff.rfl

/-- Counting through characters: a left-nondegenerate pairing gives
`|ann F'| · |F'| ≤ |G'|`. -/
theorem card_annL_mul_card_le [Finite G'] [NeZero N] (e : G →+ G' →+ ZMod N)
    (he : ∀ x, (∀ y, e x y = 0) → x = 0) (F' : AddSubgroup G') :
    Nat.card (annL e F') * Nat.card F' ≤ Nat.card G' := by
  classical
  let χ : annL e F' → AddChar (G' ⧸ F') ℂ := fun x =>
    ZMod.stdAddChar.compAddMonoidHom
      (QuotientAddGroup.lift F' (e x.1) (fun y hy => (AddMonoidHom.mem_ker).mpr (x.2 y hy)))
  have hχ : Function.Injective χ := by
    intro x z hxz
    apply Subtype.ext
    have hyz : ∀ y, e x.1 y = e z.1 y := by
      intro y
      have h := congrArg (fun ψ : AddChar (G' ⧸ F') ℂ => ψ (QuotientAddGroup.mk y)) hxz
      simp only [χ, AddChar.compAddMonoidHom_apply, QuotientAddGroup.lift_mk] at h
      exact ZMod.injective_stdAddChar h
    have h0 : ∀ y, e (x.1 - z.1) y = 0 := by
      intro y
      simp [hyz y]
    exact sub_eq_zero.mp (he _ h0)
  have hcard : Nat.card (annL e F') ≤ Nat.card (G' ⧸ F') := by
    letI : Fintype (G' ⧸ F') := Fintype.ofFinite _
    calc Nat.card (annL e F') ≤ Nat.card (AddChar (G' ⧸ F') ℂ) :=
          Nat.card_le_card_of_injective χ hχ
      _ = Fintype.card (AddChar (G' ⧸ F') ℂ) := Nat.card_eq_fintype_card
      _ ≤ Fintype.card (G' ⧸ F') := AddChar.card_addChar_le _ _
      _ = Nat.card (G' ⧸ F') := Nat.card_eq_fintype_card.symm
  calc Nat.card (annL e F') * Nat.card F' ≤ Nat.card (G' ⧸ F') * Nat.card F' :=
        Nat.mul_le_mul_right _ hcard
    _ = Nat.card G' := (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup F').symm

/-- **Annihilator equality forced by counting.** Orthogonality on both sides, nondegeneracy on
both sides and the two order identities force the left annihilator of `F'` to be exactly `T`. -/
theorem annL_eq_of_counts [Finite G] [Finite G'] [NeZero N] (e : G →+ G' →+ ZMod N)
    (heL : ∀ x, (∀ y, e x y = 0) → x = 0) (heR : ∀ y, (∀ x, e x y = 0) → y = 0)
    (T F : AddSubgroup G) (T' F' : AddSubgroup G')
    (hT : T ≤ annL e F') (hT' : T' ≤ annL e.flip F)
    (hA : Nat.card F * Nat.card T = Nat.card G)
    (hA' : Nat.card F' * Nat.card T' = Nat.card G') :
    annL e F' = T := by
  have h1 := card_annL_mul_card_le e heL F'
  have h2 := card_annL_mul_card_le e.flip (fun y hy => heR y (fun x => hy x)) F
  have hF'pos : 0 < Nat.card F' := Nat.card_pos
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have hle1 : Nat.card (annL e F') ≤ Nat.card T' := by
    refine Nat.le_of_mul_le_mul_right (h1.trans (le_of_eq ?_)) hF'pos
    rw [← hA', mul_comm]
  have hle2 : Nat.card (annL e.flip F) ≤ Nat.card T := by
    refine Nat.le_of_mul_le_mul_right (h2.trans (le_of_eq ?_)) hFpos
    rw [← hA, mul_comm]
  have hle3 : Nat.card T' ≤ Nat.card (annL e.flip F) := AddSubgroup.card_le_of_le hT'
  exact (AddSubgroup.eq_of_le_of_card_ge hT (hle1.trans (hle3.trans hle2))).symm

end Pairing

section Cast

/-- In `ZMod (ℓ^(n+c))`, an element killed by `ℓ^c` reduces to `0` modulo `ℓⁿ`. -/
theorem cast_eq_zero_of_pow_nsmul_eq_zero {ℓ : ℕ} (hℓ : 0 < ℓ) (n c : ℕ)
    (x : ZMod (ℓ ^ (n + c))) (hx : (ℓ ^ c) • x = 0) :
    ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n c)) (ZMod (ℓ ^ n)) x = 0 := by
  have : NeZero (ℓ ^ (n + c)) := ⟨(pow_pos hℓ _).ne'⟩
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [map_natCast, ZMod.natCast_eq_zero_iff]
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hx
  have hx' : ℓ ^ c * ℓ ^ n ∣ ℓ ^ c * x.val := by
    rw [← pow_add, add_comm c n]
    exact hx
  exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hℓ c) hx'

end Cast

end ToricFinitePart

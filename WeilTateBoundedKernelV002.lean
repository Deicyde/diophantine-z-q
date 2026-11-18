import WeilTateCountV002
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# Bounded kernels: both `ℓ`-adic kernels trivial without finite-level perfectness

For a self-pairing (in the application Mumford's `e^L_n(x, y) = ē_n(x, φ_L y)` with `L` defined over `K`) the
finite-level pairings are not perfect: the right kernel at level `ℓᵏ` is `K(L)[ℓᵏ]`.  This file proves, with
no hypothesis that `#K(L)` is prime to `ℓ`:

* `card_mul_card_ker`: for finite commutative groups `G`, `H`, a field `k` with enough roots of unity and a
  pairing `e : H →* (G →* kˣ)`: `#G · #(right kernel) = #H · #(left kernel)` (finite abelian duality);
* `LevelPairing.levelHom`: a level pairing at level `ℓᵏ` as a homomorphism `N[ℓᵏ] →* Hom(M[ℓᵏ], Ωˣ)`;
* `tate_eq_zero_of_order_bound`: a vector of `T_ℓ` all of whose components have order `≤ d` is zero;
* `LevelPairing.tate_kernels_of_right_bounded`: if every right-kernel element at every level lies in one
  fixed FINITE subgroup `C`, both kernels of the limit pairing `T_ℓ M × T_ℓ M → T_ℓ(μ)` are trivial
  (the left kernel at level `ℓᵏ` has the same size as the right kernel, hence at most `#C` elements).
-/

noncomputable section

namespace WeilTate

open PkgI3

section Duality

variable {G H : Type*} [CommGroup G] [CommGroup H] {k : Type*} [Field k]

/-- The left kernel `{x | ∀ h, e h x = 1}` of `e : H →* (G →* kˣ)`. -/
def leftKer (e : H →* (G →* kˣ)) : Subgroup G where
  carrier := {x | ∀ h, e h x = 1}
  one_mem' := fun h => map_one (e h)
  mul_mem' := fun {a b} ha hb h => by rw [map_mul, ha h, hb h, one_mul]
  inv_mem' := fun {a} ha h => by rw [map_inv, ha h, inv_one]

/-- The flipped pairing `G →* (H →* kˣ)`. -/
def flipHom (e : H →* (G →* kˣ)) : G →* (H →* kˣ) where
  toFun x :=
    { toFun := fun h => e h x
      map_one' := by rw [map_one]; rfl
      map_mul' := fun h h' => by rw [map_mul]; rfl }
  map_one' := MonoidHom.ext fun h => map_one (e h)
  map_mul' x y := MonoidHom.ext fun h => map_mul (e h) x y

theorem ker_flipHom (e : H →* (G →* kˣ)) : (flipHom e).ker = leftKer e := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx h
    exact DFunLike.congr_fun hx h
  · intro hx
    exact MonoidHom.ext fun h => hx h

variable [Finite G] [Finite H] [HasEnoughRootsOfUnity k (Monoid.exponent G)]
  [HasEnoughRootsOfUnity k (Monoid.exponent H)]

/-- `#H ≤ #(G ⧸ L) · #R` for any pairing (one half of duality). -/
theorem card_le_quot_mul_ker (e : H →* (G →* kˣ)) :
    Nat.card H ≤ Nat.card (G ⧸ leftKer e) * Nat.card e.ker := by
  set C := (MonoidHom.domRestrictHom (leftKer e) kˣ).ker with hCdef
  have hC : Nat.card C = Nat.card (G ⧸ leftKer e) :=
    CommGroup.card_domRestrictHom_ker (M := k) (leftKer e)
  have hmem : ∀ h, e h ∈ C := by
    intro h
    rw [MonoidHom.mem_ker]
    apply MonoidHom.ext
    intro x
    exact x.2 h
  let e1 : H →* C := e.codRestrict C hmem
  have hk : e1.ker = e.ker := MonoidHom.ker_codRestrict e C hmem
  have h1 := card_eq_range_mul_ker e1
  rw [hk] at h1
  haveI : Finite C := by
    apply Nat.finite_of_card_ne_zero
    rw [hC]
    exact Nat.card_pos.ne'
  have hle : Nat.card e1.range ≤ Nat.card C :=
    Nat.card_le_card_of_injective (fun x : e1.range => (x : C)) Subtype.val_injective
  rw [h1, ← hC]
  exact Nat.mul_le_mul_right _ hle

/-- **Finite abelian duality for kernels**: `#G · #R = #H · #L`. -/
theorem card_mul_card_ker (e : H →* (G →* kˣ)) :
    Nat.card G * Nat.card e.ker = Nat.card H * Nat.card (leftKer e) := by
  have hG := Subgroup.card_eq_card_quotient_mul_card_subgroup (leftKer e)
  have hH := Subgroup.card_eq_card_quotient_mul_card_subgroup e.ker
  have h1 := card_le_quot_mul_ker e
  have h2 := card_le_quot_mul_ker (flipHom e)
  have hfk : (flipHom e).ker = leftKer e := ker_flipHom e
  have hlf : leftKer (flipHom e) = e.ker := by
    ext h
    constructor
    · intro hh
      rw [MonoidHom.mem_ker]
      exact MonoidHom.ext fun x => hh x
    · intro hh x
      rw [MonoidHom.mem_ker] at hh
      exact DFunLike.congr_fun hh x
  rw [hfk, hlf] at h2
  have hR0 : 0 < Nat.card e.ker := Nat.card_pos
  have hL0 : 0 < Nat.card (leftKer e) := Nat.card_pos
  rw [hH] at h1
  rw [hG] at h2
  have hac : Nat.card (H ⧸ e.ker) ≤ Nat.card (G ⧸ leftKer e) := Nat.le_of_mul_le_mul_right h1 hR0
  have hca : Nat.card (G ⧸ leftKer e) ≤ Nat.card (H ⧸ e.ker) := Nat.le_of_mul_le_mul_right h2 hL0
  have heq : Nat.card (G ⧸ leftKer e) = Nat.card (H ⧸ e.ker) := le_antisymm hca hac
  rw [hG, hH, heq]
  ring

/-- For a pairing of a finite group with itself, the two kernels have the same size. -/
theorem card_leftKer_eq_card_ker (e : G →* (G →* kˣ)) :
    Nat.card (leftKer e) = Nat.card e.ker := by
  have h := card_mul_card_ker e
  have hG : 0 < Nat.card G := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_left hG h).symm

end Duality

section Level

variable {ℓ : ℕ} [Fact ℓ.Prime] {M N : Type*} [CommGroup M] [CommGroup N] {Ω : Type} [Field Ω]

theorem pow_of_mem_ker {G : Type*} [CommGroup G] {n : ℕ} {x : G}
    (h : x ∈ (powMonoidHom n : G →* G).ker) : x ^ n = 1 := by
  have h' := MonoidHom.mem_ker.mp h
  rwa [powMonoidHom_apply] at h'

theorem mem_ker_of_pow {G : Type*} [CommGroup G] {n : ℕ} {x : G} (h : x ^ n = 1) :
    x ∈ (powMonoidHom n : G →* G).ker := by
  rw [MonoidHom.mem_ker, powMonoidHom_apply]
  exact h

/-- The level-`ℓᵏ` pairing as a homomorphism `N[ℓᵏ] →* Hom(M[ℓᵏ], Ωˣ)`. -/
def LevelPairing.levelHom (P : LevelPairing ℓ M N Ω) (k : ℕ) :
    (powMonoidHom (ℓ ^ k) : N →* N).ker →* ((powMonoidHom (ℓ ^ k) : M →* M).ker →* Ωˣ) where
  toFun y :=
    { toFun := fun x => P.e k x.1 y.1
      map_one' := P.e_one_left k y.1 (pow_of_mem_ker y.2)
      map_mul' := fun x x' => P.mul_left k x.1 x'.1 y.1 (pow_of_mem_ker x.2) (pow_of_mem_ker x'.2)
        (pow_of_mem_ker y.2) }
  map_one' := MonoidHom.ext fun x => P.e_one_right k x.1 (pow_of_mem_ker x.2)
  map_mul' y y' := MonoidHom.ext fun x =>
    P.mul_right k x.1 y.1 y'.1 (pow_of_mem_ker x.2) (pow_of_mem_ker y.2) (pow_of_mem_ker y'.2)

theorem tate_eq_pow_smul {G : Type*} [CommGroup G] (t : Tate.T ℓ (Additive G)) (k a : ℕ) :
    t.1 k = (ℓ ^ a) • t.1 (k + a) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h2 : t.1 (k + a) = ℓ • t.1 (k + (a + 1)) := (t.2.2 (k + a)).symm
    rw [ih, h2, smul_smul, ← pow_succ]

/-- **A Tate vector whose components have uniformly bounded order is zero.** -/
theorem tate_eq_zero_of_order_bound {G : Type*} [CommGroup G] (t : Tate.T ℓ (Additive G)) (d : ℕ)
    (h : ∀ k, orderOf (Additive.toMul (t.1 k)) ≤ d) : t = 0 := by
  have hp : ℓ.Prime := Fact.out
  apply Subtype.ext
  funext k
  set x := Additive.toMul (t.1 (k + d)) with hx
  have hxt : x ^ (ℓ ^ (k + d)) = 1 := tors_of_tate t (k + d)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hxt)
  have hjd : ℓ ^ j ≤ d := hj ▸ h (k + d)
  have hlt : d < ℓ ^ d := Nat.lt_pow_self hp.one_lt
  have hj' : j ≤ d := by
    by_contra hc
    have := Nat.pow_le_pow_right hp.pos (not_le.1 hc).le
    omega
  have hxd : x ^ (ℓ ^ d) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hj]
    exact Nat.pow_dvd_pow ℓ hj'
  rw [tate_eq_pow_smul t k d]
  change (ℓ ^ d) • t.1 (k + d) = 0
  rw [← ofMul_toMul (t.1 (k + d)), ← ofMul_pow, ← hx, hxd]
  rfl

/-- **Both kernels of the limit of a self-pairing are trivial** when every right-kernel element at every
level lies in one fixed finite subgroup `C` (e.g. `K(L)` for `e^L`).  No perfectness at any finite level and
no condition on `#C` versus `ℓ`. -/
theorem LevelPairing.tate_kernels_of_right_bounded (P : LevelPairing ℓ M M Ω)
    (hfin : ∀ k, Finite (powMonoidHom (ℓ ^ k) : M →* M).ker)
    (hroots : ∀ k, HasEnoughRootsOfUnity Ω (Monoid.exponent (powMonoidHom (ℓ ^ k) : M →* M).ker))
    (C : Subgroup M) [Finite C]
    (hR : ∀ (k : ℕ) (y : M), y ^ (ℓ ^ k) = 1 → (∀ x : M, x ^ (ℓ ^ k) = 1 → P.e k x y = 1) → y ∈ C)
    (hlift : ∀ (k : ℕ) (x : M), x ^ (ℓ ^ k) = 1 →
      ∃ t : Tate.T ℓ (Additive M), Additive.toMul (t.1 k) = x) :
    (∀ t : Tate.T ℓ (Additive M), (∀ s, P.tatePairing t s = 0) → t = 0) ∧
    (∀ s : Tate.T ℓ (Additive M), (∀ t, P.tatePairing t s = 0) → s = 0) := by
  have hCpos : 0 < Nat.card C := Nat.card_pos
  -- order bound on the right kernel
  have hRord : ∀ (k : ℕ) (y : M), y ^ (ℓ ^ k) = 1 →
      (∀ x : M, x ^ (ℓ ^ k) = 1 → P.e k x y = 1) → orderOf y ≤ Nat.card C := by
    intro k y hy hyR
    have hyC := hR k y hy hyR
    have hdvd : orderOf (⟨y, hyC⟩ : C) ∣ Nat.card C := orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_coe] at hdvd
    exact Nat.le_of_dvd hCpos hdvd
  -- order bound on the left kernel, through duality
  have hLord : ∀ (k : ℕ) (x : M), x ^ (ℓ ^ k) = 1 →
      (∀ y : M, y ^ (ℓ ^ k) = 1 → P.e k x y = 1) → orderOf x ≤ Nat.card C := by
    intro k x hx hxL
    haveI := hfin k
    haveI := hroots k
    set e := P.levelHom k with he
    have hcard := card_leftKer_eq_card_ker e
    have hkerC : Nat.card e.ker ≤ Nat.card C := by
      let f : e.ker → C := fun y => ⟨(y.1 : M), hR k y.1.1 (pow_of_mem_ker y.1.2) (fun x' hx' => by
        have := DFunLike.congr_fun (MonoidHom.mem_ker.mp y.2) ⟨x', mem_ker_of_pow hx'⟩
        exact this)⟩
      exact Nat.card_le_card_of_injective f (fun a b hab => by
        have hab' : ((f a : C) : M) = ((f b : C) : M) := congrArg Subtype.val hab
        apply Subtype.ext
        apply Subtype.ext
        exact hab')
    have hxmem : (⟨x, mem_ker_of_pow hx⟩ : (powMonoidHom (ℓ ^ k) : M →* M).ker) ∈ leftKer e :=
      fun y => hxL y.1 (pow_of_mem_ker y.2)
    have hdvd : orderOf (⟨⟨x, mem_ker_of_pow hx⟩, hxmem⟩ : leftKer e) ∣ Nat.card (leftKer e) :=
      orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe] at hdvd
    exact (Nat.le_of_dvd Nat.card_pos hdvd).trans (hcard ▸ hkerC)
  refine ⟨fun t ht => ?_, fun s hs => ?_⟩
  · refine tate_eq_zero_of_order_bound t (Nat.card C) (fun k => ?_)
    refine hLord k _ (tors_of_tate t k) (fun y hy => ?_)
    obtain ⟨s, hs⟩ := hlift k y hy
    have h := congrArg (fun z : TMu Ω ℓ => Additive.toMul (z.1 k)) (ht s)
    simp only [tatePairing_apply, toMul_ofMul, hs] at h
    exact h
  · refine tate_eq_zero_of_order_bound s (Nat.card C) (fun k => ?_)
    refine hRord k _ (tors_of_tate s k) (fun x hx => ?_)
    obtain ⟨t, ht⟩ := hlift k x hx
    have h := congrArg (fun z : TMu Ω ℓ => Additive.toMul (z.1 k)) (hs t)
    simp only [tatePairing_apply, toMul_ofMul, ht] at h
    exact h

end Level

end WeilTate

#check @WeilTate.card_mul_card_ker
#check @WeilTate.card_leftKer_eq_card_ker
#check @WeilTate.LevelPairing.levelHom
#check @WeilTate.tate_eq_zero_of_order_bound
#check @WeilTate.LevelPairing.tate_kernels_of_right_bounded
#print axioms WeilTate.card_mul_card_ker
#print axioms WeilTate.card_leftKer_eq_card_ker
#print axioms WeilTate.LevelPairing.levelHom
#print axioms WeilTate.tate_eq_zero_of_order_bound
#print axioms WeilTate.LevelPairing.tate_kernels_of_right_bounded

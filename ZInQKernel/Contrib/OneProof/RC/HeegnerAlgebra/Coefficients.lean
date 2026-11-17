import Mathlib

/-!
# Lane RC10 (Heegner algebra), part 0: the coefficient rings `A_i` and their characters

Manuscript `diophantine_zq.tex` (11/5), Section 8 setup, tex lines 2720–2741, the conventions of
`ex:arith-data` (2743–2760) and of `ex:arith-conjugate-duality` (2779–2796), and the coefficient
ring `A = (ℤ/2^m)[t]/t^b` of the finite Heegner descent (2848–2851).

* `A_i = (ℤ/2^i)[t]/t^i` (tex 2725) is defined concretely; `1 + t` is a unit, and
  `(1 + t)^{2^{n}} = 1` for `n = 2i` ("`n_i` large enough that `(1+t)^{2^{n_i}} = 1` in `A_i`",
  tex 2785), all `PROVED`.
* The moving character `Ψ_i = (1 + t)^{ξ_i}` for `ξ_i : Gal(H_{r_i}/K) → ℤ/2^{n_i}` is a character
  with values in `A_i^×` and is inverted by conjugation when `ξ_i` is (tex 2781–2788), `PROVED`.
* For a finite elementary abelian `2`-group `G`, the universal quadratic character
  `ε : G_K → G ⊂ A[G]^×` satisfies `ε = ε⁻¹` (tex 2792–2795), `PROVED`.

The abstract statements of the other files are over an arbitrary commutative coefficient ring;
these instances show that their hypotheses are met by the manuscript's rings `A_i` and `A_i[G]`.
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

open Polynomial

/-- The coefficient ring `A_i = (ℤ/2^i)[t]/t^i` (tex 2725). -/
abbrev Acoef (i : ℕ) : Type := (ZMod (2 ^ i))[X] ⧸ Ideal.span {(X : (ZMod (2 ^ i))[X]) ^ i}

/-- The variable `t ∈ A_i`. -/
noncomputable def tA (i : ℕ) : Acoef i := Ideal.Quotient.mk _ X

/-- `t^i = 0` in `A_i`, `PROVED`. -/
theorem tA_pow (i : ℕ) : tA i ^ i = 0 := by
  rw [tA, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- `2^i = 0` in `A_i`, `PROVED`. -/
theorem two_pow_A (i : ℕ) : (2 : Acoef i) ^ i = 0 := by
  rw [show (2 : Acoef i) ^ i = ((2 ^ i : ℕ) : Acoef i) by push_cast; ring,
    ← map_natCast (algebraMap (ZMod (2 ^ i)) (Acoef i)), ZMod.natCast_self, map_zero]

/-- `1 + t` is a unit of `A_i` (`t` is nilpotent), `PROVED`. -/
theorem isUnit_one_add_tA (i : ℕ) : IsUnit (1 + tA i) :=
  (IsNilpotent.isUnit_one_add ⟨i, tA_pow i⟩)

/-- The squaring step: if `2 ∈ J` and `x - 1 ∈ J^{k+1}`, then `x² - 1 ∈ J^{k+2}`, since
`x² - 1 = (x - 1)((x - 1) + 2)`. -/
theorem sq_sub_one_mem_pow {R : Type*} [CommRing R] (J : Ideal R) (h2 : (2 : R) ∈ J) (x : R)
    (k : ℕ) (hx : x - 1 ∈ J ^ (k + 1)) : x ^ 2 - 1 ∈ J ^ (k + 2) := by
  have e : x ^ 2 - 1 = (x - 1) * ((x - 1) + 2) := by ring
  rw [e, pow_succ]
  exact Ideal.mul_mem_mul hx (J.add_mem (Ideal.pow_le_self (by omega) hx) h2)

/-- tex 2785, `PROVED`: `(1 + t)^{2^{2i}} = 1` in `A_i`; one may take `n_i = 2i`. -/
theorem one_add_tA_pow_two_pow (i : ℕ) : (1 + tA i) ^ (2 ^ (2 * i)) = 1 := by
  -- `J = (2, t)`: `(1 + t)^{2^k} - 1 ∈ J^{k+1}`, and `J^{2i} ⊆ (2^i) + (t^i) = 0`
  set J : Ideal (Acoef i) := Ideal.span {(2 : Acoef i)} ⊔ Ideal.span {tA i} with hJdef
  have h2J : (2 : Acoef i) ∈ J := Submodule.mem_sup_left (Ideal.subset_span rfl)
  have htJ : tA i ∈ J := Submodule.mem_sup_right (Ideal.subset_span rfl)
  have key : ∀ k : ℕ, (1 + tA i) ^ (2 ^ k) - 1 ∈ J ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using htJ
    | succ k ih =>
      rw [pow_succ, pow_mul]
      exact sq_sub_one_mem_pow J h2J _ k ih
  have hJ : J ^ (i + i) = ⊥ := by
    have h := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(2 : Acoef i)})
      (J := Ideal.span {tA i}) (n := i) (m := i)
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, two_pow_A, tA_pow,
      Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at h
    exact le_bot_iff.mp h
  have hmem : (1 + tA i) ^ (2 ^ (2 * i)) - 1 ∈ J ^ (i + i) :=
    Ideal.pow_le_pow_right (by omega) (key (2 * i))
  rw [hJ, Ideal.mem_bot, sub_eq_zero] at hmem
  exact hmem

/-- The power character `ℤ/2^n → A^×`, `x ↦ u^x`, for a unit `u` with `u^{2^n} = 1`
(written multiplicatively on `ℤ/2^n`). -/
noncomputable def unitPowHom {A : Type*} [CommRing A] (n : ℕ) (u : Aˣ) (hu : u ^ (2 ^ n) = 1) :
    Multiplicative (ZMod (2 ^ n)) →* Aˣ :=
  { toFun := fun x => u ^ (Multiplicative.toAdd x).val
    map_one' := by simp
    map_mul' := fun x y => by
      rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hu, pow_add] }

/-- The power character evaluates as `u^{x.val}`, `PROVED`. -/
theorem unitPowHom_apply {A : Type*} [CommRing A] (n : ℕ) (u : Aˣ) (hu : u ^ (2 ^ n) = 1)
    (x : Multiplicative (ZMod (2 ^ n))) :
    unitPowHom n u hu x = u ^ (Multiplicative.toAdd x).val := by
  rfl

/-- The moving character `Ψ = (1 + t)^ξ` (tex 2781–2783): for a homomorphism
`ξ : Γ → ℤ/2^n` (written multiplicatively) and a unit `u` of a commutative ring with
`u^{2^n} = 1` (here `u = 1 + t ∈ A_i`, `n ≥ 2i`), `γ ↦ u^{ξ(γ)}` is a character `Γ → A^×`. -/
noncomputable def movingChar {Γ A : Type*} [Group Γ] [CommRing A] (n : ℕ) (u : Aˣ)
    (hu : u ^ (2 ^ n) = 1) (ξ : Γ →* Multiplicative (ZMod (2 ^ n))) : Γ →* Aˣ :=
  (unitPowHom n u hu).comp ξ

/-- tex 2786–2788, `PROVED`: conjugation acts on the ring-class group by inversion, so
`Ψ(τ g τ⁻¹) = Ψ(g)⁻¹`. -/
theorem movingChar_conj {Γ A : Type*} [Group Γ] [CommRing A] (n : ℕ) (u : Aˣ)
    (hu : u ^ (2 ^ n) = 1) (ξ : Γ →* Multiplicative (ZMod (2 ^ n))) (c : Γ →* Γ)
    (hξ : ∀ g, ξ (c g) = (ξ g)⁻¹) (g : Γ) :
    movingChar n u hu ξ (c g) = (movingChar n u hu ξ g)⁻¹ := by
  simp only [movingChar, MonoidHom.comp_apply, hξ, map_inv]

/-- tex 2792–2795, `PROVED`: for an elementary abelian `2`-group `G`, the group-ring basis
element `[g] ∈ A[G]^×` satisfies `[g]⁻¹ = [g]`, so the universal quadratic character
`ε : G_K → G ⊂ A[G]^×` satisfies `ε^τ = ε = ε⁻¹`. -/
theorem groupRing_basis_sq {A G : Type*} [CommRing A] [Group G] (hG : ∀ g : G, g * g = 1)
    (g : G) : MonoidAlgebra.of A G g * MonoidAlgebra.of A G g = 1 := by
  rw [← map_mul, hG, map_one]

end ZInQ.Manuscript.RC.HeegnerAlgebra

import ZInQKernel.RouteK.Assembly.FirstCurve

/-!
# Route K, L5: the second curve (slot-k §2.5, steps 5–6)

`d₂ = d₁ θ`, the product of the primes `D.f₂`. Its configuration `𝒞₂` glues back to `𝒞_Σ`:

5. Lemma 2 applies to `𝒞₂` with `S' = P ∪ R_P`, `g = q₀`, `G = T` and glue primes `r_ℓ`
   (`gluing₂`). The glued vertex `q₀*` has class `3θ ≡ 3 (mod 8)`, and its symbols are those of
   `q₀`: for `p ∈ P`, `Σ_{ℓ∈T} [p/ℓ] = [θ/p] + λ_p λ_θ = 0` by (θ4) and `θ ≡ 1 (mod 4)` (written
   with Legendre reciprocity prime by prime, as rv-slot-k-proof §9.6 suggests) and
   `Σ_{ℓ∈T} [ℓ/p] = [θ/p] = 0` by (θ4); for `r_p`, all symbols with `T` vanish. So the glued
   configuration is `𝒞_Σ` up to the relabelling `q₀ ↦ q₀*` (`isoS`), and `Σ(𝒞₂)` has 8 solutions.
6. The class `σ_Σ` of step 4 lifts through Lemma 2: by (2.1),
   `u_{r_ℓ} = [|β|/ℓ] + λ_ℓ(v_{q₀} + a₀) = (sλ_ℓ + [β/ℓ]) + λ_ℓ s = 0` by (θ3); and `u_T = u_{q₀} = 0`.
   So the lifted class is again the class of `β`.
-/

namespace ZInQ.RouteK

open scoped BigOperators

/-- `Unit ⊕ X ≃ Option X`, sending the left summand to `none`. -/
def unitSumEquivOption (X : Type*) : Unit ⊕ X ≃ Option X where
  toFun := Sum.elim (fun _ => none) some
  invFun o := o.elim (.inl ()) .inr
  left_inv := by rintro (_ | x) <;> rfl
  right_inv := by rintro (_ | x) <;> rfl

/-- `[ℓ/|β|] = s λ_ℓ + [ℓ/β]`, for `s = [β < 0]`. -/
theorem legBit_natAbs {ℓ : ℕ} [Fact ℓ.Prime] {β : ℤ} (hβ : (β : ZMod ℓ) ≠ 0) :
    legBit ℓ (β.natAbs : ℤ) = signBit β * lamBit ℓ + legBit ℓ β := by
  rcases lt_or_ge β 0 with h | h
  · have e : ((β.natAbs : ℕ) : ℤ) = -1 * β := by omega
    have h1 : ((-1 : ℤ) : ZMod ℓ) ≠ 0 := by push_cast; exact neg_ne_zero.mpr one_ne_zero
    rw [e, legBit_mul h1 hβ, signBit, ite_eq_left h, one_mul, lamBit]
  · have e : ((β.natAbs : ℕ) : ℤ) = β := by omega
    rw [e, signBit, ite_eq_right (not_lt.mpr h), zero_mul, zero_add]

namespace Slots

variable {β θ : ℤ} {p₀ : ℕ} (D : Slots β θ p₀) (hI : Inputs β θ p₀)

/-- The configuration `𝒞₂` of `d₂` on `P ∪ R_P ∪ {q₀} ∪ T ∪ R_T`. -/
noncomputable def cfg₂ : Config ((Option (GP β p₀) ⊕ GP β p₀) ⊕ (Option (TP θ) ⊕ TP θ)) :=
  primeCfg D.f₂ (f₂_injective hI) (f₂_prime hI)

/-- `d₂ = d₁ θ`. -/
def d₂ : ℕ := ∏ k, D.f₂ k

include hI

/-! ### Sums over `P` and `T` -/

omit hI in
theorem sum_pP {M : Type*} [AddCommMonoid M] (hp₀ : p₀ ∈ primesOf β) (g : ℕ → M) :
    ∑ o : Option (GP β p₀), g (pP o) = ∑ p ∈ primesOf β, g p := by
  rw [Fintype.sum_option]
  change g p₀ + ∑ p : GP β p₀, g p.1 = _
  rw [Finset.sum_coe_sort (primesOf β \ {p₀}) g]
  exact (Finset.sum_eq_add_sum_sdiff_singleton_of_mem hp₀ g).symm

omit hI in
theorem prod_qT {M : Type*} [CommMonoid M] (g : ℕ → M) :
    ∏ o : Option (TP θ), g (D.qT o) = g D.q₀ * ∏ ℓ ∈ primesOf θ, g ℓ := by
  rw [Fintype.prod_option]
  change g D.q₀ * ∏ ℓ : TP θ, g ℓ.1 = _
  rw [Finset.prod_coe_sort (primesOf θ) g]

omit hI in
theorem sum_qT {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ o : Option (TP θ), g (D.qT o) = g D.q₀ + ∑ ℓ ∈ primesOf θ, g ℓ := by
  rw [Fintype.sum_option]
  change g D.q₀ + ∑ ℓ : TP θ, g ℓ.1 = _
  rw [Finset.sum_coe_sort (primesOf θ) g]

theorem θ_eq_prod : θ = ∏ ℓ ∈ primesOf θ, (ℓ : ℤ) := by
  rw [← Nat.cast_prod, hI.prod_T]
  have := hI.pos_θ
  omega

/-- `Σ_{ℓ∈T} [ℓ/p] = [θ/p] = 0` for `p ∈ P`, by (θ4). -/
theorem sum_T_legBit_P {p : ℕ} (hp : p ∈ primesOf β) : ∑ ℓ ∈ primesOf θ, legBit p ℓ = 0 := by
  have := Fact.mk (hI.mem_P hp).1
  rw [← legBit_prod _ _ fun ℓ hℓ => natCast_zmod_ne_zero_of_prime_ne (hI.mem_P hp).1
    (hI.mem_T hℓ).1 fun h => hI.disjoint hp (h ▸ hℓ), ← θ_eq_prod hI]
  exact hI.θ4 p hp

/-- `Σ_{ℓ∈T} λ_ℓ = λ_θ = 0`, since `θ ≡ 1 (mod 4)`. -/
theorem sum_T_lamBit : ∑ ℓ ∈ primesOf θ, lamBit ℓ = 0 := by
  rw [← Finset.sum_congr rfl fun ℓ hℓ => lam8_natCast_eq_lamBit (hI.mem_T hℓ).1 (hI.mem_T hℓ).2,
    ← lam8_prod _ _ fun ℓ hℓ => natCast_mem_oddClasses
      (((hI.mem_T hℓ).1.eq_two_or_odd).resolve_left (hI.mem_T hℓ).2),
    ← Nat.cast_prod, hI.prod_T, natCast_zmod8_of_mod hI.θ_natAbs_mod]
  rfl

/-- `Σ_{ℓ∈T} [p/ℓ] = [θ/p] + λ_p λ_θ = 0` for `p ∈ P`, by Legendre reciprocity prime by prime. -/
theorem sum_T_legBit_P' {p : ℕ} (hp : p ∈ primesOf β) : ∑ ℓ ∈ primesOf θ, legBit ℓ p = 0 := by
  have key : ∀ ℓ ∈ primesOf θ, legBit ℓ p = legBit p ℓ + lamBit ℓ * lamBit p := fun ℓ hℓ => by
    have h := legBit_reciprocity (hI.mem_T hℓ).1 (hI.mem_P hp).1 (hI.mem_T hℓ).2 (hI.mem_P hp).2
      fun h => hI.disjoint hp (h ▸ hℓ)
    rw [← h]
    ring_nf; reduce_mod_char
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_mul, sum_T_legBit_P hI hp,
    sum_T_lamBit hI, zero_mul, add_zero]

/-! ### Step 5: gluing the primes of `θ` onto `q₀` -/

theorem gluing₂ : (D.cfg₂ hI).Gluing where
  cls_eq_one ℓ := natCast_zmod8_of_mod (D.rT_mod_eight ℓ.1 ℓ.2)
  bit_ell ℓ := D.rT_sym_self ℓ.1 ℓ.2
  bit_g ℓ := D.rT_sym_q₀ ℓ.1 ℓ.2
  bit_other := by
    rintro ℓ ((o | p) | (_ | ℓ') | ℓ') h1 h2 h3
    · exact D.rT_sym_P ℓ.1 ℓ.2 (pP o) (pP_mem hI o)
    · exact D.rT_sym_rP ℓ.1 ℓ.2 p.1 p.2
    · exact absurd rfl h3
    · exact D.rT_sym_T ℓ.1 ℓ.2 ℓ'.1 ℓ'.2
        fun h => h2 (congrArg (fun x => Sum.inr (Sum.inl (some x))) (Subtype.ext h))
    · exact D.rT_sym_rT ℓ.1 ℓ.2 ℓ'.1 ℓ'.2
        fun h => h1 (congrArg (fun x => Sum.inr (Sum.inr x)) (Subtype.ext h))

/-- The glued vertex has the class of `q₀`: `c_{q₀*} = q₀ θ ≡ q₀ (mod 8)`. -/
theorem glue₂_cls_none : (D.cfg₂ hI).glue.cls none = (D.q₀ : ZMod 8) := by
  rw [Config.glue_cls_none]
  change ∏ o : Option (TP θ), ((D.qT o : ℕ) : ZMod 8) = _
  rw [D.prod_qT (fun n => (n : ZMod 8)), ← Nat.cast_prod, hI.prod_T,
    natCast_zmod8_of_mod hI.θ_natAbs_mod, Nat.cast_one, mul_one]

/-- The symbols of `p ∈ P` and `r_p` with `T` vanish (both directions). -/
theorem sum_T_S' (z : Option (GP β p₀) ⊕ GP β p₀) :
    ∑ ℓ ∈ primesOf θ, legBit (D.f₂ (.inl z)) ℓ = 0 ∧
      ∑ ℓ ∈ primesOf θ, legBit ℓ (D.f₂ (.inl z)) = 0 := by
  rcases z with o | p
  · exact ⟨sum_T_legBit_P hI (pP_mem hI o), sum_T_legBit_P' hI (pP_mem hI o)⟩
  · refine ⟨Finset.sum_eq_zero fun ℓ hℓ => ?_, Finset.sum_eq_zero fun ℓ hℓ => D.rP_sym_T p.1 p.2 ℓ hℓ⟩
    change legBit (D.rP p.1) ℓ = 0
    rw [D.rev_rP p.2 (hI.mem_T hℓ).1 (hI.mem_T hℓ).2
      fun h => (D.rPv_not_mem p).2 (by change D.rP p.1 ∈ _; rw [← h]; exact hℓ)]
    exact D.rP_sym_T p.1 p.2 ℓ hℓ

/-- Step 5: the glued configuration is `𝒞_Σ`, relabelled by `q₀ ↦ q₀*`. -/
noncomputable def isoS : (D.cfgS hI).sols ≃ (D.cfg₂ hI).glue.sols :=
  (D.cfg₂ hI).glue.solsEquivOfIso (unitSumEquivOption _)
    (by
      rintro (_ | z)
      · exact (D.glue₂_cls_none hI).symm
      · rfl)
    (by
      rintro (_ | z) (_ | z') h
      · exact absurd rfl h
      · change legBit (D.f₂ (.inl z')) D.q₀ =
          ∑ o : Option (TP θ), legBit (D.f₂ (.inl z')) (D.qT o)
        rw [D.sum_qT (fun n => legBit (D.f₂ (.inl z')) n), (D.sum_T_S' hI z').1, add_zero]
      · change legBit D.q₀ (D.f₂ (.inl z)) =
          ∑ o : Option (TP θ), legBit (D.qT o) (D.f₂ (.inl z))
        rw [D.sum_qT (fun n => legBit n (D.f₂ (.inl z))), (D.sum_T_S' hI z).2, add_zero]
      · rfl)

theorem cfg₂_card : (D.cfg₂ hI).sols.card = 8 := by
  rw [(D.gluing₂ hI).card_sols, ← Finset.card_eq_of_equiv (D.isoS hI), D.cfgS_card hI]

/-! ### Step 6: the class of `β` -/

/-- The image of `σ_Σ` in the glued configuration. -/
noncomputable def tau₂ : Unknowns (Option (Option (GP β p₀) ⊕ GP β p₀)) :=
  (D.sigmaS hI).comp (unitSumEquivOption _).symm

theorem tau₂_mem : D.tau₂ hI ∈ (D.cfg₂ hI).glue.sols :=
  (D.isoS hI ⟨_, D.sigmaS_mem hI⟩).2

/-- The lift `σ₂` of `σ_Σ` to `Σ(𝒞₂)`. -/
noncomputable def sigma₂ : Unknowns ((Option (GP β p₀) ⊕ GP β p₀) ⊕ (Option (TP θ) ⊕ TP θ)) :=
  (D.cfg₂ hI).glueLift (D.tau₂ hI)

theorem sigma₂_mem : D.sigma₂ hI ∈ (D.cfg₂ hI).sols :=
  ((D.gluing₂ hI).solsEquiv.symm ⟨_, D.tau₂_mem hI⟩).2

/-- (2.1): `u_{r_ℓ} = [|β|/ℓ] + λ_ℓ s = 0`, by (θ3). -/
theorem sigma₂_u_R (ℓ : TP θ) : (D.sigma₂ hI).u (.inr (.inr ℓ)) = 0 := by
  have := Fact.mk (hI.mem_T ℓ.2).1
  have hβℓ : (β : ZMod ℓ.1) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => hI.disjoint (mem_primesOf.mpr ⟨(hI.mem_T ℓ.2).1, h, hI.β_ne_zero⟩) ℓ.2
  change ∑ y : Option (GP β p₀) ⊕ GP β p₀, legBit ℓ.1 (D.f₂ (.inl y)) *
      ((D.sigmaS hI).u (.inr y) + (D.sigmaS hI).u (.inl ())) + (D.sigmaS hI).u (.inl ()) +
      (D.cfg₂ hI).lam (.inr (.inl (some ℓ))) * ((D.sigmaS hI).v (.inl ()) + signBit β) = 0
  rw [show (D.cfg₂ hI).lam (.inr (.inl (some ℓ))) = lamBit ℓ.1 from primeCfg_lam D.f₂ _ _ _,
    sigmaS_u_q₀, sigmaS_v_q₀, Fintype.sum_sum_type]
  simp only [sigmaS_u_P, D.sigmaS_u_R hI, add_zero, zero_add, mul_one, mul_zero,
    Finset.sum_const_zero]
  change ∑ o : Option (GP β p₀), legBit ℓ.1 (pP o) + lamBit ℓ.1 * signBit β = 0
  rw [sum_pP hI.p₀_mem (fun p => legBit ℓ.1 p), ← legBit_prod _ _ fun p hp =>
    natCast_zmod_ne_zero_of_prime_ne (hI.mem_T ℓ.2).1 (hI.mem_P hp).1
      fun h => hI.disjoint hp (h ▸ ℓ.2), ← natAbs_eq_prod_primesOf hI.sqf_β,
    legBit_natAbs hβℓ, hI.θ3 ℓ.1 ℓ.2]
  ring_nf; reduce_mod_char

theorem sigma₂_u (k : (Option (GP β p₀) ⊕ GP β p₀) ⊕ (Option (TP θ) ⊕ TP θ)) :
    (D.sigma₂ hI).u k = if (D.f₂ k : ℤ) ∣ β then 1 else 0 := by
  rcases k with z | (o | ℓ)
  · exact D.sigmaS_u hI (.inr z)
  · change (D.sigmaS hI).u (.inl ()) = _
    rw [sigmaS_u_q₀]
    refine (ite_eq_right fun h => ?_).symm
    have hm := (prime_dvd_β_iff hI (qT_prime hI o).1).mp h
    cases o with
    | none => exact D.q₀_not_mem.1 hm
    | some ℓ => exact hI.disjoint hm ℓ.2
  · rw [D.sigma₂_u_R hI]
    exact (ite_eq_right fun h => (D.rTv_not_mem ℓ).1 ((prime_dvd_β_iff hI (rTv_prime ℓ).1).mp h)).symm

/-- **The second curve** (steps 5–6): `Σ(𝒞_{d₂})` has 8 solutions, one with first coordinate the
class of `β`. -/
theorem selmerCertified_d₂ : SelmerCertified D.d₂ β :=
  selmerCertified_of_primeCfg D.f₂ (f₂_injective hI) (f₂_prime hI) β (D.cfg₂_card hI)
    (D.sigma₂_mem hI) rfl rfl (D.sigma₂_u hI)

/-! ### The number `d₂` -/

theorem d₂_eq : D.d₂ = D.d₁ * θ.natAbs := by
  rw [d₁_eq, ← hI.prod_T]
  simp only [d₂, f₂, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [D.prod_qT (fun n => n)]
  ring

theorem squarefree_d₂ : Squarefree D.d₂ :=
  squarefree_prod_primes D.f₂ (f₂_injective hI) (f₂_prime hI)

end Slots

end ZInQ.RouteK

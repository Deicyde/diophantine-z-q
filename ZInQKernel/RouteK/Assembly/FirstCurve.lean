import ZInQKernel.RouteK.Assembly.Data

/-!
# Route K, L5: the first curve (slot-k §2.5, steps 1–4)

`d₁ = |β| q₀ Π r_p Π r_ℓ`, the product of the primes `D.f₁`. Its configuration `𝒞₁` reduces to the
base configuration:

1. every `r_ℓ` is a partner of `q₀` (Lemma 1, `partners₁`), so `Σ(𝒞₁) ≅ Σ(𝒞_Σ)`, where `𝒞_Σ` lives
   on `P ∪ {q₀} ∪ R_P`;
2. Lemma 2 applies to `𝒞_Σ` with `S' = {q₀}`, `g = p₀`, `G = P ∖ {p₀}` and glue primes `r_p`
   (`gluingS`); the glued configuration `𝒞₀` on `{p*, q₀}` has `c_{p*} = |β| mod 8 = 7`,
   `c_{q₀} = 3` and `[q₀/p*] = Σ_{p∈P} [q₀/p] = x = s + 1`;
3. Lemma 3: `Σ(𝒞₀)` has 8 solutions, hence so do `Σ(𝒞_Σ)` and `Σ(𝒞₁)`;
4. the solution `σ₀` of Lemma 3 with `a₀ = s = [β < 0]` lifts to `σ_Σ` (`sigmaS`) with `u = 𝟏_P`:
   by (2.1), `u_{r_p} = [q₀/p] + 1 + λ_p x = 0` by the choice of `[q₀/p]`; and further to `𝒞₁`,
   with `u_{r_ℓ} = u_{q₀} = 0`. Its first coordinate is the class of `β`.
-/

namespace ZInQ.RouteK

open scoped BigOperators

namespace Slots

variable {β θ : ℤ} {p₀ : ℕ} (D : Slots β θ p₀) (hI : Inputs β θ p₀)

/-- The configuration `𝒞_Σ` on `P ∪ {q₀} ∪ R_P`. -/
noncomputable def cfgS : Config (Unit ⊕ (Option (GP β p₀) ⊕ GP β p₀)) :=
  primeCfg D.fS (fS_injective hI) (fS_prime hI)

/-- The configuration `𝒞₁` of `d₁` on `P ∪ {q₀} ∪ R_P ∪ R_T`. -/
noncomputable def cfg₁ : Config ((Unit ⊕ (Option (GP β p₀) ⊕ GP β p₀)) ⊕ TP θ) :=
  primeCfg D.f₁ (f₁_injective hI) (f₁_prime hI)

/-- `d₁ = |β| q₀ Π r_p Π r_ℓ`. -/
def d₁ : ℕ := ∏ k, D.f₁ k

include hI

theorem prime_dvd_β_iff {q : ℕ} (hq : q.Prime) : (q : ℤ) ∣ β ↔ q ∈ primesOf β :=
  ⟨fun h => mem_primesOf.mpr ⟨hq, h, hI.β_ne_zero⟩, fun h => (mem_primesOf.mp h).2.1⟩

omit hI in
theorem prod_pP (hp₀ : p₀ ∈ primesOf β) (hβ : Squarefree β) :
    ∏ o : Option (GP β p₀), pP o = β.natAbs := by
  rw [Fintype.prod_option, ← Nat.prod_primeFactors_of_squarefree (Int.squarefree_natAbs.mpr hβ)]
  change p₀ * ∏ p : GP β p₀, p.1 = _
  rw [Finset.prod_coe_sort (primesOf β \ {p₀}) (fun p => p)]
  exact (Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hp₀ (fun p => p)).symm

theorem sum_pP_q₀ : ∑ o : Option (GP β p₀), legBit (pP o) D.q₀ = signBit β + 1 := by
  rw [Fintype.sum_option, ← D.sum_q₀_sym hI.p₀_mem]
  change legBit p₀ D.q₀ + ∑ p : GP β p₀, legBit p.1 D.q₀ = _
  rw [Finset.sum_coe_sort (primesOf β \ {p₀}) (fun p => legBit p D.q₀)]
  exact (Finset.sum_eq_add_sum_sdiff_singleton_of_mem hI.p₀_mem (fun p => legBit p D.q₀)).symm

/-! ### Step 1: the partners `r_ℓ` -/

theorem partners₁ : (D.cfg₁ hI).Partners (fun _ => Sum.inl ()) where
  cls_eq_one r := natCast_zmod8_of_mod (D.rT_mod_eight r.1 r.2)
  bit_partner r := D.rT_sym_q₀ r.1 r.2
  bit_other := by
    rintro r ((_ | o | p) | r') hz hz'
    · exact absurd rfl hz'
    · exact D.rT_sym_P r.1 r.2 (pP o) (pP_mem hI o)
    · exact D.rT_sym_rP r.1 r.2 p.1 p.2
    · exact D.rT_sym_rT r.1 r.2 r'.1 r'.2 fun h => hz (congrArg Sum.inr (Subtype.ext h))

theorem restrict₁ : (D.cfg₁ hI).restrictLeft = D.cfgS hI := rfl

/-! ### Step 2: gluing the primes of `β` -/

theorem gluingS : (D.cfgS hI).Gluing where
  cls_eq_one ℓ := natCast_zmod8_of_mod (D.rP_mod_eight ℓ.1 ℓ.2)
  bit_ell ℓ := D.rP_sym_self ℓ.1 ℓ.2
  bit_g ℓ := D.rP_sym_p₀ ℓ.1 ℓ.2
  bit_other := by
    rintro ℓ (_ | (_ | p) | p) h1 h2 h3
    · exact D.rP_sym_q₀ ℓ.1 ℓ.2
    · exact absurd rfl h3
    · have hp := Finset.mem_sdiff.mp p.2
      exact D.rP_sym_P ℓ.1 ℓ.2 p.1 hp.1
        (fun h => h2 (congrArg (fun x => Sum.inr (Sum.inl (some x))) (Subtype.ext h)))
        fun h => hp.2 (Finset.mem_singleton.mpr h)
    · exact D.rP_sym_rP ℓ.1 ℓ.2 p.1 p.2 fun h => h1 (congrArg (fun x => Sum.inr (Sum.inr x))
        (Subtype.ext h))

theorem glueS_cls_none : (D.cfgS hI).glue.cls none = 7 := by
  rw [Config.glue_cls_none]
  change ∏ o : Option (GP β p₀), ((pP o : ℕ) : ZMod 8) = 7
  rw [← Nat.cast_prod, prod_pP hI.p₀_mem hI.sqf_β, natCast_zmod8_of_mod hI.mod_β]
  rfl

theorem glueS_cls_some : (D.cfgS hI).glue.cls (some ()) = 3 := by
  rw [Config.glue_cls_some]
  exact natCast_zmod8_of_mod D.q₀_mod_eight

/-- `[q₀/p*] = Σ_{p∈P} [q₀/p] = x`. -/
theorem glueS_bit : (D.cfgS hI).glue.bit (some ()) none = signBit β + 1 := by
  rw [Config.glue_bit_some_none]
  exact D.sum_pP_q₀ hI

/-! ### Step 3: Lemma 3 -/

theorem glueS_card : (D.cfgS hI).glue.sols.card = 8 :=
  Config.base_card_sols' _ (p := none) (q := some ()) (by simp)
    (fun z => by rcases z with _ | ⟨⟩ <;> simp) (D.glueS_cls_none hI) (D.glueS_cls_some hI)

theorem cfgS_card : (D.cfgS hI).sols.card = 8 := by
  rw [(D.gluingS hI).card_sols, D.glueS_card hI]

theorem cfg₁_card : (D.cfg₁ hI).sols.card = 8 := by
  rw [(D.partners₁ hI).card_sols, restrict₁ D hI, D.cfgS_card hI]

/-! ### Step 4: the class of `β` -/

omit hI in
/-- The solution `σ₀` of Lemma 3 with `a₀ = s` and `x = s + 1`. -/
def tau₀ (β : ℤ) : Unknowns (Option Unit) :=
  ⟨signBit β, 0, signBit β, 0, fun z => if z = none then 1 else 0,
    fun z => if z = none then signBit β + (signBit β + 1) else signBit β + (signBit β + 1) + 1⟩

theorem tau₀_mem : tau₀ β ∈ (D.cfgS hI).glue.sols := by
  have := Config.base_mem_sols' (D.cfgS hI).glue (p := none) (q := some ()) (by simp)
    (fun z => by rcases z with _ | ⟨⟩ <;> simp) (D.glueS_cls_none hI) (D.glueS_cls_some hI)
    (signBit β)
  rw [D.glueS_bit hI] at this
  exact this

/-- The lift `σ_Σ` of `σ₀` to `Σ(𝒞_Σ)`. -/
noncomputable def sigmaS : Unknowns (Unit ⊕ (Option (GP β p₀) ⊕ GP β p₀)) :=
  (D.cfgS hI).glueLift (tau₀ β)

theorem sigmaS_mem : D.sigmaS hI ∈ (D.cfgS hI).sols :=
  ((D.gluingS hI).solsEquiv.symm ⟨_, D.tau₀_mem hI⟩).2

theorem sigmaS_a0 : (D.sigmaS hI).a0 = signBit β := rfl

theorem sigmaS_a1 : (D.sigmaS hI).a1 = 0 := rfl

theorem sigmaS_u_q₀ : (D.sigmaS hI).u (Sum.inl ()) = 0 := rfl

theorem sigmaS_u_P (o : Option (GP β p₀)) : (D.sigmaS hI).u (Sum.inr (Sum.inl o)) = 1 := rfl

theorem sigmaS_v_q₀ : (D.sigmaS hI).v (Sum.inl ()) = 0 := by
  change signBit β + (signBit β + 1) + 1 = 0
  generalize signBit β = s
  revert s; decide

/-- (2.1): `u_{r_p} = [q₀/p] + 1 + λ_p x = 0`. -/
theorem sigmaS_u_R (p : GP β p₀) : (D.sigmaS hI).u (Sum.inr (Sum.inr p)) = 0 := by
  change ∑ y : Unit, legBit p.1 D.q₀ * ((tau₀ β).u (some y) + (tau₀ β).u none) + (tau₀ β).u none +
      (D.cfgS hI).lam (Sum.inr (Sum.inl (some p))) * ((tau₀ β).v none + (tau₀ β).a0) = 0
  rw [show (D.cfgS hI).lam (Sum.inr (Sum.inl (some p))) = lamBit p.1 from
    primeCfg_lam D.fS _ _ _, Fintype.sum_unique]
  change legBit p.1 D.q₀ * (0 + 1) + 1 + lamBit p.1 * (signBit β + (signBit β + 1) + signBit β) = 0
  rw [D.q₀_sym_P p.1 p.2]
  generalize signBit β = s
  generalize lamBit p.1 = l
  revert s l; decide

theorem sigmaS_u (k : Unit ⊕ (Option (GP β p₀) ⊕ GP β p₀)) :
    (D.sigmaS hI).u k = if (D.fS k : ℤ) ∣ β then 1 else 0 := by
  rcases k with _ | o | p
  · rw [sigmaS_u_q₀]
    exact (ite_eq_right fun h => D.q₀_not_mem.1 ((prime_dvd_β_iff hI D.q₀_prime).mp h)).symm
  · rw [sigmaS_u_P]
    exact (ite_eq_left ((prime_dvd_β_iff hI (hI.mem_P (pP_mem hI o)).1).mpr (pP_mem hI o))).symm
  · rw [D.sigmaS_u_R hI]
    exact (ite_eq_right fun h => (D.rPv_not_mem p).1 ((prime_dvd_β_iff hI (rPv_prime p).1).mp h)).symm

/-- The lift `σ₁` of `σ_Σ` to `Σ(𝒞₁)`, with `u_{r_ℓ} = u_{q₀}`. -/
noncomputable def sigma₁ : Unknowns ((Unit ⊕ (Option (GP β p₀) ⊕ GP β p₀)) ⊕ TP θ) :=
  Config.partnerExtend (fun _ => Sum.inl ()) (D.sigmaS hI)

theorem sigma₁_mem : D.sigma₁ hI ∈ (D.cfg₁ hI).sols :=
  (D.partners₁ hI).extend_mem (D.sigmaS_mem hI)

theorem sigma₁_u (k : (Unit ⊕ (Option (GP β p₀) ⊕ GP β p₀)) ⊕ TP θ) :
    (D.sigma₁ hI).u k = if (D.f₁ k : ℤ) ∣ β then 1 else 0 := by
  rcases k with k | ℓ
  · exact D.sigmaS_u hI k
  · change (D.sigmaS hI).u (Sum.inl ()) = _
    rw [sigmaS_u_q₀]
    exact (ite_eq_right fun h => (D.rTv_not_mem ℓ).1 ((prime_dvd_β_iff hI (rTv_prime ℓ).1).mp h)).symm

/-- **The first curve** (steps 1–4): `Σ(𝒞_{d₁})` has 8 solutions, one with first coordinate the
class of `β`. -/
theorem selmerCertified_d₁ : SelmerCertified D.d₁ β :=
  selmerCertified_of_primeCfg D.f₁ (f₁_injective hI) (f₁_prime hI) β (D.cfg₁_card hI)
    (D.sigma₁_mem hI) rfl rfl (D.sigma₁_u hI)

/-! ### The number `d₁` -/

omit hI in
theorem d₁_eq : D.d₁ = (∏ o : Option (GP β p₀), pP o) *
    (D.q₀ * (∏ p : GP β p₀, D.rPv p) * ∏ ℓ : TP θ, D.rTv ℓ) := by
  simp only [d₁, f₁, fS, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique]
  ring

theorem d₁_eq' : D.d₁ = β.natAbs * (D.q₀ * (∏ p : GP β p₀, D.rPv p) * ∏ ℓ : TP θ, D.rTv ℓ) := by
  rw [d₁_eq, prod_pP hI.p₀_mem hI.sqf_β]

theorem β_dvd_d₁ : β ∣ (D.d₁ : ℤ) := by
  rw [D.d₁_eq' hI, Nat.cast_mul]
  exact dvd_mul_of_dvd_left Int.dvd_natAbs_self _

theorem squarefree_d₁ : Squarefree D.d₁ :=
  squarefree_prod_primes D.f₁ (f₁_injective hI) (f₁_prime hI)

omit hI in
theorem prod_rPv_zmod : ∏ p : GP β p₀, ((D.rPv p : ℕ) : ZMod 8) = 1 :=
  Finset.prod_eq_one fun p _ => natCast_zmod8_of_mod (D.rP_mod_eight p.1 p.2)

omit hI in
theorem prod_rTv_zmod : ∏ ℓ : TP θ, ((D.rTv ℓ : ℕ) : ZMod 8) = 1 :=
  Finset.prod_eq_one fun ℓ _ => natCast_zmod8_of_mod (D.rT_mod_eight ℓ.1 ℓ.2)

theorem d₁_zmod : (D.d₁ : ZMod 8) = 5 := by
  rw [D.d₁_eq' hI]
  push_cast
  rw [prod_rPv_zmod, prod_rTv_zmod, natCast_zmod8_of_mod hI.mod_β,
    natCast_zmod8_of_mod D.q₀_mod_eight]
  rfl

theorem d₁_mod : D.d₁ % 8 = 5 := by
  rw [← ZMod.val_natCast, D.d₁_zmod hI]
  rfl

end Slots

end ZInQ.RouteK

import ZInQKernel.Contrib.OneProof.EichlerBound.Count

/-! eichler-bound, part B8: inertness when two types occur, and **the count**
`#(Emb(R, 𝒪)/𝒪^×) ≤ 2^{b(k)} · #Pic(R)`. No `sorry`. -/

set_option linter.style.longLine false

noncomputable section

namespace EichlerBound

open LeafQM LeafQM.AV GRCountX6 NumberField

section Emb

variable {k : Type} [Field k] [NumberField k] {R : Subring k} (Bs : QBasis R)

theorem coprime_conductor (hc : Nat.Coprime (conductor R) 6) {ℓ : ℤ} (hℓ : L6 ℓ) :
    IsCoprime (conductor R : ℤ) ℓ := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  rcases hℓ with rfl | rfl
  · have : Nat.Coprime (conductor R) 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
    exact_mod_cast this
  · have : Nat.Coprime (conductor R) 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hc
    exact_mod_cast this

include Bs in
/-- An element `z ∈ 𝒪_k` with `Ψ(f z) ∈ P_ℓ` is divisible by `ℓ` in `𝒪_k`, unless `Ψ(ω)` is congruent to an
integer modulo `P_ℓ`. -/
theorem dvd_of_PP (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6)
    (Ψ : OptEmb k R) {ℓ : ℤ} (hℓ : L6 ℓ) (h : ∀ m : ℤ, ¬ PP ℓ (Ψ.1 Bs.ω - ((m : ℚ) : B)))
    (z : 𝓞 k) (hz : PP ℓ (Ψ.1 ((conductor R : ℤ) • (z : k)))) : ((ℓ : ℤ) : 𝓞 k) ∣ z := by
  have hβ0 := emb_omega_mem Bs Ψ
  have hfz := conductor_smul_mem R (RingOfIntegers.isIntegral_coe z)
  obtain ⟨X, Y, hXY⟩ := Bs.span _ hfz
  have hlin : Ψ.1 ((conductor R : ℤ) • (z : k)) = ((X : ℚ) : B) + ((Y : ℚ) : B) * Ψ.1 Bs.ω := by
    rw [hXY, show ((X : k)) = ((X : ℚ) : k) by push_cast; rfl,
      show ((Y : k)) = ((Y : ℚ) : k) by push_cast; rfl, emb_lin]
  rw [hlin] at hz
  have hY : ℓ ∣ Y := by
    by_contra hnd
    have hc2 : IsCoprime ℓ Y := (Irreducible.coprime_iff_not_dvd (L6_prime hℓ).irreducible).mpr hnd
    obtain ⟨v, u, huv⟩ := hc2
    apply h (-(u * X))
    have huv' : ((v : ℚ) * ℓ + u * Y) = 1 := by exact_mod_cast huv
    have e : Ψ.1 Bs.ω - (((-(u * X) : ℤ) : ℚ) : B) =
        ((u : ℚ) : B) * (((X : ℚ) : B) + ((Y : ℚ) : B) * Ψ.1 Bs.ω) + (ℓ : ℚ) • ((v : ℚ) • Ψ.1 Bs.ω) := by
      refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> simp
      · linear_combination (-(Ψ.1 Bs.ω).re) * huv'
      · linear_combination (-(Ψ.1 Bs.ω).imI) * huv'
      · linear_combination (-(Ψ.1 Bs.ω).imJ) * huv'
      · linear_combination (-(Ψ.1 Bs.ω).imK) * huv'
    rw [e]
    exact PP_add hℓ (PP_mul_left (intCast_mem u) hz) (PP_of_LO (LO_of_smul (smul_mem_O hβ0 v)))
  obtain ⟨Y', rfl⟩ := hY
  have hX : ℓ ∣ X := by
    apply dvd_of_PP_int hℓ
    have : ((X : ℚ) : B) = (((X : ℚ) : B) + (((ℓ * Y' : ℤ) : ℚ) : B) * Ψ.1 Bs.ω) -
        (ℓ : ℚ) • ((Y' : ℚ) • Ψ.1 Bs.ω) := by
      rw [smul_smul, ← coe_mul_eq_smul]; push_cast; abel
    rw [this]
    exact PP_sub hℓ hz (PP_of_LO (LO_of_smul (smul_mem_O hβ0 Y')))
  obtain ⟨X', rfl⟩ := hX
  obtain ⟨u', v', huv'⟩ := coprime_conductor hc hℓ
  have hrR : (X' : k) + (Y' : k) * Bs.ω ∈ R :=
    R.add_mem (_root_.intCast_mem R X') (R.mul_mem (_root_.intCast_mem R Y') Bs.mem)
  obtain ⟨r', hr'⟩ : ∃ r' : 𝓞 k, (r' : k) = (X' : k) + (Y' : k) * Bs.ω := ⟨⟨_, hR hrR⟩, rfl⟩
  refine ⟨(u' : 𝓞 k) * r' + (v' : 𝓞 k) * z, ?_⟩
  apply RingOfIntegers.ext
  have hf : ((conductor R : ℤ) : k) * (z : k) = (ℓ : k) * ((X' : k) + (Y' : k) * Bs.ω) := by
    rw [← zsmul_eq_mul, hXY]; push_cast; ring
  have huv'' : (u' : k) * (conductor R : ℤ) + (v' : k) * ℓ = 1 := by exact_mod_cast huv'
  show (z : k) = algebraMap (𝓞 k) k (((ℓ : ℤ) : 𝓞 k) * ((u' : 𝓞 k) * r' + (v' : 𝓞 k) * z))
  rw [map_mul, map_add, map_mul, map_mul, map_intCast, map_intCast, map_intCast]
  change (z : k) = (ℓ : k) * ((u' : k) * (r' : k) + (v' : k) * (z : k))
  rw [hr']
  linear_combination (-(z : k)) * huv'' + (u' : k) * hf

include Bs in
/-- **Inertness**: if `Ψ(ω)` is not congruent to an integer modulo `P_ℓ`, then `ℓ 𝒪_k` is prime. -/
theorem inert_of_noint (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6)
    (Ψ : OptEmb k R) {ℓ : ℤ} (hℓ : L6 ℓ) (h : ∀ m : ℤ, ¬ PP ℓ (Ψ.1 Bs.ω - ((m : ℚ) : B))) :
    (Ideal.span {((ℓ : ℤ) : 𝓞 k)}).IsPrime := by
  have hℓ0 := L6_ne hℓ
  have hℓq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ0
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨e', he⟩ := hu.exists_right_inv
    have hk : (ℓ : k) * (e' : k) = 1 := by
      have := congrArg (fun x : 𝓞 k => (x : k)) he
      simpa using this
    have he'R : (e' : k) ∈ R := mem_of_ell_mul R hc hℓ (RingOfIntegers.isIntegral_coe e')
      (by rw [hk]; exact R.one_mem)
    have hΨ := (optEmb_mem Ψ _).2 he'R
    have : (e' : k) = (((ℓ : ℚ)⁻¹ : ℚ) : k) := by
      rw [eq_inv_of_mul_eq_one_right hk]; push_cast; rfl
    rw [this, emb_ratCast] at hΨ
    obtain ⟨w, hw⟩ := rat_mem_O hΨ
    have h1 : (ℓ : ℚ) * w = 1 := by rw [← hw, mul_inv_cancel₀ hℓq]
    have h2 : ℓ * w = 1 := by exact_mod_cast h1
    have := Int.eq_one_of_mul_eq_one_right (by rcases hℓ with rfl | rfl <;> norm_num) h2
    rcases hℓ with rfl | rfl <;> norm_num at this
  · intro x y hxy
    rw [Ideal.mem_span_singleton] at hxy ⊢
    rw [Ideal.mem_span_singleton]
    obtain ⟨w, hw⟩ := hxy
    have hwk : (x : k) * (y : k) = (ℓ : k) * (w : k) := by
      have := congrArg (fun t : 𝓞 k => (t : k)) hw
      simpa using this
    have hfx := conductor_smul_mem R (RingOfIntegers.isIntegral_coe x)
    have hfy := conductor_smul_mem R (RingOfIntegers.isIntegral_coe y)
    have hfw := conductor_smul_mem R (RingOfIntegers.isIntegral_coe w)
    have hprod : PP ℓ (Ψ.1 ((conductor R : ℤ) • (x : k)) * Ψ.1 ((conductor R : ℤ) • (y : k))) := by
      apply PP_of_LO
      rw [← map_mul, LO_iff_smul ℓ hℓ0]
      refine ⟨Ψ.1 (((conductor R : ℤ) : k) * ((conductor R : ℤ) • (w : k))),
        (optEmb_mem Ψ _).2 (R.mul_mem (_root_.intCast_mem R _) hfw), ?_⟩
      have e : ((conductor R : ℤ) • (x : k)) * ((conductor R : ℤ) • (y : k)) =
          ((ℓ : ℚ) : k) * (((conductor R : ℤ) : k) * ((conductor R : ℤ) • (w : k))) := by
        simp only [zsmul_eq_mul]; push_cast; linear_combination ((conductor R : k)) ^ 2 * hwk
      rw [e, map_mul, emb_ratCast, coe_mul_eq_smul]
    rcases PP_prime (L6_prime hℓ) ((optEmb_mem Ψ _).2 hfx) ((optEmb_mem Ψ _).2 hfy) hprod with h1 | h1
    · left; exact dvd_of_PP Bs hR hc Ψ hℓ h x h1
    · right; exact dvd_of_PP Bs hR hc Ψ hℓ h y h1

theorem PP_sub_coe_star {ℓ : ℤ} {x : B} {m : ℤ} (h : PP ℓ (x - ((m : ℚ) : B))) :
    PP ℓ (star x - ((m : ℚ) : B)) := by
  have := PP_star h; rwa [star_sub, QuaternionAlgebra.star_coe] at this

include Bs in
/-- If `ℓ` is not inert, every optimal embedding has the type of `Ψ₀` at `ℓ`. -/
theorem same_type_of_not_inert (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hc : Nat.Coprime (conductor R) 6) (Ψ0 : OptEmb k R) {ℓ : ℤ} (hℓ : L6 ℓ)
    (hni : ¬ (Ideal.span {((ℓ : ℤ) : 𝓞 k)}).IsPrime) (Φ : OptEmb k R) :
    PP ℓ (Φ.1 Bs.ω - Ψ0.1 Bs.ω) := by
  have hm : ∃ m : ℤ, PP ℓ (Ψ0.1 Bs.ω - ((m : ℚ) : B)) := by
    by_contra hcon; push Not at hcon; exact hni (inert_of_noint Bs hR hc Ψ0 hℓ hcon)
  obtain ⟨m, hm⟩ := hm
  rcases type_dichotomy Bs hℓ Ψ0 Φ with h | h
  · exact h
  · have := PP_sub hℓ (PP_add hℓ h (PP_sub_coe_star hm)) hm
    rwa [show Φ.1 Bs.ω - star (Ψ0.1 Bs.ω) + (star (Ψ0.1 Bs.ω) - ((m : ℚ) : B)) -
      (Ψ0.1 Bs.ω - ((m : ℚ) : B)) = Φ.1 Bs.ω - Ψ0.1 Bs.ω by abel] at this

/-- Two embeddings with the same type relative to `Ψ₀` have the same type. -/
theorem same_of_iff {ℓ : ℤ} (hℓ : L6 ℓ) (Ψ0 Φ Φ' : OptEmb k R)
    (h : PP ℓ (Φ.1 Bs.ω - Ψ0.1 Bs.ω) ↔ PP ℓ (Φ'.1 Bs.ω - Ψ0.1 Bs.ω)) :
    PP ℓ (Φ'.1 Bs.ω - Φ.1 Bs.ω) := by
  by_cases hA : PP ℓ (Φ.1 Bs.ω - Ψ0.1 Bs.ω)
  · have := PP_sub hℓ (h.mp hA) hA
    rwa [show Φ'.1 Bs.ω - Ψ0.1 Bs.ω - (Φ.1 Bs.ω - Ψ0.1 Bs.ω) = Φ'.1 Bs.ω - Φ.1 Bs.ω by abel] at this
  · have hA' : ¬ PP ℓ (Φ'.1 Bs.ω - Ψ0.1 Bs.ω) := fun h' => hA (h.mpr h')
    have h1 := (type_dichotomy Bs hℓ Ψ0 Φ).resolve_left hA
    have h2 := (type_dichotomy Bs hℓ Ψ0 Φ').resolve_left hA'
    have := PP_sub hℓ h2 h1
    rwa [show Φ'.1 Bs.ω - star (Ψ0.1 Bs.ω) - (Φ.1 Bs.ω - star (Ψ0.1 Bs.ω)) = Φ'.1 Bs.ω - Φ.1 Bs.ω by
      abel] at this

/-- A chosen nonzero intertwiner. -/
def cfp (hk : Module.finrank ℚ k = 2) (Ψ Φ : OptEmb k R) : B := (exists_Jo Bs hk Ψ Φ).choose

theorem cfp_spec (hk : Module.finrank ℚ k = 2) (Ψ Φ : OptEmb k R) :
    cfp Bs hk Ψ Φ ∈ Jo Ψ Φ ∧ cfp Bs hk Ψ Φ ≠ 0 := (exists_Jo Bs hk Ψ Φ).choose_spec

open Classical in
/-- The class in `Pic R` of the lattice of the chosen intertwiner. -/
def pcp (hk : Module.finrank ℚ k = 2) (Ψ Φ : OptEmb k R) : CommRing.Pic R :=
  if h : IsUnit (latA Ψ (cfp Bs hk Ψ Φ)) then Submodule.unitsToPic R k h.unit else 1

/-- **Injectivity**: embeddings without bad primes relative to `Ψ` with the same class are conjugate. -/
theorem conj_of_pcp (hk : Module.finrank ℚ k = 2) {Ψ Φ Φ' : OptEmb k R}
    (hNB : ∀ p : ℕ, p.Prime → ¬ Bad Ψ Φ p) (hNB' : ∀ p : ℕ, p.Prime → ¬ Bad Ψ Φ' p)
    (h : pcp Bs hk Ψ Φ = pcp Bs hk Ψ Φ') : ConjRel R Φ Φ' := by
  obtain ⟨hc, hne⟩ := cfp_spec Bs hk Ψ Φ
  obtain ⟨hc', hne'⟩ := cfp_spec Bs hk Ψ Φ'
  have hu := latA_isUnit Bs hk hc hne hNB
  have hu' := latA_isUnit Bs hk hc' hne' hNB'
  unfold pcp at h
  rw [dif_pos hu, dif_pos hu'] at h
  obtain ⟨x, hx⟩ := eq_smul_of_pic h
  simp only [IsUnit.unit_spec] at hx
  refine conj_of_lat Bs hk hc hne hc' hne' (unitCrit_of Bs hk Ψ Φ hNB) (unitCrit_of Bs hk Ψ Φ' hNB')
    (x : k) x.ne_zero (fun a => ?_)
  rw [← mem_latA, ← mem_latA, hx]
  constructor
  · rintro ⟨b, hb, hxb⟩
    have : b = a := mul_left_cancel₀ x.ne_zero hxb
    rwa [← this]
  · intro ha; exact ⟨a, ha, rfl⟩

theorem card_types (k : Type) [Field k] [NumberField k] :
    Nat.card {τ : Bool × Bool // (¬ (Ideal.span {(2 : 𝓞 k)}).IsPrime → τ.1 = true) ∧
      (¬ (Ideal.span {(3 : 𝓞 k)}).IsPrime → τ.2 = true)} = 2 ^ inertCount6 k := by
  classical
  unfold inertCount6
  split_ifs with h2 h3 h3 <;> simp only [h2, h3, not_true_eq_false, not_false_eq_true, false_implies,
    true_implies, true_and, and_true] <;> rw [Nat.card_eq_fintype_card] <;> decide

/-- **The count**: `#(Emb(R, 𝒪)/𝒪^×) ≤ 2^{b(k)} · #Pic(R)` for an order `R` of conductor prime to `6` in a
quadratic field, without Eichler's formula. -/
theorem conjRel_card_le (k : Type) [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2) (R : Subring k)
    (hR : R ≤ (integralClosure ℤ k).toSubring) (hc : Nat.Coprime (conductor R) 6)
    (hh : Nat.card (CommRing.Pic R) ≠ 0) :
    Finite (Quot (ConjRel R)) ∧ Nat.card (Quot (ConjRel R)) ≤ 2 ^ inertCount6 k * Nat.card (CommRing.Pic R) := by
  classical
  obtain ⟨Bs⟩ := exists_qbasis hk hR hc
  haveI : Finite (CommRing.Pic R) := Nat.finite_of_card_ne_zero hh
  by_cases hE : IsEmpty (OptEmb k R)
  · haveI : IsEmpty (Quot (ConjRel R)) := ⟨fun q => Quot.inductionOn q (fun a => hE.false a)⟩
    exact ⟨inferInstance, by rw [Nat.card_of_isEmpty]; exact Nat.zero_le _⟩
  rw [not_isEmpty_iff] at hE
  obtain ⟨Ψ0⟩ := hE
  have hni2 : ¬ (Ideal.span {(2 : 𝓞 k)}).IsPrime → ∀ Φ : OptEmb k R, PP 2 (Φ.1 Bs.ω - Ψ0.1 Bs.ω) :=
    fun h Φ => same_type_of_not_inert Bs hR hc Ψ0 (Or.inl rfl) (by simpa using h) Φ
  have hni3 : ¬ (Ideal.span {(3 : 𝓞 k)}).IsPrime → ∀ Φ : OptEmb k R, PP 3 (Φ.1 Bs.ω - Ψ0.1 Bs.ω) :=
    fun h Φ => same_type_of_not_inert Bs hR hc Ψ0 (Or.inr rfl) (by simpa using h) Φ
  let T := {τ : Bool × Bool // (¬ (Ideal.span {(2 : 𝓞 k)}).IsPrime → τ.1 = true) ∧
      (¬ (Ideal.span {(3 : 𝓞 k)}).IsPrime → τ.2 = true)}
  let τ : OptEmb k R → T := fun Φ =>
    ⟨(decide (PP 2 (Φ.1 Bs.ω - Ψ0.1 Bs.ω)), decide (PP 3 (Φ.1 Bs.ω - Ψ0.1 Bs.ω))),
      fun h => by simpa using hni2 h Φ, fun h => by simpa using hni3 h Φ⟩
  let rep : T → OptEmb k R := fun t => if h : ∃ Φ, τ Φ = t then h.choose else Ψ0
  have hrep : ∀ Φ, τ (rep (τ Φ)) = τ Φ := by
    intro Φ
    have h : ∃ Φ', τ Φ' = τ Φ := ⟨Φ, rfl⟩
    simp only [rep, dif_pos h]; exact h.choose_spec
  have hsame : ∀ Φ, ∀ ℓ : ℤ, L6 ℓ → PP ℓ (Φ.1 Bs.ω - (rep (τ Φ)).1 Bs.ω) := by
    intro Φ ℓ hℓ
    have h := hrep Φ
    rcases hℓ with rfl | rfl
    · apply same_of_iff Bs (Or.inl rfl) Ψ0
      have := congrArg (fun t : T => t.1.1) h
      simpa [τ] using this
    · apply same_of_iff Bs (Or.inr rfl) Ψ0
      have := congrArg (fun t : T => t.1.2) h
      simpa [τ] using this
  have hNB : ∀ Φ, ∀ p : ℕ, p.Prime → ¬ Bad (rep (τ Φ)) Φ p := by
    intro Φ p hp
    by_cases h6 : (p : ℤ) ∣ 6
    · have h6' : p ∣ 6 := by exact_mod_cast h6
      have : p = 2 ∨ p = 3 := by
        have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) h6'
        interval_cases p <;> simp_all <;> norm_num at hp
      rcases this with rfl | rfl
      · exact not_bad6 Bs hk hc (Or.inl rfl) (hsame Φ 2 (Or.inl rfl))
      · exact not_bad6 Bs hk hc (Or.inr rfl) (hsame Φ 3 (Or.inr rfl))
    · exact not_bad_coprime Bs hk _ _ (Nat.prime_iff_prime_int.mp hp) h6
  let G : Quot (ConjRel R) → CommRing.Pic R × T := fun q => (pcp Bs hk (rep (τ q.out)) q.out, τ q.out)
  have hG : Function.Injective G := by
    intro q1 q2 h12
    have hτ : τ q1.out = τ q2.out := congrArg Prod.snd h12
    have hp : pcp Bs hk (rep (τ q1.out)) q1.out = pcp Bs hk (rep (τ q2.out)) q2.out := congrArg Prod.fst h12
    rw [← hτ] at hp
    have hNB2 := hNB q2.out
    rw [← hτ] at hNB2
    have hconj := conj_of_pcp Bs hk (hNB q1.out) hNB2 hp
    rw [← Quot.out_eq q1, ← Quot.out_eq q2]
    exact Quot.sound hconj
  refine ⟨Finite.of_injective G hG, ?_⟩
  have := Nat.card_le_card_of_injective G hG
  rw [Nat.card_prod, card_types k, mul_comm] at this
  exact this

end Emb

end EichlerBound

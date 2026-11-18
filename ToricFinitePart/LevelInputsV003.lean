import ToricFinitePart.TateToricV001

/-!
# Primitive finite-level inputs for the toric annihilator theorem

This file reduces three hypothesis families of `annihilator_finite_le_toric` to more primitive
finite-level statements about actual points.

* `exists_levelwise_lift`: **compatible inverse-limit lifting.** Suppose multiplication by `ℓ`
  maps each level subgroup into the previous one, and every point of a level subgroup is `ℓ` times
  a point of the next (divisibility). Then every point of a level subgroup is a coordinate of a
  compatible Tate vector lying in the levelwise part. This is the inverse-limit passage, built by
  dependent choice from finite-level divisibility alone.
* `card_dvd_pow_factorization_of_injective`: an `ℓᵐ`-torsion group injecting into a fixed finite
  group has order dividing `ℓ^v`, where `v` is the `ℓ`-adic valuation of that group's order (Cauchy
  plus Lagrange). Applied to `ψ`-fixed finite-part points injected into the points of a special
  fibre over a finite field, this gives the uniform fixed-point bound.
* `count_identity_of_ranks`: the order identity `|F⁰ₙ| · |Tₙ| = |A[ℓⁿ]|` from the cardinalities
  `ℓ^{(2a+t)n}`, `ℓ^{tn}`, `ℓ^{2gn}` and `g = a + t`.
* `annihilator_finite_le_toric_of_levels`: the annihilator theorem with these primitive inputs.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ToricFinitePart

open PkgI3

variable {K : Type} [Field K] (ℓ : ℕ) {Ω : Type} [Field Ω] [Algebra K Ω]

/-- A point of `A(Ω)` lies in `A(Ω)[ℓᵏ]` and, as such, in the level subgroup `S k`. -/
def InLevel {A : AbVar K} (S : ∀ n, AddSubgroup (level ℓ A Ω n)) (k : ℕ)
    (z : Additive (A.Pt Ω)) : Prop :=
  ∃ h : z ∈ level ℓ A Ω k, (⟨z, h⟩ : level ℓ A Ω k) ∈ S k

/-- **Compatible lifting from finite-level divisibility.** -/
theorem exists_levelwise_lift [Fact ℓ.Prime] {A : AbVar K} (S : ∀ n, AddSubgroup (level ℓ A Ω n))
    (hdown : ∀ k z, InLevel ℓ S (k + 1) z → InLevel ℓ S k (ℓ • z))
    (hup : ∀ k z, InLevel ℓ S k z → ∃ w, InLevel ℓ S (k + 1) w ∧ ℓ • w = z)
    (n : ℕ) (x : level ℓ A Ω n) (hx : x ∈ S n) :
    ∃ t ∈ levelwise ℓ S, comp ℓ t n = x := by
  classical
  have hx0 : InLevel ℓ S n x.1 := ⟨x.2, hx⟩
  have hdn : ∀ j, j ≤ n → InLevel ℓ S (n - j) ((ℓ ^ j) • x.1) := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa using hx0
    | succ j ih =>
      intro hj
      have h1 := ih (Nat.le_of_succ_le hj)
      have heq : n - j = (n - (j + 1)) + 1 := by omega
      rw [heq] at h1
      have h2 := hdown _ _ h1
      rwa [← mul_smul, ← pow_succ'] at h2
  have step : ∀ j (z : {z // InLevel ℓ S (n + j) z}),
      ∃ w : {w // InLevel ℓ S (n + (j + 1)) w}, ℓ • w.1 = z.1 := by
    intro j z
    obtain ⟨w, hw, hwz⟩ := hup (n + j) z.1 z.2
    exact ⟨⟨w, by rw [← add_assoc]; exact hw⟩, hwz⟩
  let s : (j : ℕ) → {z // InLevel ℓ S (n + j) z} :=
    fun j => Nat.rec ⟨x.1, by simpa using hx0⟩ (fun j y => (step j y).choose) j
  have hs : ∀ j, ℓ • (s (j + 1)).1 = (s j).1 := fun j => (step j (s j)).choose_spec
  let u : ℕ → Additive (A.Pt Ω) :=
    fun k => if k ≤ n then (ℓ ^ (n - k)) • x.1 else (s (k - n)).1
  have hu_mem : ∀ k, InLevel ℓ S k (u k) := by
    intro k
    by_cases hk : k ≤ n
    · simp only [u, hk, ite_true]
      have h := hdn (n - k) (Nat.sub_le n k)
      rwa [Nat.sub_sub_self hk] at h
    · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
      simp only [u, hk, ite_false]
      rw [Nat.add_sub_cancel_left]
      exact (s j).2
  have hu0 : u 0 = 0 := by
    simp only [u, Nat.zero_le, ite_true, Nat.sub_zero]
    exact x.2
  have hstep : ∀ k, ℓ • u (k + 1) = u k := by
    intro k
    by_cases h : k + 1 ≤ n
    · simp only [u, h, ite_true, show k ≤ n by omega]
      rw [← mul_smul, ← pow_succ', show n - (k + 1) + 1 = n - k by omega]
    · by_cases h' : k = n
      · subst h'
        simp only [u, h, ite_false, le_refl, ite_true, Nat.sub_self, pow_zero, one_smul]
        rw [show k + 1 - k = 0 + 1 by omega]
        exact hs 0
      · simp only [u, h, ite_false, show ¬ k ≤ n by omega]
        rw [show k + 1 - n = (k - n) + 1 by omega, hs]
  let t : Tate.T ℓ (Additive (A.Pt Ω)) := ⟨u, hu0, hstep⟩
  refine ⟨t, ?_, ?_⟩
  · intro k
    obtain ⟨h, hmem⟩ := hu_mem k
    exact hmem
  · apply Subtype.ext
    show u n = x.1
    simp [u]

/-- An `ℓᵐ`-torsion group injecting into a finite group has order dividing the `ℓ`-part of that
group's order. -/
theorem card_dvd_pow_factorization_of_injective [hℓ : Fact ℓ.Prime] {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Finite H] (m : ℕ) (hG : ∀ x : G, (ℓ ^ m) • x = 0)
    (inj : G →+ H) (hinj : Function.Injective inj) :
    Nat.card G ∣ ℓ ^ (Nat.card H).factorization ℓ := by
  haveI : Finite G := Finite.of_injective inj hinj
  have hp : IsPGroup ℓ (Multiplicative G) := fun g => ⟨m, by
    apply Multiplicative.toAdd.injective
    simpa using hG (Multiplicative.toAdd g)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hk' : Nat.card G = ℓ ^ k := hk
  have hdvd : Nat.card G ∣ Nat.card H := AddSubgroup.card_dvd_of_injective inj hinj
  have hH : Nat.card H ≠ 0 := Nat.card_pos.ne'
  rw [hk'] at hdvd ⊢
  exact pow_dvd_pow ℓ ((hℓ.out.pow_dvd_iff_le_factorization hH).mp hdvd)

/-- The uniform fixed-point bound from injections of the `σ`-fixed level points into one finite
group. -/
theorem fixed_card_dvd_of_injective [Fact ℓ.Prime] {A : AbVar K} (σ : Ω ≃ₐ[K] Ω)
    (F : ∀ n, AddSubgroup (level ℓ A Ω n)) {H : Type*} [AddCommGroup H] [Finite H]
    (inj : ∀ n, fixedIn ℓ σ (F n) →+ H) (hinj : ∀ n, Function.Injective (inj n)) (n : ℕ) :
    Nat.card (fixedIn ℓ σ (F n)) ∣ ℓ ^ (Nat.card H).factorization ℓ :=
  card_dvd_pow_factorization_of_injective ℓ n (fun y => Subtype.ext (Subtype.ext y.1.2))
    (inj n) (hinj n)

/-- The order identity from the cardinalities of the identity-component and toric levels. -/
theorem count_identity_of_ranks {F T G : ℕ} (a t g n : ℕ)
    (hF : F = ℓ ^ ((2 * a + t) * n)) (hT : T = ℓ ^ (t * n)) (hG : G = ℓ ^ (2 * g * n))
    (hg : g = a + t) : F * T = G := by
  subst hF hT hG hg
  rw [← pow_add]
  congr 1
  ring

/-- **The annihilator theorem with primitive finite-level inputs.** -/
theorem annihilator_finite_le_toric_of_levels [Fact ℓ.Prime] {A A' : AbVar K}
    {P : Type} [AddCommGroup P] [Module ℤ_[ℓ] P]
    (B : Tate.T ℓ (Additive (A.Pt Ω)) →ₗ[ℤ_[ℓ]] Tate.T ℓ (Additive (A'.Pt Ω)) →ₗ[ℤ_[ℓ]] P)
    (e : ∀ n, level ℓ A Ω n →+ level ℓ A' Ω n →+ ZMod (ℓ ^ n))
    (r : ∀ n, P →+ ZMod (ℓ ^ n))
    (hB : ∀ t s n, r n (B t s) = e n (comp ℓ t n) (comp ℓ s n))
    (heL : ∀ n x, (∀ y, e n x y = 0) → x = 0) (heR : ∀ n y, (∀ x, e n x y = 0) → y = 0)
    (hcompat : ∀ (t : Tate.T ℓ (Additive (A.Pt Ω))) (s : Tate.T ℓ (Additive (A'.Pt Ω)))
      (n k : ℕ), e n (comp ℓ t n) (comp ℓ s n) =
        ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n k)) (ZMod (ℓ ^ n))
          (e (n + k) (comp ℓ t (n + k)) (comp ℓ s (n + k))))
    (ψ : Ω ≃ₐ[K] Ω) (Q : ℕ) (hQ : Nat.Coprime Q ℓ)
    (hequiv : ∀ n a b, e n (galLevel ℓ A ψ n a) (galLevel ℓ A' ψ n b) = Q • e n a b)
    (Tor : ∀ n, AddSubgroup (level ℓ A Ω n)) (Tor' : ∀ n, AddSubgroup (level ℓ A' Ω n))
    (hTor : ∀ n x, x ∈ Tor n → galLevel ℓ A ψ n x = Q • x)
    (hTor' : ∀ n x, x ∈ Tor' n → galLevel ℓ A' ψ n x = Q • x)
    (hdown : ∀ k z, InLevel ℓ Tor (k + 1) z → InLevel ℓ Tor k (ℓ • z))
    (hup : ∀ k z, InLevel ℓ Tor k z → ∃ w, InLevel ℓ Tor (k + 1) w ∧ ℓ • w = z)
    (hdown' : ∀ k z, InLevel ℓ Tor' (k + 1) z → InLevel ℓ Tor' k (ℓ • z))
    (hup' : ∀ k z, InLevel ℓ Tor' k z → ∃ w, InLevel ℓ Tor' (k + 1) w ∧ ℓ • w = z)
    (Fin : ∀ n, AddSubgroup (level ℓ A Ω n)) (Fin' : ∀ n, AddSubgroup (level ℓ A' Ω n))
    (hFinSt : ∀ n y, y ∈ Fin n → galLevel ℓ A ψ n y ∈ Fin n)
    (hFinSt' : ∀ n y, y ∈ Fin' n → galLevel ℓ A' ψ n y ∈ Fin' n)
    {H H' : Type} [AddCommGroup H] [Finite H] [AddCommGroup H'] [Finite H']
    (inj : ∀ n, fixedIn ℓ ψ (Fin n) →+ H) (hinj : ∀ n, Function.Injective (inj n))
    (inj' : ∀ n, fixedIn ℓ ψ (Fin' n) →+ H') (hinj' : ∀ n, Function.Injective (inj' n))
    (hfinA : ∀ n, Finite (level ℓ A Ω n)) (hfinA' : ∀ n, Finite (level ℓ A' Ω n))
    (hcount : ∀ n, Nat.card (coordImage ℓ (levelwise ℓ Fin) n) * Nat.card (Tor n) =
      Nat.card (level ℓ A Ω n))
    (hcount' : ∀ n, Nat.card (coordImage ℓ (levelwise ℓ Fin') n) * Nat.card (Tor' n) =
      Nat.card (level ℓ A' Ω n)) :
    annihilator B (levelwise ℓ Fin') ≤ levelwise ℓ Tor :=
  annihilator_finite_le_toric ℓ B e r hB heL heR hcompat ψ Q hQ hequiv Tor Tor' hTor hTor'
    (fun n x hx => exists_levelwise_lift ℓ Tor hdown hup n x hx)
    (fun n x hx => exists_levelwise_lift ℓ Tor' hdown' hup' n x hx)
    Fin Fin' hFinSt hFinSt' _ _ (fixed_card_dvd_of_injective ℓ ψ Fin inj hinj)
    (fixed_card_dvd_of_injective ℓ ψ Fin' inj' hinj') hfinA hfinA' hcount hcount'

end ToricFinitePart

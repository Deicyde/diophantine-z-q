import ToricFinitePart.LevelInputsV003

/-!
# Inertia-fixed finite parts and square-zero inertia defects

The finite level subgroups are now the actual inertia-fixed points
`{x ∈ A(Ω)[ℓⁿ] | σ x = x for every σ in the inertia group of w}` (`PkgI2.IsInertia`, Mathlib's
decomposition and inertia subgroups). Then:

* `mem_levelwise_inertiaFixed_iff`: the levelwise inertia-fixed part of the Tate module is exactly
  the submodule of Tate vectors fixed by every inertia element under the original Tate action;
* `inertiaFixed_stable`: an element of the decomposition group preserves the inertia-fixed levels
  (inertia is normal in the decomposition group);
* `inertia_fixed_of_annihilator`: under the primitive level inputs, every Tate vector in the
  annihilator of the dual inertia-fixed Tate part is fixed by inertia;
* `inertia_defect_sq_zero`: if moreover the Tate-level pairing is inertia-invariant, every product
  of two inertia defects vanishes: `(σ - 1)((τ - 1) x) = 0` on the original Tate module.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ToricFinitePart

open PkgI3

variable {K : Type} [Field K] (ℓ : ℕ) {Ω : Type} [Field Ω] [Algebra K Ω]

/-- The original Galois action composes as the group law. -/
theorem galAct_galAct (A : AbVar K) (σ τ : Ω ≃ₐ[K] Ω) (P : A.Pt Ω) :
    A.galAct σ (A.galAct τ P) = A.galAct (σ * τ) P := by
  show AbVar.galHom σ ≫ (AbVar.galHom τ ≫ P) = AbVar.galHom (σ * τ) ≫ P
  rw [AbVar.galHom_mul, Category.assoc]

/-- The inertia-fixed points of `A(Ω)[ℓⁿ]`. -/
def inertiaFixed (A : AbVar K) (w : ValuationSubring Ω) (n : ℕ) :
    AddSubgroup (level ℓ A Ω n) where
  carrier := {x | ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → galLevel ℓ A σ n x = x}
  zero_mem' := fun _ _ => map_zero _
  add_mem' := by
    intro a b ha hb σ hσ
    rw [map_add, ha σ hσ, hb σ hσ]
  neg_mem' := by
    intro a ha σ hσ
    rw [map_neg, ha σ hσ]

/-- The levelwise inertia-fixed part is the submodule of inertia-fixed Tate vectors. -/
theorem mem_levelwise_inertiaFixed_iff [Fact ℓ.Prime] (A : AbVar K) (w : ValuationSubring Ω)
    (t : Tate.T ℓ (Additive (A.Pt Ω))) :
    t ∈ levelwise ℓ (inertiaFixed ℓ A w) ↔
      ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ →
        Tate.map (MonoidHom.toAdditive (A.galAct σ)) t = t := by
  constructor
  · intro ht σ hσ
    exact tate_fixed_of_levelwise ℓ σ (inertiaFixed ℓ A w) (fun n x hx => hx σ hσ) ht
  · intro h n σ hσ
    apply Subtype.ext
    exact congrArg (fun s : Tate.T ℓ (Additive (A.Pt Ω)) => s.1 n) (h σ hσ)

/-- Conjugating an inertia element by an element of the decomposition group stays in inertia. -/
theorem isInertia_conj (w : ValuationSubring Ω) {ψ σ : Ω ≃ₐ[K] Ω}
    (hψ : ψ ∈ w.decompositionSubgroup K) (hσ : PkgI2.IsInertia w σ) :
    PkgI2.IsInertia w (ψ⁻¹ * σ * ψ) := by
  obtain ⟨hσD, hσI⟩ := hσ
  have hD : ψ⁻¹ * σ * ψ ∈ w.decompositionSubgroup K :=
    (w.decompositionSubgroup K).mul_mem
      ((w.decompositionSubgroup K).mul_mem ((w.decompositionSubgroup K).inv_mem hψ) hσD) hψ
  refine ⟨hD, ?_⟩
  have hconj := (MonoidHom.normal_ker (MulSemiringAction.toRingAut (w.decompositionSubgroup K)
    (IsLocalRing.ResidueField w))).conj_mem ⟨σ, hσD⟩ hσI (⟨ψ, hψ⟩⁻¹)
  have heq : (⟨ψ⁻¹ * σ * ψ, hD⟩ : w.decompositionSubgroup K) =
      (⟨ψ, hψ⟩ : w.decompositionSubgroup K)⁻¹ * ⟨σ, hσD⟩ *
        ((⟨ψ, hψ⟩ : w.decompositionSubgroup K)⁻¹)⁻¹ := by
    apply Subtype.ext
    simp
  rw [heq]
  exact hconj

/-- Decomposition-group elements preserve the inertia-fixed levels. -/
theorem inertiaFixed_stable (A : AbVar K) (w : ValuationSubring Ω) {ψ : Ω ≃ₐ[K] Ω}
    (hψ : ψ ∈ w.decompositionSubgroup K) (n : ℕ) (y : level ℓ A Ω n)
    (hy : y ∈ inertiaFixed ℓ A w n) : galLevel ℓ A ψ n y ∈ inertiaFixed ℓ A w n := by
  intro σ hσ
  have hy' := congrArg Subtype.val (hy _ (isInertia_conj w hψ hσ))
  apply Subtype.ext
  show Additive.ofMul (A.galAct σ (A.galAct ψ (Additive.toMul y.1))) =
    Additive.ofMul (A.galAct ψ (Additive.toMul y.1))
  have hσψ : σ * ψ = ψ * (ψ⁻¹ * σ * ψ) := by
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]
  rw [galAct_galAct, hσψ, ← galAct_galAct]
  exact congrArg (fun z => Additive.ofMul (A.galAct ψ (Additive.toMul z))) hy'

/-- **Inertia fixes the annihilator of the dual inertia-fixed Tate part**, from the primitive
level inputs (Frobenius orthogonality inputs, divisibility, fixed-point injections, counts). -/
theorem inertia_fixed_of_annihilator [Fact ℓ.Prime] {A A' : AbVar K} (w : ValuationSubring Ω)
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
    (ψ : Ω ≃ₐ[K] Ω) (hψ : ψ ∈ w.decompositionSubgroup K) (Q : ℕ) (hQ : Nat.Coprime Q ℓ)
    (hequiv : ∀ n a b, e n (galLevel ℓ A ψ n a) (galLevel ℓ A' ψ n b) = Q • e n a b)
    (Tor : ∀ n, AddSubgroup (level ℓ A Ω n)) (Tor' : ∀ n, AddSubgroup (level ℓ A' Ω n))
    (hTorFix : ∀ n, Tor n ≤ inertiaFixed ℓ A w n)
    (hTor : ∀ n x, x ∈ Tor n → galLevel ℓ A ψ n x = Q • x)
    (hTor' : ∀ n x, x ∈ Tor' n → galLevel ℓ A' ψ n x = Q • x)
    (hdown : ∀ k z, InLevel ℓ Tor (k + 1) z → InLevel ℓ Tor k (ℓ • z))
    (hup : ∀ k z, InLevel ℓ Tor k z → ∃ w, InLevel ℓ Tor (k + 1) w ∧ ℓ • w = z)
    (hdown' : ∀ k z, InLevel ℓ Tor' (k + 1) z → InLevel ℓ Tor' k (ℓ • z))
    (hup' : ∀ k z, InLevel ℓ Tor' k z → ∃ w, InLevel ℓ Tor' (k + 1) w ∧ ℓ • w = z)
    {H H' : Type} [AddCommGroup H] [Finite H] [AddCommGroup H'] [Finite H']
    (inj : ∀ n, fixedIn ℓ ψ (inertiaFixed ℓ A w n) →+ H)
    (hinj : ∀ n, Function.Injective (inj n))
    (inj' : ∀ n, fixedIn ℓ ψ (inertiaFixed ℓ A' w n) →+ H')
    (hinj' : ∀ n, Function.Injective (inj' n))
    (hfinA : ∀ n, Finite (level ℓ A Ω n)) (hfinA' : ∀ n, Finite (level ℓ A' Ω n))
    (hcount : ∀ n, Nat.card (coordImage ℓ (levelwise ℓ (inertiaFixed ℓ A w)) n) *
      Nat.card (Tor n) = Nat.card (level ℓ A Ω n))
    (hcount' : ∀ n, Nat.card (coordImage ℓ (levelwise ℓ (inertiaFixed ℓ A' w)) n) *
      Nat.card (Tor' n) = Nat.card (level ℓ A' Ω n))
    {t : Tate.T ℓ (Additive (A.Pt Ω))}
    (ht : t ∈ annihilator B (levelwise ℓ (inertiaFixed ℓ A' w)))
    (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) :
    Tate.map (MonoidHom.toAdditive (A.galAct σ)) t = t := by
  have hle := annihilator_finite_le_toric_of_levels ℓ B e r hB heL heR hcompat ψ Q hQ hequiv
    Tor Tor' hTor hTor' hdown hup hdown' hup' (inertiaFixed ℓ A w) (inertiaFixed ℓ A' w)
    (inertiaFixed_stable ℓ A w hψ) (inertiaFixed_stable ℓ A' w hψ) inj hinj inj' hinj'
    hfinA hfinA' hcount hcount'
  have htor := hle ht
  have hfix := levelwise_mono ℓ hTorFix htor
  exact (mem_levelwise_inertiaFixed_iff ℓ A w t).mp hfix σ hσ

/-- **Square-zero inertia defects** on the original Tate module, from the primitive level inputs
and inertia-invariance of the Tate-level pairing. -/
theorem inertia_defect_sq_zero [Fact ℓ.Prime] {A A' : AbVar K} (w : ValuationSubring Ω)
    {P : Type} [AddCommGroup P] [Module ℤ_[ℓ] P]
    (B : Tate.T ℓ (Additive (A.Pt Ω)) →ₗ[ℤ_[ℓ]] Tate.T ℓ (Additive (A'.Pt Ω)) →ₗ[ℤ_[ℓ]] P)
    (e : ∀ n, level ℓ A Ω n →+ level ℓ A' Ω n →+ ZMod (ℓ ^ n))
    (r : ∀ n, P →+ ZMod (ℓ ^ n))
    (hB : ∀ t s n, r n (B t s) = e n (comp ℓ t n) (comp ℓ s n))
    (hBinv : ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ → ∀ x y,
      B (Tate.map (MonoidHom.toAdditive (A.galAct τ)) x)
        (Tate.map (MonoidHom.toAdditive (A'.galAct τ)) y) = B x y)
    (heL : ∀ n x, (∀ y, e n x y = 0) → x = 0) (heR : ∀ n y, (∀ x, e n x y = 0) → y = 0)
    (hcompat : ∀ (t : Tate.T ℓ (Additive (A.Pt Ω))) (s : Tate.T ℓ (Additive (A'.Pt Ω)))
      (n k : ℕ), e n (comp ℓ t n) (comp ℓ s n) =
        ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right n k)) (ZMod (ℓ ^ n))
          (e (n + k) (comp ℓ t (n + k)) (comp ℓ s (n + k))))
    (ψ : Ω ≃ₐ[K] Ω) (hψ : ψ ∈ w.decompositionSubgroup K) (Q : ℕ) (hQ : Nat.Coprime Q ℓ)
    (hequiv : ∀ n a b, e n (galLevel ℓ A ψ n a) (galLevel ℓ A' ψ n b) = Q • e n a b)
    (Tor : ∀ n, AddSubgroup (level ℓ A Ω n)) (Tor' : ∀ n, AddSubgroup (level ℓ A' Ω n))
    (hTorFix : ∀ n, Tor n ≤ inertiaFixed ℓ A w n)
    (hTor : ∀ n x, x ∈ Tor n → galLevel ℓ A ψ n x = Q • x)
    (hTor' : ∀ n x, x ∈ Tor' n → galLevel ℓ A' ψ n x = Q • x)
    (hdown : ∀ k z, InLevel ℓ Tor (k + 1) z → InLevel ℓ Tor k (ℓ • z))
    (hup : ∀ k z, InLevel ℓ Tor k z → ∃ w, InLevel ℓ Tor (k + 1) w ∧ ℓ • w = z)
    (hdown' : ∀ k z, InLevel ℓ Tor' (k + 1) z → InLevel ℓ Tor' k (ℓ • z))
    (hup' : ∀ k z, InLevel ℓ Tor' k z → ∃ w, InLevel ℓ Tor' (k + 1) w ∧ ℓ • w = z)
    {H H' : Type} [AddCommGroup H] [Finite H] [AddCommGroup H'] [Finite H']
    (inj : ∀ n, fixedIn ℓ ψ (inertiaFixed ℓ A w n) →+ H)
    (hinj : ∀ n, Function.Injective (inj n))
    (inj' : ∀ n, fixedIn ℓ ψ (inertiaFixed ℓ A' w n) →+ H')
    (hinj' : ∀ n, Function.Injective (inj' n))
    (hfinA : ∀ n, Finite (level ℓ A Ω n)) (hfinA' : ∀ n, Finite (level ℓ A' Ω n))
    (hcount : ∀ n, Nat.card (coordImage ℓ (levelwise ℓ (inertiaFixed ℓ A w)) n) *
      Nat.card (Tor n) = Nat.card (level ℓ A Ω n))
    (hcount' : ∀ n, Nat.card (coordImage ℓ (levelwise ℓ (inertiaFixed ℓ A' w)) n) *
      Nat.card (Tor' n) = Nat.card (level ℓ A' Ω n))
    (σ τ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) (hτ : PkgI2.IsInertia w τ)
    (x : Tate.T ℓ (Additive (A.Pt Ω))) :
    Tate.map (MonoidHom.toAdditive (A.galAct σ))
        (Tate.map (MonoidHom.toAdditive (A.galAct τ)) x - x) -
      (Tate.map (MonoidHom.toAdditive (A.galAct τ)) x - x) = 0 := by
  have hdef : Tate.map (MonoidHom.toAdditive (A.galAct τ)) x - x ∈
      annihilator B (levelwise ℓ (inertiaFixed ℓ A' w)) := by
    intro y hy
    have hyfix := (mem_levelwise_inertiaFixed_iff ℓ A' w y).mp hy τ hτ
    have h1 := hBinv τ hτ x y
    rw [hyfix] at h1
    rw [map_sub, LinearMap.sub_apply, h1, sub_self]
  exact sub_eq_zero.mpr (inertia_fixed_of_annihilator ℓ w B e r hB heL heR hcompat ψ hψ Q hQ
    hequiv Tor Tor' hTorFix hTor hTor' hdown hup hdown' hup' inj hinj inj' hinj' hfinA hfinA'
    hcount hcount' hdef σ hσ)

end ToricFinitePart

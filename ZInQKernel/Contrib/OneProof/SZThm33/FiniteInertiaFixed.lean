import ZInQKernel.Contrib.OneProof.SZThm33.IntermediateTate
import ZInQKernel.Contrib.OneProof.DirectWeil.InertiaCoisotropy

/-!
# Fixed vectors before and after finite extension
-/

noncomputable section

open ReductSplit

namespace SZRaynaud

section Period

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem eq_of_periodic_of_sub_apply_sub_apply_eq_zero [CharZero k]
    (g : V →ₗ[k] V) (x : V) (hunip : g (g x - x) - (g x - x) = 0)
    (n : ℕ) (hn : 0 < n) (hperiod : (g : V → V)^[n] x = x) : g x = x := by
  let d := g x - x
  have hd : g d = d := sub_eq_zero.mp hunip
  have hgx : g x = x + d := by rw [← sub_add_cancel (g x) x, add_comm]
  have hit : ∀ j : ℕ, (g : V → V)^[j] x = x + j • d := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, map_add, map_nsmul, hd, hgx,
        add_nsmul, one_nsmul, add_assoc, add_comm d]
  have hn0 : n • d = 0 := by
    apply add_left_cancel (a := x)
    rw [add_zero, ← hit, hperiod]
  have hn0' : (n : k) • d = 0 := by simpa only [Nat.cast_smul_eq_nsmul] using hn0
  exact sub_eq_zero.mp ((smul_eq_zero.mp hn0').resolve_left (Nat.cast_ne_zero.mpr hn.ne'))

end Period

/-- An automorphism has a positive power fixing any finite
intermediate field pointwise. -/
theorem exists_pos_pow_fix_intermediateField
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    (σ : Ω ≃ₐ[K] Ω) :
    ∃ n : ℕ, 0 < n ∧ ∀ e : E, (σ ^ n) e = e := by
  let f (n : ℕ) : E →ₐ[K] Ω := (σ ^ n).toAlgHom.comp E.val
  have hfin : (Set.univ : Set (E →ₐ[K] Ω)).Finite := Set.toFinite _
  obtain ⟨a, b, hab, hab'⟩ := hfin.exists_lt_map_eq_of_forall_mem (f := f) fun _ => Set.mem_univ _
  refine ⟨b - a, Nat.sub_pos_of_lt hab, fun e => (σ ^ a).injective ?_⟩
  have h := congrArg (fun f : E →ₐ[K] Ω => f e) hab'
  change (σ ^ a) (e : Ω) = (σ ^ b) (e : Ω) at h
  rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_of_le hab.le]
  exact h.symm

/-- The finite-index inertia subgroup for an intermediate field contains
a positive power of every inertia element at the base. -/
theorem exists_pos_pow_inertia_over_intermediateField
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) :
    ∃ (n : ℕ) (_ : 0 < n) (τ : Ω ≃ₐ[E] Ω), PkgI2.IsInertia w τ ∧
      ∀ x, τ x = (σ ^ n) x := by
  obtain ⟨n, hn, h⟩ := exists_pos_pow_fix_intermediateField E σ
  let τ : Ω ≃ₐ[E] Ω :=
    { (σ ^ n).toRingEquiv with commutes' := h }
  obtain ⟨hD, hI⟩ := hσ
  let d : w.decompositionSubgroup K := ⟨σ, hD⟩
  have hd : d ∈ w.inertiaSubgroup K := hI
  have hp : PkgI2.IsInertia w (σ ^ n) := by
    refine ⟨(d ^ n).2, ?_⟩
    exact (w.inertiaSubgroup K).pow_mem hd n
  exact ⟨n, hn, τ, ReductSplit.isInertia_restrict E w (σ ^ n) τ (fun _ => rfl) hp, fun _ => rfl⟩

/-- Level-two unipotence makes no new inertia-fixed vectors after any
finite extension in the common algebraic closure. -/
theorem fixed_of_intermediateFixed_of_levelTwo
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (A : PkgI3.AbVar K) (E : IntermediateField K Ω) [FiniteDimensional K E]
    (w : ValuationSubring Ω) (ℓ : ℕ) [Fact ℓ.Prime]
    (hTwo : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ x : VΩ A Ω ℓ,
      galVΩ A ℓ σ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x)
    (y : VΩ (A.baseChange E) Ω ℓ)
    (hy : ∀ τ : Ω ≃ₐ[E] Ω, PkgI2.IsInertia w τ → galVΩ (A.baseChange E) ℓ τ y = y)
    (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) :
    galVΩ A ℓ σ (intermediateRationalTateEquiv A E ℓ y) =
      intermediateRationalTateEquiv A E ℓ y := by
  let x := intermediateRationalTateEquiv A E ℓ y
  obtain ⟨n, hn, τ, hτ, he⟩ := exists_pos_pow_inertia_over_intermediateField E w σ hσ
  let d : w.inertiaSubgroup K := ⟨⟨σ, hσ.1⟩, hσ.2⟩
  have hτ' : τ.restrictScalars K = (d ^ n).1.1 := AlgEquiv.ext he
  have hτx := intermediateRationalTateEquiv_action A E ℓ τ y
  rw [hy τ hτ, hτ'] at hτx
  have hpow : inertiaTateRep A w ℓ (d ^ n) x = x := hτx.symm
  have hp : (galVΩ A ℓ σ : VΩ A Ω ℓ → VΩ A Ω ℓ)^[n] x = x := by
    simpa only [map_pow, Module.End.pow_apply, inertiaTateRep_apply] using hpow
  exact eq_of_periodic_of_sub_apply_sub_apply_eq_zero (galVΩ A ℓ σ) x
    (sub_eq_zero.mpr (hTwo σ hσ x)) n hn hp

#print axioms fixed_of_intermediateFixed_of_levelTwo

end SZRaynaud

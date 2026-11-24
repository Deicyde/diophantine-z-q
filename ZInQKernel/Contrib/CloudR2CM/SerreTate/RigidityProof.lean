import ZInQKernel.Contrib.CloudR2CM.SerreTate.SerreRigidity
import ZInQKernel.Contrib.HDecomp.I3Linalg.RhoCont

/-!
# P2, rigidity at one place: `P2InertiaRigidity` from Serre's lemma

`p2InertiaRigidity_of_serre` proves `P2InertiaRigidity` from `SerreLemmaTate`, which is its
explicit premise here. For an inertia element `σ` the endomorphism `g = galTΩ σ` of `T_ℓ(A)`:

* has finite order: `σ ↦ galTΩ σ` is multiplicative, the powers of `σ` are inertia elements, so
  the powers of `g` lie in the finite inertia image; `g` is invertible (`galTΩ σ⁻¹`), so two equal
  powers give `g ^ n = 1` with `n > 0`;
* is congruent to `1` modulo `ℓ^k`: the `k`-th coordinate of `g x - x` is `σ • x_k - x_k = 0`
  because inertia fixes `A(Ω)[ℓ^k]`, and the kernel of the `k`-th coordinate is `ℓ^k T_ℓ(A)`
  (`PkgI3.Tate.coord_eq_zero_iff`).

Serre's lemma then gives `g = 1`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace HDec.CMSerreTate

section Rigidity

variable {K : Type} [Field K] (A : _root_.PkgI3.AbVar K) {Ω : Type} [Field Ω] [Algebra K Ω]

/-- The Galois action on points is multiplicative. -/
theorem galAct_mul_apply (σ τ : Ω ≃ₐ[K] Ω) (P : A.Pt Ω) :
    A.galAct (σ * τ) P = A.galAct σ (A.galAct τ P) := by
  show _root_.PkgI3.AbVar.galHom (σ * τ) ≫ P =
    _root_.PkgI3.AbVar.galHom σ ≫ (_root_.PkgI3.AbVar.galHom τ ≫ P)
  rw [_root_.PkgI3.AbVar.galHom_mul, CategoryTheory.Category.assoc]

/-- The identity acts trivially on points. -/
theorem galAct_one_apply (P : A.Pt Ω) : A.galAct (1 : Ω ≃ₐ[K] Ω) P = P := by
  show _root_.PkgI3.AbVar.galHom (1 : Ω ≃ₐ[K] Ω) ≫ P = P
  rw [_root_.PkgI3.AbVar.galHom_one, CategoryTheory.Category.id_comp]

/-- Inertia elements are closed under powers. -/
theorem isInertia_pow {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω}
    (h : _root_.PkgI2.IsInertia w σ) (n : ℕ) : _root_.PkgI2.IsInertia w (σ ^ n) := by
  obtain ⟨hd, hi⟩ := h
  refine ⟨pow_mem hd n, ?_⟩
  have e : (⟨σ ^ n, pow_mem hd n⟩ : w.decompositionSubgroup K) =
      (⟨σ, hd⟩ : w.decompositionSubgroup K) ^ n := Subtype.ext (by simp)
  rw [e]
  exact pow_mem hi n

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The coordinates of `galTΩ σ x`. -/
theorem galTΩ_apply_coord (σ : Ω ≃ₐ[K] Ω) (x : _root_.ReductSplit.TΩ A Ω ℓ) (n : ℕ) :
    (_root_.ReductSplit.galTΩ A ℓ σ x).1 n =
      Additive.ofMul (A.galAct σ (Additive.toMul (x.1 n))) := rfl

/-- `σ ↦ galTΩ σ` is multiplicative. -/
theorem galTΩ_mul (σ τ : Ω ≃ₐ[K] Ω) :
    _root_.ReductSplit.galTΩ A ℓ (σ * τ) =
      _root_.ReductSplit.galTΩ A ℓ σ * _root_.ReductSplit.galTΩ A ℓ τ := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  rw [Module.End.mul_apply, galTΩ_apply_coord, galTΩ_apply_coord, galTΩ_apply_coord,
    galAct_mul_apply, toMul_ofMul]

/-- `galTΩ 1 = 1`. -/
theorem galTΩ_one : _root_.ReductSplit.galTΩ A ℓ (1 : Ω ≃ₐ[K] Ω) = 1 := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  rw [galTΩ_apply_coord, galAct_one_apply, ofMul_toMul, Module.End.one_apply]

/-- `galTΩ (σ ^ n) = (galTΩ σ) ^ n`. -/
theorem galTΩ_pow (σ : Ω ≃ₐ[K] Ω) (n : ℕ) :
    _root_.ReductSplit.galTΩ A ℓ (σ ^ n) = _root_.ReductSplit.galTΩ A ℓ σ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, galTΩ_one]
  | succ n ih => rw [pow_succ, pow_succ, galTΩ_mul, ih]

/-- An inertia element acts on `T_ℓ(A)` with finite order when the inertia image is finite. -/
theorem exists_pow_galTΩ_eq_one {w : ValuationSubring Ω} (hfin : FiniteInertiaImage A w ℓ)
    {σ : Ω ≃ₐ[K] Ω} (hσ : _root_.PkgI2.IsInertia w σ) :
    ∃ n : ℕ, 0 < n ∧ _root_.ReductSplit.galTΩ A ℓ σ ^ n = 1 := by
  have hmem : ∀ n : ℕ, _root_.ReductSplit.galTΩ A ℓ σ ^ n ∈
      Set.range (fun σ' : {σ' : Ω ≃ₐ[K] Ω // _root_.PkgI2.IsInertia w σ'} =>
        _root_.ReductSplit.galTΩ A ℓ σ'.1) :=
    fun n => ⟨⟨σ ^ n, isInertia_pow hσ n⟩, galTΩ_pow A ℓ σ n⟩
  obtain ⟨a, b, hab, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun n : ℕ => _root_.ReductSplit.galTΩ A ℓ σ ^ n) hmem hfin
  have he' : _root_.ReductSplit.galTΩ A ℓ σ ^ a = _root_.ReductSplit.galTΩ A ℓ σ ^ b := he
  have hu : IsUnit (_root_.ReductSplit.galTΩ A ℓ σ) := by
    refine ⟨⟨_root_.ReductSplit.galTΩ A ℓ σ, _root_.ReductSplit.galTΩ A ℓ σ⁻¹, ?_, ?_⟩, rfl⟩
    · rw [← galTΩ_mul, mul_inv_cancel, galTΩ_one]
    · rw [← galTΩ_mul, inv_mul_cancel, galTΩ_one]
  refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
  have h2 : _root_.ReductSplit.galTΩ A ℓ σ ^ a * _root_.ReductSplit.galTΩ A ℓ σ ^ (b - a) =
      _root_.ReductSplit.galTΩ A ℓ σ ^ a * 1 := by
    rw [← pow_add, Nat.add_sub_of_le hab.le, mul_one, he']
  exact (hu.pow a).mul_left_cancel h2

/-- If `σ` fixes `A(Ω)[ℓ^k]`, then `galTΩ σ ≡ 1` modulo `ℓ^k`. -/
theorem galTΩ_sub_eq_smul (σ : Ω ≃ₐ[K] Ω) (k : ℕ)
    (hfix : ∀ x : A.Pt Ω, x ^ (ℓ ^ k) = 1 → A.galAct σ x = x)
    (x : _root_.ReductSplit.TΩ A Ω ℓ) :
    ∃ y : _root_.ReductSplit.TΩ A Ω ℓ,
      _root_.ReductSplit.galTΩ A ℓ σ x - x = ((ℓ : ℤ_[ℓ]) ^ k) • y := by
  rw [← _root_.PkgI3.Tate.coord_eq_zero_iff]
  have hx := _root_.PkgI3.Tate.pow_smul_eq_zero x.2 k
  have hP : (Additive.toMul (x.1 k)) ^ (ℓ ^ k) = 1 := by
    rw [← toMul_nsmul, hx, toMul_zero]
  show (_root_.ReductSplit.galTΩ A ℓ σ x).1 k - x.1 k = 0
  rw [galTΩ_apply_coord, hfix _ hP, ofMul_toMul, sub_self]

end Rigidity

/-- **P2, rigidity at one place**, with Serre's lemma as its explicit premise. -/
theorem p2InertiaRigidity_of_serre (hS : SerreLemmaTate) : P2InertiaRigidity := by
  intro K _ A Ω _ _ w ℓ _ k hk hfin hfix σ hσ t
  have h1 : _root_.ReductSplit.galTΩ A ℓ σ = 1 :=
    hS ℓ k hk (Additive (A.Pt Ω)) (_root_.ReductSplit.galTΩ A ℓ σ)
      (exists_pow_galTΩ_eq_one A ℓ hfin hσ) (galTΩ_sub_eq_smul A ℓ σ k (hfix σ hσ))
  rw [h1, Module.End.one_apply]

end HDec.CMSerreTate

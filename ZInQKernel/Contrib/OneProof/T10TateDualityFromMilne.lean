import ZInQKernel.Contrib.OneProof.MilneTateDualityEtale
import ZInQKernel.Contrib.OneProof.EllAdic.T10EtaleRebaseBindingV1
import ZInQKernel.Contrib.OneProof.EllAdic.EllAdicHOneRebaseNaturalityV2

/-!
# `t10TateDuality` is equivalent to Milne's printed Tate duality on the étale site

`T10Etale.T10_TateDuality` states Tate duality on Mathlib's pro-étale `ℓ`-adic cohomology with the
Galois action `T10Etale.galH`. `MilneAV86Thm151aRem155` states it on classical étale cohomology
(compatible families of `H¹_et(A_K̄, ℤ/ℓⁿ)`) as Milne prints it. The two are equivalent:

* the integral comparison `ellAdicHOne_actualEtale_linearEquiv` (Stacks 099V, kernel-checked) is
  `ℤ_ℓ`-linear for the module structure of `T10Etale`;
* `galH A ℓ σ` is the pullback along `(galIso A σ⁻¹).symm` (`galH_eq_ellAdicHOne_rebase`);
* the comparison commutes with that pullback (`ellAdicHOne_actualEtale_linearEquiv_rebase`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory RC53.EllAdic
open scoped RC53.EllAdic.FiniteAbDictionary
open PkgI3 MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.OneProof.MilneTateDuality

/-- The comparison intertwines `T10Etale.galH` with the étale Galois action. -/
theorem comparison_galH {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Field.absoluteGaloisGroup K)
    (x : (A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1) :
    ellAdicHOne_actualEtale_linearEquiv (A.baseChange (AlgebraicClosure K)).X.left ℓ
        (T10Etale.galH A ℓ σ x) =
      etaleGalH A ℓ σ
        (ellAdicHOne_actualEtale_linearEquiv (A.baseChange (AlgebraicClosure K)).X.left ℓ x) := by
  rw [T10Binding.galH_eq_ellAdicHOne_rebase]
  exact ellAdicHOne_actualEtale_linearEquiv_rebase _ ℓ x

/-- Transport of an equivariant isomorphism along an intertwining linear equivalence. -/
theorem exists_equivariant_iff {R M N D G : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup D] [Module R D]
    (Φ : M ≃ₗ[R] N) (g : G → M →+ M) (h : G → N →+ N) (d : G → D →ₗ[R] D)
    (hΦ : ∀ σ x, Φ (g σ x) = h σ (Φ x)) :
    (∃ φ : M ≃ₗ[R] D, ∀ σ x, φ (g σ x) = d σ (φ x)) ↔
      (∃ ψ : N ≃ₗ[R] D, ∀ σ y, ψ (h σ y) = d σ (ψ y)) := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨Φ.symm.trans φ, fun σ y => ?_⟩
    obtain ⟨x, rfl⟩ := Φ.surjective y
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← hΦ, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
    exact hφ σ x
  · rintro ⟨ψ, hψ⟩
    refine ⟨Φ.trans ψ, fun σ x => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hΦ]
    exact hψ σ (Φ x)

set_option maxHeartbeats 4000000 in
/-- **`t10TateDuality` is equivalent to Milne's printed statement.** -/
theorem t10TateDuality_iff_milneAV86 :
    T10Etale.T10_TateDuality ↔ MilneAV86Thm151aRem155 := by
  refine forall_congr' fun K => forall_congr' fun _ => forall_congr' fun A => forall_congr' fun ℓ =>
    forall_congr' fun _ => forall_congr' fun _ => ?_
  let _inst := etaleHOneKernelModule (A.baseChange (AlgebraicClosure K)).X.left ℓ
  exact exists_equivariant_iff
    (ellAdicHOne_actualEtale_linearEquiv (A.baseChange (AlgebraicClosure K)).X.left ℓ)
    (fun σ => (T10Etale.galH A ℓ σ).toAddMonoidHom) (etaleGalH A ℓ)
    (fun σ => (A.galT (ℓ := ℓ) σ⁻¹).dualMap) (comparison_galH A ℓ)

/-- `t10TateDuality` from Milne's printed Tate duality. -/
theorem t10TateDuality_of_milneAV86 (h : MilneAV86Thm151aRem155) : T10Etale.T10_TateDuality :=
  t10TateDuality_iff_milneAV86.mpr h

/-! ## Characteristic zero

The single proof reads `t10TateDuality` only over finite extensions of `ℚ_p`. Over fields of
characteristic zero the row is equivalent to `MilneAV86Thm151aRem155CharZero`, where `K̄` is a
separable closure of `K` and no step from `k_s` to `K̄` is needed. -/

/-- `T10Etale.T10_TateDuality` over fields of characteristic zero. -/
def T10TateDualityCharZero : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    ∃ φ : (A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1 ≃ₗ[ℤ_[ℓ]]
        Module.Dual ℤ_[ℓ] (A.T ℓ),
      ∀ (σ : Field.absoluteGaloisGroup K) x,
        φ (T10Etale.galH A ℓ σ x) = (A.galT (ℓ := ℓ) σ⁻¹).dualMap (φ x)

theorem t10TateDualityCharZero_of_t10TateDuality (h : T10Etale.T10_TateDuality) :
    T10TateDualityCharZero :=
  fun K _ _ A ℓ _ hℓ => h K A ℓ hℓ

theorem milneAV86CharZero_of_milneAV86 (h : MilneAV86Thm151aRem155) :
    MilneAV86Thm151aRem155CharZero :=
  fun K _ _ A ℓ _ hℓ => h K A ℓ hℓ

set_option maxHeartbeats 4000000 in
/-- **In characteristic zero, `t10TateDuality` is equivalent to Milne's printed statement.** -/
theorem t10TateDualityCharZero_iff_milneAV86CharZero :
    T10TateDualityCharZero ↔ MilneAV86Thm151aRem155CharZero := by
  refine forall_congr' fun K => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun A =>
    forall_congr' fun ℓ => forall_congr' fun _ => forall_congr' fun _ => ?_
  let _inst := etaleHOneKernelModule (A.baseChange (AlgebraicClosure K)).X.left ℓ
  exact exists_equivariant_iff
    (ellAdicHOne_actualEtale_linearEquiv (A.baseChange (AlgebraicClosure K)).X.left ℓ)
    (fun σ => (T10Etale.galH A ℓ σ).toAddMonoidHom) (etaleGalH A ℓ)
    (fun σ => (A.galT (ℓ := ℓ) σ⁻¹).dualMap) (comparison_galH A ℓ)

/-- `t10TateDuality` over fields of characteristic zero from Milne's printed Tate duality. -/
theorem t10TateDualityCharZero_of_milneAV86CharZero (h : MilneAV86Thm151aRem155CharZero) :
    T10TateDualityCharZero :=
  t10TateDualityCharZero_iff_milneAV86CharZero.mpr h

end ZInQ.OneProof.MilneTateDuality

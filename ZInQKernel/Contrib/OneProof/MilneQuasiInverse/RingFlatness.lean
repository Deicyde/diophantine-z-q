/-
ZInQKernel/Contrib/OneProof/MilneQuasiInverse/RingFlatness.lean

New code for this repository (not vendored). Commutative algebra for the flatness input of
`AvSplit.MilneIsogenyQuasiInverse`: a finite module over a reduced ring whose fibre dimension is
the same at every prime is flat (Hartshorne II Ex. 5.8(c); the Stacks Project states the
equivalence "finite locally free iff locally constant rank" over reduced rings), and its use for
`S ⊗[R] S` over `S`.

Status: compiled by milne-compile on 2026-11-16 at Lean 4.35.0 / Mathlib v4.35.0 (no change needed;
only standard axioms). Written against the declarations of Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 read in source form (FreeLocus, LocalRing/Module,
LocalRing/ResidueField/{Basic,Ideal,Fiber}, Flat/{Basic,Localization,Stability},
TensorProduct/Tower, Dimension/{Constructions,Free}, FiniteDimensional/Lemmas, Nilpotent/Lemmas).
No proof placeholders, no added axioms, no native evaluation, no reflection and no
build-time code.
-/
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Constant fibre rank over a reduced ring implies flatness

Main results (namespace `ZInQ.Contrib.MilneQuasiInverse.RingFlatness`):

* `finrank_tensor_eq_finrank_fiber`: for a prime `p` of `R` and a field `L` over `κ(p)`,
  `dim_L (L ⊗[R] M) = dim_{κ(p)} (κ(p) ⊗[R] M)`.
* `finrank_fiber_comap`: the same along a ring map `R → A`, for a prime of `A` and its contraction.
* `linearCombination_injective_of_finrank_fiber`: over a reduced ring, a generating family of
  `M` with as many members as every fibre dimension is linearly independent.
* `free_of_isLocalRing_of_finrank_fiber`: over a reduced local ring, constant fibre dimension
  implies free.
* `flat_of_finrank_fiber`: over a reduced ring, a finite module whose fibre dimension is the same
  at every prime is flat.
* `flat_of_rankAtStalk_tensor_self`: if `S` is a finite `R`-algebra, `R` is reduced,
  `Spec S → Spec R` is surjective, and `S ⊗[R] S` is flat over `S` (left factor) of constant
  rank, then `S` is flat over `R`.
-/

noncomputable section

open TensorProduct

namespace ZInQ.Contrib.MilneQuasiInverse.RingFlatness

universe u v w

section FiberRank

variable {R : Type u} [CommRing R]

/-- The dimension of the fibre of `M` does not change under an extension `L / κ(p)`. -/
theorem finrank_tensor_eq_finrank_fiber {M : Type v} [AddCommGroup M] [Module R M]
    (p : Ideal R) [p.IsPrime] (L : Type w) [Field L] [Algebra R L]
    [Algebra p.ResidueField L] [IsScalarTower R p.ResidueField L] :
    Module.finrank L (L ⊗[R] M) = Module.finrank p.ResidueField (p.Fiber M) :=
  (AlgebraTensorModule.cancelBaseChange R p.ResidueField L L M).finrank_eq.symm.trans
    Module.finrank_baseChange

/-- Fibre dimensions along a ring map `R → A`: at a prime `q` of `A` the dimension of
`κ(q) ⊗[R] M` is the fibre dimension of `M` at the contraction of `q`. -/
theorem finrank_fiber_comap {A : Type v} [CommRing A] [Algebra R A]
    {M : Type w} [AddCommGroup M] [Module R M] (q : Ideal A) [q.IsPrime] :
    Module.finrank q.ResidueField (q.ResidueField ⊗[R] M) =
      Module.finrank (q.comap (algebraMap R A)).ResidueField
        ((q.comap (algebraMap R A)).Fiber M) := by
  let φ : (q.comap (algebraMap R A)).ResidueField →ₐ[R] q.ResidueField :=
    Ideal.ResidueField.mapₐ (q.comap (algebraMap R A)) q (Algebra.ofId R A) rfl
  letI : Algebra (q.comap (algebraMap R A)).ResidueField q.ResidueField := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R (q.comap (algebraMap R A)).ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  exact finrank_tensor_eq_finrank_fiber (q.comap (algebraMap R A)) q.ResidueField

/-- **Kernel argument.** Over a reduced ring, if `v : Fin n → M` spans `M` and every fibre of
`M` has dimension `n`, then `v` is linearly independent: an element `x` of the kernel of
`Finsupp.linearCombination R v` has `x j ∈ p` for every prime `p` (the base change of the
surjection to `κ(p)` is a surjection between `n`-dimensional spaces), so `x j` is nilpotent. -/
theorem linearCombination_injective_of_finrank_fiber [IsReduced R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] {n : ℕ}
    (v : Fin n → M) (hv : Submodule.span R (Set.range v) = ⊤)
    (h : ∀ p : PrimeSpectrum R, Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) = n) :
    Function.Injective (Finsupp.linearCombination R v) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  ext j
  rw [Finsupp.zero_apply]
  apply IsReduced.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  haveI := hJ
  haveI : Nontrivial R := (⟨J, hJ⟩ : PrimeSpectrum R).nontrivial
  have hsurj : Function.Surjective
      ((Finsupp.linearCombination R v).baseChange J.ResidueField) := by
    apply LinearMap.baseChange_surjective
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hv]
  have hdim : Module.finrank J.ResidueField (J.ResidueField ⊗[R] (Fin n →₀ R)) =
      Module.finrank J.ResidueField (J.ResidueField ⊗[R] M) := by
    rw [Module.finrank_baseChange, Module.finrank_finsupp_self, Fintype.card_fin]
    exact (h ⟨J, hJ⟩).symm
  have hinj : Function.Injective
      ((Finsupp.linearCombination R v).baseChange J.ResidueField) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  have h1 : (1 : J.ResidueField) ⊗ₜ[R] x = 0 := by
    apply hinj
    rw [LinearMap.baseChange_tmul, hx, TensorProduct.tmul_zero, map_zero]
  have h2 : TensorProduct.rid R J.ResidueField
      ((Finsupp.lapply j).lTensor J.ResidueField ((1 : J.ResidueField) ⊗ₜ[R] x)) = 0 := by
    rw [h1, map_zero, map_zero]
  rw [LinearMap.lTensor_tmul, Finsupp.lapply_apply, TensorProduct.rid_tmul,
    Algebra.smul_def, mul_one] at h2
  exact Ideal.algebraMap_residueField_eq_zero.mp h2

/-- Over a reduced local ring, a finite module whose fibre dimension is `n` at every prime is
free. -/
theorem free_of_isLocalRing_of_finrank_fiber [IsLocalRing R] [IsReduced R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] {n : ℕ}
    (h : ∀ p : PrimeSpectrum R, Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) = n) :
    Module.Free R M := by
  -- `κ(m) → k`, the canonical `R`-algebra map from the residue field of `R_m` to that of `R`.
  let ψ : (IsLocalRing.maximalIdeal R).ResidueField →ₐ[R] IsLocalRing.ResidueField R :=
    Ideal.ResidueField.liftₐ (IsLocalRing.maximalIdeal R)
      (Algebra.ofId R (IsLocalRing.ResidueField R))
      (fun x hx => by
        rw [RingHom.mem_ker]
        exact (IsLocalRing.residue_eq_zero_iff x).mpr hx)
      (fun x hx => by
        rw [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr fun h0 =>
          (Ideal.mem_primeCompl_iff.mp hx) ((IsLocalRing.residue_eq_zero_iff x).mp h0))
  letI : Algebra (IsLocalRing.maximalIdeal R).ResidueField (IsLocalRing.ResidueField R) :=
    ψ.toRingHom.toAlgebra
  haveI : IsScalarTower R (IsLocalRing.maximalIdeal R).ResidueField
      (IsLocalRing.ResidueField R) :=
    IsScalarTower.of_algebraMap_eq' ψ.comp_algebraMap.symm
  have hk : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] M) = n :=
    (finrank_tensor_eq_finrank_fiber (IsLocalRing.maximalIdeal R)
      (IsLocalRing.ResidueField R)).trans (h (IsLocalRing.closedPoint R))
  have b : Module.Basis (Fin n) (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] M) :=
    Module.finBasisOfFinrankEq _ _ hk
  obtain ⟨v, hv⟩ :=
    (TensorProduct.mk_surjective R M (IsLocalRing.ResidueField R)
      IsLocalRing.residue_surjective).comp_left b
  have hspan : Submodule.span R (Set.range v) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis v b (congr_fun hv)
  have hinj := linearCombination_injective_of_finrank_fiber v hspan h
  have hsurj : Function.Surjective (Finsupp.linearCombination R v) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hspan]
  exact Module.Free.of_basis
    (Module.Basis.ofRepr (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm)

/-- **Constant fibre rank over a reduced ring implies flatness.** A finite module over a reduced
ring whose fibre `κ(p) ⊗[R] M` has the same dimension at every prime `p` is flat. -/
theorem flat_of_finrank_fiber [IsReduced R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] {n : ℕ}
    (h : ∀ p : PrimeSpectrum R, Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) = n) :
    Module.Flat R M := by
  apply Module.flat_of_localized_maximal
  intro P _
  have hfib : ∀ q : PrimeSpectrum (Localization.AtPrime P),
      Module.finrank q.asIdeal.ResidueField
        (q.asIdeal.Fiber (Localization.AtPrime P ⊗[R] M)) = n := fun q =>
    (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime P) q.asIdeal.ResidueField
        q.asIdeal.ResidueField M).finrank_eq.trans
      ((finrank_fiber_comap (R := R) (M := M) q.asIdeal).trans
        (h ⟨q.asIdeal.comap (algebraMap R (Localization.AtPrime P)), inferInstance⟩))
  haveI : Module.Free (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] M) :=
    free_of_isLocalRing_of_finrank_fiber hfib
  haveI : Module.Flat R (Localization.AtPrime P ⊗[R] M) :=
    Module.Flat.trans R (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] M)
  exact Module.Flat.of_linearEquiv
    ((LocalizedModule.equivTensorProduct P.primeCompl M).restrictScalars R)

/-- The fibre dimension of `S` over `R` at a prime `p` is the rank at a prime `q` over `p` of
`S ⊗[R] S`, viewed as an `S`-module through the left factor. -/
theorem finrank_fiber_eq_of_rankAtStalk_tensor {S : Type v} [CommRing S] [Algebra R S]
    [Module.Finite R S] (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)))
    [Module.Flat S (S ⊗[R] S)] {n : ℕ}
    (hN : ∀ q : PrimeSpectrum S, Module.rankAtStalk (R := S) (S ⊗[R] S) q = n)
    (p : PrimeSpectrum R) :
    Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber S) = n := by
  obtain ⟨q, rfl⟩ := hsurj p
  refine (finrank_fiber_comap (R := R) (A := S) (M := S) q.asIdeal).symm.trans ?_
  refine (AlgebraTensorModule.cancelBaseChange R S q.asIdeal.ResidueField
    q.asIdeal.ResidueField S).finrank_eq.symm.trans ?_
  exact (Module.rankAtStalk_eq (M := S ⊗[R] S) q).symm.trans (hN q)

/-- **Ring-level flatness criterion used for isogenies.** -/
theorem flat_of_rankAtStalk_tensor_self {S : Type v} [CommRing S] [Algebra R S] [IsReduced R]
    [Module.Finite R S] (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)))
    [Module.Flat S (S ⊗[R] S)] {n : ℕ}
    (hN : ∀ q : PrimeSpectrum S, Module.rankAtStalk (R := S) (S ⊗[R] S) q = n) :
    Module.Flat R S :=
  flat_of_finrank_fiber (fun p => finrank_fiber_eq_of_rankAtStalk_tensor hsurj hN p)

end FiberRank

end ZInQ.Contrib.MilneQuasiInverse.RingFlatness

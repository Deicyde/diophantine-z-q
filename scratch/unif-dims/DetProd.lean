import ZInQKernel.HDecomp.Faltings.HodgeLattice

/-! # unif-dims: `DetLatticeProd` (determinant lattice of a direct sum), proof attempt -/

namespace ZInQ.UnifDims

open NumberField TensorProduct ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice
open scoped nonZeroDivisors

section Line

variable {K : Type} [Field K] [NumberField K]
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M]

/-- The determinant functional `K ⊗ ⋀^g M → K` of a `K`-basis of `K ⊗ M`. -/
noncomputable def detFun {g : ℕ} (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)) :
    (K ⊗[𝓞 K] ⋀[𝓞 K]^g M) →ₗ[K] K :=
  (exteriorPower.alternatingMapLinearEquiv
    ({ toMultilinearMap := (b.det.toMultilinearMap.restrictScalars (𝓞 K)).compLinearMap
          (fun _ => TensorProduct.mk (𝓞 K) K M 1)
       map_eq_zero_of_eq' := fun v i j hv hij =>
          b.det.map_eq_zero_of_eq (fun k => (1 : K) ⊗ₜ[𝓞 K] v k) (by simp [hv]) hij } :
      M [⋀^Fin g]→ₗ[𝓞 K] K)).liftBaseChange K

theorem detFun_tmul {g : ℕ} (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)) (v : Fin g → M) :
    detFun b ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g v) =
      b.det (fun k => (1 : K) ⊗ₜ[𝓞 K] v k) := by
  simp only [detFun, LinearMap.liftBaseChange_one_tmul,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The determinant functional of a basis `1 ⊗ wⱼ` is injective (the Hodge space is the line
spanned by `1 ⊗ ∧w`); steps 2-4 of hodge-lattice's `hodgeLattice_of_lattice`. -/
theorem detFun_injective {g : ℕ} (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)) (w : Fin g → M)
    (hbw : ∀ j, (1 : K) ⊗ₜ[𝓞 K] w j = b j) : Function.Injective (detFun b) := by
  have hclear := exists_clear (K := K) w (fun v => by
    have hr : Set.range (fun j => (1 : K) ⊗ₜ[𝓞 K] w j) = Set.range b := by
      rw [show (fun j => (1 : K) ⊗ₜ[𝓞 K] w j) = b from funext hbw]
    rw [hr, b.span_eq]; exact Submodule.mem_top)
  set s0 : K ⊗[𝓞 K] ⋀[𝓞 K]^g M := (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g w with hs0
  have hone : ∀ x : ⋀[𝓞 K]^g M, (1 : K) ⊗ₜ[𝓞 K] x ∈ Submodule.span K {s0} := by
    intro x
    have hx : x ∈ Submodule.span (𝓞 K) (Set.range (exteriorPower.ιMulti (𝓞 K) g)) := by
      rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact tmul_ιMulti_mem_span w hclear v
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [TensorProduct.tmul_smul]; exact Submodule.smul_of_tower_mem _ r hy
  have htop : Submodule.span K {s0} = ⊤ := by
    rw [eq_top_iff]
    rintro h -
    induction h using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul k x =>
      have : k ⊗ₜ[𝓞 K] x = k • ((1 : K) ⊗ₜ[𝓞 K] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]; exact Submodule.smul_mem _ k (hone x)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have hΨ : detFun b s0 = 1 := by
    rw [hs0, detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] w k) = b from funext hbw,
      Module.Basis.det_self]
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have : x ∈ Submodule.span K {s0} := htop ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp this
  rw [LinearMap.mem_ker, map_smul, hΨ, smul_eq_mul, mul_one] at hx
  rw [hx, zero_smul]
  exact Submodule.zero_mem _

/-- Step 1 of hodge-lattice's `hodgeLattice_of_lattice`: a `K`-basis of `K ⊗ M` of the form
`1 ⊗ wⱼ` with `wⱼ ∈ ω`. -/
theorem exists_basis_of_span {g : ℕ} (ω : Submodule (𝓞 K) M)
    (hrank : Module.rank K (K ⊗[𝓞 K] M) = g)
    (hspan : Submodule.span K (Set.range fun x : ω => (1 : K) ⊗ₜ[𝓞 K] (x : M)) = ⊤) :
    ∃ (w : Fin g → ω) (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)),
      ∀ j, (1 : K) ⊗ₜ[𝓞 K] (w j : M) = b j := by
  classical
  set V := K ⊗[𝓞 K] M
  set f : ω → V := fun x => (1 : K) ⊗ₜ[𝓞 K] (x : M) with hf
  have : FiniteDimensional K V := Module.finite_of_rank_eq_nat hrank
  have hfin : Module.finrank K V = g := Module.finrank_eq_of_rank_eq hrank
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range f)
  let bs : Module.Basis s K V := Module.Basis.mk hs_li (by
    rw [Subtype.range_coe, hs_span, hspan])
  let b : Module.Basis (Fin g) K V :=
    bs.reindex (bs.indexEquiv (Module.finBasisOfFinrankEq K V hfin))
  have hmem : ∀ j, ∃ x : ω, f x = b j := fun j => by
    have : (b j : V) ∈ s := by
      simp only [b, Module.Basis.reindex_apply, bs, Module.Basis.coe_mk]
      exact Subtype.mem _
    exact hs_sub this
  choose w hw using hmem
  exact ⟨w, b, hw⟩

/-- `secIndex` is invariant under an injective `K`-linear map. -/
theorem secIndex_map {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (Ψ : V →ₗ[K] K) (hΨ : Function.Injective Ψ)
    (Λ : Submodule (𝓞 K) V) (s : V) :
    secIndex Λ s = secIndex (Λ.map (Ψ.restrictScalars (𝓞 K))) (Ψ s) := by
  unfold secIndex
  have hspan : Submodule.map (Ψ.restrictScalars (𝓞 K)) (Submodule.span (𝓞 K) {s}) =
      Submodule.span (𝓞 K) {Ψ s} := by
    rw [Submodule.map_span, Set.image_singleton]; rfl
  rw [← hspan, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  exact (AddSubgroup.relIndex_map_map_of_injective _ _
    (f := ((Ψ.restrictScalars (𝓞 K)) : V →+ K)) hΨ).symm

/-- **Indices of `1` multiply** in a product of finitely generated `𝓞_K`-submodules of `K`
containing `1` (through `FractionalIdeal.absNorm` and the kernel's `secIndex_mul_absNorm`). -/
theorem secIndex_one_mul (I J : Submodule (𝓞 K) K) (hI : I.FG) (hJ : J.FG) (h1I : (1 : K) ∈ I)
    (h1J : (1 : K) ∈ J) : secIndex (I * J) 1 = secIndex I 1 * secIndex J 1 := by
  let I' : FractionalIdeal (𝓞 K)⁰ K := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩
  let J' : FractionalIdeal (𝓞 K)⁰ K := ⟨J, FractionalIdeal.isFractional_of_fg hJ⟩
  have hIJ : ((I' * J' : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = I * J :=
    FractionalIdeal.coe_mul _ _
  have h1 : (1 : K) ∈ (I' * J' : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.mem_coe, hIJ, ← mul_one (1 : K)]
    exact Submodule.mul_mem_mul h1I h1J
  have e1 := secIndex_mul_absNorm I' h1I one_ne_zero
  have e2 := secIndex_mul_absNorm J' h1J one_ne_zero
  have e3 := secIndex_mul_absNorm (I' * J') h1 one_ne_zero
  rw [hIJ] at e3
  simp only [map_one, abs_one, map_mul] at e1 e2 e3
  have : (secIndex (I * J) 1 : ℚ) = secIndex I 1 * secIndex J 1 := by
    have hI0 : FractionalIdeal.absNorm I' ≠ 0 := by
      intro h; rw [h, mul_zero] at e1; exact zero_ne_one e1
    have hJ0 : FractionalIdeal.absNorm J' ≠ 0 := by
      intro h; rw [h, mul_zero] at e2; exact zero_ne_one e2
    change (secIndex (I * J) 1 : ℚ) * (FractionalIdeal.absNorm I' * FractionalIdeal.absNorm J')
      = 1 at e3
    change (secIndex I 1 : ℚ) * FractionalIdeal.absNorm I' = 1 at e1
    change (secIndex J 1 : ℚ) * FractionalIdeal.absNorm J' = 1 at e2
    linear_combination (-(secIndex (I * J) 1 : ℚ)) * e1 +
      (-(secIndex (I * J) 1 : ℚ) * secIndex I 1 * FractionalIdeal.absNorm I') * e2 +
      ((secIndex I 1 : ℚ) * secIndex J 1) * e3
  exact_mod_cast this

end Line

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.detFun_injective
#print axioms ZInQ.UnifDims.secIndex_map
#print axioms ZInQ.UnifDims.secIndex_one_mul

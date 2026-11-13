import ZInQKernel.HDecomp.I3Linalg.RhoCont
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.Conductor.LadicCond

/-!
# g8-local, part B: the Tate action from torsion points, D2's algebra, fields of definition

Task g8-local (2026-11-13). Lemmas on pkg-I3's abelian varieties (`PkgI3.AbVar`), their points
`A.Pt K̄`, the Galois action `A.galAct` and the Tate representation.

* `repBaseChange_galRep_eq_one_of_fix`: if `σ ∈ G_K` fixes every point of `A(K̄)[ℓⁿ]` for all
  `n`, then `σ` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)`.
* `fixed_of_unipSq_of_pow`: D2's algebra (the proof of `PkgI2.fixed_of_unipSq_of_iterate`, restated
  for `PkgI3.AbVar`): `(σ − 1)² x = 0`, `x ∈ A[ℓⁿ]` and `σ^{qᵃ} x = x` with `qᵃ` prime to `ℓⁿ` give
  `σ x = x`.
* `exists_fix_field`: every `K̄`-point is fixed by `G_E` for some `E ⊆ ℚ̄` finite over `ℚ`, read
  through an embedding `ι : ℚ̄ → K̄` onto (glue-rho-cont's open stabilizers + Krull topology).
* `algClosure_surjective`: for a number field `K`, every `ℚ`-embedding `ℚ̄ → K̄` is onto.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.G8Local

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar

variable {K : Type} [Field K]

/-! ### §1. Trivial action on all `ℓ`-power torsion gives trivial Tate action -/

theorem galT_eq_id_of_fix (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K)
    (h : ∀ n : ℕ, ∀ x : A.Pt (AlgebraicClosure K), x ^ (ℓ ^ n) = 1 → A.galAct σ x = x) :
    A.galT (ℓ := ℓ) σ = LinearMap.id := by
  apply LinearMap.ext; intro y; apply Subtype.ext; funext n
  change Additive.ofMul (A.galAct σ (Additive.toMul (y.1 n))) = y.1 n
  have hy : (ℓ ^ n) • y.1 n = 0 := Tate.pow_smul_eq_zero y.2 n
  have hy' : (Additive.toMul (y.1 n)) ^ (ℓ ^ n) = 1 := by
    rw [← toMul_nsmul, hy, toMul_zero]
  rw [h n _ hy']
  rfl

/-- **`σ` fixing `A(K̄)[ℓ^∞]` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)`.** -/
theorem repBaseChange_galRep_eq_one_of_fix (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Field.absoluteGaloisGroup K)
    (h : ∀ n : ℕ, ∀ x : A.Pt (AlgebraicClosure K), x ^ (ℓ ^ n) = 1 → A.galAct σ x = x) :
    GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ) σ = 1 := by
  have h1 : A.galRep ℓ σ = LinearMap.id := by
    change (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ] = LinearMap.id
    rw [galT_eq_id_of_fix A ℓ σ h, LinearMap.baseChange_id]
  change (A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) = 1
  rw [h1, LinearMap.baseChange_id]
  rfl

/-! ### §2. D2's algebra for `PkgI3.AbVar` -/

theorem galAct_pow_apply (A : AbVar K) (σ : Field.absoluteGaloisGroup K) (k : ℕ)
    (x : A.Pt (AlgebraicClosure K)) : A.galAct (σ ^ k) x = (A.galAct σ)^[k] x := by
  induction k generalizing x with
  | zero =>
    rw [pow_zero, Function.iterate_zero_apply]
    change galHom 1 ≫ x = x
    rw [galHom_one, Category.id_comp]
  | succ k ih =>
    rw [pow_succ, RhoCont.galAct_mul, ih, Function.iterate_succ_apply]

/-- **D2's algebra (proof of `PkgI2.fixed_of_unipSq_of_iterate`, for `PkgI3.AbVar`).** -/
theorem fixed_of_unipSq_of_pow (A : AbVar K) (σ : Field.absoluteGaloisGroup K)
    (x : A.Pt (AlgebraicClosure K)) (ℓ n q a : ℕ) (hcop : Nat.Coprime (q ^ a) (ℓ ^ n))
    (hx : x ^ (ℓ ^ n) = 1)
    (hu : A.galAct σ (A.galAct σ x) * (A.galAct σ x)⁻¹ * (A.galAct σ x)⁻¹ * x = 1)
    (hit : A.galAct (σ ^ (q ^ a)) x = x) : A.galAct σ x = x := by
  set g := A.galAct (L := AlgebraicClosure K) σ with hg
  set N := g x * x⁻¹ with hN
  have hσN : g N = N := by
    rw [hN, map_mul, map_inv]
    have h2 : g (g x) * (g x)⁻¹ = ((g x)⁻¹ * x)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hu]; group
    rw [h2, mul_inv_rev, inv_inv, mul_comm]
  have hiter : ∀ k : ℕ, g^[k] x = N ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hσN, pow_succ, hN]
      group
  have h1 : N ^ (q ^ a) = 1 := by
    have := hiter (q ^ a)
    rw [← galAct_pow_apply, hit] at this
    exact (mul_eq_right.mp this.symm)
  have h2 : N ^ (ℓ ^ n) = 1 := by
    rw [hN, mul_pow, ← map_pow, hx, map_one, inv_pow, hx]; simp
  have hN1 : N = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [hN] at hN1
  exact mul_inv_eq_one.mp hN1

/-! ### §3. Fields of definition of points, read in `ℚ̄` -/

/-- **Every `K̄`-point is fixed by `G_E` for a finite `E ⊆ ℚ̄`**, through an embedding
`ι : ℚ̄ → K̄` and a map `r : G_K → G_ℚ` with `ι ∘ r(τ) = τ ∘ ι` (e.g. `G0Galois.resQ`). -/
theorem exists_fix_field (A : AbVar K) (P : A.Pt (AlgebraicClosure K))
    (emb : AlgebraicClosure ℚ →+* AlgebraicClosure K) (hemb : Function.Surjective emb)
    (r : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hr : ∀ (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) x, emb (r τ x) = τ (emb x)) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∀ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, r τ ∈ E.fixingSubgroup →
        A.galAct τ P = P := by
  obtain ⟨H, hH⟩ := RhoCont.exists_openSubgroup_galAct_eq A P
  obtain ⟨E', hE'fd, hE'⟩ := (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K)
    (H : Set (Field.absoluteGaloisGroup K))).mp (H.isOpen.mem_nhds H.one_mem)
  haveI := hE'fd
  let b := Module.finBasis K E'
  choose f hf using fun i => hemb (b i : AlgebraicClosure K)
  let E := IntermediateField.adjoin ℚ (Set.range f)
  haveI : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin (fun z _ => Algebra.IsIntegral.isIntegral z)
  refine ⟨E, inferInstance, fun τ hτ => hH τ (hE' ?_)⟩
  show τ ∈ E'.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have hb : ∀ i, τ (b i : AlgebraicClosure K) = b i := by
    intro i
    rw [← hf i, ← hr]
    congr 1
    exact (IntermediateField.mem_fixingSubgroup_iff E (r τ)).mp hτ _
      (IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩)
  have hlin : ((τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K).toLinearMap ∘ₗ
      E'.val.toLinearMap) = E'.val.toLinearMap := b.ext fun i => hb i
  intro x hx
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

/-- For a number field `K`, every ring map `ℚ̄ → K̄` is onto. -/
theorem algClosure_surjective (K : Type) [Field K] [NumberField K]
    (emb : AlgebraicClosure ℚ →+* AlgebraicClosure K) : Function.Surjective emb := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure K) := Algebra.IsAlgebraic.trans ℚ K _
  let g : AlgebraicClosure K →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  exact (Algebra.IsAlgebraic.algHom_bijective₂ (K := ℚ) g emb.toRatAlgHom).2.2

end ZInQ.Contrib.G8Local

end

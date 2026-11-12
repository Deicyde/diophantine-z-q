import Mathlib

/-!
# glue-c10: C10 of h-trust (N5 L776-795), one compatible system at 3 and 5

Leaves copied verbatim from `scratch/pkg-I6/I6.lean` (`ChebotarevExists`, `BrauerNesbittChar0`).
-/

open NumberField

namespace GlueC10

/-! ## Leaves (copied from pkg-I6) -/

/-- **Leaf I6.4 (Chebotarev, existence form)** — verbatim from pkg-I6. -/
def ChebotarevExists : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M),
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q

/-- **Leaf I6.5 (Brauer–Nesbitt, characteristic 0, trace form)** — verbatim from pkg-I6. -/
def BrauerNesbittChar0 : Prop :=
  ∀ (k G V W : Type) [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) σ.asModule →
    (∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) →
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule)

/-! ## Part A. Finite level (the form recommended by glue-I6-rest)

A representation that factors through a finite Galois group `Gal(M/ℚ)`: traces that agree at
every unramified Frobenius outside `S` agree everywhere, hence the representations are
isomorphic. -/

/-- `σ ∈ Gal(M/ℚ)` is the Frobenius at some prime of `𝓞_M` over a rational prime `p ∉ S`
that is unramified in `M`. -/
def IsUnramFrob (M : Type) [Field M] [NumberField M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q

/-- Chebotarev: every element of `Gal(M/ℚ)` is an unramified Frobenius outside `S`. -/
theorem isUnramFrob_all (hC : ChebotarevExists) (M : Type) [Field M] [NumberField M]
    [IsGalois ℚ M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M) : IsUnramFrob M S σ :=
  hC M S σ

/-- **C10 at finite level (GLUE, proved from I6.4 and I6.5).** Two semisimple
finite-dimensional representations of `Gal(M/ℚ)` over a field of characteristic `0` whose traces
agree at every unramified Frobenius outside a finite set `S` are isomorphic. -/
theorem iso_of_trace_eq_frob_finite (hC : ChebotarevExists) (hBN : BrauerNesbittChar0)
    (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (S : Finset ℕ)
    (k V W : Type) [Field k] [CharZero k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k (M ≃ₐ[ℚ] M) V) (σ : Representation k (M ≃ₐ[ℚ] M) W)
    (hρ : IsSemisimpleModule (MonoidAlgebra k (M ≃ₐ[ℚ] M)) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra k (M ≃ₐ[ℚ] M)) σ.asModule)
    (htr : ∀ g, IsUnramFrob M S g → LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k (M ≃ₐ[ℚ] M)] σ.asModule) :=
  hBN k _ V W ρ σ hρ hσ fun g => htr g (isUnramFrob_all hC M S g)

/-! ## Part B. The absolute Galois group `G_ℚ` -/

/-- `\bar ℚ`. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(\bar ℚ/ℚ)` with the Krull topology.  Definitionally Mathlib's
`GQ` (which is a non-reducible `def` of the same type). -/
abbrev GQ : Type := Qbar ≃ₐ[ℚ] Qbar

example : GQ = Field.absoluteGaloisGroup ℚ := rfl

/-- `\bar ℤ`, the integral closure of `ℤ` in `\bar ℚ`. -/
abbrev Zbar : Type := integralClosure ℤ Qbar

/-- `g ∈ G_ℚ` is an arithmetic Frobenius at the rational prime `p`: there is a prime `𝔓` of
`\bar ℤ` over `p` with `g x ≡ x^p (mod 𝔓)` for every `x ∈ \bar ℤ`. -/
def IsFrobAt (g : GQ) (p : ℕ) : Prop :=
  ∃ P : Ideal Zbar, P.IsPrime ∧ P.under ℤ = Ideal.span {(p : ℤ)} ∧
    ∀ x y : Zbar, (y : Qbar) = g (x : Qbar) - (x : Qbar) ^ p → y ∈ P

/-- **Frobenius density (GLUE).** For every finite subextension `E/ℚ` of `\bar ℚ` and every
`g ∈ G_ℚ` there is a Frobenius `h` at a prime `p ∉ S` with `h = g` on `E`.  By
`krullTopology_mem_nhds_one_iff` this says that Frobenius elements at primes outside `S` are
dense in `G_ℚ`. -/
def FrobDense (S : Finset ℕ) : Prop :=
  ∀ (E : IntermediateField ℚ Qbar), FiniteDimensional ℚ E → ∀ g : GQ,
    ∃ h : GQ, ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ IsFrobAt h p ∧
      ∀ x ∈ E, h x = g x

/-- **The lift of a finite-level Frobenius to `G_ℚ` (GLUE, not proved here).**  For a finite
Galois `E ⊂ \bar ℚ` and `τ ∈ Gal(E/ℚ)` that is the Frobenius at a prime `Q` of `𝓞_E` over `p`
unramified in `E`, some `h ∈ G_ℚ` restricting to `τ` is a Frobenius at `p` in `G_ℚ`.
Proof sketch: choose `𝔓 | Q` in `\bar ℤ`; an arithmetic Frobenius `h ∈ D_𝔓` exists by
compactness of `G_ℚ` and `exists_isArithFrobAt` in every finite Galois layer; `h|_E` is a
Frobenius at `Q`, and Frobenius at an unramified prime is unique
(`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`). -/
def FrobLift : Prop :=
  ∀ (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E] [IsGalois ℚ E]
    (τ : E ≃ₐ[ℚ] E) (p : ℕ) (Q : Ideal (𝓞 E)) [Q.IsPrime],
    Q.under ℤ = Ideal.span {(p : ℤ)} → Algebra.IsUnramifiedAt ℤ Q → IsArithFrobAt ℤ τ Q →
      ∃ h : GQ, IsFrobAt h p ∧ AlgEquiv.restrictNormal h E = τ

/-- **Frobenius density from Chebotarev (GLUE, proved from I6.4 and `FrobLift`).** -/
theorem frobDense_of_chebotarev (hC : ChebotarevExists) (hL : FrobLift) (S : Finset ℕ) :
    FrobDense S := by
  intro E hE g
  set N := IntermediateField.normalClosure ℚ E Qbar
  have : FiniteDimensional ℚ N := normalClosure.is_finiteDimensional ℚ E Qbar
  have : Normal ℚ N := normalClosure.normal ℚ E Qbar
  have : IsGalois ℚ N := ⟨⟩
  have : NumberField N := ⟨⟩
  obtain ⟨p, hp, hpS, Q, hQ, hQp, hQu, hQf⟩ := hC N S (AlgEquiv.restrictNormal g N)
  obtain ⟨h, hh, hres⟩ := hL N _ p Q hQp hQu hQf
  refine ⟨h, p, hp, hpS, hh, fun x hx => ?_⟩
  have hxN : x ∈ N := E.le_normalClosure hx
  have e1 := AlgEquiv.restrictNormal_commutes h N ⟨x, hxN⟩
  have e2 := AlgEquiv.restrictNormal_commutes g N ⟨x, hxN⟩
  rw [hres] at e1
  simpa using e1.symm.trans e2

/-- **Passage from Frobenius classes to `G_ℚ` (GLUE, proved).**  Two continuous functions on
`G_ℚ` with values in a Hausdorff space that agree on the Frobenius elements at primes outside `S`
are equal, given `FrobDense S`. -/
theorem eq_of_eq_on_frob {X : Type*} [TopologicalSpace X] [T2Space X] (S : Finset ℕ)
    (hD : FrobDense S) (f₁ f₂ : GQ → X)
    (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (hfr : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → f₁ g = f₂ g) : f₁ = f₂ := by
  funext g
  by_contra hne
  have hopen : IsOpen {x | f₁ x ≠ f₂ x} := isOpen_ne_fun h₁ h₂
  have hmem : (fun y => g * y) ⁻¹' {x | f₁ x ≠ f₂ x} ∈ nhds (1 : GQ) := by
    apply (hopen.preimage (continuous_const.mul continuous_id)).mem_nhds
    simpa using hne
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Qbar _).mp hmem
  obtain ⟨h, p, hp, hpS, hh, hEq⟩ := hD E hE g
  have hfix : g⁻¹ * h ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change g⁻¹ (h x) = x
    rw [hEq x hx]
    exact AlgEquiv.symm_apply_apply g x
  have := hsub hfix
  simp only [Set.mem_preimage, mul_inv_cancel_left, Set.mem_setOf_eq] at this
  exact this (hfr h p hp hpS hh)

/-- The trace of `ρ g` is the trace of its matrix in any basis. -/
lemma trace_eq_matrix {E V ι : Type*} [Field E] [AddCommGroup V] [Module E V] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι E V) (f : V →ₗ[E] V) :
    LinearMap.trace E V f = (LinearMap.toMatrix b b f).trace :=
  LinearMap.trace_eq_matrix_trace E b f

lemma continuous_trace {E V ι : Type*} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
    [AddCommGroup V] [Module E V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E V)
    {G : Type*} [Monoid G] [TopologicalSpace G] (ρ : Representation E G V)
    (hρ : Continuous fun g => LinearMap.toMatrix b b (ρ g)) :
    Continuous fun g => LinearMap.trace E V (ρ g) := by
  simp_rw [trace_eq_matrix b]
  exact (continuous_finsetSum _ fun i _ => (continuous_apply_apply i i).comp hρ)

/-- **C10, the comparison in `G_ℚ` (GLUE, proved from I6.5 and `FrobDense`).**  Two continuous
semisimple finite-dimensional representations of `G_ℚ` over a Hausdorff topological field of
characteristic `0` (e.g. `ℚ_ℓ`, a finite extension, or `\bar ℚ_ℓ`) whose traces agree at the
Frobenius elements at all primes outside `S` are isomorphic.  Continuity is that of the matrix
coefficients in some basis. -/
theorem iso_of_trace_eq_on_frob (hBN : BrauerNesbittChar0) (S : Finset ℕ) (hD : FrobDense S)
    (k V W ι κ : Type) [Field k] [CharZero k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (bV : Module.Basis ι k V) (bW : Module.Basis κ k W)
    (ρ : Representation k (GQ) V)
    (σ : Representation k (GQ) W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g))
    (hρ : IsSemisimpleModule (MonoidAlgebra k (GQ)) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra k (GQ)) σ.asModule)
    (htr : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k (GQ)] σ.asModule) := by
  have heq := eq_of_eq_on_frob S hD _ _ (continuous_trace bV ρ hρc) (continuous_trace bW σ hσc)
    htr
  exact hBN k _ V W ρ σ hρ hσ fun g => congrFun heq g

end GlueC10

#print axioms GlueC10.iso_of_trace_eq_frob_finite
#print axioms GlueC10.frobDense_of_chebotarev
#print axioms GlueC10.eq_of_eq_on_frob
#print axioms GlueC10.iso_of_trace_eq_on_frob

import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Chebotarev
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.TraceModelInstance
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Density
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Lattice

/-!
# Extending good-prime operators to all constituents

Appendix F, tex 9655–9668 and 9762–9797. The test set allows every lift of Frobenius;
unramifiedness is what allows the comparison with the chosen lifts in the model.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TraceLimits

open AddressGenuine
open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]

/-- All Frobenius lifts at the good primes outside a prescribed finite set. -/
def frobeniusTests (T : TypeData L ε) (avoid : Finset ℕ) : Set GalQ :=
  {g | ∃ q, T.Good q ∧ q ∉ avoid ∧ IsFrobAt g q}

/-- Frobenius tests outside any finite set are dense in the Krull topology (tex 9666–9668). -/
theorem dense_frobeniusTests (T : TypeData L ε) (avoid : Finset ℕ) :
    Dense (frobeniusTests T avoid) := by
  refine (dense_arithmeticFrobenius (avoid ∪ T.m.primeFactors)).mono ?_
  rintro g ⟨q, hq, hqavoid, hf⟩
  have hgood : T.Good q :=
    ⟨hq, (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd =>
      hqavoid (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hq, hd, T.m_pos.ne'⟩))⟩
  exact ⟨q, hgood, fun hqa => hqavoid (Finset.mem_union_left _ hqa),
    (isFrobAt_iff_c10 hq).2 hf⟩

/-- The good-prime Hecke and diamond operators on the integral module, with their
identification with the scalar operators (tex 9660–9668, 9720–9721, 9795–9796). -/
structure GoodOperators (T : TypeData L ε) (avoid : Finset ℕ) (frob : ℕ → GalQ)
    (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K)) where
  hecke : ℕ → Λ →ₗ[O] Λ
  diamond : ℕ → Λ →ₗ[O] Λ
  trace_eq : ∀ q, T.Good q → q ∉ avoid → ∀ v : Λ, tV ρ (frob q) v = hecke q v
  det_eq : ∀ q, T.Good q → q ∉ avoid → ∀ v : Λ, dV ρ (frob q) v = ((q : O) • diamond q v : Λ)

/-- Good-prime inertia acts trivially in all constituents, away from their levels
and the coefficient prime (tex 9524–9550, 9649–9654, 9773–9797). -/
def UnramifiedConstituents (T : TypeData L ε) (avoid : Finset ℕ)
    (ρ : I → GalQ →* GL (Fin 2) K) : Prop :=
  ∀ q : ℕ, T.Good q → q ∉ avoid → ∀ Q : Ideal Zbar, Q.IsMaximal →
    ((q : ℤ) : Zbar) ∈ Q → ∀ σ ∈ Q.inertia GalQ, ∀ i, ρ i σ = 1

/-- The representations of two Frobenius lifts differ by simultaneous conjugation
on every unramified constituent. -/
theorem frobenius_conj_in_constituents (T : TypeData L ε) {avoid : Finset ℕ}
    {ρ : I → GalQ →* GL (Fin 2) K} (hunr : UnramifiedConstituents T avoid ρ)
    {q : ℕ} (hq : T.Good q) (hqa : q ∉ avoid) {g f : GalQ}
    (hg : IsFrobAt g q) (hf : IsFrobAt f q) :
    ∃ τ : GalQ, ∀ i, ρ i g = ρ i (τ * f * τ⁻¹) := by
  obtain ⟨τ, Q, hQ, hqQ, hι⟩ := IsFrobAt.exists_mul_inv_mem_inertia hq.1 hg hf
  exact ⟨τ, fun i => by
    have h := hunr q hq hqa Q hQ hqQ _ hι i
    rwa [map_mul, map_inv, mul_inv_eq_one] at h⟩

/-- Conjugation invariance of the scalar determinant operator. -/
theorem dV_conj (ρ : I → GalQ →* GL (Fin 2) K) (g h : GalQ) :
    dV ρ (h * g * h⁻¹) = dV ρ g := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [dV, scalarOp_apply, map_mul, map_inv, Units.val_mul]
  rw [Matrix.det_units_conj]

/-- Both scalar operators at any good Frobenius lift agree with those at the chosen lift. -/
theorem operators_eq_at_frobenius (T : TypeData L ε) {avoid : Finset ℕ}
    {ρ : I → GalQ →* GL (Fin 2) K} (hunr : UnramifiedConstituents T avoid ρ)
    {q : ℕ} (hq : T.Good q) (hqa : q ∉ avoid) {g f : GalQ}
    (hg : IsFrobAt g q) (hf : IsFrobAt f q) :
    tV ρ g = tV ρ f ∧ dV ρ g = dV ρ f := by
  obtain ⟨τ, hτ⟩ := frobenius_conj_in_constituents T hunr hq hqa hg hf
  rw [← tV_conj ρ f τ, ← dV_conj ρ f τ]
  constructor
  · apply LinearMap.ext
    intro v
    funext i
    simp only [tV, scalarOp_apply, hτ i]
  · apply LinearMap.ext
    intro v
    funext i
    simp only [dV, scalarOp_apply, hτ i]

variable [TopologicalSpace K]

/-- Pointwise continuity on the lattice, supplied by the constituent representations
(tex 9666–9668, 9762–9767). -/
structure ContinuousOperators (ρ : I → GalQ →* GL (Fin 2) K)
    (Λ : Submodule O (I → K)) : Prop where
  trace : ∀ v : Λ, Continuous fun g => tV ρ g v
  det : ∀ v : Λ, Continuous fun g => dV ρ g v

/-- Continuity of the constituent matrix entries gives both operator continuity
hypotheses (tex 9666–9668, 9762–9767). -/
theorem continuousOperators_of_matrix [IsTopologicalRing K]
    {ρ : I → GalQ →* GL (Fin 2) K} {Λ : Submodule O (I → K)}
    (hρ : ∀ i, Continuous fun g => ((ρ i g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) :
    ContinuousOperators ρ Λ := by
  constructor
  · intro v
    apply continuous_pi
    intro i
    simp only [tV, scalarOp_apply, Matrix.trace_fin_two]
    exact (((hρ i).matrix_elem 0 0).add ((hρ i).matrix_elem 1 1)).mul continuous_const
  · intro v
    apply continuous_pi
    intro i
    simp only [dV, scalarOp_apply, Matrix.det_fin_two]
    exact ((((hρ i).matrix_elem 0 0).mul ((hρ i).matrix_elem 1 1)).sub
      (((hρ i).matrix_elem 0 1).mul ((hρ i).matrix_elem 1 0))).mul continuous_const

/-- Continuous operators preserving the lattice on the dense Frobenius test set preserve
it everywhere (tex 9666–9668). -/
theorem stable_operators (T : TypeData L ε) {avoid : Finset ℕ} {frob : ℕ → GalQ}
    {ρ : I → GalQ →* GL (Fin 2) K} {Λ : Submodule O (I → K)}
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hΛ : IsClosed (Λ : Set (I → K))) (hcont : ContinuousOperators ρ Λ)
    (hunr : UnramifiedConstituents T avoid ρ) (ops : GoodOperators T avoid frob ρ Λ) :
    (∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) ∧ (∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ) := by
  have dense := dense_frobeniusTests T avoid
  constructor
  · intro g v hv
    refine dense.induction (P := fun k => tV ρ k v ∈ Λ) ?_ (hΛ.preimage (hcont.trace ⟨v, hv⟩)) g
    rintro h ⟨q, hq, hqa, hf⟩
    have eq := (operators_eq_at_frobenius T hunr hq hqa hf (hfrob q hq)).1
    change tV ρ h v ∈ Λ
    rw [eq, ops.trace_eq q hq hqa ⟨v, hv⟩]
    exact (ops.hecke q ⟨v, hv⟩).2
  · intro g v hv
    refine dense.induction (P := fun k => dV ρ k v ∈ Λ) ?_ (hΛ.preimage (hcont.det ⟨v, hv⟩)) g
    rintro h ⟨q, hq, hqa, hf⟩
    have eq := (operators_eq_at_frobenius T hunr hq hqa hf (hfrob q hq)).2
    change dV ρ h v ∈ Λ
    rw [eq, ops.det_eq q hq hqa ⟨v, hv⟩]
    exact ((q : O) • ops.diamond q ⟨v, hv⟩).2

#print axioms dense_frobeniusTests
#print axioms frobenius_conj_in_constituents
#print axioms dV_conj
#print axioms operators_eq_at_frobenius
#print axioms continuousOperators_of_matrix
#print axioms stable_operators

end ZInQ.Manuscript.RC.TraceLimits

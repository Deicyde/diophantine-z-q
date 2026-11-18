import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Limits
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Fourier

/-!
# Extending the determinant calculation at positive Fourier indices

Tex 9712–9729. The density argument allows a new avoidance set for each
index. Its conclusion is divisibility of each coefficient in the coefficient
ring; identifying the abstract residue class needs an additional proof.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TraceLimits

open AddressGenuine
open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]
variable {T : TypeData L ε} {avoid : Finset ℕ} {frob : ℕ → GalQ}
variable {ρ : I → GalQ →* GL (Fin 2) K} {Λ : Submodule O (I → K)}
variable {m : Ideal O}

/-- Fourier formulas required from the genuine form and its undivided corrections
(tex 9655–9662, 9719–9727). The subscripts of the nonzero unary series are positive. -/
structure DeterminantFourierData (ops : GoodOperators T avoid frob ρ Λ) (m : Ideal O) (F : Λ) where
  coeff : ℕ → Λ →ₗ[O] O
  subscripts : Finset ℕ
  pos : ∀ j ∈ subscripts, j ≠ 0
  unary : ℕ → ℕ → O
  hecke_eq : ∀ q, T.Good q → q ∉ avoid → HeckeFourier coeff (ops.hecke q) (ops.diamond q) q
  unary_eq : ∀ j ∈ subscripts, ∀ n, (∀ k : ℕ, n ≠ j * k ^ 2) → unary j n ∈ m
  correction : ∀ r, T.Good r → r ∉ avoid → ∃ a : ℕ → O, ∀ n,
    coeff n ((r : O) • ops.diamond r F - F) - ∑ j ∈ subscripts, a j * unary j n ∈ m

variable [TopologicalSpace K] [IsTopologicalRing K] [TopologicalSpace O]

/-- The determinant identity holds coefficientwise at every positive index for
arbitrary Galois elements, under the Fourier formulas of the genuine forms
(tex 9712–9729). This is the coefficientwise identity of the manuscript. -/
theorem detOrbit_coefficient
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hcont : ContinuousOperators ρ Λ) (hunr : UnramifiedConstituents T avoid ρ)
    (ops : GoodOperators T avoid frob ρ Λ)
    (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ)
    (hsd : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ)
    (F : Λ) (D : DeterminantFourierData ops m F) (hm : IsClosed (m : Set O))
    (n : ℕ) (hn : n ≠ 0) (hcoeff : Continuous (D.coeff n))
    (u v : GalQ) :
    D.coeff n ⟨dV ρ u (tV ρ v F) - tV ρ v F,
      Λ.sub_mem (hsd u _ (hst v _ F.2)) (hst v _ F.2)⟩ ∈ m := by
  classical
  let trace (g : GalQ) (x : Λ) : Λ := ⟨tV ρ g x, hst g _ x.2⟩
  let det (g : GalQ) (x : Λ) : Λ := ⟨dV ρ g x, hsd g _ x.2⟩
  have hc (g h : GalQ) : det g (trace h F) - trace h F = trace h (det g F - F) := by
    apply Subtype.ext
    funext i
    simp only [trace, det, tV, dV, Submodule.coe_sub, Pi.sub_apply, scalarOp_apply]
    ring
  change D.coeff n (det u (trace v F) - trace v F) ∈ m
  refine (dense_frobeniusTests T avoid).induction
    (P := fun u => D.coeff n (det u (trace v F) - trace v F) ∈ m) ?_
    (hm.preimage (hcoeff.comp (((hcont.det (trace v F)).subtype_mk _).sub continuous_const))) u
  rintro g ⟨r, hr, hra, hfr⟩
  rw [hc]
  let A := avoid ∪ n.primeFactors ∪ D.subscripts.biUnion Nat.primeFactors
  refine (dense_frobeniusTests T A).induction
    (P := fun v => D.coeff n (trace v (det g F - F)) ∈ m) ?_
    (hm.preimage (hcoeff.comp ((hcont.trace (det g F - F)).subtype_mk _))) v
  rintro h ⟨q, hq, hqA, hfq⟩
  have hqa : q ∉ avoid := fun e =>
    hqA (Finset.mem_union_left _ (Finset.mem_union_left _ e))
  have hqn : ¬ q ∣ n := fun e => hqA
    (Finset.mem_union_left _ (Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hq.1, e, hn⟩)))
  have hqj (j : ℕ) (hj : j ∈ D.subscripts) : ¬ q ∣ j := fun e => hqA
    (Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨j, hj, Nat.mem_primeFactors.2 ⟨hq.1, e, D.pos j hj⟩⟩))
  have ed : det g F = (r : O) • ops.diamond r F := by
    apply Subtype.ext
    change dV ρ g F = _
    rw [(operators_eq_at_frobenius T hunr hr hra hfr (hfrob r hr)).2, ops.det_eq r hr hra]
  have et (x : Λ) : trace h x = ops.hecke q x := by
    apply Subtype.ext
    change tV ρ h x = _
    rw [(operators_eq_at_frobenius T hunr hq hqa hfq (hfrob q hq)).1, ops.trace_eq q hq hqa]
  rw [ed, et, D.hecke_eq q hq hqa, ite_eq_right hqn, add_zero]
  obtain ⟨a, ha⟩ := D.correction r hr hra
  have hsum : (∑ j ∈ D.subscripts, a j * D.unary j (q * n)) ∈ m :=
    m.sum_mem fun j hj => m.mul_mem_left _ (D.unary_eq j hj _ (fresh_mul_ne_unary hq.1 hqn (hqj j hj)))
  exact (m.sub_mem_iff_left hsum).1 (ha (q * n))

#print axioms detOrbit_coefficient

end ZInQ.Manuscript.RC.TraceLimits

import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Fourier
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Limits

/-!
# Diamond operators on coefficientwise reduced expansions

The manuscript gives the good Hecke formula and approximates traces at each index
using primes avoiding that index (tex 9660–9668, 9712–9717). This implies trace
congruence on the whole integral module. Testing the Hecke formula at a multiple of
a fixed good prime then gives diamond congruence (on-the-spot, provenance (c)).
-/

namespace ZInQ.Manuscript.RC.Diamond

open AddressGenuine PrintsArith TraceLimits
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]
variable [TopologicalSpace K] [TopologicalSpace O]
variable {T : TypeData L ε} {avoid : Finset ℕ} {frob : ℕ → GalQ}
variable {ρ : I → GalQ →* GL (Fin 2) K} {Λ : Submodule O (I → K)} {m : Ideal O}

/-- At each positive index `n` the trace can be tested on Frobenius at primes
not dividing `n`. Thus trace congruence needs no prior diamond congruence. -/
theorem trace_congruence_of_fresh_hecke
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hcont : ContinuousOperators ρ Λ) (hunr : UnramifiedConstituents T avoid ρ)
    (ops : GoodOperators T avoid frob ρ Λ)
    (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ)
    (coeff : ℕ → Λ →ₗ[O] O)
    (hhecke : ∀ q, T.Good q → q ∉ avoid →
      HeckeFourier coeff (ops.hecke q) (ops.diamond q) q)
    (hm : IsClosed (m : Set O)) (hcoeff : ∀ n, Continuous (coeff n))
    (v : Λ) (hv : ∀ n, n ≠ 0 → coeff n v ∈ m) (g : GalQ) :
    ∀ n, n ≠ 0 → coeff n ⟨tV ρ g v, hst g _ v.2⟩ ∈ m := by
  intro n hn
  refine (dense_frobeniusTests T (avoid ∪ n.primeFactors)).induction
    (P := fun g => coeff n ⟨tV ρ g v, hst g _ v.2⟩ ∈ m) ?_
    (hm.preimage ((hcoeff n).comp ((hcont.trace v).subtype_mk _))) g
  rintro h ⟨q, hq, hqA, hfq⟩
  have hqa : q ∉ avoid := fun e => hqA (Finset.mem_union_left _ e)
  have hqn : ¬ q ∣ n := fun e => hqA
    (Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hq.1, e, hn⟩))
  have et : (⟨tV ρ h v, hst h _ v.2⟩ : Λ) = ops.hecke q v := by
    apply Subtype.ext
    change tV ρ h v = _
    rw [(operators_eq_at_frobenius T hunr hq hqa hfq (hfrob q hq)).1,
      ops.trace_eq q hq hqa]
  show coeff n ⟨tV ρ h v, hst h _ v.2⟩ ∈ m
  rw [et, hhecke q hq hqa n v, ite_eq_right hqn, add_zero]
  exact hv _ (Nat.mul_ne_zero hq.1.ne_zero hn)

/-- The exact `hdiam` input of `TraceLimits.buildConstituentModel`. At the
index `q * n`, subtracting the coefficient at `q * (q * n)` from that of
the Hecke translate isolates `q` times the diamond coefficient at `n`.
Every good prime is odd, so its image modulo `m` is one. -/
theorem hdiam_of_hecke
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hcont : ContinuousOperators ρ Λ) (hunr : UnramifiedConstituents T avoid ρ)
    (ops : GoodOperators T avoid frob ρ Λ)
    (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ)
    (coeff : ℕ → Λ →ₗ[O] O)
    (hhecke : ∀ q, T.Good q → q ∉ avoid →
      HeckeFourier coeff (ops.hecke q) (ops.diamond q) q)
    (hm2 : (2 : O) ∈ m) (hm : IsClosed (m : Set O))
    (hcoeff : ∀ n, Continuous (coeff n)) :
    ∀ q, T.Good q → q ∉ avoid → ∀ v : Λ, (∀ n, n ≠ 0 → coeff n v ∈ m) →
      ∀ n, n ≠ 0 → coeff n (ops.diamond q v) ∈ m := by
  intro q hq hqa v hv n hn
  have hqn : q * n ≠ 0 := Nat.mul_ne_zero hq.1.ne_zero hn
  have ht := trace_congruence_of_fresh_hecke hfrob hcont hunr ops hst coeff hhecke hm hcoeff
    v hv (frob q) (q * n) hqn
  have et : (⟨tV ρ (frob q) v, hst _ _ v.2⟩ : Λ) = ops.hecke q v :=
    Subtype.ext (ops.trace_eq q hq hqa v)
  rw [et, hhecke q hq hqa, ite_eq_left (dvd_mul_right q n),
    Nat.mul_div_cancel_left n hq.1.pos] at ht
  have hd := (m.add_mem_iff_right (hv _ (Nat.mul_ne_zero hq.1.ne_zero hqn))).mp ht
  obtain ⟨k, hk⟩ := hq.1.odd_of_ne_two hq.ne_two
  have hq' : (q : O) - 1 ∈ m := by
    have he := congrArg (fun j : ℕ => (j : O)) hk
    push_cast at he
    rw [he, add_sub_cancel_right]
    exact m.mul_mem_right _ hm2
  have h := m.sub_mem hd (m.mul_mem_right (coeff n (ops.diamond q v)) hq')
  simpa only [sub_mul, one_mul, sub_sub_cancel] using h

#print axioms trace_congruence_of_fresh_hecke
#print axioms hdiam_of_hecke

end ZInQ.Manuscript.RC.Diamond

import ZInQKernel.Contrib.OneProof.RC.EvenJoin.OneSeedLattice

/-! The coefficientwise two-fresh argument with one active seed. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine PrintsArith TraceLimits ThetaCoeff
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

set_option maxHeartbeats 900000

variable {I K O G L : Type} [Fintype I] [Field K] [CommRing O] [Algebra O K]
variable [Group G] [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {U : Finset ℕ}
variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
variable [TopologicalSpace O] [CompactSpace O] [ContinuousSMul O K] [IsNoetherianRing O]
variable {frob : ℕ → GalQ} (A : Basis I K G (Test T U)) (z : I → K) (ρ₀ : Attachment A frob)
variable (hinj : Function.Injective (algebraMap O K))
variable (hz : ∀ u n, A.eval n (A.diamond u z) ∈ integralRange (O := O))

private theorem dense_pair_avoid (avoid : Finset ℕ) :
    Dense {x : GalQ × GalQ | ∃ q r, T.Good q ∧ T.Good r ∧ q ∉ avoid ∧ r ∉ avoid ∧
      q ≠ r ∧ IsFrobAt x.1 q ∧ IsFrobAt x.2 r} := by
  refine dense_iff_inter_open.mpr ?_
  rintro W hW ⟨⟨g, h⟩, hgh⟩
  obtain ⟨V₁, V₂, hV₁, hV₂, hg, hh, hVW⟩ := isOpen_prod_iff.mp hW g h hgh
  obtain ⟨x, ⟨q, hq, hqa, hx⟩, hxV⟩ :=
    (dense_frobeniusTests T avoid).exists_mem_open hV₁ ⟨g, hg⟩
  obtain ⟨y, ⟨r, hr, hra, hy⟩, hyV⟩ :=
    (dense_frobeniusTests T (insert q avoid)).exists_mem_open hV₂ ⟨h, hh⟩
  exact ⟨(x, y), hVW ⟨hxV, hyV⟩, q, r, hq, hr, hqa,
    fun e => hra (Finset.mem_insert_of_mem e),
    fun e => hra (e ▸ Finset.mem_insert_self q avoid), hx, hy⟩

/-- To get the entire two-trace orbit modulo the maximal ideal, it suffices
to know the coefficients of the seed at indices with two specified fresh
prime factors, each of exponent one. -/
theorem oneSeed_twoTrace {m : Ideal O}
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hclosed : IsClosed (m : Set O))
    (he : Topology.IsEmbedding (algebraMap O K))
    (hcoef : ∀ (q r n : ℕ), n ≠ 0 → T.Good q → T.Good r →
      q ∉ U → r ∉ U → q ≠ r → ¬ q ∣ n → ¬ r ∣ n →
      oneCoeff A z hinj hz (r * (q * n)) (oneLatSeed A z U) ∈ m) :
    let st := (oneLattice_stable A z ρ₀ hinj hz hfrob).1
    ∀ g h (n : ℕ), n ≠ 0 → oneCoeff A z hinj hz n
      (latT ρ₀.ρ _ st g (latT ρ₀.ρ _ st h (oneLatSeed A z U))) ∈ m := by
  intro st g h n hn
  let V := oneLatSeed A (O := O) z U
  let tr (g : GalQ) (x : oneLattice A (O := O) z) : oneLattice A (O := O) z :=
    latT ρ₀.ρ _ st g x
  have ht : Continuous fun x : GalQ × GalQ => tV ρ₀.ρ x.1 (tV ρ₀.ρ x.2 V) := by
    apply continuous_pi
    intro i
    let c (g : GalQ) := ((ρ₀.ρ i g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace
    have hc : Continuous c := by
      simp only [c, Matrix.trace_fin_two]
      exact ((ρ₀.continuous i).matrix_elem 0 0).add ((ρ₀.continuous i).matrix_elem 1 1)
    change Continuous fun x : GalQ × GalQ => c x.1 * (c x.2 * (V : I → K) i)
    exact (hc.comp continuous_fst).mul ((hc.comp continuous_snd).mul continuous_const)
  have hc : Continuous fun x : GalQ × GalQ => oneCoeff A z hinj hz n (tr x.1 (tr x.2 V)) :=
    (A.hcoeff (oneSeed z) hinj (oneSeed_integral A z hz) he n).comp (ht.subtype_mk _)
  let avoid := U ∪ n.primeFactors
  change oneCoeff A z hinj hz n (tr g (tr h V)) ∈ m
  refine (dense_pair_avoid (T := T) avoid).induction
    (P := fun x => oneCoeff A z hinj hz n (tr x.1 (tr x.2 V)) ∈ m)
    ?_ (hclosed.preimage hc) (g, h)
  rintro ⟨x, y⟩ ⟨q, r, hq, hr, hqa, hra, hqr, hx, hy⟩
  have hout {p : ℕ} (hp : p ∉ avoid) : p ∉ U := fun e =>
    hp (Finset.mem_union_left _ e)
  have hnp {p : ℕ} (hp : T.Good p) (hpa : p ∉ avoid) : ¬ p ∣ n := fun hd =>
    hpa (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp.1, hd, hn⟩))
  have hrqn : ¬ r ∣ q * n := fun hd => (hr.1.dvd_mul.mp hd).elim
    (fun hd => hqr ((Nat.prime_dvd_prime_iff_eq hr.1 hq.1).mp hd).symm) (hnp hr hra)
  let ops := oneOps A z ρ₀ (O := O)
  have htr {p : ℕ} {σ : GalQ} (hp : T.Good p) (hpa : p ∉ avoid)
      (hσ : IsFrobAt σ p) (v : oneLattice A (O := O) z) : tr σ v = ops.hecke p v := by
    apply Subtype.ext
    change tV ρ₀.ρ σ v = _
    rw [(operators_eq_at_frobenius T ρ₀.unramified hp (hout hpa) hσ (hfrob p hp)).1,
      ops.trace_eq p hp (hout hpa)]
  change oneCoeff A z hinj hz n (tr x (tr y V)) ∈ m
  rw [htr hr hra hy, htr hq hqa hx, oneCoeff_hecke A z ρ₀ hinj hz q hq (hout hqa),
    ite_eq_right (hnp hq hqa), add_zero, oneCoeff_hecke A z ρ₀ hinj hz r hr (hout hra),
    ite_eq_right hrqn, add_zero]
  exact hcoef q r n hn hq hr (hout hqa) (hout hra) hqr (hnp hq hqa) (hnp hr hra)

end ZInQ.Manuscript.RC.EvenJoin

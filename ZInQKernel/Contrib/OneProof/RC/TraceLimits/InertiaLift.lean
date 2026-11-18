import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Algebra.Squarefree.Basic

/-!
# Lifting inertia through a profinite invariant subgroup

On-the-spot, provenance (c), for tex 9748–9750. This is the profinite version
of Mathlib's `Ideal.map_inertia_of_surjective`: the proofs of decomposition
transitivity and residue stabilizer surjectivity already have profinite forms.
-/

namespace ZInQ.Manuscript.RC.TraceLimits

open MulAction
open scoped Pointwise

/-- With profinite invariant subgroup, inertia surjects under restriction.
The assumed map on the ambient groups is compatible with the two actions. -/
theorem map_inertia_of_profinite {R S G G' : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Group G'] [MulSemiringAction G S] [MulSemiringAction G' R]
    (f : G →* G') (H : Subgroup G)
    [TopologicalSpace H] [CompactSpace H] [TotallyDisconnectedSpace H] [IsTopologicalGroup H]
    [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul H S] [Algebra.IsInvariant R S H]
    (p : Ideal R) (q : Ideal S) [q.LiesOver p] [q.IsPrime]
    (hf_surj : Function.Surjective f) (hf_ker : H ≤ f.ker)
    (hf : ∀ g x, algebraMap R S (f g • x) = g • algebraMap R S x) :
    (q.inertia G).map f = p.inertia G' := by
  have hk (h : H) : f h = 1 := hf_ker h.2
  have : SMulCommClass H R S := ⟨fun h x y => by
    simp [Algebra.smul_def, H.smul_def, ← hf, hk]⟩
  apply le_antisymm
  · rintro - ⟨g, hg, rfl⟩ x
    simpa [Ideal.over_def q p, map_sub, hf] using hg (algebraMap R S x)
  · intro g hg
    obtain ⟨b, rfl⟩ := hf_surj g
    have hq : (b • q).under R = q.under R := by
      ext x
      rw [Ideal.mem_under, Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← hf, ← Ideal.mem_under,
        ← Ideal.over_def q p, map_inv, ← Ideal.mem_pointwise_smul_iff_inv_smul_mem,
        (MulAction.mem_stabilizer_iff.1 (p.inertia_le_stabilizer hg))]
    have : (b • q).IsPrime := by
      rw [Ideal.pointwise_smul_eq_comap]
      infer_instance
    obtain ⟨a, ha⟩ :=
      Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (G := H) (b • q) q hq
    let c : stabilizer G q := ⟨(a : G) * b, by
      rw [MulAction.mem_stabilizer_iff, mul_smul]
      exact ha.symm⟩
    have hfc : f c = f b := by simp [c, hk]
    let φ : (S ⧸ q) ≃ₐ[R ⧸ p] (S ⧸ q) :=
      { __ := Ideal.Quotient.stabilizerHom q (q.under ℤ) G c
        commutes' x := by
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
          specialize hg x
          rw [← hfc] at hg
          rw [Submodule.mem_toAddSubgroup, Ideal.over_def q p, Ideal.mem_under, map_sub, hf,
            ← Ideal.Quotient.eq] at hg
          simpa }
    obtain ⟨c', hc'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H) p q φ
    let v : stabilizer G q := ⟨c', c'.2⟩⁻¹ * c
    refine ⟨v, ?_, by simp [v, hfc, hk]⟩
    rw [SetLike.mem_coe, Ideal.coe_mem_inertia, ← Ideal.Quotient.ker_stabilizerHom q (q.under ℤ) G,
      MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    rw [AlgEquiv.ext_iff] at hc' ⊢
    assumption

/-- If a squarefree integer has a square root in the ring of integers, every
prime above a divisor of that integer has ramification index at least two. -/
theorem ramificationIdx_two_le_of_square {R : Type*} [CommRing R] [IsDedekindDomain R]
    [FaithfulSMul ℤ R] {q : ℕ} (hq : q.Prime) {d : ℤ} (hd : Squarefree d) (hqd : q ∣ d.natAbs)
    (P : Ideal R) (hP : P.IsPrime) (hP0 : P ≠ ⊥) [P.LiesOver (Ideal.span {(q : ℤ)})]
    (x : R) (hx : x ^ 2 = (d : R)) : 2 ≤ (Ideal.span {(q : ℤ)}).ramificationIdx' P := by
  let p : Ideal ℤ := Ideal.span {(q : ℤ)}
  let D : Ideal ℤ := Ideal.span {d}
  have : Fact q.Prime := ⟨hq⟩
  have hp : p.IsPrime := (Int.ideal_span_isMaximal_of_prime q).isPrime
  have hp0 : p ≠ ⊥ := by
    change Ideal.span {(q : ℤ)} ≠ ⊥
    simpa using hq.ne_zero
  have hD : D ≠ ⊥ := by simpa [D] using hd.ne_zero
  have hqdz : (q : ℤ) ∣ d := Int.natCast_dvd.2 hqd
  have hemp : emultiplicity p D = (1 : ℕ) := by
    apply emultiplicity_eq_of_dvd_of_not_dvd
    · rw [pow_one]
      exact Ideal.span_singleton_dvd_span_singleton_iff_dvd.2 hqdz
    · change ¬ p ^ 2 ∣ D
      rw [show p ^ 2 = Ideal.span {((q : ℤ) ^ 2)} by
        change (Ideal.span {(q : ℤ)}) ^ 2 = _
        rw [pow_two, Ideal.span_singleton_mul_span_singleton, pow_two]]
      rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd, pow_two]
      exact fun h => (Nat.prime_iff_prime_int.1 hq).not_isUnit (hd _ h)
  have hdx : (d : R) ∈ P := by
    rw [← eq_intCast (algebraMap ℤ R) d, ← Ideal.mem_under, ← Ideal.over_def P p]
    exact Ideal.mem_span_singleton.2 hqdz
  have hxP : x ∈ P :=
    (hP.mem_or_mem (by simpa only [← pow_two, hx] using hdx : x * x ∈ P)).elim id id
  have hspan : D.map (algebraMap ℤ R) ≤ P ^ 2 := by
    change (Ideal.span {d}).map (algebraMap ℤ R) ≤ _
    rw [Ideal.map_span, Set.image_singleton, eq_intCast, Ideal.span_singleton_le_iff_mem, ← hx]
    exact Ideal.pow_mem_pow hxP 2
  have hm := (pow_dvd_iff_le_emultiplicity (k := 2)).1 (Ideal.dvd_iff_le.2 hspan)
  rw [Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hD
    (Ideal.prime_of_isPrime hp0 hp).irreducible (Ideal.prime_of_isPrime hP0 hP).irreducible hP0,
    hemp, Nat.cast_one, mul_one] at hm
  exact_mod_cast hm

#print axioms map_inertia_of_profinite
#print axioms ramificationIdx_two_le_of_square

end ZInQ.Manuscript.RC.TraceLimits

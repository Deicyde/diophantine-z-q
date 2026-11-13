import ZInQKernel.Contrib.UnramifiedCocycle.FiniteQuotient

/-!
# Actual odd-degree finite Galois cases by a product cochain

For a finite group of odd order, the literal product `B(g) = ∏ x, ε(g,x)`
trivializes every sign cocycle.  This includes unnormalized cocycles.  Inflation
along the actual finite Galois restriction then handles every odd-degree `L`
over `ℚ`, at every finite prime, without any unramified-quotient assumption.
This is a scoped actual-field result, not the full unramified leaf.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open GlueDescent.B2 GlueDescent.B2Q
open scoped BigOperators

variable {G U : Type*} [Fintype G] [CommGroup U]

/-- A literal finite-product cochain; normalization is not required. -/
def finiteProductCochain (ε : G → G → U) (g : G) : U := ∏ x : G, ε g x

theorem finiteProductCochain_sq (ε : G → G → U) (hs : ∀ g h, ε g h ^ 2 = 1) (g : G) :
    finiteProductCochain ε g ^ 2 = 1 := by
  rw [finiteProductCochain, ← Finset.prod_pow]
  simp [hs]

variable [Group G]

/-- The finite product of the cocycle equation, with the required permutation
of the entire finite index set supplied by left multiplication. -/
theorem finiteProductCochain_mul (ε : G → G → U) (hc : CocycleLaw ε) (g h : G) :
    ε g h ^ Fintype.card G * finiteProductCochain ε (g * h) =
      finiteProductCochain ε g * finiteProductCochain ε h := by
  unfold finiteProductCochain
  calc
    _ = ∏ x : G, ε (g * h) x * ε g h := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ]
      exact mul_comm _ _
    _ = ∏ x : G, ε h x * ε g (h * x) := by
      apply Finset.prod_congr rfl
      intro x _
      exact hc g h x
    _ = (∏ x : G, ε h x) * ∏ x : G, ε g (h * x) := Finset.prod_mul_distrib
    _ = (∏ x : G, ε h x) * ∏ x : G, ε g x := by
      rw [Fintype.prod_equiv (Equiv.mulLeft h) (fun x : G => ε g (h * x))
        (fun x : G => ε g x) (fun _ => rfl)]
    _ = _ := mul_comm _ _

/-- Odd exponents act as the identity on an element with square `1`. -/
theorem sign_pow_odd (a : U) (ha : a ^ 2 = 1) (n : ℕ) (hn : Odd n) : a ^ n = a := by
  obtain ⟨k, hk⟩ := hn
  have hnk : n = 2 * k + 1 := by omega
  rw [hnk, pow_add, pow_mul, ha, one_pow, pow_one, one_mul]

/-- Every sign cocycle on a finite odd-order group has an explicit sign cochain. -/
theorem signCob_finite_odd [TopologicalSpace G] [DiscreteTopology G]
    (hodd : Odd (Fintype.card G)) (ε : G → G → U) (hε : IsSignCocycle ε) : SignCob ε := by
  refine ⟨finiteProductCochain ε, IsLocallyConstant.of_discrete _,
    finiteProductCochain_sq ε hε.2.1, ?_⟩
  intro g h
  have hm := finiteProductCochain_mul ε hε.2.2 g h
  rw [sign_pow_odd (ε g h) (hε.2.1 g h) (Fintype.card G) hodd] at hm
  change ε g h = finiteProductCochain ε g * finiteProductCochain ε h *
    (finiteProductCochain ε (g * h))⁻¹
  exact (eq_mul_inv_iff_mul_eq).2 hm

/-- A genuine odd-degree finite Galois field gives an actual global sign
coboundary, not merely a vanishing class in an abstract cohomology group. -/
theorem signCob_of_odd_degree
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hodd : Odd (Module.finrank ℚ L))
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hi : InflatedFrom L ε) : SignCob ε := by
  let : Fintype (L ≃ₐ[ℚ] L) := AlgEquiv.fintype ℚ L
  have hcard : Odd (Fintype.card (L ≃ₐ[ℚ] L)) := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact hodd
  have hfinite := signCob_finite_odd hcard (finiteCocycle L ε)
    (finiteCocycle_isSignCocycle L ε hε hi)
  have hr : Continuous (finiteRestriction L) := InfiniteGalois.restrictNormalHom_continuous L
  have h := signCob_pull_continuous (finiteRestriction L) hr hfinite
  have he : pull (finiteRestriction L) (finiteCocycle L ε) = ε := by
    funext σ τ
    exact finiteCocycle_apply L ε hi σ τ
  rwa [he] at h

/-- All finite primes, including `2`, are covered in the actual odd-degree case.
No unramifiedness hypothesis is needed for this stronger scoped result. -/
theorem signCob_local_of_odd_degree
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hodd : Odd (Module.finrank ℚ L))
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hi : InflatedFrom L ε) (p : Nat.Primes) :
    SignCob (pull (resp p) ε) :=
  signCob_pull_continuous (resp p) (resp_continuous p) (signCob_of_odd_degree L hodd ε hε hi)

end ZInQ.Contrib.UnramifiedCocycle

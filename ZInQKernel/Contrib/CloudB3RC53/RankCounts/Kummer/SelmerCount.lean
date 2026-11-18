import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.Statements
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.SInteger.SelmerGroup.NumberField
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.SInteger.Rank
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.SInteger.ClassGroup

/-!
# `kummer`, stage K-A: the order of the Selmer group `K(S,2)` (tex 4482–4492)

For an imaginary quadratic field `K` and a finite set `S` of primes,
`|K(S,2)| = 2^{1 + |S| + rk₂ Cl(𝒪_{K,S})}` (`selmerCount_proof : SelmerCount`): the unit term
`𝒪_{K,S}^×/(𝒪_{K,S}^×)²` has `2^{1+|S|}` elements ("the unit rank is `|S_T|` and the roots of unity
contribute one dimension", tex 4488–4489) and the class-group term is `Cl(𝒪_{K,S})[2]`, of order
`2^{rk₂}`. Inputs: Tau Ceti's exact sequence of the Selmer group, the `S`-unit rank, and the
2-rank cardinality identity. Kinds: PROVED.
-/

noncomputable section

open NumberField IsDedekindDomain

namespace ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS

variable (K : Type) [Field K] [NumberField K]

theorem unitRank_eq_zero (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) :
    Module.finrank ℤ (Additive (𝓞 K)ˣ) = 0 := by
  rw [NumberField.Units.finrank_eq, NumberField.Units.rank,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  have h := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [NumberField.nrRealPlaces_eq_zero_iff.mpr hTC, hK2] at h
  rw [NumberField.nrRealPlaces_eq_zero_iff.mpr hTC]
  omega

theorem card_rootsOfUnity_two : Nat.card (rootsOfUnity 2 K) = 2 :=
  (IsPrimitiveRoot.neg_one 0 (by norm_num)).card_rootsOfUnity

theorem card_sUnit_quot (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    Nat.card (S.unit K ⧸ (powMonoidHom 2 : S.unit K →* S.unit K).range) = 2 ^ (1 + S.ncard) := by
  have : Finite S := hS.to_subtype
  have h := TauCeti.relIndex_range_powMonoidHom_sUnits (𝓞 K) K S 2
  rw [Subgroup.relIndex, Set.range_powMonoidHom_subgroupOf_unit, unitRank_eq_zero K hK2 hTC,
    card_rootsOfUnity_two, zero_add, Nat.card_coe_set_eq] at h
  rw [← Subgroup.index, h, pow_add, pow_one, mul_comm]

theorem card_classGroup_twoTorsion (S : Set (HeightOneSpectrum (𝓞 K))) :
    Nat.card (powMonoidHom 2 : ClassGroup (S.integer K) →* ClassGroup (S.integer K)).ker =
      2 ^ TauCeti.twoRank (ClassGroup (S.integer K)) := by
  rw [← TauCeti.card_elementaryTwoQuotient_eq_two_pow_twoRank,
    TauCeti.card_elementaryTwoQuotient_eq_card_twoTorsion]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [MonoidHom.mem_ker])

/-- **The count of `K(S,2)`** (tex 4482–4492): `|K(S,2)| = 2^{1 + |S| + rk₂ Cl(𝒪_{K,S})}` for an
imaginary quadratic field `K` and a finite set `S` of primes. PROVED from Tau Ceti's exact sequence
`1 → 𝒪_S^×/(𝒪_S^×)² → K(S,2) → Cl(𝒪_{K,S})[2] → 1`, the `S`-unit rank (Dirichlet: the unit rank
of `K` is `0`, `μ₂(K) = {±1}`), and `|Cl/Cl²| = |Cl[2]|`. -/
theorem selmerCount_proof : SelmerCount := by
  intro K _ _ hK2 hTC S hS
  set G := IsDedekindDomain.selmerGroup (R := 𝓞 K) (K := K) (S := S) (n := 2)
  let g := IsDedekindDomain.selmerGroup.toClassGroup K S 2
  let f := IsDedekindDomain.selmerGroup.fromSUnitLift K S 2
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at hcard
  have hrange : Nat.card g.range = 2 ^ TauCeti.twoRank (ClassGroup (S.integer K)) := by
    rw [IsDedekindDomain.selmerGroup.range_toClassGroup]
    exact card_classGroup_twoTorsion K S
  have hker : Nat.card g.ker = 2 ^ (1 + S.ncard) := by
    rw [IsDedekindDomain.selmerGroup.ker_toClassGroup,
      ← IsDedekindDomain.selmerGroup.range_fromSUnitLift,
      ← Nat.card_congr (MonoidHom.ofInjective
        (IsDedekindDomain.selmerGroup.fromSUnitLift_injective K S 2)).toEquiv]
    exact card_sUnit_quot K hK2 hTC S hS
  rw [hcard, hrange, hker, ← pow_add, add_comm]

end ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS

import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.Statements
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Kummer.Ramification
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.SelmerGroup
import ZInQKernel.Contrib.TauCeti.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# `kummer`, stage `⊇`: square roots of Selmer classes lie in `K_S`

Manuscript `diophantine_zq.tex`, tex 4482–4492 (Kummer theory for `G_{K,S_T}`). For `S` containing
the primes above `2` and `a ∈ K(S,2)`, every square root `x` of `a` in `K̄` lies in
`K_S = unramifiedOutside K S` (`sqrtMemOfSelmer_proof : SqrtMemOfSelmer`).

* `isUnramifiedOutside_iff`: for a finite subextension `L`, the ramification-index condition
  `IsUnramifiedOutside K S L` (primes of the integral closure of `𝒪_K` in `L`) is Mathlib's
  `Algebra.IsUnramifiedIn (𝒪_L) v` at every `v ∉ S`; via `ramificationIdx_comap_symm`
  (ramification indices are invariant under algebra isomorphisms) and
  `IsIntegralClosure.equiv`.
* `normal_adjoin_sqrt`: `K(√a)` is the splitting field of `X² − a`.
* `isUnramifiedIn_of_sqrt_unit`: Tau Ceti's radical criterion
  (`TauCeti.NumberField.isUnramifiedIn_of_pow_eq_of_valuation_eq_one`).

Kinds: PROVED.
-/

open NumberField IsDedekindDomain
noncomputable section
namespace ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS

section Transport
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Ramification indices are invariant under algebra isomorphisms: for `e : A ≃ₐ[R] B`, the prime
`q` of `A` and its image `e(q) = q.comap e⁻¹` of `B` have the same ramification index over `R`. -/
theorem ramificationIdx_comap_symm (e : A ≃ₐ[R] B) (q : Ideal A) :
    (q.comap (e.symm : B →+* A)).ramificationIdx R = q.ramificationIdx R := by
  have hback : (q.comap (e.symm : B →+* A)).comap (e : A →+* B) = q := by
    rw [Ideal.comap_comap]
    convert Ideal.comap_id q
    ext a; simp
  by_cases hq : q.IsPrime; swap
  · have : ¬ (q.comap (e.symm : B →+* A)).IsPrime := fun h => hq (by
      have := Ideal.comap_isPrime (e : A →+* B) (q.comap (e.symm : B →+* A))
      rwa [hback] at this)
    rw [Ideal.ramificationIdx_of_not_isPrime _ _ hq, Ideal.ramificationIdx_of_not_isPrime _ _ this]
  · set q' := q.comap (e.symm : B →+* A) with hq'def
    have hq' : q'.IsPrime := Ideal.comap_isPrime _ q
    let p := q.under R
    have : q.LiesOver p := ⟨rfl⟩
    have : q'.LiesOver p := ⟨by
      simp only [Ideal.under, p, q', Ideal.comap_comap]
      congr 1
      ext r; simp⟩
    let Sq := Localization.AtPrime q
    let Sq' := Localization.AtPrime q'
    let f : Sq ≃ₐ[R] Sq' := Localization.localAlgEquiv q q' e hback.symm
    let : Algebra Sq Sq' := f.toRingHom.toAlgebra
    have : IsScalarTower R Sq Sq' := IsScalarTower.of_algHom f.toAlgHom
    let g : (Sq ⧸ p.map (algebraMap R Sq)) ≃ₐ[Sq] Sq' ⧸ p.map (algebraMap R Sq') :=
      Ideal.quotientEquivAlg _ _ (AlgEquiv.ofBijective (Algebra.ofId Sq Sq') f.bijective)
        (by
          rw [IsScalarTower.algebraMap_eq R Sq Sq', ← Ideal.map_map]
          rfl)
    rw [Ideal.ramificationIdx_eq p q, Ideal.ramificationIdx_eq p q',
      g.toLinearEquiv.length_eq, Module.length_eq_of_surjective f.surjective]
end Transport

section Transport2
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

theorem liesOver_comap_symm (e : A ≃ₐ[R] B) {Q : Ideal A} {p : Ideal R} (h : Q.LiesOver p) :
    (Q.comap (e.symm : B →+* A)).LiesOver p := ⟨by
  rw [h.over]
  simp only [Ideal.under, Ideal.comap_comap]
  congr 1
  ext r; simp⟩

/-- Transport of "every prime over `p` has ramification index one" along an algebra isomorphism. -/
theorem forall_ramificationIdx_eq_one_of_equiv (e : A ≃ₐ[R] B) (p : Ideal R)
    (h : ∀ P : Ideal B, P.IsPrime → P.LiesOver p → P.ramificationIdx R = 1) :
    ∀ Q : Ideal A, Q.IsPrime → Q.LiesOver p → Q.ramificationIdx R = 1 := by
  intro Q hQ hlo
  rw [← ramificationIdx_comap_symm e Q]
  exact h _ (Ideal.comap_isPrime _ Q) (liesOver_comap_symm e hlo)
end Transport2

variable (K : Type) [Field K] [NumberField K]

/-- A finite subextension of `K̄/K` is a number field. -/
instance numberField_of_finiteDimensional (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] : NumberField L :=
  @NumberField.mk _ _ inferInstance (Module.Finite.trans K L)

/-- The integral closure of `𝒪_K` in a finite subextension `L` is `𝒪_L`. -/
def integralClosureEquiv (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] :
    integralClosure (𝓞 K) L ≃ₐ[𝓞 K] 𝓞 L :=
  IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)

/-- **Unramified outside `S` in the sense of `K_S` is Mathlib's `Algebra.IsUnramifiedIn`** at
every `v ∉ S` (tex 4482–4492). PROVED. -/
theorem isUnramifiedOutside_iff (S : Set (HeightOneSpectrum (𝓞 K)))
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] :
    IsUnramifiedOutside K S L ↔ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal := by
  constructor
  · intro h v hv
    rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
    intro P _ hP
    exact forall_ramificationIdx_eq_one_of_equiv (integralClosureEquiv K L).symm v.asIdeal
      (h v hv) P inferInstance hP
  · intro h v hv
    have h' := (Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mp (h v hv))
    exact forall_ramificationIdx_eq_one_of_equiv (integralClosureEquiv K L) v.asIdeal
      (fun P hP hlo => h' P hlo)


open Polynomial in
omit [NumberField K] in
/-- `K(√a)` is normal over `K`: it is the splitting field of `X² − a`. -/
theorem normal_adjoin_sqrt {a : K} (x : AlgebraicClosure K) (hx : x ^ 2 = algebraMap K _ a) :
    Normal K (IntermediateField.adjoin K {x}) := by
  set p : K[X] := X ^ 2 - C a
  have hp0 : p ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) a
  have hroot : ∀ z : AlgebraicClosure K, z ∈ p.rootSet (AlgebraicClosure K) ↔ z ^ 2 = x ^ 2 := by
    intro z
    rw [mem_rootSet, hx]
    simp [p, hp0, sub_eq_zero]
  have hsplit : (p.map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  have := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hN : Normal K (IntermediateField.adjoin K (p.rootSet (AlgebraicClosure K))) :=
    Normal.of_isSplittingField p
  have heq : IntermediateField.adjoin K (p.rootSet (AlgebraicClosure K)) =
      IntermediateField.adjoin K {x} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((hroot z).mp hz) with rfl | rfl
      · exact IntermediateField.mem_adjoin_simple_self K z
      · exact neg_mem (IntermediateField.mem_adjoin_simple_self K x)
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin K _ ((hroot x).mpr rfl)
  rw [← heq]
  exact hN

/-- A radical of a `v`-unit generates a field unramified at `v ∤ 2`. -/
theorem isUnramifiedIn_of_sqrt_unit {u : K} (y : AlgebraicClosure K)
    (hy : y ^ 2 = algebraMap K _ u) {v : HeightOneSpectrum (𝓞 K)} (h2 : (2 : 𝓞 K) ∉ v.asIdeal)
    (hu : v.valuation K u = 1) (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] (hL : IntermediateField.adjoin K {y} = L) :
    Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal := by
  subst hL
  refine TauCeti.NumberField.isUnramifiedIn_of_pow_eq_of_valuation_eq_one
    (α := IntermediateField.AdjoinSimple.gen K y)
    (IntermediateField.adjoin_adjoinSimple_gen_eq_top y) (n := 2) (a := u) ?_ (by exact_mod_cast h2) hu
  apply Subtype.ext
  simp [IntermediateField.AdjoinSimple.coe_gen, hy]

/-- **`SqrtMemOfSelmer`** (tex 4482–4492, the inclusion `K(S,2) → H¹(G_{K,S}, 𝔽₂)`): a square
root of a Selmer class `a ∈ K(S,2)` lies in `K_S`, when `S` contains the primes above `2`.
`K(√a)` is finite and normal, and at `v ∉ S` the valuation of `a` is even, so `a = u·c⁻²` with `u`
a `v`-unit and `K(√a) = K(√u)` is unramified at `v ∤ 2` (Tau Ceti's radical criterion). PROVED. -/
theorem sqrtMemOfSelmer_proof : SqrtMemOfSelmer := by
  intro K _ _ S hS2 a x hx hsel
  set L := IntermediateField.adjoin K {x} with hLdef
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hint
  have hN : Normal K L := normal_adjoin_sqrt K x hx
  have hU : IsUnramifiedOutside K S L := by
    rw [isUnramifiedOutside_iff]
    intro v hv
    have h2 : (2 : 𝓞 K) ∉ v.asIdeal := fun h => hv (hS2 v h)
    have hdvd : ((2 : ℕ) : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero a) :=
      (HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff v 2 a).mp (hsel v hv)
    obtain ⟨m, hm⟩ := hdvd
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    have hπ0 : π ≠ 0 := by
      intro h; rw [h, map_zero] at hπ; exact (WithZero.zero_ne_coe hπ).elim
    set c : K := π ^ m
    set u : K := (a : K) * c ^ 2
    have hu : v.valuation K u = 1 := by
      have ha : v.valuation K (a : K) = WithZero.exp (2 * m) := by
        push_cast at hm
        rw [← HeightOneSpectrum.valuationOfNeZero_eq]
        have : v.valuationOfNeZero a = Multiplicative.ofAdd (2 * m) := by
          rw [← hm]; rfl
        rw [this]; rfl
      simp only [u, c, map_mul, map_pow, map_zpow₀, hπ, ha]
      rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
      simp
    set y : AlgebraicClosure K := x * algebraMap K _ c
    have hy : y ^ 2 = algebraMap K _ u := by
      simp only [y, u, mul_pow, hx, map_mul, map_pow]
    have hc0 : c ≠ 0 := zpow_ne_zero m hπ0
    have hyL : IntermediateField.adjoin K {y} = L := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact mul_mem (IntermediateField.mem_adjoin_simple_self K x)
          (IntermediateField.algebraMap_mem _ c)
      · rw [hLdef, IntermediateField.adjoin_simple_le_iff]
        have : x = y * algebraMap K _ c⁻¹ := by
          simp only [y, map_inv₀, mul_assoc]
          rw [mul_inv_cancel₀ ((map_ne_zero _).mpr hc0), mul_one]
        rw [this]
        exact mul_mem (IntermediateField.mem_adjoin_simple_self K y)
          (IntermediateField.algebraMap_mem _ _)
    exact isUnramifiedIn_of_sqrt_unit K y hy h2 hu L hyL
  have hle : L ≤ unramifiedOutside K S :=
    le_iSup₂_of_le (f := fun (L : IntermediateField K (AlgebraicClosure K))
      (_ : FiniteDimensional K L ∧ Normal K L ∧ IsUnramifiedOutside K S L) => L) L
      ⟨inferInstance, hN, hU⟩ le_rfl
  exact hle (IntermediateField.mem_adjoin_simple_self K x)

end ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS

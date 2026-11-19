import ZInQKernel.Contrib.OneProof.RC.AppF.Stage
import ZInQKernel.Contrib.OneProof.RC.O12Eisenstein.Characters
import ZInQKernel.Contrib.OneProof.RC.Symbols.Forest
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Open
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.TypeSupport

/-! The fixed coefficient support of one odd theta stage (tex 9471–9483)
and its type (tex 2016–2029). The Eichler level and the exact Fourier sieve
primes are explicit inputs, as neither is indexed in `AppF.ThetaStage`. -/

noncomputable section

namespace ZInQ.Manuscript.RC.TypeCoverage

open AddressGenuine PrintsArith Symbols TraceLimits
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped BigOperators

variable {R : Type*} [CommRing R] (S : AppF.ThetaStage R)

/-- `N` is the Eichler level (tex 8464–8469); `S.m` is `|h_*|` and
`S.ℓ₀` the current reduction prime. `late` consists precisely of the
additional zero-or-retain Fourier sieves of this source. -/
def coefficientSupport (N : ℕ) (late : Finset ℕ) : Finset ℕ :=
  insert 2 (insert S.ℓ₀ (N.primeFactors ∪ S.m.primeFactors ∪ late))

/-- The primes whose coordinates must be added to the old stage type. -/
def extraSupport (N : ℕ) (late : Finset ℕ) (m₁ : ℕ) : Finset ℕ :=
  coefficientSupport S N late \ insert S.ℓ₀ m₁.primeFactors

/-- The conductor of the stationary squareclasses; the moving bit stays separate. -/
def fixedModulus (N : ℕ) (late : Finset ℕ) (m₁ : ℕ) : ℕ :=
  m₁ * ∏ p ∈ extraSupport S N late m₁, p

variable {S} {N : ℕ} {late : Finset ℕ} {m₁ : ℕ}

theorem mem_coefficientSupport {q : ℕ} :
    q ∈ coefficientSupport S N late ↔
      q = 2 ∨ q = S.ℓ₀ ∨ q ∈ N.primeFactors ∨ q ∈ S.m.primeFactors ∨ q ∈ late := by
  simp only [coefficientSupport, Finset.mem_insert, Finset.mem_union, or_assoc]

theorem prime_of_mem_coefficientSupport (hℓ : S.ℓ₀.Prime)
    (hlate : ∀ p ∈ late, Nat.Prime p) {p : ℕ} (hp : p ∈ coefficientSupport S N late) :
    p.Prime := by
  rcases mem_coefficientSupport.mp hp with rfl | rfl | h | h | h
  · exact Nat.prime_two
  · exact hℓ
  · exact (Nat.mem_primeFactors.mp h).1
  · exact (Nat.mem_primeFactors.mp h).1
  · exact hlate p h

theorem dvd_fixedModulus : m₁ ∣ fixedModulus S N late m₁ :=
  dvd_mul_right _ _

theorem fixedModulus_pos (hm : 0 < m₁) (hℓ : S.ℓ₀.Prime)
    (hlate : ∀ p ∈ late, Nat.Prime p) : 0 < fixedModulus S N late m₁ := by
  apply Nat.mul_pos hm
  exact Finset.prod_pos fun p hp =>
    (prime_of_mem_coefficientSupport hℓ hlate (Finset.mem_sdiff.mp hp).1).pos

theorem moving_coprime (hℓ : S.ℓ₀.Prime) (hcop : S.ℓ₀.Coprime m₁)
    (hlate : ∀ p ∈ late, Nat.Prime p) :
    S.ℓ₀.Coprime (fixedModulus S N late m₁) := by
  apply hcop.mul_right
  apply (Nat.Prime.coprime_iff_not_dvd hℓ).2
  intro hd
  obtain ⟨p, hp, hdp⟩ := hℓ.prime.dvd_finsetProd_iff _ |>.mp hd
  have hprime := prime_of_mem_coefficientSupport hℓ hlate (Finset.mem_sdiff.mp hp).1
  have e := (Nat.prime_dvd_prime_iff_eq hℓ hprime).mp hdp
  exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_insert.mpr (Or.inl e.symm))

variable (hm : 0 < m₁) (h8 : 8 ∣ m₁) (hℓ : S.ℓ₀.Prime)
  (hcop : S.ℓ₀.Coprime m₁) (hlate : ∀ p ∈ late, Nat.Prime p)

/-- Refine the existing stage type using only the additional coefficient primes.
Its classes and sign are those of the existing CRT construction. -/
def coveredType :
    TypeData (SqClass (fixedModulus S N late m₁) × ZMod 2)
      (stageSign _ ((show 4 ∣ 8 by decide).trans (h8.trans dvd_fixedModulus))) :=
  stageTypeData _ (fixedModulus_pos hm hℓ hlate)
    ((show 4 ∣ 8 by decide).trans (h8.trans dvd_fixedModulus)) S.ℓ₀ hℓ
    (moving_coprime hℓ hcop hlate)

theorem coveredType_primeFactors :
    (coveredType (N := N) hm h8 hℓ hcop hlate).m.primeFactors =
      m₁.primeFactors ∪ coefficientSupport S N late := by
  change (fixedModulus S N late m₁ * S.ℓ₀).primeFactors = _
  have hprime : ∀ p ∈ extraSupport S N late m₁, p.Prime :=
    fun _ hp => prime_of_mem_coefficientSupport hℓ hlate (Finset.mem_sdiff.mp hp).1
  have hprod : (∏ p ∈ extraSupport S N late m₁, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => (hprime p hp).ne_zero
  rw [Nat.primeFactors_mul (fixedModulus_pos hm hℓ hlate).ne' hℓ.ne_zero,
    fixedModulus, Nat.primeFactors_mul hm.ne' hprod, Nat.primeFactors_prod hprime, hℓ.primeFactors]
  ext p
  simp only [extraSupport, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_singleton, mem_coefficientSupport]
  tauto

theorem good_not_mem_support {q : ℕ} (hq : (coveredType (N := N) hm h8 hℓ hcop hlate).Good q) :
    q ∉ coefficientSupport S N late := by
  intro hqS
  have hf : q ∈ (coveredType (N := N) hm h8 hℓ hcop hlate).m.primeFactors := by
    rw [coveredType_primeFactors]
    exact Finset.mem_union_right _ hqS
  exact (Nat.Prime.coprime_iff_not_dvd hq.1).mp hq.2 (Nat.mem_primeFactors.mp hf).2.1

/-- The refinement removes exactly the coefficient primes from the old good-prime domain. -/
theorem good_iff_old_good_and_outside {q : ℕ} :
    (coveredType (N := N) hm h8 hℓ hcop hlate).Good q ↔
      (stageTypeData m₁ hm ((show 4 ∣ 8 by decide).trans h8) S.ℓ₀ hℓ hcop).Good q ∧
        q ∉ coefficientSupport S N late := by
  let T := coveredType (N := N) hm h8 hℓ hcop hlate
  have hdiv : m₁ * S.ℓ₀ ∣ T.m := Nat.mul_dvd_mul_right dvd_fixedModulus S.ℓ₀
  refine ⟨fun hq => ⟨⟨hq.1, hq.2.of_dvd_right hdiv⟩,
    good_not_mem_support hm h8 hℓ hcop hlate hq⟩, ?_⟩
  rintro ⟨hq, hout⟩
  refine ⟨hq.1, (Nat.Prime.coprime_iff_not_dvd hq.1).2 fun hd => ?_⟩
  have h : q ∈ T.m.primeFactors := hq.1.mem_primeFactors hd T.m_pos.ne'
  rw [coveredType_primeFactors] at h
  rcases Finset.mem_union.mp h with hbase | hsupport
  · exact (Nat.Prime.coprime_iff_not_dvd hq.1).mp hq.2
      ((Nat.mem_primeFactors.mp hbase).2.1.trans (dvd_mul_right m₁ S.ℓ₀))
  · exact hout hsupport

theorem stage_good
    (hstage : ∀ p, p.Prime → p ∉ coefficientSupport S N late → S.Good p) :
    ∀ p, (coveredType (N := N) hm h8 hℓ hcop hlate).Good p → S.Good p :=
  fun p hp => hstage p hp.1 (good_not_mem_support hm h8 hℓ hcop hlate hp)

/-- The sign-preserving projection drops the new stationary coordinates. -/
def projectType (S : AppF.ThetaStage R) (N : ℕ) (late : Finset ℕ) (m₁ : ℕ) :
    SqClass (fixedModulus S N late m₁) × ZMod 2 →+ SqClass m₁ × ZMod 2 :=
  ((sqProj dvd_fixedModulus).comp (AddMonoidHom.fst _ _)).prod (AddMonoidHom.snd _ _)

theorem project_type_of_good {p : ℕ}
    (hp : (coveredType (N := N) hm h8 hℓ hcop hlate).Good p) :
    projectType S N late m₁ ((coveredType (N := N) hm h8 hℓ hcop hlate).typ p) =
      (sqClassOf m₁ p, legBit p S.ℓ₀) := by
  change (sqProj dvd_fixedModulus (sqClassOf (fixedModulus S N late m₁) p), _) = _
  rw [sqProj_sqClassOf _ (isUnit_natCast_of_coprime hp.2.coprime_mul_right_right)]
  rfl

theorem project_sign (x : SqClass (fixedModulus S N late m₁) × ZMod 2) :
    stageSign m₁ ((show 4 ∣ 8 by decide).trans h8) (projectType S N late m₁ x) =
      stageSign (fixedModulus S N late m₁)
        ((show 4 ∣ 8 by decide).trans (h8.trans dvd_fixedModulus)) x :=
  signChar_sqProj dvd_fixedModulus _ x.1

/-- The same primes realize the graph after projecting to the old stage alphabet. -/
theorem project_realization {Γ : Config (SqClass (fixedModulus S N late m₁) × ZMod 2)}
    {f : ℕ → ℕ} (hf : IsReal (coveredType (N := N) hm h8 hℓ hcop hlate) Γ f) :
    IsReal (stageTypeData m₁ hm ((show 4 ∣ 8 by decide).trans h8) S.ℓ₀ hℓ hcop)
      (Γ.mapType (projectType S N late m₁)) f := by
  refine ⟨hf.1, fun v hv => ?_, hf.2.2⟩
  obtain ⟨hgood, htype⟩ := hf.2.1 v hv
  have hdiv : m₁ * S.ℓ₀ ∣ fixedModulus S N late m₁ * S.ℓ₀ :=
    Nat.mul_dvd_mul_right dvd_fixedModulus S.ℓ₀
  refine ⟨⟨hgood.1, hgood.2.of_dvd_right hdiv⟩, ?_⟩
  change (sqClassOf m₁ (f v), legBit (f v) S.ℓ₀) = projectType S N late m₁ (Γ.t v)
  rw [← htype, project_type_of_good hm h8 hℓ hcop hlate hgood]

/-- The character of the refined stationary modulus and the same moving bit. -/
def coveredChar (hm : 0 < m₁) (hℓ : S.ℓ₀.Prime) (hlate : ∀ p ∈ late, Nat.Prime p) :
    GalQ →* Multiplicative (SqClass (fixedModulus S N late m₁) × ZMod 2) :=
  letI : NeZero (fixedModulus S N late m₁) := ⟨(fixedModulus_pos hm hℓ hlate).ne'⟩
  stageChar (fixedModulus S N late m₁) S.ℓ₀

theorem isTypeChar_covered :
    IsTypeChar (coveredType (N := N) hm h8 hℓ hcop hlate) (coveredChar (N := N) hm hℓ hlate) := by
  let : NeZero (fixedModulus S N late m₁) := ⟨(fixedModulus_pos hm hℓ hlate).ne'⟩
  exact isTypeChar_stage _ rfl (fun _ => rfl) hℓ
    (ne_two_of_coprime_even ((show 2 ∣ 8 by decide).trans h8) hcop)

theorem project_coveredChar [NeZero m₁] (g : GalQ) :
    projectType S N late m₁ (Multiplicative.toAdd (coveredChar (N := N) hm hℓ hlate g)) =
      Multiplicative.toAdd (stageChar m₁ S.ℓ₀ g) := by
  let : NeZero (fixedModulus S N late m₁) := ⟨(fixedModulus_pos hm hℓ hlate).ne'⟩
  change (sqProj dvd_fixedModulus (sqMk (cycChar (fixedModulus S N late m₁) g)), _) = _
  rw [sqProj_sqMk, O12Eisenstein.cycChar_unitsMap]
  rfl

theorem openTypeKernel_covered :
    OpenTypeKernel (L := SqClass (fixedModulus S N late m₁) × ZMod 2) (coveredChar (N := N) hm hℓ hlate) := by
  let : NeZero (fixedModulus S N late m₁) := ⟨(fixedModulus_pos hm hℓ hlate).ne'⟩
  exact exists_fixingSubgroup_le_ker_stageChar (fixedModulus S N late m₁) S.ℓ₀

theorem detects_radicals_covered :
    TypeDetectsRadicals (L := SqClass (fixedModulus S N late m₁) × ZMod 2) (coveredChar (N := N) hm hℓ hlate)
      ((coveredType (N := N) hm h8 hℓ hcop hlate).m.primeFactors) := by
  let m := fixedModulus S N late m₁
  have hmpos : 0 < m := fixedModulus_pos hm hℓ hlate
  let : NeZero m := ⟨hmpos.ne'⟩
  have h8m : 8 ∣ m := h8.trans dvd_fixedModulus
  have h4m : 4 ∣ m := (show 4 ∣ 8 by decide).trans h8m
  change TypeDetectsRadicals (L := SqClass m × ZMod 2) (stageChar m S.ℓ₀) ((m * S.ℓ₀).primeFactors)
  rw [Nat.primeFactors_mul hmpos.ne' hℓ.ne_zero, hℓ.primeFactors, Finset.union_singleton]
  apply stageChar_detects_radicals m S.ℓ₀ hℓ.ne_zero m.primeFactors h4m
  intro p hp
  obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hp
  by_cases e : p = 2
  · simpa [e] using h8m
  · have hc : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).2 e
    have hc4 : p.Coprime 4 := by simpa using hc.mul_right hc
    exact hc4.symm.mul_dvd_of_dvd_of_dvd h4m hd

/-- Every finite exclusion leaves a good prime with any prescribed refined type. -/
theorem exists_good_of_type (avoid : Finset ℕ)
    (a : SqClass (fixedModulus S N late m₁) × ZMod 2) :
    ∃ q, (coveredType (N := N) hm h8 hℓ hcop hlate).Good q ∧ q ∉ avoid ∧
      (coveredType (N := N) hm h8 hℓ hcop hlate).typ q = a := by
  obtain ⟨q, hq, _, hqa, hχ, _⟩ :=
    exists_good_frob _ (isTypeChar_covered hm h8 hℓ hcop hlate)
      (fun _ h => chooseFrob_spec frobeniusExists h.1) ∅ avoid (by simp) a (fun _ => 0)
  rw [isTypeChar_covered hm h8 hℓ hcop hlate _ _ hq
    (chooseFrob_spec frobeniusExists hq.1)] at hχ
  exact ⟨q, hq, hqa, congrArg Multiplicative.toAdd hχ⟩

theorem two_mem_type_support :
    2 ∈ (coveredType (N := N) hm h8 hℓ hcop hlate).m.primeFactors := by
  rw [coveredType_primeFactors]
  exact Finset.mem_union_right _ (by simp [coefficientSupport])

#print axioms coveredType
#print axioms coveredChar
#print axioms mem_coefficientSupport
#print axioms prime_of_mem_coefficientSupport
#print axioms dvd_fixedModulus
#print axioms fixedModulus_pos
#print axioms moving_coprime
#print axioms coveredType_primeFactors
#print axioms good_not_mem_support
#print axioms good_iff_old_good_and_outside
#print axioms stage_good
#print axioms project_type_of_good
#print axioms project_sign
#print axioms project_realization
#print axioms isTypeChar_covered
#print axioms project_coveredChar
#print axioms openTypeKernel_covered
#print axioms detects_radicals_covered
#print axioms exists_good_of_type
#print axioms two_mem_type_support

end ZInQ.Manuscript.RC.TypeCoverage
